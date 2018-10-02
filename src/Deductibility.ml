(* Deductibility in the theory of XOR with inverses *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Unification

(* ** Basic definitions *)

type frame = {
    frame_names : string list;
    frame_sigma : expr list;
  }

let not_ground_msg = "The expression is not ground"
let fun_symbol_msg = "The expression cannot contain function symbols"
let xor_symbol_msg = "The expression cannot contain XOR symbols"

(* ** XOR deductibility *)

module Z2 = MakeAlgebra.Z2
module Lin = LinAlg.LinAlg(Z2)

let rec ground_xor_to_list expr =
  match expr with
  | Zero    -> []
  | Const a -> [a]
  | Var _   -> failwith not_ground_msg
  | F(_)    -> failwith fun_symbol_msg
  | XOR(exprs) -> L.map exprs ~f:ground_xor_to_list |> L.concat


let xor_deduce frame expr =
  let knowledge = L.map frame.frame_sigma ~f:ground_xor_to_list in
  let e = ground_xor_to_list expr in
  let constants =
    L.map (expr :: frame.frame_sigma) ~f:atoms |> L.concat
    |> L.map ~f:(function | Const a -> a | _ -> assert false)
    |> L.dedup ~compare:String.compare
  in
  let forbidden = L.filter constants ~f:(L.mem frame.frame_names ~equal:S.equal) in
  let contains_const c l = L.mem l c ~equal:S.equal in
  let matrix = L.map forbidden ~f:(fun c -> L.map knowledge ~f:(contains_const c)) in
  let vector = L.map forbidden ~f:(fun c -> contains_const c e) in
  if L.length matrix = 0 then Some expr
  else
    match Lin.solve matrix vector with
    | None -> None
    | Some matrix ->
       let solution = matrix in
       let sum =
         XOR(
             (L.fold_left (L.zip_exn solution frame.frame_sigma)
                          ~init:expr
                          ~f:(fun sum' (b,e') -> if b then XOR([sum'; e']) else sum')
             ) :: (
               L.filter (L.zip_exn (range 0 (L.length solution)) solution) ~f:(fun (_,s) -> s)
               |> L.map ~f:(fun (i,_) -> Var ("%" ^ (string_of_int (i+1))) )
             )
           )
         |> simplify_expr
       in
       Some sum


(* ** Functions with inverses deductibility *)

let rec get_funs_with_arity expr =
  match expr with
  | Zero | Const _ -> []
  | Var _ -> failwith not_ground_msg
  | XOR(_) -> failwith xor_symbol_msg
  | F(name,_,_,(left,right),inv,_,_) ->
     let other_funs = L.map (left @ right) ~f:get_funs_with_arity |> L.concat in
     (name,inv,L.length left, L.length right) :: other_funs
     |> L.fold_left ~init:[]
            ~f:(fun list (name,inv,n,m) ->
              begin match L.find list ~f:(fun (name',_,_,_) -> name = name') with
              | None -> list @ [(name,inv,n,m)]
              | Some (_,inv',n',m') ->
                 if inv = inv' && n = n' && m = m' then list
                 else failwith ("The arity/invertibility of function " ^ name ^ " functions is not consistent")
              end
            )

let rec get_all_funs expr =
  match expr with
  | Zero | Const _ -> []
  | Var _ -> failwith not_ground_msg
  | XOR(_) -> failwith xor_symbol_msg
  | F(_,_,_,(left,right),_,_,_) ->
     expr :: (L.map (left @ right) ~f:get_all_funs |> L.concat)
     |> L.dedup ~compare:compare_expr

let cluster_funs functions =
  (* This function looks for a sets of invertible F_i(u;t) for all i in 1...len(t) with
     the same u and the same t in case it finds some, it adds the tuple (u,t) to the output *)
  let rec aux output = function
    | [] -> output
    | f :: rest ->
       begin match f with
       | F(name,i,m,(left,right),inv,_,a) ->
          if not inv then aux output rest
          else
            let idxs, others =
              L.fold_left rest
                  ~init:([i],[])
                  ~f:(fun (idxs,others) f' ->
                    begin match f' with
                    | F(name',i',m',(left',right'),inv',_,_) ->
                       if name = name' && m = m' && inv' &&
                           (compare_lists (left @ right) (left' @ right') ~compare:compare_expr ) = 0 then
                         (i' :: idxs, others)
                       else (idxs, others @ [f'])
                    | _ -> assert false
                    end
                  )
            in
            let cmp = Int.compare in
            if (compare_lists (range 0 (L.length right)) (L.sort idxs ~cmp) ~compare:cmp ) = 0 then
              aux (output @ [name,m,(left,right),inv,a]) others
            else aux output others
       | _ -> assert false
       end
  in
  aux [] functions


let fun_deduce frame expr =
  let all_funs = L.map frame.frame_sigma ~f:get_all_funs |> L.concat |> L.dedup ~compare:compare_expr in
  let clusters = cluster_funs all_funs in
  let known_constants =
    L.map (expr :: frame.frame_sigma) ~f:atoms |> L.concat
    |> L.map ~f:(function | Const a -> a | _ -> assert false)
    |> L.dedup ~compare:S.compare
    |> L.filter ~f:(fun n -> not(L.mem frame.frame_names n ~equal:S.equal))
  in
  let indexed_sigma = L.zip_exn (range 0 (L.length frame.frame_sigma)) frame.frame_sigma in
  let rec aux former_attempts expr =
    match L.find indexed_sigma ~f:(fun (_,e) -> equal_expr e expr) with
    | Some (i,_) -> Some (Var ("%" ^ (string_of_int (i+1))))
    | None ->
       if L.mem (Zero :: (L.map known_constants ~f:(fun a -> Const a))) expr ~equal:equal_expr then Some expr
       else if L.mem former_attempts expr ~equal:equal_expr then None
       else
         begin match expr with
         | Zero -> None
         | Var _ -> failwith not_ground_msg
         | XOR(_) -> failwith xor_symbol_msg
         | _ ->
            let solution =
              match expr with
              | F(name,i,m,(left,right),inv,b,a) ->
                 begin match
                   L.fold_left (left @ right)
                      ~init:(Some [])
                      ~f:(fun s e' ->
                        begin match s with
                        | None -> None
                        | Some l ->
                           begin match aux former_attempts e' with
                           | None -> None
                           | Some sol -> Some (l @ [sol])
                           end
                        end
                      )
                 with
                 | None -> None
                 | Some left_right ->
                    let left', right' = split_list_by_idx (L.length left) left_right in
                    Some (F(name,i,m,(left',right'),inv,b,a))
                 end
              | _ -> None
            in
            if some solution then solution
            else
              L.fold_left clusters
                 ~init:None
                 ~f:(fun s (name,m,(left,right),inv,a) ->
                   if some s then s
                   else
                     if L.exists (expr :: former_attempts) ~f:(L.mem left ~equal:equal_expr ) then None
                     else
                       begin match L.find (L.zip_exn (range 0 (L.length right)) right) ~f:(fun (_,e') -> equal_expr e' expr) with
                       | None -> None
                       | Some (i,_) ->
                          let must_be_deductible_without_expr =
                            left @ (L.map (range 0 (L.length right)) ~f:(fun j -> F(name,j,m,(left,right),inv,false,a)))
                          in
                          let deduced =
                            L.fold_left must_be_deductible_without_expr
                               ~init:(Some [])
                               ~f:(fun s e ->
                                 begin match s with
                                 | None -> None
                                 | Some list ->
                                    begin match aux (expr :: former_attempts) e with
                                    | None -> None
                                    | Some sol -> Some (list @ [sol])
                                    end
                                 end
                               )
                          in
                          begin match deduced with
                          | None -> None
                          | Some list ->
                             let left',right' = split_list_by_idx (L.length left) list in
                             Some (F(name,i,inv_mode m,(left',right'),inv,false,a))
                          end
                       end
                 )
         end
  in
  aux [] expr

(* ** Deducibility for the combined theory *)

(* *** Basic definitions *)

type signature = | XOR_sig | F_sig | Bot

(* Two expressions are alien if they have different sign *)
let sign expr =
  match expr with
  | Zero | Const _ | Var _ -> Bot
  | XOR(_) -> XOR_sig
  | F(_) -> F_sig

let factors expr =
  (* The factors are the maximal syntactic subterms of the expression that are alien to it *)
  let rec aux s e =
    if (sign e) <> s then [e]
    else
      L.map (match e with | F(_,_,_,(left,right),_,_,_) -> left@right | XOR(exprs) -> exprs | _ -> [])
         ~f:(fun e' -> aux s e')
      |> L.concat
  in
  aux (sign expr) expr
  |> dedup_preserving_order ~equal:equal_expr

let rec factor_subterms expr =
  [expr] @ (L.map (factors expr) ~f:factor_subterms |> L.concat) |> dedup_preserving_order ~equal:equal_expr

let deduce frame expr =
  let frame = {frame with frame_sigma = L.map frame.frame_sigma ~f:simplify_expr; } in
  let expr = simplify_expr expr in
  let constants =
    L.map (expr :: frame.frame_sigma) ~f:atoms |> L.concat
    |> L.map ~f:(function | Const a -> a | _ -> failwith not_ground_msg)
    |> L.dedup ~compare:S.compare
  in
  safe_fresh_idxs constants;
  let known_constants = L.filter constants ~f:(fun n -> not(L.mem frame.frame_names n ~equal:S.equal)) in

  let sub = L.map (expr :: frame.frame_sigma) ~f:(fun e -> factor_subterms (simplify_expr e))
            |> L.concat
            |> dedup_preserving_order ~equal:equal_expr
  in
  let fun_subterms = L.filter sub ~f:(fun t -> sign t = F_sig) in
  let fun_subterms =
    fun_subterms
    |> safe_sort
         ~cmp:(fun t1 t2 ->
           if equal_expr t1 t2 then 0
           else if expr_is_subterm_of_expr t1 t2 then +1
           else if expr_is_subterm_of_expr t2 t1 then -1
           else 0) (* Int.compare (fun_depth t2) (fun_depth t1)) *)
  in
  let xor_subterms = L.filter sub ~f:(fun t -> sign t = XOR_sig) in
  let xor_subterms =
    xor_subterms
    |> safe_sort
         ~cmp:(fun t1 t2 ->
           if equal_expr t1 t2 then 0
           else if expr_is_subterm_of_expr t1 t2 then +1
           else if expr_is_subterm_of_expr t2 t1 then -1
           else 0 (* match t1,t2 with
                | XOR(l1), XOR(l2) -> Int.compare (L.length l2) (L.length l1)
                | _ -> assert false)*)
         )
  in
  let fun_names = fresh_name_vector (L.length fun_subterms) in
  let xor_names = fresh_name_vector (L.length xor_subterms) in

  let replace list e = L.fold_left list ~init:e ~f:(fun e' (t,n) -> replace_expr e' ~old:t ~by:(Const n)) in
  let fun_replace e = replace (L.zip_exn fun_subterms fun_names) (simplify_expr e) in
  let xor_replace e = replace (L.zip_exn xor_subterms xor_names) (simplify_expr e) in

  let idxs = (range 0 (L.length frame.frame_sigma)) in
  let deduced_terms =
    (L.zip_exn frame.frame_sigma (L.map idxs ~f:(fun i -> Var ("%" ^ (string_of_int (i+1))) ))) @
      (L.map known_constants ~f:(fun c -> (Const c, Const c)))
  in
  let rec aux deduced =
    match L.find deduced ~f:(fun (e,_) -> equal_expr e expr) with
    | Some (_,production) -> Some production
    | None ->
       let missing_subterms = L.filter sub ~f:(fun s -> not(L.exists deduced ~f:(fun (e,_) -> equal_expr e s))) in
       begin
         match L.fold_left missing_subterms
               ~init:None
               ~f:(fun s t ->
                 if some s then s
                 else
                   (* We try to deduce with functions & inverses theory *)
                   let knowledge = L.map deduced ~f:(fun (e,_) -> xor_replace e) in
                   let frame' = { frame_sigma = knowledge; frame_names = xor_names @ frame.frame_names; } in
                   begin match fun_deduce frame' (xor_replace t) with
                     | Some sol ->
                        let safe_names = fresh_name_vector (L.length deduced) |> L.map ~f:(fun n -> Var n) in
                        let prod =
                          L.fold_left (L.zip_exn (range 0 (L.length safe_names)) safe_names)
                             ~init:sol
                             ~f:(fun e' (i,safe) -> replace_expr e' ~old:(Var ("%" ^ (string_of_int (i+1)))) ~by:safe)
                        in
                        Some(t,
                         L.fold_left (L.zip_exn safe_names deduced)
                            ~init:prod
                            ~f:(fun e' (safe,(_,prod)) -> replace_expr e' ~old:safe ~by:prod )
                          )
                     | None ->
                        (* We try to deduce with the XOR theory *)
                        let knowledge = L.map deduced ~f:(fun (e,_) -> fun_replace e) in
                        let frame' = { frame_sigma = knowledge; frame_names = fun_names @ frame.frame_names; } in
                        begin match xor_deduce frame' (fun_replace t) with
                        | Some sol ->
                           let safe_names = fresh_name_vector (L.length deduced) |> L.map ~f:(fun n -> Var n) in
                           let prod =
                             L.fold_left (L.zip_exn (range 0 (L.length safe_names)) safe_names)
                                         ~init:sol
                                         ~f:(fun e' (i,safe) -> replace_expr e' ~old:(Var ("%" ^ (string_of_int (i+1)))) ~by:safe)
                           in
                           Some(t,
                                L.fold_left (L.zip_exn safe_names deduced)
                                            ~init:prod
                                            ~f:(fun e' (safe,(_,prod)) -> replace_expr e' ~old:safe ~by:prod )
                               )
                        | None -> None
                        end
                   end
               )
         with
         | None -> None
         | Some (t,prod) -> aux (deduced @ [(t,prod)])
       end
  in
  aux deduced_terms
