(* Unification modulo the theory of XOR with inverses *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions

type unif_problem = {
    unif_equalities   : expr list;
    unif_inequalities : expr list;
  }

let make_unif_problem eqs ineqs =
  { unif_equalities = eqs; unif_inequalities = ineqs }

type unifier = expr String.Map.t

let equal_unif u1 u2 =
  let compare (s1,e1) (s2,e2) =
    let d = String.compare s1 s2 in
    if d <> 0 then d
    else compare_expr e1 e2
  in
  (compare_lists (Map.to_alist u1) (Map.to_alist u2) ~compare) = 0

let rec apply_unifier_expr sigma expr =
  let f = apply_unifier_expr sigma in
  match expr with
  | Const _ | Zero -> expr
  | Var x -> (optional ~d:expr (Map.find sigma x))
  | F(n,i,m,(left,right),inv,b,a) -> F(n,i,m,(L.map left ~f, L.map right ~f),inv,b,a)
  | XOR(exprs) -> XOR(L.map exprs ~f)

let apply_unifier sigma unifp =
  { unif_equalities = L.map ~f:(apply_unifier_expr sigma) unifp.unif_equalities;
    unif_inequalities = L.map ~f:(apply_unifier_expr sigma) unifp.unif_inequalities
  }

let update_unifier sigma (x,e) =
  Map.map sigma ~f:(apply_unifier_expr (String.Map.of_alist_exn [(x,e)]))
  |> Map.add ~key:x ~data:e

(* ** Pretty printing *)

let string_of_unif_problem unifp =
  let equalities =
    if L.length unifp.unif_equalities = 0 then ""
    else (string_of_list " = 0 /\\ \n " string_of_expr unifp.unif_equalities) ^ " = 0"
  in
  if L.length unifp.unif_inequalities = 0 then "unify(\n " ^ equalities ^ "\n)"
  else
    "unify(\n " ^ equalities ^ ";\n " ^
      (string_of_list " <> 0 /\\ \n " string_of_expr unifp.unif_inequalities) ^ " <> 0\n)"

let string_of_assignment (x,e) =
    (color "red" x) ^ " -> " ^ (string_of_expr e)

let string_of_unifier unifier =
  "{ " ^ (string_of_list ";\n  " string_of_assignment (String.Map.to_alist unifier)) ^ " }"

let string_of_unifier_option = function
  | None   -> "No solution"
  | Some u -> string_of_unifier u

let pp_unif_problem _ unifp = F.printf "%s" (string_of_unif_problem unifp)
let pp_unifier _ unifier = F.printf "%s" (string_of_unifier unifier)
let pp_unifier_option _ u_opt = F.printf "%s" (string_of_unifier_option u_opt)


(* ** Util functions *)

let fresh_idx = ref 0

let safe_fresh_idxs variables = (* Be careful with user variable names starting with 'r' *)
  L.iter variables
      ~f:(fun x ->
        let first, rest = (S.slice x 0 1), (S.slice x 1 (S.length x)) in
        if first = "r" then
          try
            let i = int_of_string rest in
            fresh_idx := i + 1;
          with
          | Failure _ -> ()
        else ()
      )

let fresh_name () =
  fresh_idx := !fresh_idx + 1;
  (* Just a test to prevent unexpected behaviour, the bound is set to 2^60 *)
  if !fresh_idx > 1152921504606846976 then failwith "Overflow"
  else "r" ^ (string_of_int !fresh_idx)

let fresh_var () = Var (fresh_name ())

let fresh_name_vector n =
  let rec aux output k =
    if k = 0 then output
    else aux (output @ [fresh_name ()]) (k-1)
  in
  aux [] n

let fresh_var_vector n = L.map (fresh_name_vector n) ~f:(fun x -> Var x)

let check_inequalities sigma inequalities =
  not (L.exists inequalities ~f:(fun e -> is_zero (simplify_expr (apply_unifier_expr sigma e))) )

(* ** Unification algorithms *)

(* *** Liu's algorithm adapted *)

let rec is_pure expr =
  match expr with
  | Const _ | Var _ | Zero -> true
  | XOR(_) -> false
  | F(_,_,_,(left,right),_,_,_) ->
     L.fold_left (left @ right) ~init:true ~f:(fun b e -> if not b then false else is_pure e)

let rec first_xor_not_in_top expr =
  let aux list = L.fold_left list ~init:None ~f:(fun s e -> if some s then s else first_xor_not_in_top e) in
  match expr with
  | Const _ | Var _ | Zero -> None
  | XOR(exprs) -> aux exprs
  | F(_,_,_,(left,right),_,_,_) ->
     begin match L.find (left @ right) ~f:(function XOR(_) -> true | _ -> false) with
     | Some a -> Some a
     | None -> aux (left @ right)
     end

let is_pure_sum expr =
  match expr with
  | XOR(exprs) ->
     L.fold_left exprs ~init:true ~f:(fun b e -> if not b then false else is_pure e)
  | _ -> is_pure expr

let rec replace_xor_by_expr ~xor ~by expr =
  let xor_list = match (simplify_expr xor) with | XOR(exprs) -> exprs | _ -> assert false in
  let expr = simplify_expr expr in
  let f = replace_xor_by_expr ~xor ~by in
  match expr with
  | Const _ | Var _ | Zero -> expr
  | F(n,i,m,(left,right),inv,b,a) -> F(n,i,m,(L.map left ~f, L.map right ~f),inv,b,a)
  | XOR(exprs) ->
     let new_exprs =
       if L.fold_left xor_list
           ~init:true ~f:(fun b e -> if not b then false else L.mem exprs e ~equal:equal_expr )
       then by :: (L.filter exprs ~f:(fun e -> not(L.mem xor_list e ~equal:equal_expr )))
       else exprs
     in
     XOR(L.map new_exprs ~f) |> simplify_expr

let purify equalities =
  let rec aux purified = function
    | [] -> purified
    | eq :: rest ->
       let eq = simplify_expr eq in
       if is_pure_sum eq then aux (purified @ [eq]) rest
       else
         begin match first_xor_not_in_top eq with
         | Some xor ->
            let y = fresh_var () in
            aux purified ((L.map (eq :: rest) ~f:(replace_xor_by_expr ~xor ~by:y )) @ [XOR([y; xor]) |> simplify_expr])
         | None -> assert false
         end
  in
  aux [] equalities

let purify_unif_problem unifp =
  { unifp with unif_equalities = purify unifp.unif_equalities }

let is_unconstrained ~var expr =
  let rec aux top = function
    | Const _ | Zero -> true
    | Var x -> if x = var then top else true
    | F(_,_,_,(left,right),_,_,_) ->
       L.fold_left (left @ right) ~init:true ~f:(fun b e -> if b then aux false e else false)
    | XOR(exprs) ->
       L.fold_left exprs ~init:true ~f:(fun b e -> if b then aux top e else false)
  in
  aux true expr

let find_unconstrained_var exprs =
  let variables = L.map exprs ~f:vars |> L.concat |> L.dedup ~compare:S.compare in
  L.fold_left variables
     ~init:None
     ~f:(fun sol var ->
       if some sol then sol
       else if L.exists exprs ~f:(fun e -> not(is_unconstrained ~var e)) then None
       else Some var
     )

let similar_fun fun1 fun2 =
  match fun1, fun2 with
  | F(n1,i1,m1,(left1,right1),inv1,_,_), F(n2,i2,m2,(left2,right2),inv2,_,_) ->
     if n1 = n2 && i1 = i2 && m1 = m2 then
       (assert ((L.length left1) = (L.length left2) && (L.length right1) = (L.length right2));
        assert (inv1 = inv2);
        true
       )
     else false
  | _ -> false

let not_equalized equalized (e1,e2) =
  L.exists equalized
     ~f:(fun (e1',e2') ->
       (equal_expr e1 e1' && equal_expr e2 e2') || (equal_expr e1 e2' && equal_expr e1' e2)
     )
  |> not

let find_two_top_fun_not_equalized equalized expr =
  let expr = simplify_expr expr in
  match expr with
  | Const _ | Var _ | F(_) | Zero -> None
  | XOR(exprs) ->
     let rec aux = function
       | [] -> None
       | e :: rest ->
          match L.find rest ~f:(fun e' -> (similar_fun e e') && not_equalized equalized (e,e')) with
          | Some e' -> Some (e,e')
          | None -> aux rest
     in
     aux exprs

let unify_liu unifp =
  let rec aux sigma equalized unifp =
    let equalities = L.map unifp.unif_equalities ~f:simplify_expr
                     |> L.dedup ~compare:compare_expr
                     |> L.filter ~f:(function | Zero -> false | _ -> true)
    in
    let without_vars, with_vars = split_list ~f:(fun e -> L.length (vars e) = 0) equalities in
    if L.exists without_vars ~f:(fun e -> not (equal_expr e Zero)) then None
    else
      if with_vars = [] then
        if check_inequalities sigma unifp.unif_inequalities then Some sigma
        else None
      else
        match find_unconstrained_var with_vars with
        | Some x ->
           let eq = L.find_exn with_vars ~f:(fun e -> L.mem (vars e) x ~equal:S.equal) in
           let e = XOR [eq; Var x] |> simplify_expr in
           let sigma' = update_unifier sigma (x,e) in
           let equalized' =
             L.map equalized
                   ~f:(fun (e1,e2) -> apply_unifier_expr sigma' e1 |> simplify_expr,
                                      apply_unifier_expr sigma' e2 |> simplify_expr
                      )
           in
           aux sigma' equalized' (apply_unifier sigma' { unifp with unif_equalities = with_vars })
        | None ->
           let sol =
             L.fold_left with_vars
               ~init:None
               ~f:(fun sol eq ->
                 if some sol then sol
                 else
                   begin match find_two_top_fun_not_equalized equalized eq with
                   | None -> None
                   | Some (e1,e2) -> Some (eq,e1,e2)
                   end
               )
           in
           begin match sol with
           | None -> None
           | Some (eq,e1,e2) ->
              let solution =
                begin match e1,e2 with
                | F(_,_,_,(left1,right1),_,_,_), F(_,_,_,(left2,right2),_,_,_) ->
                   let new_eqs1 = (XOR[e1; e2; eq]) :: (L.filter with_vars ~f:(fun e -> not (equal_expr e eq))) in
                   let new_eqs2 = L.map (L.zip_exn (left1 @ right1) (left2 @ right2)) ~f:(fun (e1,e2) -> XOR[e1; e2]) in
                   aux sigma equalized { unifp with unif_equalities = new_eqs1 @ new_eqs2 }
                | _ -> assert false
                end
              in
              if some solution then solution
              else
                let new_equalized = equalized @ [(e1,e2)] in
                aux sigma new_equalized unifp
           end
  in
  aux String.Map.empty [] (purify_unif_problem unifp)

let rec find_unblocked_fun expr =
  match expr with
  | Const _ | Var _ | Zero -> None
  | F(_,_,_,(left,right),inv,b,_) ->
     if not b && inv then Some expr
     else
       L.fold_left (left @ right)
            ~init:None
            ~f:(fun s e -> if some s then s else find_unblocked_fun e)
  | XOR(exprs) ->
     L.fold_left exprs
            ~init:None
            ~f:(fun s e -> if some s then s else find_unblocked_fun e)

let unify unifp =
  let rec aux unifp =
    let equalities = L.map unifp.unif_equalities ~f:simplify_expr
                     |> L.dedup ~compare:compare_expr
                     |> L.filter ~f:(function | Zero -> false | _ -> true)
    in
    (*F.printf "%d\n" (L.length equalities); F.print_flush();*)
    let without_vars, with_vars = split_list ~f:(fun e -> L.length (vars e) = 0) equalities in
    if L.exists without_vars ~f:(fun e -> not (equal_expr e Zero)) then None
    else
      let unblocked = L.fold_left with_vars ~init:None ~f:(fun s eq -> if some s then s else find_unblocked_fun eq) in
      match unblocked with
      | None -> unify_liu { unifp with unif_equalities = with_vars }
      | Some F(n,i,mode,(left,right),inv,b,a) ->
         assert (inv && not b);
         let solution =
           let new_eqs = L.map with_vars
              ~f:(replace_expr ~old:(F(n,i,mode,(left,right),inv,false,a) ) ~by:(F(n,i,mode,(left,right),inv,true,a)) )
           in
           aux { unifp with unif_equalities = new_eqs }
         in
         if some solution then solution
         else
           let m = L.length right in
           let y_vec = fresh_var_vector m in
           let new_eqs =
             with_vars @
               (L.map (L.zip_exn (range 0 m) right)
                 ~f:(fun (k,t) -> XOR([t; F(n,k,inv_mode mode,(left,y_vec),true,true,a)])))
             |> L.map ~f:(replace_expr ~old:(F(n,i,mode,(left,right),inv,false,a) ) ~by:(L.nth_exn y_vec i))
           in
           aux { unifp with unif_equalities = new_eqs }
      | Some _ -> assert false
  in
  aux unifp
  |> function
    | None -> None
    | Some sigma ->
       let variables = L.fold_left unifp.unif_equalities ~init:[] ~f:(fun l e -> l @ (vars e)) in
       let list = Map.to_alist sigma
                  |> L.filter ~f:(fun (x,_) -> L.mem variables x ~equal:S.equal)
                  |> L.map ~f:(fun (x,e) -> (x, simplify_expr e))
       in
       Some (String.Map.of_alist_exn list)
