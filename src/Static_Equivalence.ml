(* Static equivalence in the theory of XOR with inverses *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Deductibility
open Unification

(* ** XOR static equivalence *)


let pp_bool _fmt b = if b then F.printf "1" else F.printf "0"

let find_all_solutions matrix =
  F.printf "MATRIX:\n";
  (L.iter matrix
     ~f:(fun row -> F.printf "[%a]\n" (pp_list ", " pp_bool) row)
  );
  (* This function computes all the solutions of a linear system, given the matrix (A | b) in echelon form *)
  let n_vars = (L.length (L.hd_exn matrix)) - 1 in
  let non_free_cols =
    L.fold_left (range 0 n_vars)
       ~init:([],[])
       ~f:(fun (cols,rows) c ->
           let count, row =
             L.fold_left matrix
               ~init:(0,None)
               ~f:(fun (count,r) row -> if Z2.is_zero (L.nth_exn row c) then (count,r) else (count+1, Some row) ) in
           if count = 1 && not(L.mem rows row) then (cols @ [c], rows @ [row])
           else (cols,rows)
         )
    |> (fun (cols,_) -> cols)
  in
  let free_cols = L.filter (range 0 n_vars) ~f:(fun c -> not(L.mem non_free_cols c)) in
  (*  let free_cols =
    L.filter (range 0 n_vars)
       ~f:(fun c ->
         let count = L.fold_left matrix ~init:0 ~f:(fun count row -> if Z2.is_zero (L.nth_exn row c) then count else count+1 ) in
         count <> 1
       )
  in
  *)
  (*let () = F.printf "HOLALA %d\n" (L.length free_cols) in
    let () = F.printf "%a\n" (pp_list ", " pp_int) free_cols in*)
  L.map (all_bit_strings (L.length free_cols))
    ~f:(fun free ->
        let solution_list  = L.zip_exn free_cols free in
        let solution = Int.Map.of_alist_exn solution_list in
        L.map matrix
          ~f:(fun row ->
            match L.filter (range 0 n_vars) ~f:(fun c -> (Z2.is_one (L.nth_exn row c)) && not(L.mem free_cols c)) with
              | [c] ->
                let value =
                  L.fold_left (range 0 n_vars)
                    ~init:Z2.zero
                    ~f:(fun v c' -> if c = c' || (Z2.is_zero (L.nth_exn row c')) then v else Z2.add v (Map.find_exn solution c'))
                in
                [(c, Z2.add value (L.nth_exn row n_vars))]
              | _ -> assert (Z2.is_zero (L.nth_exn row n_vars)); [] (* Otherwise, there is no solution and this should not be executed *)
            )
        |> (fun l ->
            L.sort ((L.concat l) @ solution_list) ~cmp:(fun (a,_) (b,_) -> Int.compare a b)
            |> L.map ~f:(fun (_,v) -> v)
          )
      )

let linalg_nth_solution ~nth matrix =
  (* This function computes all the solutions of a linear system, given the matrix (A | b) in echelon form *)
  let n_vars = (L.length (L.hd_exn matrix)) - 1 in
  let non_free_cols =
    L.fold_left (range 0 n_vars)
       ~init:([],[])
       ~f:(fun (cols,rows) c ->
         let count, row =
           L.fold_left matrix
               ~init:(0,None)
               ~f:(fun (count,r) row -> if Z2.is_zero (L.nth_exn row c) then (count,r) else (count+1, Some row) ) in
         if count = 1 && not(L.mem rows row) then (cols @ [c], rows @ [row])
         else (cols,rows)
       )
    |> (fun (cols,_) -> cols)
  in
  let free_cols = L.filter (range 0 n_vars) ~f:(fun c -> not(L.mem non_free_cols c)) in
  match nth_bit_string ~nth (L.length free_cols) with
  | None -> None
  | Some free ->
     let solution_list  = L.zip_exn free_cols free in
     let solution = Int.Map.of_alist_exn solution_list in
     Some (L.map matrix
        ~f:(fun row ->
          match L.filter (range 0 n_vars) ~f:(fun c -> (Z2.is_one (L.nth_exn row c)) && not(L.mem free_cols c)) with
          | [c] ->
             let value =
               L.fold_left (range 0 n_vars)
                   ~init:Z2.zero
                   ~f:(fun v c' -> if c = c' || (Z2.is_zero (L.nth_exn row c')) then v else Z2.add v (Map.find_exn solution c'))
             in
             [(c, Z2.add value (L.nth_exn row n_vars))]
          | _ -> assert (Z2.is_zero (L.nth_exn row n_vars)); [] (* Otherwise, there is no solution and this should not be executed *)
        )
     |> (fun l ->
       L.sort ((L.concat l) @ solution_list) ~cmp:(fun (a,_) (b,_) -> Int.compare a b)
       |> L.map ~f:(fun (_,v) -> v)
           ))

let xor_lin_span frame expr =
  let knowledge = L.map frame.frame_sigma ~f:ground_xor_to_list in
  let e = ground_xor_to_list expr in
  let constants =
    L.map (expr :: frame.frame_sigma) ~f:atoms |> L.concat
    |> L.map ~f:(function | Const a -> a | _ -> assert false)
    |> L.dedup ~compare:String.compare
  in
  let forbidden = L.filter constants ~f:(L.mem frame.frame_names ~equal:S.equal) in
  if forbidden = [] then []
  else
    let contains_const c l = L.mem l c ~equal:S.equal in
    let matrix = L.map forbidden ~f:(fun c -> L.map knowledge ~f:(contains_const c)) in
    let vector = L.map forbidden ~f:(fun c -> contains_const c e) in
    Lin.reduced_row_echelon_form matrix vector
(*
    let matrix = Lin.reduced_row_echelon_form matrix vector in
    L.map (find_all_solutions matrix)
        ~f:(fun solution ->
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
          )
*)

let xor_static_equivalence frame1 frame2 =
  (*
  F.printf "static equivalent {%a} with names = {%a}\n vs\n {%a} with names = {%a}\n"
    (pp_list ", " pp_expr) frame1.frame_sigma (pp_list ", " pp_string) frame1.frame_names
    (pp_list ", " pp_expr) frame2.frame_sigma (pp_list ", " pp_string) frame2.frame_names;
  *)

  let names_str = "Please, use the same list of forbidden names for both frames" in
  if compare_lists ~compare:String.compare frame1.frame_names frame2.frame_names <> 0 then
    failwith names_str
  else if (L.length frame1.frame_sigma) <> (L.length frame2.frame_sigma) then failwith names_str
  else
    let span1 = xor_lin_span frame1 Zero in
    let span2 = xor_lin_span frame2 Zero in

    let different =
      if (L.length span1) <> (L.length span2) then true
      else
        L.exists (L.zip_exn span1 span2)
          ~f:(fun (row1, row2) ->
              L.exists (L.zip_exn row1 row2) ~f:(fun (t1,t2) -> t1 <> t2))
    in
    not (different)

    (*
    let substitution2 =
      String.Map.of_alist_exn
        (L.zip_exn (L.map (range 0 (L.length frame2.frame_sigma)) ~f:(fun i -> "%" ^ (string_of_int (i+1)))) frame2.frame_sigma)
    in
    if L.exists zero_productions1 ~f:(fun p -> not (equal_expr (simplify_expr (apply_unifier_expr substitution2 p)) Zero)) then
      false
    else

      let zero_productions2 = xor_deduce_all frame2 Zero in
      let substitution1 =
        String.Map.of_alist_exn
          (L.zip_exn (L.map (range 0 (L.length frame1.frame_sigma)) ~f:(fun i -> "%" ^ (string_of_int (i+1)))) frame1.frame_sigma)
      in
      not (L.exists zero_productions2 ~f:(fun p -> not (equal_expr (simplify_expr (apply_unifier_expr substitution1 p)) Zero)))
*)

(* ** Static equivalence for functions with inverses *)

let compute_cE funs =
  (* This function returns the bound cE for the size of contexts that is enough to analyze.
     That is, it is sufficient to limit the size of contexts to cE for analyzing static equivalence
     The bound is described in M. Abadi, V. Cortier Theoretical Computer Science 367 (2006) 2-32
   *)
  L.fold_left funs ~init:2 ~f:(fun d (_,inv,d1,d2) -> let m = if inv then 1+d1+2*d2 else 1+d1+d2 in if m > d then m else d)

let build_all_contexts_of_at_most_size_n n atoms funs =
  let all_contexts = ref (Int.Map.of_alist_exn [(1, atoms)]) in

  let rec compute_contexts k =
    if k = 1 then atoms
    else
      let calculated =
        L.map funs ~f:(fun (name,inv,d1,d2) ->
           L.map (all_k_lists_sum_n (d1+d2) (k-1))
             ~f:(fun l ->
               let contexts = L.map l ~f:(fun d -> compute_contexts d) in
               let combinations = combine_lists_all_combinations contexts in
               L.map combinations
                  ~f:(fun comb ->
                    let left,right = split_list_by_idx d1 comb in
                    if inv then
                      (L.map (range 0 d2) ~f:(fun i -> F(name,i,POS,(left,right),inv,false,None))) @
                        (L.map (range 0 d2) ~f:(fun i -> F(name,i,NEG,(left,right),inv,false,None)))
                    else
                      L.map (range 0 d2) ~f:(fun i -> F(name,i,POS,(left,right),inv,false,None))
                  )
               |> L.concat
             )
           |> L.concat
          )
        |> L.concat
      in
      let calculated = L.map calculated ~f:simplify_expr |> dedup_preserving_order ~equal:equal_expr in
      all_contexts := Map.add !all_contexts ~key:k ~data:calculated;
      calculated
  in

  let rec asc_iter k =
    if k > n then ()
    else
      let _ = compute_contexts k in
      asc_iter (k+1)
  in
  asc_iter 2;
  Map.find_exn !all_contexts n

let rec subterms expr =
  match simplify_expr expr with
  | Zero | Const _ | Var _ -> [expr]
  | XOR(list) -> expr :: (L.map list ~f:subterms |> L.concat) |> dedup_preserving_order ~equal:equal_expr
  | F(_,_,_,(left,right),_,_,_) ->
     expr :: (L.map (left@right) ~f:subterms |> L.concat) |> dedup_preserving_order ~equal:equal_expr

let saturate_frame frame =
  let frame_subterms = L.map frame.frame_sigma ~f:subterms |> L.concat |> dedup_preserving_order ~equal:equal_expr in
  L.map frame_subterms
      ~f:(fun s -> match fun_deduce frame s with
                   | None -> []
                   | Some sol -> [(s, sol)]
         )
  |> L.concat

let one_dir_fun_static_equivalence frame1 frame2 =
  (* We put them inside a fake F to analyze them at the same time *)
  (*let funs =
    get_funs_with_arity (F("fakename", 0, POS, (frame1.frame_sigma @ frame2.frame_sigma, []), false, false, None))
    |> L.tl_exn
  in
  L.iter funs ~f:(fun (n,_,_,_) -> assert (n <> "fakename")); (* Soundness check *)
  L.iter funs ~f:(fun (n,_,d1,d2) -> F.printf "%s, %d, %d\n" n d1 d2 );
  let cE = compute_cE funs in
  F.printf "cE: %d\n" cE;*)
  let sat = saturate_frame frame1 in
  let sat =
    L.fold_left (range 1 ((L.length frame1.frame_sigma)+1))
       ~init:sat
       ~f:(fun list i ->
         L.map list ~f:(fun (e,formula) ->
             e, replace_expr formula ~old:(Var ("%"^(string_of_int i))) ~by:(Var ("%%"^(string_of_int i))) )
       )
    |> safe_sort ~cmp:(fun (e1,_) (e2,_) -> Int.compare (L.length (subterms e1)) (L.length (subterms e2)))
  in
  let (_,b) =
    L.fold_left sat
       ~init:([],true)
       ~f:(fun (accum_sat,b) (e,f) ->
         if not b then ([],b)
         else
           begin match fun_deduce { frame_names = frame1.frame_names; frame_sigma = accum_sat; } e with
           | None -> (accum_sat @ [e]), b
           | Some formula ->
              let formula' =
                L.fold_left (range 0 (L.length accum_sat))
                   ~init:formula
                   ~f:(fun formula' i ->
                     let (_,by) = L.nth_exn sat i in
                     replace_expr formula' ~old:(Var ("%"^(string_of_int (i+1)))) ~by)
              in
              (*F.printf "FORMULA: %a -> %a\n" pp_expr e pp_expr formula';*)
              let f2, formula2 =
                L.fold_left (range 0 (L.length frame2.frame_sigma))
                    ~init:(f,formula')
                    ~f:(fun (f2,formula2) i ->
                      let old = Var ("%%"^(string_of_int (i+1))) in
                      let by = L.nth_exn frame2.frame_sigma i in
                      (replace_expr f2 ~old ~by |> simplify_expr,
                       replace_expr formula2 ~old ~by |> simplify_expr)
                    )
              in
              (*F.printf "HOLA: %a vs %a\n" pp_expr f2 pp_expr formula2;*)
              if equal_expr f2 formula2 then (accum_sat @ [e]), b
              else
                (*let () = F.printf "We can distinguish by: %a vs %a\n" pp_expr f pp_expr formula' in *)
                ([], false)
           end
       )
  in
  b

let fun_static_equivalence frame1 frame2 =
  if compare_lists ~compare:String.compare frame1.frame_names frame2.frame_names <> 0 then false
  else if (L.length frame1.frame_sigma) <> (L.length frame2.frame_sigma) then false
  else
    if one_dir_fun_static_equivalence frame1 frame2 then one_dir_fun_static_equivalence frame2 frame1
    else false

(* ** Static equivalence for the combined theory *)

let extend_frame frame1 frame2 =
  (*let () = F.printf "I am here\n" in*)
  let subterms2 =
    L.map frame2.frame_sigma ~f:subterms |> L.concat
    |> L.filter ~f:(fun e -> not (L.mem frame2.frame_sigma e ~equal:(fun e1 e2 -> equal_expr (simplify_expr e1) (simplify_expr e2))) )
  in
  let recipes =
    L.map subterms2 ~f:(fun s -> match deduce frame2 s with | None -> [] | Some recipe -> [recipe])
    |> L.concat
  in
  let new_terms_for_sigma1 =
    L.map recipes
       ~f:(fun r ->
         L.fold_left (range 0 (L.length frame1.frame_sigma))
               ~init:r
               ~f:(fun r' i ->
                 let old = Var ("%"^(string_of_int (i+1))) in
                 let by = L.nth_exn frame1.frame_sigma i in
                 replace_expr r' ~old ~by |> simplify_expr
               )
       )
    |> L.map ~f:simplify_expr
  in
  { frame1 with frame_sigma = (L.map (frame1.frame_sigma @ new_terms_for_sigma1) ~f:simplify_expr ) }

let static_equivalence frame1 frame2 =
  (*let () = F.printf "HELLO!!!\n" in*)
  if compare_lists ~compare:String.compare frame1.frame_names frame2.frame_names <> 0 then false
  else if (L.length frame1.frame_sigma) <> (L.length frame2.frame_sigma) then false
  else
    let extension1 = extend_frame frame1 frame2 in
    let frame1' = extend_frame extension1 extension1 in
    let frame2' = extend_frame (extend_frame frame2 frame2) extension1 in
    (*
    F.printf "[%a]\n" (pp_list ", " pp_expr) frame1'.frame_sigma;
    F.printf "[%a]\n" (pp_list ", " pp_expr) frame2'.frame_sigma;
    *)

    let sub = L.map (frame1'.frame_sigma @ frame2'.frame_sigma) ~f:(fun e -> factor_subterms (simplify_expr e))
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
                  | _ -> assert false) *)
           )
    in
    let fun_names = fresh_name_vector (L.length fun_subterms) in
    let xor_names = fresh_name_vector (L.length xor_subterms) in
    let replace list e = L.fold_left list ~init:e ~f:(fun e' (t,n) -> replace_expr e' ~old:t ~by:(Const n)) in

    let fun_replace e = replace (L.zip_exn fun_subterms fun_names) (simplify_expr e) in
    let xor_replace e = replace (L.zip_exn xor_subterms xor_names) (simplify_expr e) in
    let frame1'_rho_xor =
      { frame_names = xor_names @ frame1.frame_names;
        frame_sigma = L.map frame1'.frame_sigma ~f:xor_replace;
      }
    in
    let frame2'_rho_xor =
      { frame_names = xor_names @ frame2.frame_names;
        frame_sigma = L.map frame2'.frame_sigma ~f:xor_replace;
      }
    in
    let b = fun_static_equivalence frame1'_rho_xor frame2'_rho_xor in
    (*let () = F.printf "\nAAAAA\n" in*)
    if b then
      let frame1'_rho_fun =
        { frame_names = fun_names @ frame1.frame_names;
          frame_sigma = L.map frame1'.frame_sigma ~f:fun_replace;
        }
      in
      let frame2'_rho_fun =
        { frame_names = fun_names @ frame2.frame_names;
          frame_sigma = L.map frame2'.frame_sigma ~f:fun_replace;
        }
      in
      xor_static_equivalence frame1'_rho_fun frame2'_rho_fun
    else
      false
