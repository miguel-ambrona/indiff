(* Functions for automatically finding an indifferentiability attack for cryptographic primitives *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Unification
open Deductibility

(* ** Primitives *)

let feistel ~n inputs =
  let rec aux k (xk_2,xk_1) =
    if k = n+2 then [xk_2; xk_1]
    else
      let xk = XOR([xk_2; F("F"^(string_of_int (k-1)), 0, POS, ([],[xk_1]), false, false, None)]) in
      aux (k+1) (xk_1,xk)
  in
  match inputs with
  | x0 :: x1 :: [] ->  aux 2 (x0,x1)
  | _ -> failwith "Feistel requires exactly two inputs"


(* ** Building all contexts *)

let rec number_of_funs expr =
  let count_rec = L.fold_left ~init:0 ~f:(fun s e -> s + (number_of_funs e)) in
  match expr with
  | F(_,_,_,(left,right),_,_,_) -> 1 + (count_rec (left@right))
  | XOR(list) -> count_rec list
  | _ -> 0

let rec get_funs_with_arity expr =
  begin match expr with
  | Zero | Const _ | Var _ -> []
  | XOR(list) -> L.map list ~f:get_funs_with_arity |> L.concat
  | F(name,_,_,(left,right),inv,_,_) ->
     let other_funs = L.map (left @ right) ~f:get_funs_with_arity |> L.concat in
     (name,inv,L.length left, L.length right) :: other_funs
  end
  |> L.fold_left
       ~init:[]
       ~f:(fun list (name,inv,n,m) ->
         begin match L.find list ~f:(fun (name',_,_,_) -> name = name') with
         | None -> list @ [(name,inv,n,m)]
         | Some (_,inv',n',m') ->
            if inv = inv' && n = n' && m = m' then list
            else failwith ("The arity/invertibility of function " ^ name ^ " functions is not consistent")
         end
       )

let all_contexts_of_size_at_most_n n atoms _funs =
  (* This function does not produce contexts with two functions immediately nested *)
  let all_contexts = ref (Int.Map.of_alist_exn [(1, atoms)]) in

  let rec compute_contexts k =
    if k = 1 then atoms
    else
      let xor_merge =
        L.map (all_k_lists_sum_n 2 (k-1))
          ~f:(function
              | d1 :: d2 :: [] ->
                 if d1 < d2 then []
                 else
                   combine_lists_all_combinations [compute_contexts d1; compute_contexts d2]
                   |> L.map ~f:(fun l -> XOR(l))
              | _ -> assert false
             )
        |> L.concat
      in
      (* Uncomment for the general context search *)
      (*let calculated =
        L.map _funs ~f:(fun (name,inv,d1,d2) ->
           L.map (all_k_lists_sum_n (d1+d2) (k-1))
             ~f:(fun l ->
               let contexts = L.map l ~f:(fun d -> compute_contexts d |> L.filter ~f:(fun c -> number_of_funs c = 0)) in
               let combinations = combine_lists_all_combinations contexts in
               L.map combinations
                  ~f:(fun comb ->
                    if L.exists comb ~f:(fun e -> sign e = F_sig) then []
                    else
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
      in*)
      let calculated = [] in
      let contexts = L.map (xor_merge @ calculated) ~f:simplify_expr |> dedup_preserving_order ~equal:equal_expr in
      all_contexts := Map.add !all_contexts ~key:k ~data:contexts;
      contexts
  in

  let rec asc_iter k =
    if k > n then ()
    else
      let _ = compute_contexts k in
      asc_iter (k+1)
  in
  asc_iter 2;
  L.fold_left (range 0 n) ~init:[] ~f:(fun ctxs i -> ctxs @ (Map.find_exn !all_contexts (i+1)) )
  |> dedup_preserving_order ~equal:equal_expr

let all_contexts_of_size_at_most_n_2 n atoms funs =
  let all_contexts = ref (Int.Map.of_alist_exn [(1, atoms)]) in

  let rec compute_contexts k =
    if k = 1 then atoms
    else
      let xor_merge =
        L.map (all_k_lists_sum_n 2 (k-1))
          ~f:(function
              | d1 :: d2 :: [] ->
                 if d1 < d2 then []
                 else
                   combine_lists_all_combinations [compute_contexts d1; compute_contexts d2]
                   |> L.map ~f:(fun l -> XOR(l))
              | _ -> assert false
             )
        |> L.concat
      in
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
      F.printf "[%a]\n" (pp_list "\n,   " pp_expr) (xor_merge @ calculated);
      let contexts = L.map (xor_merge @ calculated) ~f:simplify_expr |> dedup_preserving_order ~equal:equal_expr in
      all_contexts := Map.add !all_contexts ~key:k ~data:contexts;
      contexts
  in
  let rec asc_iter k =
    if k > n then ()
    else
      let _ = compute_contexts k in
      asc_iter (k+1)
  in
  asc_iter 2;
  L.fold_left (range 0 n) ~init:[] ~f:(fun ctxs i -> ctxs @ (Map.find_exn !all_contexts (i+1)) )
  |> dedup_preserving_order ~equal:equal_expr

(* ** Heuristics *)

let heuristic1 ~primitive ~k ~n ~oname n_inputs rel1 rel2 =
  let var_name v i = (string_of_int v) ^ (S.make i '\'') in
  let variable_tuples  =
    L.map (range 0 n_inputs)
          ~f:(fun i ->
            L.map (range 0 n) ~f:(fun v -> Var ("X"^(var_name v i))),
            L.map (range 0 n) ~f:(fun v -> Var ("Y"^(var_name v i)))
          )
  in
  let keys = L.map (range 0 k) ~f:(fun i -> Var ("K"^(string_of_int i))) in
  let equations =
    L.map variable_tuples
        ~f:(fun (inputs,outputs) ->
          L.map (L.zip_exn (primitive keys inputs) outputs) ~f:(fun (e1,e2) -> XOR([e1;e2]) |> simplify_expr)
        )
    |> L.concat
  in
  let input_vars, output_vars = L.fold_left variable_tuples ~init:([],[]) ~f:(fun (l1,l2) (xs,ys) -> (l1 @ xs, l2 @ ys) ) in
  let relations =
    [L.fold_left (range 0 (n_inputs*n)) ~init:rel1 ~f:(fun rel i -> replace_expr rel ~old:(Var (string_of_int i)) ~by:(L.nth_exn input_vars i));
     L.fold_left (range 0 (n_inputs*n)) ~init:rel2 ~f:(fun rel i -> replace_expr rel ~old:(Var (string_of_int i)) ~by:(L.nth_exn output_vars i))]
  in
  let inequalities =
    L.fold_left (range 0 (n_inputs*n))
        ~init:rel2
        ~f:(fun rel j ->
          let old = Var (string_of_int j) in
          let v = j%n in
          let i = j/n in
          let vars, _ = L.nth_exn variable_tuples i in
          let by = F(oname, v, POS, (keys, vars), true, false, None) in (* TODO: Write a different R, checking that it is fresh *)
          replace_expr rel ~old ~by
        )
  in
  let inequalities =
    inequalities ::
      (L.map variable_tuples
             ~f:(fun (vec1, _) ->
               L.map variable_tuples ~f:(fun (vec2, _) ->
                       if (compare_lists ~compare:compare_expr vec1 vec2) = 0 then []
                       else [XOR(L.map (range 0 (L.length vec1))
                               ~f:(fun i ->
                                 XOR([F("G"^(string_of_int i), 0, POS, ([], [L.nth_exn vec1 i]), false, false, None);
                                      F("G"^(string_of_int i), 0, POS, ([], [L.nth_exn vec2 i]), false, false, None)])
                            ))]
                     )
               |> L.concat
             )
       |> L.concat
      )
  in

  let u = { unif_equalities = equations @ relations; unif_inequalities = inequalities; } in
  let sol = unify u in
  (*
  F.printf "%a\n\n\n" (pp_list ",\n" pp_expr) equations;
  F.printf "%a\n" (pp_list ",\n" pp_expr) relations;
  F.printf "%a <> 0\n" pp_expr inequalities;
  F.printf "%a\n" pp_unifier_option (sol);
   *)
  sol, relations, (variable_tuples,keys)

let heuristic ~primitive ~k ~n ~oname ~context_size =
  (* We put them inside a fake F to analyze them at the same time *)
  let exprs = primitive (list_repeat (Var ".") k) (list_repeat (Var ".") n) in
  let funs =
    get_funs_with_arity (F("fakename", 0, POS, (exprs, []), false, false, None))
    |> L.tl_exn
  in
  let aux n_inputs =
    let atoms = L.map (range 0 (n_inputs*n)) ~f:(fun i -> Var (string_of_int i)) in
    let contexts = all_contexts_of_size_at_most_n context_size atoms funs in
    (* let contexts = L.filter contexts ~f:(fun c -> L.length (vars c |> L.dedup) >= n_inputs) in*)
    let contexts = L.filter contexts ~f:(fun c -> number_of_funs c <= 1 && (match c with | F(_) -> false | _ -> true)) in
    let contexts =
      L.filter contexts
               ~f:(fun c ->
                 let c_vars = L.map (vars c) ~f:Int.of_string in
                 L.fold_left (range 0 n_inputs)
                    ~init:true
                    ~f:(fun b i -> if not b then b
                                   else if not (L.exists (range (n*i) (n*(i+1))) ~f:(fun j -> L.mem c_vars j )) then false
                                   else true
                       )
               )
    in
    (* F.printf "%a\n\n" (pp_list ",\n" pp_expr) contexts;*)
    let aaa = ref 0 in
    (*    F.printf "Total: %d^2\n" (L.length contexts);
    F.print_flush (); *)
    L.fold_left contexts
       ~init:None
       ~f:(fun solved rel1 ->
         match solved with
         | Some _ -> solved
         | None ->
            L.fold_left contexts
               ~init:None
               ~f:(fun solved rel2 ->
                 (*F.printf "Analyzed: %d\n" !aaa;
                 F.print_flush ();*)
                 begin match solved with
                 | Some _ -> solved
                 | None ->
                    aaa := !aaa + 1;
                    begin match heuristic1 ~primitive ~k ~n ~oname n_inputs rel1 rel2 with
                    | Some sol, relations, vars -> Some (sol, relations, vars)
                    | None, _, _  -> None
                    end
                 end
               )
       )
  in
  L.fold_left (range 3 5)
      ~init:None
      ~f:(fun solved i -> match solved with Some _ -> solved | None -> aux i)

type attack = Indiff | INDCCA | INDCPA

let heuristic2 ~primitive ~inv_primitive ~attack_type ~k ~n ~oname ~atoms ~size ~sol_number =
  (* We put them inside a fake F to analyze them at the same time *)
  let exprs = primitive (list_repeat (Var ".") k) (list_repeat (Var ".") n) in
  let funs =
    match attack_type with
    | Indiff -> get_funs_with_arity (F("fakename", 0, POS, (exprs, []), false, false, None)) |> L.tl_exn
    | _ -> []
  in
  let funs =
    funs @
      (match attack_type with
       | INDCPA -> [(oname, false, k, n)]
       | _ -> [(oname, (match inv_primitive with | None -> false | Some _ -> true), k, n)]
      )
  in
  let contexts =
    all_contexts_of_size_at_most_n_2 size (L.map atoms ~f:(fun s -> Const s)) funs
    |> L.filter ~f:(fun c -> sign c <> XOR_sig)
  in
  let rec convert_to_real_world expr =
    match expr with
    | Zero | Const _ | Var _ -> expr
    | XOR(list) -> XOR(L.map ~f:convert_to_real_world list)
    | F(name,i,m,(left,right),invertible,b,a) ->
       let left'  = L.map left ~f:convert_to_real_world in
       let right' = L.map right ~f:convert_to_real_world in
       if name = oname then
         let prim = if m = POS then primitive else
                      (assert invertible;
                       match inv_primitive with | Some p -> p | None -> assert false)
         in
         L.nth_exn (prim left' right') i
       else
         F(name,i,m,(left',right'),invertible,b,a)
  in
  let rec get_terms = function | Zero -> [] | XOR(exprs) -> L.map exprs ~f:get_terms |> L.concat | e -> [e] |> L.dedup ~compare:compare_expr in
  let pairs =
    L.map contexts ~f:(fun c ->
            let real = convert_to_real_world c |> simplify_expr in
            (c, real, get_terms real))
  in
  (* We will solve a system of linear equations, trying to find a zero linear combination of
     terms in pairs (real) *)
  let terms = L.fold_left pairs ~init:[] ~f:(fun l (_,_,ts) -> l @ ts) |> L.dedup ~compare:compare_expr in
  let linear_system =
    L.map terms ~f:(fun t -> L.map pairs ~f:(fun (_,_,ts) -> L.mem ts t ~equal:equal_expr ))
  in
  let vector = list_repeat false (L.length linear_system) in

  (*L.iter pairs ~f:(fun (rand,real,_) -> F.printf "%a vs %a\n" pp_expr rand pp_expr real);
  F.printf "\n\n\n";
  L.iter terms ~f:(fun t -> F.printf "%a\n" pp_expr t);*)

  match Lin.solve_matrix linear_system vector with
  | None -> None
  | Some matrix ->
     let solution = Static_Equivalence.linalg_nth_solution ~nth:sol_number matrix in
     begin match solution with
     | None -> None
     | Some sol ->
        let rand_expr = XOR(L.map (L.zip_exn contexts sol) ~f:(fun (c,b) -> if b then c else Zero)) in
        let valid = not (equal_expr Zero (simplify_expr rand_expr)) in
        let relation = L.fold_left (L.zip_exn sol contexts) ~init:Zero ~f:(fun acc (b,c) -> if b then XOR([acc; c]) else acc) |> simplify_expr in
        Some (relation, valid)
     end

let validate_solution ~oname ~atoms relations =
  GenerateDistinguisher.generate_code2 ~oname ~atoms relations

let iterative_heuristic2 ~primitive ~inv_primitive ~attack_type ~k ~n ~oname =
  let max_atoms = ["b"; "c"; "d"] in
  let max_size = 5 in
  L.fold_left max_atoms
     ~init:(None,["a"])
     ~f:(fun (b,atoms) const ->
       match b with
       | Some _ -> (b,atoms)
       | None ->
          let atoms = atoms @ [const] in
          L.fold_left (range 2 (max_size + 1))
             ~init:None
             ~f:(fun b size ->
               begin match b with
               | Some _ -> b
               | None ->
                  let rec iterate sol_number =
                    let () = F.printf "Sol number: %d. size: %d. Atoms: [%a]\n" sol_number size (pp_list ", " pp_string) atoms in
                    F.print_flush();
                    match heuristic2 ~primitive ~inv_primitive ~attack_type ~k ~n ~oname ~atoms ~size ~sol_number with
                    | None -> None
                    | Some (sol, valid) ->
                       if valid && validate_solution ~oname ~atoms [sol] then
                         (F.printf "[%a], valid: %b\n" pp_expr sol valid;
                          Some sol)
                       else iterate (sol_number+1)
                  in
                  iterate 0
               end
             ), atoms
     )
  |> (fun (sol,_) -> match sol with Some _ -> true | None -> false)
