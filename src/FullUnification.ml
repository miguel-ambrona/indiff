(* Full unification modulo the theory of XOR with inverses *)
(* These functions find all solutions to the unification problem *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Unification

let unify_liu_all unifp =
  let rec aux sigma equalized unifp =
    let equalities = L.map unifp.unif_equalities ~f:simplify_expr
                     |> L.dedup ~compare:compare_expr
                     |> L.filter ~f:(function | Zero -> false | _ -> true)
    in
    let without_vars, with_vars = split_list ~f:(fun e -> L.length (vars e) = 0) equalities in
    if L.exists without_vars ~f:(fun e -> not (equal_expr e Zero)) then []
    else
      if with_vars = [] then
        if check_inequalities sigma unifp.unif_inequalities then [sigma]
        else []
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
           | None -> []
           | Some (eq,e1,e2) ->
              let solutions =
                begin match e1,e2 with
                | F(_,_,_,(left1,right1),_,_,_), F(_,_,_,(left2,right2),_,_,_) ->
                   let new_eqs1 = (XOR[e1; e2; eq]) :: (L.filter with_vars ~f:(fun e -> not (equal_expr e eq))) in
                   let new_eqs2 = L.map (L.zip_exn (left1 @ right1) (left2 @ right2)) ~f:(fun (e1,e2) -> XOR[e1; e2]) in
                   aux sigma equalized { unifp with unif_equalities = new_eqs1 @ new_eqs2 }
                | _ -> assert false
                end
              in
              let new_equalized = equalized @ [(e1,e2)] in
              solutions @ (aux sigma new_equalized unifp)
           end
  in
  aux String.Map.empty [] (purify_unif_problem unifp)

let unify_all unifp =
  let rec aux unifp =
    let equalities = L.map unifp.unif_equalities ~f:simplify_expr
                     |> L.dedup ~compare:compare_expr
                     |> L.filter ~f:(function | Zero -> false | _ -> true)
    in
    let without_vars, with_vars = split_list ~f:(fun e -> L.length (vars e) = 0) equalities in
    if L.exists without_vars ~f:(fun e -> not (equal_expr e Zero)) then []
    else
      let unblocked = L.fold_left with_vars ~init:None ~f:(fun s eq -> if some s then s else find_unblocked_fun eq) in
      match unblocked with
      | None -> unify_liu_all { unifp with unif_equalities = with_vars }
      | Some F(n,i,mode,(left,right),inv,b,a) ->
         assert (inv && not b);
         let solutions =
           let new_eqs = L.map with_vars
              ~f:(replace_expr ~old:(F(n,i,mode,(left,right),inv,false,a) ) ~by:(F(n,i,mode,(left,right),inv,true,a)) )
           in
           aux { unifp with unif_equalities = new_eqs }
         in
         let m = L.length right in
         let y_vec = fresh_var_vector m in
         let new_eqs =
           with_vars @
             (L.map (L.zip_exn (range 0 m) right)
               ~f:(fun (k,t) -> XOR([t; F(n,k,inv_mode mode,(left,y_vec),true,true,a)])))
           |> L.map ~f:(replace_expr ~old:(F(n,i,mode,(left,right),inv,false,a) ) ~by:(L.nth_exn y_vec i))
         in
         solutions @ (aux { unifp with unif_equalities = new_eqs })
      | Some _ -> assert false
  in
  aux unifp
  |> L.map ~f:(fun sigma ->
            let variables = L.fold_left unifp.unif_equalities ~init:[] ~f:(fun l e -> l @ (vars e)) in
            let list = Map.to_alist sigma
                       |> L.filter ~f:(fun (x,_) -> L.mem variables x ~equal:S.equal)
                       |> L.map ~f:(fun (x,e) -> (x, simplify_expr e))
            in
            String.Map.of_alist_exn list
           )
