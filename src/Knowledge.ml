(* Functions to analyze knowledge constraints *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Unification
open FullUnification
open Deductibility

let rec freeze_variables = function
  | Var n -> Const ("%" ^ n)
  | Zero -> Zero
  | Const n -> assert (S.slice n 0 1 <> "%"); Const n
  | XOR(list) -> XOR(L.map list ~f:freeze_variables )
  | F(name,i,mode,(left,right),inv,block,a) ->
     F(name,i,mode,(L.map left ~f:freeze_variables,L.map right ~f:freeze_variables ), inv, block, a)

let simplify_frame_for_deduction f =
  let new_names =
    L.filter f.frame_names
       ~f:(fun n -> not (L.exists f.frame_sigma ~f:(function | Const n' -> n = n' | _ -> false)))
  in
  let new_sigma = L.filter f.frame_sigma ~f:(function | Const _ -> false | _ -> true) in
  { frame_names = new_names; frame_sigma = new_sigma }

let deduce_with_vars frame e =
  let fresh = fresh_name () in
  let fresh_const = Const fresh in
  let fresh2 = fresh_name () in
  let fresh_const2 = Const fresh2 in

  let sts = (L.map (e :: frame.frame_sigma) ~f:factor_subterms |> L.concat |> dedup_preserving_order ~equal:equal_expr) in
  assert (equal_expr e (L.hd_exn sts));
  let sts = if vars e = [] then sts else L.tl_exn sts in
  let sts = [fresh_const; fresh_const2] @ sts @ [Zero] in
  let sts = dedup_preserving_order sts ~equal:equal_expr in
  (* F.printf "sts: [%a]\n" (pp_list ", " pp_expr) sts; *)
  (*  (L.map (e :: sts)
     ~f:(fun e' ->
       L.map (e :: sts)
          ~f:(fun e'' ->
            let u = { unif_equalities = [XOR([e';e''])]; unif_inequalities = []; } in
            unify_all u
          )
     )
   |> L.concat
  )*)
  L.map sts
        ~f:(fun e' ->
          let u = { unif_equalities = [XOR([e';e])]; unif_inequalities = []; } in
          unify_all u
        ) (* Check this *)
  |> L.concat
  |> dedup_preserving_order ~equal:equal_unif
  |> L.filter
       ~f:(fun u ->
         let f expr = apply_unifier_expr u expr |> simplify_expr in
         let frame' = { frame with frame_sigma = L.map frame.frame_sigma ~f; } in
         let e' = f e in
         let constants = L.map (e' :: frame'.frame_sigma) ~f:consts |> L.concat in
         assert (not(L.exists constants ~f:(fun n -> S.slice n 0 1 = "%")));
         let frame'' = { frame with frame_sigma = L.map frame'.frame_sigma ~f:freeze_variables } in
         let e'' = freeze_variables e' in
         let is_deductible = match deduce frame'' e'' with | None -> false | Some _ -> true in
         is_deductible
       )

let knowledge_constraints (constraints : (expr * frame) list) =
  let constraints = L.map constraints ~f:(fun (e,f) -> (e, simplify_frame_for_deduction f)) in
(*  L.iter constraints
         ~f:(fun (e,f) ->
           let subts = (L.map (e :: f.frame_sigma) ~f:factor_subterms |> L.concat |> dedup_preserving_order ~equal:equal_expr) in
           F.printf "[%a]\n\n\n" (pp_list ",\n" pp_expr) subts;
         );
  F.printf "[%a]\n" (pp_list ", " pp_int) (L.map constraints ~f:(fun (e,f) -> L.length (L.map (e :: f.frame_sigma) ~f:factor_subterms |> L.concat |> dedup_preserving_order ~equal:equal_expr)));
  F.print_flush();*)
  let rec aux previous unifier = function
    | [] -> [unifier]
    | (e,f) :: rest ->
       L.map (deduce_with_vars f e)
          ~f:(fun u ->
            let g expr = apply_unifier_expr u expr |> simplify_expr in
            let update (e',f') = (g e', {f' with frame_sigma = L.map f'.frame_sigma ~f:g }) in
            let unifier' =
              String.Map.of_alist_exn
                ((L.map (String.Map.to_alist unifier) ~f:(fun (n,e) -> (n,g e))) @
                   (String.Map.to_alist u)
                )
            in
            if L.exists previous
                  ~f:(fun (e,f) -> let (e',f') = update (e,f) in
                                   let f'' = { f' with frame_sigma = L.map f'.frame_sigma ~f:freeze_variables } in
                                   let e'' = freeze_variables e' in
                                   begin match deduce f'' e'' with
                                   | None -> true
                                   | Some _ -> false
                                   end
                     )
            then []
            else aux (previous @ [update (e,f)]) unifier' (L.map rest ~f:update )
          )
       |> L.concat
  in
  aux [] String.Map.empty constraints

let lazy_knowledge_constraints ~validate (constraints : (expr * frame) list) =
  let constraints = L.map constraints ~f:(fun (e,f) -> (e, simplify_frame_for_deduction f)) in
  (*L.iter constraints ~f:(fun (e,f) -> F.printf "%a from {%a} with names = {%a}\n" pp_expr e (pp_list ", " pp_expr) f.frame_sigma (pp_list ", " pp_string) f.frame_names);
  F.print_flush(); *)
  let rec aux previous unifier = function
    | [] -> validate unifier
    | (e,f) :: rest ->
       L.fold_left (deduce_with_vars f e)
          ~init:None
          ~f:(fun solved u ->
            begin match solved with
            | Some _ -> solved
            | None ->
               let g expr = apply_unifier_expr u expr |> simplify_expr in
               let update (e',f') = (g e', {f' with frame_sigma = L.map f'.frame_sigma ~f:g }) in
               let unifier' =
                 String.Map.of_alist_exn
                   ((L.map (String.Map.to_alist unifier) ~f:(fun (n,e) -> (n,g e))) @
                      (String.Map.to_alist u)
                   )
               in
               if L.exists previous
                    ~f:(fun (e,f) -> let (e',f') = update (e,f) in
                                     let f'' = { f' with frame_sigma = L.map f'.frame_sigma ~f:freeze_variables } in
                                     let e'' = freeze_variables e' in
                                     begin match deduce f'' e'' with
                                     | None -> true
                                     | Some _ -> false
                                     end
                       )
               then None
               else aux (previous @ [update (e,f)]) unifier' (L.map rest ~f:update )
            end
          )
  in
  aux [] String.Map.empty constraints
