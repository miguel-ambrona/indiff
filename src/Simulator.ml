(* Functions to find a simulator satisfying all restrictions *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Unification
open Deductibility
open FullUnification
open Knowledge

let update_knowledge u knowledge =
  let g = apply_unifier_expr u in
  L.map knowledge
     ~f:(fun (e,f) -> (g e, {f with frame_sigma = L.map f.frame_sigma ~f:g; }))


let find_simulator (u, knowledge, additional) =
  let rec aux = function
    | [] -> None
    | unifier :: rest ->
       let knowledge' = update_knowledge unifier knowledge in
       let candidate_solutions = knowledge_constraints knowledge' in
       F.printf "Candidates: %d\n" (L.length candidate_solutions);
       match
         L.fold_left candidate_solutions
            ~init:None
            ~f:(fun solved candidate ->
              begin match solved with
              | Some _ -> solved
              | None ->
                 let unifier' =
                   S.Map.of_alist_exn
                     ((S.Map.to_alist (S.Map.map unifier
                                            ~f:(fun e -> apply_unifier_expr candidate e |> simplify_expr)))
                      @ (S.Map.to_alist candidate))
                 in
                 (* F.printf "unif:\n%a\n\n" pp_unifier unifier'; *)
                 let is_valid_unifier = L.fold_left additional
                    ~init:true
                    ~f:(fun b (v1,v2) ->
                      if not b then b
                      else
                        let find_frame v =
                          begin match L.find knowledge ~f:(fun (v',_) -> equal_expr v v') with
                          | None -> assert false
                          | Some (_,frame) -> frame
                          end
                        in
                        let frame1 = find_frame v1 in
                        let frame2 = find_frame v2 in
                        let prepare e = apply_unifier_expr unifier' e |> freeze_variables |> simplify_expr in
                        (*F.printf "frame = {%a} %a\n" (pp_list ", " pp_expr) (L.map frame1.frame_sigma ~f:prepare) pp_expr (prepare v1); *)
                        begin match deduce { frame1 with frame_sigma = L.map frame1.frame_sigma ~f:prepare; } (prepare v1) with
                        | None -> assert false
                        | Some formula ->
                           let v2' =
                             L.fold_left (range 0 (L.length frame2.frame_sigma))
                                 ~init:formula
                                 ~f:(fun formula' i -> replace_expr formula' ~old:(Var ("%"^(string_of_int (i+1)))) ~by:(L.nth_exn frame2.frame_sigma i))
                           in
                           (*F.printf "1) %a\n" pp_expr formula;
                           F.printf "2) %a\n" pp_expr (prepare v2);
                           F.printf "3) %a\n\n" pp_expr (prepare v2');*)
                           equal_expr (prepare v2) (prepare v2')
                        end
                    )
                 in
                 if not is_valid_unifier then None
                 else
                   (* At this point we just need to check unifier' satisfies the inequlities *)
                   if check_inequalities unifier' u.unif_inequalities then Some unifier'
                   else None
              end
            )
       with
       | Some sol -> Some sol
       | None -> aux rest
  in
  if L.length u.unif_equalities = 0 then Some (S.Map.empty)
  else aux (unify_all u)


let find_simulator2 (u, knowledge, additional) =
  let rec aux = function
    | [] -> None
    | unifier :: rest ->
       let knowledge' = update_knowledge unifier knowledge in
       let validate candidate =
         let unifier' =
           S.Map.of_alist_exn
             ((S.Map.to_alist (S.Map.map unifier
                                         ~f:(fun e -> apply_unifier_expr candidate e |> simplify_expr)))
              @ (S.Map.to_alist candidate))
         in
         let is_valid_unifier = L.fold_left additional
              ~init:true
              ~f:(fun b (v1,v2) ->
                if not b then b
                else
                  let find_frame v =
                    begin match L.find knowledge ~f:(fun (v',_) -> equal_expr v v') with
                    | None -> assert false
                    | Some (_,frame) -> frame
                    end
                  in
                  let frame1 = find_frame v1 in
                  let frame2 = find_frame v2 in
                  let prepare e = apply_unifier_expr unifier' e |> freeze_variables |> simplify_expr in
                  let forbidden = consts (prepare v1) |> L.filter ~f:(fun s -> S.slice s 0 1 = "%") in
                  begin match deduce { frame_names = frame1.frame_names @ forbidden; frame_sigma = L.map frame1.frame_sigma ~f:prepare; } (prepare v1) with
                  | None -> false (* assert false *)
                  | Some formula ->
                     let v2' =
                       L.fold_left (range 0 (L.length frame2.frame_sigma))
                             ~init:formula
                             ~f:(fun formula' i -> replace_expr formula' ~old:(Var ("%"^(string_of_int (i+1)))) ~by:(L.nth_exn frame2.frame_sigma i))
                     in
                     equal_expr (prepare v2) (prepare v2')
                  end
              )
         in
         if not is_valid_unifier then None
         else
           (* At this point we just need to check unifier' satisfies the inequlities *)
           if check_inequalities unifier' u.unif_inequalities then Some unifier'
           else None
       in
       let sol = lazy_knowledge_constraints ~validate knowledge' in
       match sol with
       | Some _ -> sol
       | None -> aux rest
  in
  if L.length u.unif_equalities = 0 then Some (S.Map.empty)
  else aux (unify_all u)
