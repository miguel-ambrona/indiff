(* Evaluate input from the Parser *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Unification
open Deductibility
open Static_Equivalence
open FullUnification
open Knowledge
open Simulator
open EvalTypes

let make_unif_problem equations =
  let rec aux eqs ineqs = function
    | [] -> make_unif_problem eqs ineqs
    | (Eq,e)   :: rest-> aux (eqs @ [e]) ineqs rest
    | (Ineq,e) :: rest -> aux eqs (ineqs @ [e]) rest
  in
  aux [] [] equations

let make_frame (exprs, names) = { frame_names = names; frame_sigma = exprs; }

type command =
  | Simplify  of expr
  | Unify     of unif_problem
  | Deduce    of expr * frame
  | StaticE   of frame * frame
  | Knowledge of expr list * frame list
  | IsUniversal  of (round list) * (oracle_raw list) * distProgram

let analyze_if_it_is_universal ?(print = true) (rs, os, program) =
  L.iter rs ~f:(fun (n,_) ->
        if (L.count rs ~f:(fun (n',_) -> n = n')) <> 1 then failwith ("Round function " ^ n ^ " is multiply defined") else ());
  let oracles = L.map os ~f:process_oracle in
  let oracles = L.map oracles ~f:(fun (n,inv,klength,a,exprs) -> (n, inv, klength, a, L.map exprs ~f:(adjust_rounds rs oracles))) in
  check_oracle_inverses oracles;
  let knowledges, system, atoms = build_system_from_program rs oracles program in
  let additional = static_equivalent_conditions knowledges in
  let knowledge_conditions =
    build_knowledge_conditions atoms knowledges
    |> dedup_preserving_order
         ~equal:(fun (v1,f1) (v2,f2) ->
           if equal_expr v1 v2 then (assert ((compare_lists f1.frame_sigma f2.frame_sigma ~compare:compare_expr ) = 0); true)
           else false)
  in
  let equalities, inequalities = split_list system ~f:(function | (Eq,_) -> true | _ -> false) in
  let equalities = L.map equalities ~f:(fun (_,e) -> simplify_expr e) |> dedup_preserving_order ~equal:equal_expr in
  let inequalities = L.map inequalities ~f:(fun (_,e) -> simplify_expr e) |> dedup_preserving_order ~equal:equal_expr in
  let u = { unif_equalities = equalities; unif_inequalities = inequalities; } in
  let variables = L.map (u.unif_equalities @ u.unif_inequalities) ~f:vars |> L.concat |> L.dedup ~compare:S.compare in
  safe_fresh_idxs variables;
  safe_fresh_idxs atoms;

  if print then
    (F.printf "atoms: [%a]\n\n" (pp_list ", " pp_string) atoms;
     L.iter (L.zip_exn (range 0 (L.length knowledges)) knowledges)
            ~f:(fun (i,k) -> F.printf "Branch %d:\n" (i+1);
                             L.iter k ~f:(fun (var,name,i,_,exprs) ->
                                      F.printf " (%a, %s, %d, %a)\n" pp_expr var name i
                                               (pp_list "; " pp_expr) exprs); F.printf "end\n\n");

     F.printf "Unification problem:\n%a\n\n" pp_unif_problem u;
     F.printf "Static-eq constraints:\n";
     L.iter additional ~f:(fun (e1,e2) -> F.printf " (%a,%a)\n" pp_expr e1 pp_expr e2);
     F.printf "\n";

     F.printf "Knowledge constraints:\n";
     L.iter knowledge_conditions ~f:(fun (v,f)->
              F.printf "%a -> {%a} with names = {%a}\n" pp_expr v (pp_list ", " pp_expr) f.frame_sigma (pp_list ", " pp_string) f.frame_names);
     F.printf "\n\n";
     F.print_flush ();
    )
  else ();

  let t1 = Unix.gettimeofday() in
  let solution = find_simulator2 (u, knowledge_conditions, additional) in
  let t2 = Unix.gettimeofday() in

  match solution with
  | None ->
     if print then
       (F.printf "There does not exist a simulator for the distinguisher\n\n";
        print_time t1 t2;  F.printf "\n")
     else ();
     true
  | Some sol ->
     if print then
       (F.printf "The following assignment represents a valid simulator for the distinguisher:\n%a\n\n"
                 pp_unifier sol;
        print_time t1 t2;  F.printf "\n")
     else ();
     false

let process_command cmd =
  match cmd with
  | Simplify e ->
     F.printf "simplify %a:\n %a\n\n\n\n" pp_expr e pp_expr (simplify_expr e)

  | Unify u ->
     let variables = L.map (u.unif_equalities @ u.unif_inequalities) ~f:vars |> L.concat |> L.dedup ~compare:S.compare in
     safe_fresh_idxs variables;
     let t1 = Unix.gettimeofday() in
     (* let solutions =  match unify u with Some a -> [a] | None -> [] in *)
     let solutions = unify_all u in
     let t2 = Unix.gettimeofday() in
     F.printf "%a\n%a\nNumber of solutions: %d\n" pp_unif_problem u pp_unifier_option (L.hd solutions) (L.length solutions);
     print_time t1 t2;
     F.printf "\n\n"

  | Deduce (e,f) ->
     F.printf "deduce %a from {%a} with names = {%a}\n"
          pp_expr e (pp_list ", " pp_expr) f.frame_sigma (pp_list ", " pp_string) f.frame_names;
     if L.exists (e :: f.frame_sigma) ~f:(fun e' -> vars e' <> []) then
       let t1 = Unix.gettimeofday() in
       let unifiers = deduce_with_vars f e in
       let t2 = Unix.gettimeofday() in
       (if unifiers = [] then F.printf "The term is not deducible for any assignment\n"
        else F.printf "The term is deducible if one of the following assignments is applied:\n%a\n"
                      (pp_list "\n\n\n" pp_unifier) unifiers;
       );
       print_time t1 t2;
       F.printf "\n\n"

     else
       let t1 = Unix.gettimeofday() in
       let solution = deduce f e in
       let t2 = Unix.gettimeofday() in
       begin match solution with
       | None -> F.printf "Non-deductible\n\n";
       | Some sol ->
          F.printf "Solution: %a\n" pp_expr sol;
          print_time t1 t2;
          F.printf "\n\n"
       end

  | StaticE (f1,f2) ->
     F.printf "static equivalent {%a} with names = {%a} vs {%a} with names = {%a}\n"
              (pp_list ", " pp_expr) f1.frame_sigma (pp_list ", " pp_string) f1.frame_names
              (pp_list ", " pp_expr) f2.frame_sigma (pp_list ", " pp_string) f2.frame_names;
     let t1 = Unix.gettimeofday() in
     let equivalent = static_equivalence f1 f2 in
     let t2 = Unix.gettimeofday() in
     F.printf "%b\n" equivalent;
     print_time t1 t2;
     F.printf "\n\n"

  | Knowledge (es,fs) ->
     if L.length es <> L.length fs then failwith "The number of expressions does not match the number of frames"
     else
       let t1 = Unix.gettimeofday() in
       let assignments = knowledge_constraints (L.zip_exn es fs) in
       let t2 = Unix.gettimeofday() in

       let color_config = !use_colors in
       use_colors := false; (* Unable colors to measure expressions length *)
       let lengths = L.map es ~f:(fun e -> S.length (string_of_expr e)) in
       use_colors := color_config;
       let max_length = L.fold_left lengths ~init:0 ~f:(fun m l -> if l > m then l else m) in
       F.printf "knowledge constraints:\n";
       L.iter (L.zip_exn (L.zip_exn lengths es) fs)
              ~f:(fun ((l,e),f) ->
                F.printf "  %a%s\tfrom {%a} with names = {%a}\n"
                         pp_expr e (S.make (max_length - l) ' ')
                         (pp_list ", " pp_expr) f.frame_sigma
                         (pp_list ", "  pp_string) f.frame_names);

       (if assignments = [] then F.printf "  There are no valid assignments\n"
        else F.printf "  Valid assignments:\n    * %a\n" (pp_list "\n    * " pp_unifier) assignments;
       );
       print_time t1 t2;
       F.printf "\n\n"

  | IsUniversal (rs, os, program) ->
     let _ = analyze_if_it_is_universal (rs, os, program) in
     ()
