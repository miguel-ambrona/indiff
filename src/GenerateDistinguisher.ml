open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Unification

let analyzing_file = ref ""

let generate_code2 ~oname ~atoms relations =
  let function_subterms_all =
    L.map relations ~f:(fun e -> syntactic_subterms e)
    |> L.concat
    |> L.filter ~f:(function | F(name,_,_,(_,_),_,_,_) -> name <> oname | _ -> false)
    |> L.dedup ~compare:compare_expr
    |> top_sort ~cmp:(fun t1 t2 -> (* Smaller first *)
                  if equal_expr t1 t2 then 0
                  else if expr_is_subterm_of_expr t1 t2 then -1
                  else if expr_is_subterm_of_expr t2 t1 then +1
                  else 0
                )
  in

  let rec aux assignments = function
    | [] -> assignments
    | s :: rest ->
       let name = fresh_name () in
       let assignments' = assignments @ [(s, name)] in
       let rest' = L.map rest ~f:(replace_expr ~old:s ~by:(Var name) ) in
       aux assignments' rest'
  in
  (*
  F.printf "Total: %d\n" (L.length function_subterms_all);
  L.iter function_subterms_all ~f:(fun s -> F.printf "%a\n\n" (pp_list ",\n" pp_expr) s);
   *)
  L.fold_left function_subterms_all
      ~init:false
      ~f:(fun b function_subterms ->
        if b then b
        else
          let assignments = aux [] function_subterms in
          let replace e = L.fold_left assignments ~init:e ~f:(fun e' (s,name) -> replace_expr e' ~old:s ~by:(Var name) |> simplify_expr) in
          let file_code =
            match S.split ~on:'{' !analyzing_file with
            | _ :: s :: [] ->
               begin match S.split ~on:'}' s with
               | code :: _ :: [] -> code
               | _ -> assert false
               end
            | _ -> failwith "Please, introduce one single attack search problem in the input file"
          in

          let filename = "/tmp/attack.txt" in

          let out_file = open_out filename in
          fprintf out_file "is_universal{%s\n  distinguisher :=\n" file_code;
          let colors = !use_colors in
          use_colors := false;
          let old_xor_symbol = !xor_symbol in
          xor_symbol := "+";
          L.iter atoms ~f:(fun n -> fprintf out_file "    %s <-$ {0,1}^n;\n" n);
          L.iter assignments ~f:(fun (s,name) -> fprintf out_file "    %s <- %s;\n" name (string_of_expr s)); fprintf out_file "\n";
          L.iter relations ~f:(fun r -> fprintf out_file "    assert %s = 0;\n" (string_of_expr (replace r)));
          fprintf out_file "    return 1;\n";
          fprintf out_file "  .\n\n}.\n";

          let _ = close_out_noerr out_file in

          use_colors := colors;
          xor_symbol := old_xor_symbol;

          let cmds = Analyze.input_file filename in
          begin match Parse.p_cmds cmds with
          | Eval.IsUniversal (rs, os, program) :: [] ->
             Eval.analyze_if_it_is_universal ~print:false (rs, os, program)

          | _ -> failwith "Please, introduce a single problem for checking that an attacker is universal"
          end
      )


let generate_distinguishers_code ~oname (sol, relations, (variable_tuples, keys)) =
  let inputs = L.filter (Map.to_alist sol) ~f:(function | (n,_) -> (S.slice n 0 1) = "X") in
  let atoms = L.map inputs ~f:(fun (_,e) -> vars e ) |> L.concat |> L.dedup in

  let function_subterms_all =
    L.map (relations @ (L.map inputs ~f:(fun (_,e) -> e))) ~f:(fun e -> syntactic_subterms e)
    |> L.concat
    |> L.filter ~f:(function | F(_) -> true | _ -> false)
    |> L.dedup ~compare:compare_expr
    |> top_sort ~cmp:(fun t1 t2 -> (* Smaller first *)
                  if equal_expr t1 t2 then 0
                  else if expr_is_subterm_of_expr t1 t2 then -1
                  else if expr_is_subterm_of_expr t2 t1 then +1
                  else 0
                )
  in

  let rec aux assignments = function
    | [] -> assignments
    | s :: rest ->
       let name = fresh_name () in
       let assignments' = assignments @ [(s, name)] in
       let rest' = L.map rest ~f:(replace_expr ~old:s ~by:(Var name) ) in
       aux assignments' rest'
  in

  F.printf "Total: %d\n" (L.length function_subterms_all);
  L.iter function_subterms_all ~f:(fun s -> F.printf "%a\n\n" (pp_list ",\n" pp_expr) s);

  L.fold_left function_subterms_all
      ~init:false
      ~f:(fun b function_subterms ->
        if b then b
        else
          let assignments = aux [] function_subterms in
          let replace e = L.fold_left assignments ~init:e ~f:(fun e' (s,name) -> replace_expr e' ~old:s ~by:(Var name) |> simplify_expr) in
          let file_code =
            match S.split ~on:'{' !analyzing_file with
            | _ :: s :: [] ->
               begin match S.split ~on:'}' s with
               | code :: _ :: [] -> code
               | _ -> assert false
               end
            | _ -> failwith "Please, introduce one single attack search problem in the input file"
          in

          let filename = "/tmp/attack.txt" in

          let out_file = open_out filename in
          fprintf out_file "is_universal{%s\n  distinguisher :=\n" file_code;
          let colors = !use_colors in
          use_colors := false;
          let old_xor_symbol = !xor_symbol in
          xor_symbol := "+";
          L.iter atoms ~f:(fun n -> fprintf out_file "    %s <-$ {0,1}^n;\n" n); fprintf out_file "\n";
          L.iter assignments ~f:(fun (s,name) -> fprintf out_file "    %s <- %s;\n" name (string_of_expr s)); fprintf out_file "\n";
          L.iter inputs ~f:(fun (n,e) -> fprintf out_file "    %s = %s;\n" n (string_of_expr (replace e))); fprintf out_file "\n";
          let sep = if keys = [] then "" else "; " in
          L.iter variable_tuples
                 ~f:(fun (ins,outs) ->
                   L.iter (range 0 (L.length outs))
                          ~f:(fun i -> fprintf out_file "    %s = %s_%d(%s%s%s);\n" (string_of_expr (L.nth_exn outs i)) oname (i+1)
                                               (string_of_list ", " string_of_expr keys) sep
                                               (string_of_list ", " string_of_expr ins);
                             )
                 )
          ; fprintf out_file "\n";
          L.iter relations ~f:(fun r -> fprintf out_file "    assert %s = 0;\n" (string_of_expr r));

          let variables = L.map variable_tuples ~f:(fun (ins,outs) -> (ins @ outs)) |> L.concat in

          let replace2 = function | Var n -> (begin match Map.find sol n with | Some e -> e | None -> Var n |> simplify_expr end) | _ -> assert false in
          let n_vars = L.length variables in
          L.iter (range 0 (n_vars - 1))
                 ~f:(fun i -> L.iter (range (i+1) (n_vars - 1))
                                     ~f:(fun j ->
                                       let vi = L.nth_exn variables i in
                                       let vj = L.nth_exn variables j in
                                       F.printf "%a %a\n" pp_expr (replace2 vi) pp_expr (replace2 vj);
                                       if equal_expr (replace2 vi) (replace2 vj) then fprintf out_file "    assert %s = %s;\n" (string_of_expr vi) (string_of_expr vj)
                                       else fprintf out_file "    assert %s <> %s;\n" (string_of_expr vi) (string_of_expr vj)
                                     )
                    );
          fprintf out_file "    return 1;\n";
          fprintf out_file "  .\n\n}.\n";

          let _ = close_out_noerr out_file in

          use_colors := colors;
          xor_symbol := old_xor_symbol;

          let cmds = Analyze.input_file filename in
          begin match Parse.p_cmds cmds with
          | Eval.IsUniversal (rs, os, program) :: [] ->
             Eval.analyze_if_it_is_universal (rs, os, program)

          | _ -> failwith "Please, introduce a single problem for checking that an attacker is universal"
          end
      )
