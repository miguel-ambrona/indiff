(* Attacks search *)

open Core_kernel.Std
open Abbrevs

let analyze_commands h primitive =
  GenerateDistinguisher.(
    analyzing_file := primitive;
    EvalSearch.search_for_attack ~heuristic:h (Parse.p_attack primitive);
  );
  exit 0

let attacks_search =
  if Array.length Sys.argv <> 3 then
    output_string stderr (F.sprintf "usage: %s {1/2} <scheme file>\n" Sys.argv.(0))
  else
    analyze_commands (Int.of_string Sys.argv.(1)) (Analyze.input_file Sys.argv.(2))
