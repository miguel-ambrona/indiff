(* Test *)

open Abbrevs

let analyze_commands cmds =
  L.iter (Parse.p_cmds cmds) ~f:(fun cmd -> Eval.process_command cmd; F.print_flush());
  exit 0

let test =
  if Array.length Sys.argv <> 2 then
    output_string stderr (F.sprintf "usage: %s <scheme file>\n" Sys.argv.(0))
  else
    analyze_commands (Analyze.input_file Sys.argv.(1))
