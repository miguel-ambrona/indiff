(* Evaluate input from the Parser *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open EvalTypes

let search_for_attack ~heuristic (t, rs, os) =
  let attack_type = match t with | 0 -> Attacks_Search.INDCPA | 1 -> Attacks_Search.INDCCA | 2 -> Attacks_Search.Indiff | _ -> assert false in
  L.iter rs ~f:(fun (n,_) ->
           if (L.count rs ~f:(fun (n',_) -> n = n')) <> 1 then failwith ("Round function " ^ n ^ " is multiply defined") else ());
  let oracles = L.map os ~f:process_oracle in
  let oracles = L.map oracles ~f:(fun (n,inv,klength,a,exprs) -> (n, inv, klength, a, L.map exprs ~f:(adjust_rounds rs oracles))) in
  check_oracle_inverses oracles;
  L.iter oracles
         ~f:(fun (name,inv,klength,_,exprs) ->
           match inv with
           | POS -> F.printf "Defined oracle %s with %d+%d inputs\n" name klength (L.length exprs);
           | NEG -> F.printf "Defined inverse oracle %s with %d+%d inputs\n" name klength (L.length exprs)
         );
  F.printf "\n";
  let n_orcls = L.length (L.fold_left oracles ~init:[] ~f:(fun l (n,_,_,_,_) -> if L.mem l n then l else n :: l)) in
  if n_orcls <> 1 then failwith ("You must define exactly one oracle (" ^ (string_of_int n_orcls) ^ " given)")
  else
    let (name,_,k,_,exprs) = L.find_exn oracles ~f:(fun (_,inv,_,_,_) -> inv = POS) in
    let primitive keys inputs =
      assert (L.length keys = k && L.length exprs = L.length inputs);
      L.fold_left (L.zip_exn (range 0 (L.length (keys@inputs))) (keys@inputs))
                  ~init:exprs
                  ~f:(fun exprs' (i,e) -> L.map exprs' ~f:(replace_expr ~old:(Var ("%"^(string_of_int (i+1)))) ~by:e ))
    in
    let inv_primitive =
      match L.find oracles ~f:(fun (_,inv,_,_,_) -> inv = NEG) with
      | None -> None
      | Some (name',_,k,_,exprs) ->
         Some (fun keys inputs ->
             assert (name = name');
             assert (L.length keys = k && L.length exprs = L.length inputs);
             L.fold_left (L.zip_exn (range 0 (L.length (keys@inputs))) (keys@inputs))
                       ~init:exprs
                       ~f:(fun exprs' (i,e) -> L.map exprs' ~f:(replace_expr ~old:(Var ("%"^(string_of_int (i+1)))) ~by:e ))
           )
    in
    if heuristic = 2 then
      let t1 = Unix.gettimeofday() in
      let attack = Attacks_Search.iterative_heuristic2 ~primitive ~inv_primitive ~attack_type ~k ~n:(L.length exprs) ~oname:name in
      let t2 = Unix.gettimeofday() in
      F.printf "Found attack: %b\n" attack;
      print_time t1 t2
    else
      let t1 = Unix.gettimeofday() in
      let attack = Attacks_Search.heuristic ~primitive ~k ~n:(L.length exprs) ~oname:name ~context_size:7 in
      (match attack with
       | None -> F.printf "Found attack: false\n";
       | Some att ->
          let _ = GenerateDistinguisher.generate_distinguishers_code ~oname:name att in
          F.printf "Found attack: true\n";
          ()
      );
      let t2 = Unix.gettimeofday() in
      print_time t1 t2;
      F.printf "\n"

