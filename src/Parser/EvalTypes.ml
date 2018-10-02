(* Eval Modules Types *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Deductibility
open Static_Equivalence
open Knowledge

type is_eq = Eq | Ineq

type assignment = name * expr
type round = name * bool (* name * invertible *)
type oracle_raw = name * mode * (alias option) * (string list) * (assignment list) * (expr list)

type oracle = name * mode * int * (alias option) * (expr list) (* name, POS/NEG, key_length, alias, outputs *)

type distCmd =
  | DistCmdSamp of name
  | DistCmdAssign of name * expr
  | DistCmdSimQuery of name * name * mode * int * (expr list)
  | DistCmdAssert of (is_eq * expr)

type distProgram =
  | DistProgCmd of distCmd * distProgram
  | DistProgChoice of distProgram list
  | DistProgReturn

type primitive = int * (round list) * (oracle_raw list)

let apply_replacement rep expr =
  L.fold_left (L.rev rep) ~init:expr ~f:(fun e' (v,by) -> replace_expr e' ~old:(Const v) ~by)

let process_oracle (name, invertible, alias, inputs, assignments, outputs) =
  let rec aux replacement = function
    | [] -> L.map outputs ~f:(apply_replacement replacement)
    | (v,e) :: rest -> aux (replacement @ [(v, apply_replacement replacement e)]) rest
  in
  name, invertible, ((L.length inputs) - (L.length outputs)), alias,
  aux (L.map (range 0 (L.length inputs)) ~f:(fun i -> (L.nth_exn inputs i, Var ("%"^(string_of_int (i+1))))) ) assignments

let fun_args = ref String.Map.empty

let check_arguments_consistency (name,d_left,d_right) =
  match Map.find !fun_args name with
  | None -> fun_args := Map.add !fun_args ~key:name ~data:(d_left,d_right)
  | Some (l,r) ->
     if l = d_left && r = d_right then ()
     else
       let msg = F.sprintf "Function %s takes %d+%d inputs, %d+%d given" name l r d_left d_right in
       failwith msg

let adjust_rounds rounds os expr =
  let rec aux = function
    | Zero | Const _ | Var _ as e -> e
    | XOR(list) -> XOR(L.map list ~f:aux )
    | F(name, i, mode, (left,right), invertible, blocked, alias) ->
       check_arguments_consistency (name, L.length left, L.length right);
       begin match L.find rounds ~f:(fun (n,_) -> n = name) with
       | None ->
          if L.exists os ~f:(fun (n,inv,_,_,_) -> n = name && inv = mode) then
            let left' = L.map left ~f:aux in
            let right' = L.map right ~f:aux in
            F(name, i, mode, (left', right'), invertible, blocked, alias)
          else
            failwith ("Round function " ^ name ^ " is not defined")
       | Some (_,invertible) ->
          if not invertible && mode = NEG then failwith ("Round function " ^ name ^ " is not invertible")
          else
            let left' = L.map left ~f:aux in
            let right' = L.map right ~f:aux in
            F(name, i, mode, (left', right'), invertible, blocked, alias)
       end
  in
  aux expr

let check_oracle_inverses oracles =
  L.iter oracles
     ~f:(fun (name,m,k,_,exprs) ->
       check_arguments_consistency (name, k, L.length exprs);
       match L.filter oracles ~f:(fun (name',m',k',_,_) -> if name = name' && m <> m' then (assert (k = k'); true) else false) with
       | [] -> ()
       | (_,_,_,_,exprs') :: [] ->
          let keys = L.map (range 0 k) ~f:(fun i -> Var ("V" ^ (string_of_int i))) in
          let inputs = L.map (range 0 (L.length exprs)) ~f:(fun i -> Var ("X" ^ (string_of_int i))) in
          L.iter (range 0 (L.length exprs))
                 ~f:(fun i ->
                   let right =
                     L.map (range 0 (L.length exprs))
                        ~f:(fun i' ->
                          L.fold_left (range 0 ((L.length keys) + (L.length inputs)))
                             ~init:(L.nth_exn exprs' i')
                             ~f:(fun e j -> replace_expr e ~old:(Var ("%"^(string_of_int (j+1)))) ~by:(L.nth_exn (keys@inputs) j))
                        )
                   in
                   let this_expr =
                     L.fold_left (range 0 ((L.length keys) + (L.length inputs)))
                         ~init:(L.nth_exn exprs i)
                         ~f:(fun e j -> replace_expr e ~old:(Var ("%"^(string_of_int (j+1)))) ~by:(L.nth_exn (keys@right) j))
                   in
                   if (L.nth_exn inputs i) = (simplify_expr this_expr) then ()
                   else
                     (F.printf "%a\nis not equal to\n%a\n" pp_expr (L.nth_exn inputs i) pp_expr (simplify_expr this_expr);
                      failwith ("The inverse of oracle " ^ name ^ " is not properly defined"));
                 )
       | _ -> failwith ("Oracle " ^ name ^ " is defined too many times")
     )

let apply_oracles_to_expr ~real oracles expr =
  let rec aux = function
    | Zero | Const _ | Var _ as e -> e
    | XOR (list) -> XOR(L.map list ~f:aux )
    | F(name, i, mode, (left,right),invertible,blocked,alias) ->
       check_arguments_consistency (name, L.length left, L.length right);
       let left' = L.map left ~f:aux in
       let right' = L.map right ~f:aux in
       let arguments = left' @ right' in
       begin match L.find oracles ~f:(fun (n',m',_,_,_) -> n' = name && m' = mode) with
       | None -> F(name,i,mode,(left',right'),invertible,blocked,alias) (* This comes from a round function *)
       | Some (_,_,_,new_alias,outputs) ->
          if real then
            L.fold_left (range 0 (L.length arguments))
                ~init:(L.nth_exn outputs i)
                ~f:(fun e j -> replace_expr e ~old:(Var ("%"^(string_of_int (j+1)))) ~by:(L.nth_exn arguments j))
          else
            let invertible =
              begin match L.find oracles ~f:(fun (n',m',_,_,_) -> n' = name && m' = NEG) with
              | Some _ -> true
              | None -> if mode = NEG then failwith ("The inverse of oracle " ^ name ^ " is not defined") else false
              end
            in
            F(name,i,mode,(left',right'),invertible,blocked,new_alias)
       end
  in
  aux expr

let rec contains_round rs = function
  | Zero | Const _ | Var _ -> false
  | XOR(list) -> L.exists list ~f:(contains_round rs)
  | F(name,_,_,(left,right),_,_,_) ->
     check_arguments_consistency (name, L.length left, L.length right);
     if L.exists rs ~f:(fun (n,_) -> n = name) then true else L.exists (left@right) ~f:(contains_round rs)


let build_system_from_program rs oracles program =
  let var_counter = ref 0 in
  let atoms = ref [] in
  let variables = ref [] in
  let check_constants list e =
    L.iter (consts e) ~f:(fun c -> if L.mem list c ~equal:S.equal then () else failwith ("Undefined value " ^ c))
  in
  let rec aux rep sim_rep knowledge system = function
    | DistProgCmd(cmd, p) ->
       begin match cmd with
       | DistCmdSamp (n) -> atoms := !atoms @ [n]; aux rep sim_rep knowledge system p
       | DistCmdAssign (v,e) ->
          variables := !variables @ [v];
          check_constants (!atoms @ !variables) e;
          if contains_round rs (adjust_rounds rs oracles e) then
            failwith "Do not use round functions in an assigment, make explicit calls to round functions with '<-'"
          else aux (rep @ [(v, apply_replacement rep e)]) (sim_rep @ [(v, apply_replacement sim_rep e)]) knowledge system p
       | DistCmdSimQuery (v,n,m,i,args) ->
          variables := !variables @ [v];
          L.iter args ~f:(check_constants (!atoms @ !variables));
          let invertible =
            begin match L.find rs ~f:(fun (n',_) -> n = n') with
            | Some (_,inv) -> inv
            | None -> failwith ("Round function " ^ n ^ " is not defined")
            end
          in
          let () = if not invertible && m = NEG then failwith ("Round function " ^ n ^ " is not invertible") else () in
          let e = F(n,i,m,([],L.map args ~f:(apply_replacement rep)), invertible, false, None) in
          var_counter := !var_counter + 1;
          let e' = Var ("V" ^ (string_of_int !var_counter)) in
          aux (rep @ [(v,e)]) (sim_rep @ [(v,e')]) (knowledge @ [(e',n,i,m,L.map args ~f:(apply_replacement sim_rep))]) system p
       | DistCmdAssert(is_eq, e) ->
          if contains_round rs e then
            failwith "Do not use round functions in an assigment, make explicit calls to round functions with '<-'"
          else
            let e' = apply_replacement rep e in
            check_constants (!atoms @ !variables) e';
            let e' = apply_oracles_to_expr ~real:true oracles e' |> simplify_expr in
            if (equal_expr e' Zero && is_eq = Ineq) || (not (equal_expr e' Zero) && is_eq = Eq) then
              (F.printf "Assert %a %s 0 does not hold in the real world\n" pp_expr e
                        (match is_eq with | Eq -> "=" | Ineq -> "<>");
               F.printf "The expression equals %a\n" pp_expr e';
               failwith "Redefine your distinguisher to include the opposite operator in this assert")
            else
              let e'' = apply_replacement sim_rep e |> (apply_oracles_to_expr ~real:false oracles) in
              aux rep sim_rep knowledge (system @ [(is_eq,e'')]) p
       end
    | DistProgChoice(ps) ->
       L.fold_left (L.map ps ~f:(aux rep sim_rep knowledge system))
           ~init:([],[])
           ~f:(fun (knowledges, accum_system) (knowledge, system) -> knowledges @ knowledge, accum_system @ system)

    | DistProgReturn -> [knowledge], system
  in
  let knowledges, system = aux [] [] [] [] program in
  (knowledges, system, !atoms)



let equivalent_branches ~k b1 b2 =
  if k >= (L.length b1) || k >= (L.length b2) then false
  else
    let b1_k = L.slice b1 0 (k+1) in
    let b2_k = L.slice b2 0 (k+1) in
    if L.exists (L.zip_exn b1_k b2_k) ~f:(fun ((_,n1,i1,m1,_),(_,n2,i2,m2,_)) -> n1 <> n2 || i1 <> i2 || m1 <> m2) then false
    else
      let frame1_elements = L.fold_left b1_k ~init:[] ~f:(fun l (_,_,_,_,args) -> l @ args ) in
      let frame2_elements = L.fold_left b2_k ~init:[] ~f:(fun l (_,_,_,_,args) -> l @ args ) in
      let forbidden_names = L.fold_left (frame1_elements @ frame2_elements) ~init:[] ~f:(fun l e -> l @ (consts e)) |> L.dedup in
      assert (L.length frame1_elements = L.length frame2_elements);
      assert (not (L.exists forbidden_names ~f:(fun n -> "%" = (S.slice n 0 1))));
      let rec f = function
        | Zero | Const _  as e -> e
        | Var n -> Const ("%" ^ n)
        | F(n,i,m,(left,right),inv,b,a) ->
           check_arguments_consistency (n, L.length left, L.length right);
           F(n,i,m,(L.map left ~f, L.map right ~f),inv,b,a)
        | XOR(l) -> XOR(L.map l ~f)
      in
      let frame1 = { frame_names = forbidden_names; frame_sigma = L.map frame1_elements ~f; } in
      let frame2 = { frame_names = forbidden_names; frame_sigma = L.map frame2_elements ~f; } in
      (*      F.printf "frame1: %a\n" (pp_list ", " pp_expr) frame1.frame_sigma;
      F.printf "frame2: %a\n" (pp_list ", " pp_expr) frame2.frame_sigma;
      F.printf "%b\n\n" b;*)
      let b = static_equivalence frame1 frame2 in
      b

let static_equivalent_conditions branches =
  let rec aux k = function
    | [] | _ :: [] -> []
    | branch :: rest ->
       (* Up to the k-th query, all branches are equivalent *)
       if k >= (L.length branch) then aux k rest
       else
         let (var,_,_,_,_) = L.nth_exn branch k in
         let eq_to_branch, others = split_list rest ~f:(fun b -> equivalent_branches branch b ~k) in
         (L.map eq_to_branch ~f:(fun b' -> let (var',_,_,_,_) = L.nth_exn b' k in (var, var')))
           @ (aux (k+1) (branch :: eq_to_branch)) @ (aux k others)
  in
  aux 0 branches
  |> L.filter ~f:(fun (e1,e2) -> not (equal_expr e1 e2))

let simplify_frame known_vars frame =
  let known_vars = L.map known_vars ~f:freeze_variables in
  let consts = L.map known_vars ~f:consts |> L.concat |> L.dedup ~compare:S.compare in
  let frame' = { frame_sigma = (L.map frame.frame_sigma ~f:freeze_variables ) @ known_vars;
                 frame_names = frame.frame_names @ consts }
  in
  let deductible_names = L.filter frame.frame_names ~f:(fun n -> match deduce frame' (Const n) with | Some _ -> true | None -> false) in
  { frame_sigma = L.filter frame.frame_sigma ~f:(fun e -> match deduce frame' (freeze_variables e) with | None -> true | Some _ -> false);
    frame_names = L.filter frame.frame_names ~f:(fun n -> not (L.mem deductible_names n ~equal:S.equal)) }

let build_knowledge_conditions atoms knowledges =
  let rec aux frames known known_vars = function
    | [] -> frames
    | (var,_,_,_,exprs) :: rest ->
       let new_frame = { frame_names = atoms; frame_sigma = known @ exprs } in
       aux (frames @ [(var,new_frame,known_vars)]) (known @ exprs) (known_vars @ [var]) rest
  in
  L.map knowledges ~f:(fun k -> aux [] [] [] k)
  |> L.concat
  |> L.map ~f:(fun (v,f,k) -> (v, simplify_frame k f))
