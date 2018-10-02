(* Expressions and simplification functions *)

open Core_kernel.Std
open Abbrevs
open Util

(* ** Expression definitions *)

type mode = | POS | NEG
type name = string
type alias = string
type idx = int
type invertible = bool
type blocked = bool

type expr =
  | Const of string
  | Var   of string
  | F     of name * idx * mode * (expr list * expr list) * invertible * blocked * (alias option)
  | XOR   of expr list
  | Zero

(* ** Pretty printing *)

let string_of_mode = function
  | POS -> ""
  | NEG ->
     if !use_colors then "\xE2\x81\xBB" ^ "\xC2\xB9"
     else "^{-1}"

let rec string_of_expr = function
  | Const(c) -> c
  | Var(x)   -> (color "red" x)
  | F(name, i, mode, (left_input, right_input), inv, blocked, alias) ->
     let idx =
       if L.length right_input = 1 then
         if not (i = 0) then assert false
         else  ""
       else "_" ^ (string_of_int (i+1))
     in
     let right_content = string_of_list "," string_of_expr right_input in
     let content =
       if L.length left_input = 0 then right_content
       else (string_of_list "," string_of_expr left_input)^ "; " ^ right_content
     in
     (color (if blocked then "yellow" else if inv then "blue" else "none")
            (match alias with
             | None -> name ^ (string_of_mode mode)
             | Some a -> a
            )
     )
     ^ idx ^ "("  ^ content ^ ")"
  | XOR(exprs) -> string_of_list (" " ^ !xor_symbol ^ " ") string_of_expr exprs
  | Zero        -> "0"

let pp_expr _fmt expr =
  F.printf "%s" (string_of_expr expr)


(* ** Comparison functions *)

let inv_mode = function
  | POS -> NEG
  | NEG -> POS

let compare_mode m1 m2 =
  match m1, m2 with
  | POS, NEG -> +1
  | NEG, POS -> -1
  | _ -> 0

let compare_name = compare_string
let compare_idx = compare_int
let compare_blocked = compare_bool

let rec compare_expr e1 e2 =
  match e1, e2 with
  | Zero, Zero         -> 0
  | Zero, _            -> -1
  | _, Zero            -> +1
  | Const c1, Const c2 -> compare_string c1 c2
  | Const _, _         -> -1
  | _, Const _         -> +1
  | Var x1, Var x2     -> compare_string x1 x2
  | Var _, _           -> -1
  | _, Var _           -> +1

  | F(n1,i1,m1,(l1,r1),_,_,_), F(n2,i2,m2,(l2,r2),_,_,_) ->
     let c = compare_name n1 n2 in if c <> 0 then c
     else let c = compare_idx i1 i2 in if c <> 0 then c
     else let c = compare_mode m1 m2 in if c <> 0 then c
     else let c = compare_lists ~compare:compare_expr l1 l2 in if c <> 0 then c
     else compare_lists ~compare:compare_expr r1 r2

  | F(_), _ -> -1
  | _, F(_) -> +1
  | XOR exs1, XOR exs2 -> compare_lists ~compare:compare_expr exs1 exs2

let equal_mode m1 m2    = compare_mode m1 m2 = 0
let equal_name n1 n2    = compare_name n1 n2 = 0
let equal_idx i1 i2     = compare_idx i1 i2 = 0
let equal_blocked b1 b2 = compare_blocked b1 b2 = 0
let equal_expr e1 e2    = compare_expr e1 e2 = 0

let is_zero = function | Zero -> true | _ -> false

(* ** Simplification functions *)

let rec normalize_xor expr =
  match expr with
  | XOR exprs ->
     let exprs' = L.map ~f:normalize_xor exprs in
     let with_xor, without_xor = split_list ~f:(function | XOR(_) -> true | _ -> false) exprs' in
     XOR ((L.map with_xor ~f:(function XOR(l) -> l | a -> [a]) |> L.concat) @ without_xor)

  | F(n,i,m,(left,right),inv,b,a) ->
     let f = normalize_xor in
     F(n,i,m,(L.map ~f left, L.map ~f right),inv,b,a)

  | _ -> expr

let check_inverse n i m left right =
  let rec aux k y = function
    | [] -> Some (L.nth_exn y i)
    | e :: rest ->
       begin match e with
       | F(n',i',m',(left',right'),inv,_,_) ->
          if not inv then None
          else
            let y = if y = [] then right' else y in
            if not (equal_name n n') || not (equal_idx k i') || not (equal_mode m m') then None
            else
              if not ((compare_lists ~compare:compare_expr left left') = 0) then None
              else if not ((compare_lists ~compare:compare_expr y right') = 0) then None
              else aux (k+1) y rest
       | _ -> None
       end
  in
  aux 0 [] right

let rec simplify_expr_step expr =
  let expr = normalize_xor expr in
  match expr with
  | Zero | Const _ | Var _ -> expr

  | F(n,i,m,(left,right),inv,b,a) ->
     let left' = L.map ~f:simplify_expr_step left in
     let right' = L.map ~f:simplify_expr_step right in
     begin match check_inverse n i (inv_mode m) left' right' with
     | Some res -> res
     | None -> F(n,i,m,(left',right'),inv,b,a)
     end

  | XOR exprs ->
     let exprs' =
       L.map ~f:(fun e -> simplify_expr_step e |> normalize_xor) exprs
       |> L.sort ~cmp:compare_expr
     in
     if L.length exprs' = 0 then Zero
     else
       let rec aux output = function
         | [] -> output
         | a :: [] -> output @ [a]
         | a :: b :: rest ->
            if equal_expr a b then aux output rest
            else aux (output @ [a]) (b :: rest)
       in
       begin match (aux [] exprs') |> L.filter ~f:(function | Zero -> false | _ -> true) with
       | [] -> Zero
       | e :: [] -> e
       | list -> XOR (list)
       end

let simplify_expr expr =
  let rec aux previous this =
    if equal_expr previous this then this
    else aux this (simplify_expr_step this)
  in
  aux expr (simplify_expr_step expr)

let rec replace_expr ~old ~by expr =
  if equal_expr (simplify_expr old) (simplify_expr expr) then by
  else
    match expr with
    | Const _ | Var _ | Zero -> expr
    | F(n,i,m,(left,right),inv,b,a) ->
       let left' = L.map left ~f:(replace_expr ~old ~by) in
       let right' = L.map right ~f:(replace_expr ~old ~by) in
       F(n,i,m,(left',right'),inv,b,a)
    | XOR(exprs) -> XOR(L.map exprs ~f:(replace_expr ~old ~by))

(* ** Util functions *)

let rec atoms expr =
  begin match expr with
  | Zero -> []
  | Const _ | Var _ -> [expr]
  | F(_,_,_,(left,right),_,_,_) -> L.map (left @ right) ~f:atoms |> L.concat
  | XOR(exprs) -> L.map exprs ~f:atoms |> L.concat
  end
  |> L.dedup ~compare:compare_expr

let vars expr = L.map (atoms expr) ~f:(function | Var x -> [x] | _ -> []) |> L.concat

let consts expr = L.map (atoms expr) ~f:(function | Const x -> [x] | _ -> []) |> L.concat

let rec fun_depth = function
  | Zero | Const _ | Var _ -> 0
  | XOR(exprs) -> list_maximum (L.map exprs ~f:fun_depth ) ~greater_than_or_equal:(>)
  | F(_,_,_,(left,right),_,_,_) ->
     1 + (list_maximum (L.map (left@right) ~f:fun_depth ) ~greater_than_or_equal:(>))

let rec syntactic_subterms expr =
  let clean list = L.concat list |> dedup_preserving_order ~equal:equal_expr in
  match expr with
  | Zero | Const _ | Var _ -> [expr]
  | XOR(exprs) -> expr :: (L.map exprs ~f:syntactic_subterms |> clean )
  | F(_,_,_,(left,right),_,_,_) -> expr :: (L.map (left @ right) ~f:syntactic_subterms |> clean)

let expr_is_subterm_of_expr e1 e2 =
  L.exists (syntactic_subterms e2) ~f:(equal_expr e1)
