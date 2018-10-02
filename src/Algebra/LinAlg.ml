(* * Simple linear algebra (equation solving) over a field. *)

(* ** Imports *)

open Array
open Util

module type Field = sig
  type t
  val pp : Format.formatter -> t -> unit
  val add  : t -> t -> t
  val neg  : t -> t
  val mul  : t -> t -> t
  val inv  : t -> t
  val one  : t
  val zero : t
  val is_zero : t -> bool
  val is_one : t -> bool
end

module LinAlg (Field : Field) = struct

  (* ** Types and utility functions
   * ----------------------------------------------------------------------- *)
  type t = Field.t
  let ( +! ) = Field.add
  let ( *! ) = Field.mul
  let inv = Field.inv
  let neg = Field.neg
  let one = Field.one
  let zero = Field.zero
  let is_zero = Field.is_zero
  let is_one = Field.is_one

  type col = int

  type row = int

  type solved =
      Pivot of row * col
    | Solved of (t list) option

  let cols m = length m.(0) - 1 (* the last column is the solution *)

  let rows m = length m

  let sol_col m = cols m

  let _col_to_list m c =
    let res = ref [] in
    for r = rows m - 1 downto 0 do
      res := m.(r).(c)::!res
    done;
    !res

  let pp_row_vec pp_entry fmt v =
    let entries = to_list v in
    Format.fprintf fmt "[%a]" (pp_list ";" pp_entry) entries

  let pp_matrix pp_entry fmt m =
    let rows = to_list m in
    Format.fprintf fmt "@[<hov 1>[%a]@]" (pp_list ";@. " (pp_row_vec pp_entry)) rows

  let iter_rows m f =
    for r = 0 to rows m - 1 do
      f r
    done

  let _iter_cols m f =
    for c = 0 to cols m - 1 do
      f c
    done

  let iter_cols_with_sol m f =
    for c = 0 to cols m do
      f c
    done

  (* ** Equation solving
   * ----------------------------------------------------------------------- *)

  let make_pivot_one m r c =
    let pivot_inverse = inv m.(r).(c) in
    iter_cols_with_sol m (fun c' ->
      m.(r).(c') <- m.(r).(c') *! pivot_inverse)

  (** Find all-zero columns and columns that only have one non-zero entry. *)
  let classify_cols m =
    let col_is_z    = make (cols m + 1) false in (* i-th column is zero vector, also track for solution *)
    let col_is_std  = make (cols m + 1) false in (* i-th column is standard basis vector *)
    let std_has_col = make (rows m) None      in (* i-th standard basis vector is equal to given column of m *)
    iter_cols_with_sol m (fun c ->
      let one_rowidx = ref None in
      (try
         iter_rows m (fun r ->
           if not (is_zero m.(r).(c)) then (
             if !one_rowidx = None
             then one_rowidx := Some(r)
             else raise Not_found (*i two non-zero entries i*)));
         match !one_rowidx with
         | None ->
            col_is_z.(c) <- true
         | Some(ri) ->
            if c <> sol_col m then (
              make_pivot_one m ri c;
              col_is_std.(c)   <- true;
              std_has_col.(ri) <- Some(c))
       with Not_found -> ()));
    (col_is_z, col_is_std, std_has_col)

  let is_solved m =
    let (col_is_z,col_is_std,std_has_col) = classify_cols m in
    let module M = struct exception Found of solved end in
    try
      iter_cols_with_sol m (fun c ->
        if not (col_is_z.(c) || col_is_std.(c)) then (
          iter_rows m (fun r ->
            if not (is_zero m.(r).(c)) && std_has_col.(r) = None then (
              if c <> sol_col m then raise (M.Found(Pivot(r,c)))
              else raise (M.Found(Solved None))))));
      let sol = make (cols m) zero in
      iter_rows m (fun r ->
        if not (is_zero m.(r).(sol_col m)) then
          match std_has_col.(r) with
          | Some c -> sol.(c) <- m.(r).(sol_col m)
          | None -> failwith "impossible");
      Solved(Some (to_list sol))
    with
      M.Found sol -> sol

  let add_row_to m r1 r2 f =
    iter_cols_with_sol m (fun c ->
      m.(r1).(c) <- m.(r1).(c) +! (f *! m.(r2).(c)))

  let reduce_pivot m r c =
    make_pivot_one m r c;
    iter_rows m (fun r' ->
      if r' <> r && not (is_zero m.(r').(c)) then
        add_row_to m r' r (neg m.(r').(c)))

  let transpose m =
    let rownum = length m in
    let colnum = length m.(0) in
    let newrow = make rownum zero in
    let m'     = make colnum newrow in
    iter_rows m' (fun r ->
      m'.(r) <- make rownum zero;
      iter_cols_with_sol m' (fun c ->
        m'.(r).(c) <- m.(c).(r)));
    m'

  let solve (m0 : (t list) list) (b : t list) =
    let m0 = to_list (transpose (of_list (List.map of_list m0))) in
    let m = of_list (m0 @ [of_list b]) in
    let m = transpose m in
    let rec go () =
      match is_solved m with
      | Pivot(r,c) ->
         reduce_pivot m r c;
         go ()
      | Solved s -> s
    in go ()

  let solve_matrix (m0 : (t list) list) (b : t list) =
    let m0 = to_list (transpose (of_list (List.map of_list m0))) in
    let m = of_list (m0 @ [of_list b]) in
    let m = transpose m in
    let rec go () =
      match is_solved m with
      | Pivot(r,c) ->
         reduce_pivot m r c;
         go ()
      | Solved a ->
         match a with | None -> None | Some _ -> Some (List.map to_list (to_list m))
    in go ()

end
