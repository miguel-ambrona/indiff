(* Util functions *)

open Abbrevs

let print_time t1 t2 =
  F.printf "Solved in %F ms\n" (Pervasives.ceil ((1000000.0 *. (t2 -. t1))) /. 1000.0)

let use_colors = ref true

let color col s =
  if !use_colors then
    match col with
    | "none"   -> s
    | "red"    -> "\027[31m" ^ s ^ "\027[0m"
    | "yellow" -> "\027[33m" ^ s ^ "\027[0m"
    | "blue"  -> "\027[34m" ^ s ^ "\027[0m"
    | _        -> failwith "unknown color"
  else s

let xor_symbol = ref "\xE2\x8A\x95 "

let range i j =
  let rec aux output k =
    if k >= j then output
    else aux (output @ [k]) (k+1)
  in
  aux [] i

let list_repeat a n =
  let rec aux output k =
    if k >= n then output
    else aux (a :: output) (k+1)
  in
  aux [] 0

let list_find_and_remove ~f list =
  let rec aux others = function
    | [] -> raise Not_found
    | a :: rest -> if f a then (a, others @ rest) else aux (others @ [a]) rest
  in
  aux [] list

let pp_int _ i = F.printf "%d" i
let pp_string _ s = F.printf "%s" s

let string_of_list sep string_of_a list =
  let rec aux output = function
    | []        -> output
    | a :: []   -> output ^ (string_of_a a)
    | a :: rest -> aux (output ^ (string_of_a a) ^ sep) rest
  in
  aux "" list

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> F.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let pp_matrix pp_elt f m =
  L.iter m ~f:(F.fprintf f "[%a]\n" (pp_list ", " pp_elt))

let rec compare_lists ~compare list1 list2 =
  let list1 = L.sort ~cmp:compare list1 in
  let list2 = L.sort ~cmp:compare list2 in
  match list1, list2 with
  | [], [] -> 0
  | [], _  -> -1
  | _ , [] -> +1
  | a :: rest1, b :: rest2 ->
     let c = compare a b in
     if c = 0 then compare_lists ~compare rest1 rest2 else c

let split_list ~f list =
  let rec aux out1 out2 = function
    | [] -> (out1, out2)
    | a :: rest ->
       if f a then aux (out1 @ [a]) out2 rest
       else aux out1 (out2 @ [a]) rest
  in
  aux [] [] list

let split_list_by_idx idx list =
  let rec aux k list1 list2 =
    if k = 0 then list1, list2
    else match list2 with
         | [] -> list1, list2
         | a :: rest -> aux (k-1) (list1 @ [a]) rest
  in
  aux idx [] list

(* insert x at all positions into a list *)
let rec insert x list =
  match list with
  | [] -> [[x]]
  | hd::tl -> (x::list) :: (L.map ~f:(fun l -> hd::l) (insert x tl))

(* list of all permutations of a list *)
let rec perms = function
  | [] -> [[]]
  | hd::tl -> L.concat (L.map ~f:(insert hd) (perms tl))

let some = function
  | Some _ -> true
  | None   -> false

let extract_option = function
  | Some a -> a
  | None   -> assert false

let dedup_preserving_order list ~equal =
  let rec aux output = function
    | [] -> output
    | a :: rest -> if L.mem output a ~equal then aux output rest else aux (output @ [a]) rest
  in
  aux [] list

let list_maximum list ~greater_than_or_equal =
  if list = [] then failwith "The list is empty"
  else
    L.fold_left (L.tl_exn list)
       ~init:(L.hd_exn list)
       ~f:(fun max t -> if greater_than_or_equal t max then t else max)

(* this function creates a list of n bits (integers false/true) containing all different bit-strings of length n *)
let all_bit_strings n =
  let rec aux output k =
    if k <= 0 then output
    else aux ((L.map output ~f:(fun l -> true :: l)) @ (L.map output ~f:(fun l -> false :: l))) (k-1)
  in
  aux [[]] n
  |> L.rev

let int_to_binary n =
  let rec maxpower out = let new_out = 2*out in if new_out > n then out else maxpower new_out in
  let rec aux output m number =
    if m = 1 then (if number = 1 then output @ [true] else output @ [false])
    else if m <= number then aux (output @ [true]) (m/2) (number - m)
    else aux (output @ [false]) (m/2) number
  in
  if n < 0 then assert false else if n = 0 then [] else aux [] (maxpower 1) n

let nth_bit_string ~nth n =
  let bin = int_to_binary nth in
  let d = n - (L.length bin) in
  if d < 0 then None
  else Some ((list_repeat false d) @ bin)

module OrderedIntPair =
  struct
    type t = int * int
    let compare (x1,x2) (y1,y2) =
      if x1 < y1 then -1
      else if x1 > y1 then 1
      else if x2 < y2 then -1
      else if x2 > y2 then 1
      else 0
  end

module AssocIntPair = Map.Make (OrderedIntPair)

let all_lists_Table = ref AssocIntPair.empty
let rec all_k_lists_sum_n k n =
  (* This function returns all lists of positive natural numbers of length k and sum n *)

  let aux k n =
    if k <= 0 then [[]]
    else if k = 1 then [[n]]
    else
      let answer =
        L.map (range 1 (n-k+2)) ~f:(fun d -> L.map (all_k_lists_sum_n (k-1) (n-d)) ~f:(fun l -> d :: l))
        |> L.concat
      in
      all_lists_Table := AssocIntPair.add (k,n) answer !all_lists_Table;
      answer
  in
  try AssocIntPair.find (k,n) !all_lists_Table with
  | Not_found -> aux k n

let combine_lists_all_combinations lists =
  (* This function takes a list of lists [l1,l2,...,lk] and outputs a list of lists
     of length k, containing all possible combinations of taking one element from every list *)

  let rec aux = function
    | [] -> [[]]
    | l :: rest ->
       let combine_rest = aux rest in
       L.map l ~f:(fun el -> L.map combine_rest ~f:(fun list -> el :: list)) |> L.concat
  in
  aux lists

let safe_sort list ~cmp =
  (* This function sorts the list even if cmp is a weak ordering comparator. *)
  let rec aux visited sorted = function
    | [] -> assert (L.length sorted = L.length list); sorted
    | a :: rest ->
       if L.exists (visited @ rest) ~f:(fun a' -> cmp a a' > 0) then aux (visited @ [a]) sorted rest
       else aux [] (sorted @ [a]) (rest @ visited)
  in
  aux [] [] list
(*
let safe_sort list ~cmp ~pp =
  let rec aux = function
    | [] -> []
    | a :: rest ->
       let order = aux rest in
       F.printf "Hello\n";
       let i = L.find_exn (range 0 ((L.length order)+1))
                          ~f:(fun i -> let previous, next = split_list_by_idx i order in
                                       if L.exists previous ~f:(fun a' -> cmp a a' < 0) ||
                                            L.exists next ~f:(fun a' -> cmp a a' > 0) then false
                                       else true)
       in
       F.printf "Ciao\n";
       let previous, next = split_list_by_idx i order in
       previous @ [a] @ next
  in
  aux list
 *)
let top_sort list ~cmp =
  let rec aux = function
    | [] -> [[]]
    | a :: rest ->
       let orders = aux rest in
       L.map orders
           ~f:(fun o ->
             L.map (range 0 ((L.length o) + 1))
                 ~f:(fun i ->
                   let previous, next = split_list_by_idx i o in
                   if L.exists previous ~f:(fun a' -> cmp a a' < 0) ||
                        L.exists next ~f:(fun a' -> cmp a a' > 0) then []
                   else [previous @ [a] @ next]
                 )
             |> L.concat
           )
       |> L.concat
  in
  aux list
