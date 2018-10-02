open Abbrevs
open LinAlg

module Z2 = struct
  type t = bool
  let pp fmt a = F.fprintf fmt "%s" (match a with | true -> "1" | false -> "0")
  let add a b = a <> b
  let neg a = a
  let mul a b = a && b
  let inv a = match a with | true -> true | false -> failwith "0 has no inverse in Z2"
  let one = true
  let zero = false
  let is_zero a = not a
  let is_one a = a
end

module type Z2 = (Field with type t = bool)
