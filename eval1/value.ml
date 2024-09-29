open Syntax

(* Definitional interpreter for λ-calculus with 4 delimited continuation operations : eval1 *)

(* Value *)
type v = VNum of int
       | VFun of (e * string * string list * v list)
       | VContS of c * t
       | VContC of c * t

and c = v -> t -> m -> v

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * t) * m


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"


(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
