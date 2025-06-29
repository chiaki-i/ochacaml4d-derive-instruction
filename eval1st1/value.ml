open Syntax

(* Definitional interpreter for λ-calculus with 4 delimited continuation operations
  with tail optimization : eval1st *)

(* Value *)
type v = VNum of int
       | VFun of (v -> v list -> c -> t -> m -> v)
       | VContS of c * t (*(v -> v list -> c -> t -> m -> v) *)
       | VContC of c * t
       | VEmpty

and c = v -> t -> m -> v

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * t) * m


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VEmpty -> "<ε>"


(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
