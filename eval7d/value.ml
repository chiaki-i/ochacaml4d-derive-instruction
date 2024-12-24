open Syntax

(* Defunctionalized interpreter with values passed via stack : eval7d wo r.s.*)

(* Value *)
type v = VNum of int
       | VFun of (c -> s -> t -> m -> v)
       | VContS of c * s * t
       | VContC of c * s * t
       | VArg of v

and c = C0
      | CApp0 of c
      | CApp1 of i * v list * c
      | COpP0 of c
      | COpP1 of i * v list * c
      | COpM0 of c
      | COpM1 of i * v list * c
      | COpT0 of c
      | COpT1 of i * v list * c
      | COpD0 of c
      | COpD1 of i * v list * c

and s = v list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * t) * m

and i = v list -> c -> s -> t -> m -> v


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VArg (v) -> "<VArg: " ^ to_string v ^ ">"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
