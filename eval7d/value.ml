open Syntax

(* Defunctionalized interpreter with values passed via stack : eval7d *)

(* Value *)
type v = VNum of int
       | VFun of (c -> s -> r -> t -> m -> v)
       | VContS of c * s * r * t
       | VContC of c * s * r * t
       | VEnv of v list
       | VArg of v

and c = C0
      | CApp0 of c
      | CApp1 of e * string list * c
      | COp0 of e * string list * op * c
      | COp1 of op * c

and s = v list

and r = v list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * r * t) * m


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VEnv (_) -> "<VEnv>"
  | VArg (v) -> "<VArg: " ^ to_string v ^ ">"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
