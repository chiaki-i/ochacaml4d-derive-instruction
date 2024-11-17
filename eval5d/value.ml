open Syntax

(* Delinearized interpreter : eval5 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> s -> r -> t -> m -> v)
       | VContS of c * s * r * t
       | VContC of c * s * r * t
       | VEnv of v list
       | VArg of v

and c = C0
      | CApp0 of c
      | CApp1 of i * c
      | COpP0 of c
      | COpP1 of i * c
      | COpM0 of c
      | COpM1 of i * c
      | COpT0 of c
      | COpT1 of i * c
      | COpD0 of c
      | COpD1 of i * c

and s = v list

and r = v list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * r * t) * m

and i = v list -> c -> s -> r -> t -> m -> v


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
