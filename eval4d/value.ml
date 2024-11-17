open Syntax

(* Stack-based interpreter : eval4 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> s -> r -> t -> m -> v)
       | VContS of c * s * r * t
       | VContC of c * s * r * t
       | VEnv of v list (* VEnv: new constructor *)
       | VArg of v (* VArg: new constructor *)

and f = CApp0
      | CApp1 of i
      | COpP0
      | COpP1 of i
      | COpM0
      | COpM1 of i
      | COpT0
      | COpT1 of i
      | COpD0
      | COpD1 of i

and c = f list

(* Stack: new datatype *)
and s = v list

and r = v list (* return stack *)

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
