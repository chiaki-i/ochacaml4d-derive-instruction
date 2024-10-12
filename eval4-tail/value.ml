open Syntax

(* Stack-based interpreter with tail optimization : eval4-tail *)

(* Value *)
type v = VNum of int
       | VFun of (e * string * string list * v list)
       | VContS of c * s * t
       | VContC of c * s * t
       | VEnv of v list (* VEnv: new constructor *)
       | VMark

and f = CApp0
      | CApp1 of e * string list
      | CApp2 of e * e * string list
      | CAppS0
      | CAppS1 of e * string list
      | CRet
      | COp0 of e * string list * op
      | COp1 of op

and c = f list

(* Stack: new datatype *)
and s = v list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * t) * m


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VEnv (_) -> "<VEnv>"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
