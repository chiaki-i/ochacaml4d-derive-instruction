open Syntax

(* Stack-based interpreter : eval4 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> s -> t -> m -> v)
       | VContS of c * s * t
       | VContC of c * s * t
       | VEnv of v list (* VEnv: new constructor *)
       | VArgs of v list (* VArgs: new constructor *)

and f = CApp0
      | CApp1 of e * string list
      | CApp2 of e * e * string list
      | CAppS0
      | CAppS1 of e * string list
      | CRet
      | COp0 of e * string list * op
      | COp1 of op
      | COp2 of e * string list * op
      | COp3 of op

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
  | VArgs (_) -> "<VArgs>"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
