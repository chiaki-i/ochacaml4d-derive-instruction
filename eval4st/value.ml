open Syntax

(* interpreter with defunctionalized continuations: eval2st *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> s -> t -> m -> v)
       | VContS of c * s * t
       | VContC of c * s * t
       | VArgs of v list

and f = CRet
      | CAppT0 of e * string list * v list
      | CAppS0
      | CAppS1 of e * string list * v list
      | COp0 of op
      | COp1 of e * string list * op * v list

and c = f list

and s = v list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * t) * m

(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VArgs (_) -> "<VArgs>"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
