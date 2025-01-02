open Syntax

(* Linearized interpreter : eval3 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> t -> m -> v)
       | VContS of c * t
       | VContC of c * t

and f = CApp0 of v list
      | CAppS0 of v list * cs
      | COp0 of v * op
      | COp1 of e * string list * op * v list
      | CRet

and c = f list

and cs = CApp2 of e * string list * v list
       | CAppS1 of e * string list * v list * cs

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
