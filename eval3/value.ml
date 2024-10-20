open Syntax

(* Linearized interpreter : eval3 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> v list -> c -> t -> m -> v)
       | VContS of c * t
       | VContC of c * t

(* Frame: new datatype *)
and f = CApp0 of v * v list
      | CApp1 of e * string list * v list * v list
      | CApp2 of e * e * string list * v list
      | CAppS0 of v list
      | CAppS1 of e * string list * v list
      | CRet of v list
      | COp0 of e * string list * v list * op
      | COp1 of v * op
      | COp2 of e * string list * v list * v list * op
      | COp3 of v * v list * op

(* Continuation becomes a single list of frames *)
and c = f list

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
