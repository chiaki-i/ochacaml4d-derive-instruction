open Syntax

(* Defunctionalized interpreter : eval2 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> v list -> c -> t -> m -> v)
       | VContS of c * t
       | VContC of c * t

and c = C0
      | CApp0 of v * v list * c
      | CApp1 of e * string list * v list * v list * c
      | CAppS0 of v list * cs
      | CRet of v list * c
      | COp0 of e * string list * v list * op * c
      | COp1 of v * op * c
      | COp2 of e * string list * v list * v list * op * c
      | COp3 of v * v list * op * c

and cs = CApp2 of e * e * string list * v list * c (* v list list の先頭に [] を入れることに相当する？ *)
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
