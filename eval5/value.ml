open Syntax

(* Delinearized interpreter : eval5 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> v list -> c -> s -> t -> m -> v)
       | VContS of c * s * t
       | VContC of c * s * t
       | VEnv of v list
       | VArgs of v list

and c = C0
      | CApp0 of c
      | CApp1 of e * string list * c
      | CApp2 of e * e * string list * c
      | CAppS0 of c
      | CAppS1 of e * string list * c
      | CRet of c
      | COp0 of e * string list * op * c
      | COp1 of op * c
      | COp2 of e * string list * op * c
      | COp3 of op * c

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
