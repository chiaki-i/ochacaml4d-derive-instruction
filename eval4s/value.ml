open Syntax

(* Stack-based interpreter : eval4 (without return stack) *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> s -> t -> m -> v)
       | VContS of c * s * t
       | VContC of c * s * t
       | VArgs of v list

and f = CApp0
      | CApp1 of e * string list * v list
      | CAppS0 of cs
      | CApplyS
      | COp0 of e * string list * v list * op
      | COp1 of op

and c = f list

and s = v list

and cs = CApp2 of e * e * string list * v list
       | CAppS1 of e * string list * v list * cs

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * t) * m


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VArgs ([]) -> "[]"
  | VArgs (v :: vs) ->
    "[" ^ List.fold_left (fun s v -> s ^ "; " ^ to_string v)
                         (to_string v) vs ^ "]"


(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
