open Syntax

(* Defunctionalized interpreter with values passed via stack : eval7d w r.s.*)
(* Add superfluous v list to CApp0, CAppS0, and COp0 *)

(* Value *)
type v = VNum of int
       | VFun of (c -> s -> r -> t -> m -> v)
       | VContS of c * s * r * t
       | VContC of c * s * r * t
       | VArgs of v list
       | VK of c

and c = C0
      | CApp0 of v list * c
      | CApp2 of e * string list * v list * c
      | CAppS0 of v list * c
      | COp0 of op * v list * c
      | COp1 of e * string list * op * v list * c
      | CAppS1 of e * string list * v list * c

and s = v list

and r = v list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * r * t) * m


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
  | VK (_) -> "<VK>"


(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
