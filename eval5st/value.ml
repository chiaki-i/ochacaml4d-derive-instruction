open Syntax

(* Defunctionalized interpreter : eval2 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> s -> r -> t -> m -> v)
       | VContS of c * s * r * t
       | VContC of c * s * r * t
       | VArgs of v list

and c = C0
      | CApp0 of c | CAppT0 of c
      | CAppS0 of c
      | COp0 of op * c
      | COp1 of e * string list * op * v list * c
      | CApp2 of e * string list * v list * c
      | CAppT2 of e * string list * v list * c
      | CAppS1 of e * string list * v list * c

and s = v list

and r = (c * v list) list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * r * t) * m


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"

(* s_to_string : s -> string *)
let rec s_to_string s =
  "[" ^
  begin match s with
    [] -> ""
  | first :: rest ->
    to_string first ^
    List.fold_left (fun str v -> str ^ "; " ^ to_string v) "" rest
  end
  ^ "]"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str