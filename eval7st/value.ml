open Syntax

(* interpreter with arg stack, with value on top of it: eval7st *)

(* Value *)
type v = VNum of int
       | VFun of (c -> s -> t -> m -> v)
       | VContS of c * s * t
       | VContC of c * s * t
       | VArgs of v list

and c = C0
      | CApp of c
      | CAppT0 of e * string list * v list * c
      | CAppS0 of c
      | CAppS1 of e * string list * v list * c
      | COp0 of op * c
      | COp1 of e * string list * op * v list * c

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

(* c_to_string : c -> string *)
let rec c_to_string cont = match cont with
    C0 -> "<C0>"
  | CApp (_) -> "<CApp>"
  | CAppT0 (_, _, _, _) -> "<CAppT0>"
  | CAppS1 (_, _, _, _) -> "<CAppS1>"
  | CAppS0 (_) -> "<CAppS0>"
  | COp0 (_, _) -> "<COp0>"
  | COp1 (_, _, _, _, _) -> "<COp1>"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str