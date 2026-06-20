open Syntax

(* Definitional interpreter for λ-calculus with 4 delimited continuation operations : eval1 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> s -> t -> m -> v)
       | VContS of c * s * t
       | VContC of c * s * t

(* c の中に static と dynamic な変数が含まれているので、
  それを分離してできたのが s である *)
and c = C0
      | CApp1 of c
      | CApp2 of c
      | CApp3 of c
      | CAppS1 of e * string list * v list * c
      | CAppS2 of e * string list * v list * c
      | COp0 of v * op * c
      | COp1 of e * string list * op * v list * c

and s = (v list) list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * t) * m

(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"

(* s_to_string : s -> string *)
let vlist_to_string vs =
  "[" ^
  begin match vs with
    [] -> ""
  | first :: rest ->
    to_string first ^
    List.fold_left (fun str v -> str ^ "; " ^ to_string v) "" rest
  end
  ^ "]"

let s_to_string s =
  "[" ^
  begin match s with
    [] -> ""
  | first :: rest ->
    vlist_to_string first ^
    List.fold_left (fun str vs -> str ^ "; " ^ vlist_to_string vs) "" rest
  end
  ^ "]"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
