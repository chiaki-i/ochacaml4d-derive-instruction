open Syntax

(* Interpreter with linear instructions : eval10 *)

(* Value *)
type v = VNum of int
       | VFun of c * v list
       | VContS of c * s * t
       | VContC of c * s * t
       | VArg of v

and i = IVArg
      | INum of int
      | IAccess of int
      | IOp of op
      | IApply
      | IGrab of c
      | IShift of c | IControl of c
      | IShift0 of c | IControl0 of c
      | IReset of c

and c = i list

and s = v list

and h = Hold of c * s
      | Append of h * h

and t = TNil | Trail of h

type m = (c * s * t) list


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VArg (v) -> "<VArg: " ^ to_string v ^ ">"

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
