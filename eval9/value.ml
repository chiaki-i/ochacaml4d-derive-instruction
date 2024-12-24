open Syntax

(* Defunctionalized interpreter : eval9 (without return stack) *)

(* Value *)
type v = VNum of int
       | VFun of i * v list
       | VContS of c * s * t
       | VContC of c * s * t
       | VArg of v

and i = IVArg
      | INum of int
      | IAccess of int
      | IOp of op
      | IApply
      | IGrab of i
      | ISeq of i * i (* >> の実体 *)
      | IShift of i | IControl of i
      | IShift0 of i | IControl0 of i
      | IReset of i
      | IReturn

and c = (i * v list) list

and s = v list

and h = Hold of c * s
      | Append of h * h

and t = TNil | Trail of h

and m = (c * s * t) list


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VArg (v) -> "<VArg: " ^ to_string v ^ ">"

(* s_to_string : v -> string *)
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
