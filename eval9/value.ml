open Syntax

(* Defunctionalized interpreter : eval9 *)

(* Value *)
type v = VNum of int
       | VFun of i
       | VContS of c * s * r * t
       | VContC of c * s * r * t
       | VEnv of v list
       | VArg of v

and i = IVArg
      | INum of int
      | IAccess of int
      | IOp of op
      | IApply
      | IClosure of i * v list
      | IGrab of i
      | ISeq of i * i (* >> の実体 *)
      | IShift of i | IControl of i
      | IShift0 of i | IControl0 of i
      | IReset of i

(* and i = INum of int | IAccess of int
      | IPush_closure of i | IReturn
      | IPush_env | IPop_env | IOp of op | ICall
      | ISeq of i * i *)

and c = i list

and s = v list

and r = v list

and h = Hold of c * s * r
      | Append of h * h

and t = TNil | Trail of h

and m = (c * s * r * t) list


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VEnv (_) -> "<VEnv>"
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
