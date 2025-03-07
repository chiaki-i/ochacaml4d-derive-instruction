open Syntax

(* defunctionalize VFun from eval9st: eval9st1 *)

(* Value *)
type v = VNum of int
       | VFun of i * v list
       | VContS of c * s * t
       | VContC of c * s * t
       | VArgs of v list

and c = C0
      | CSeq of i * v list * c

and i = IPush
      | IPushmark
      | INum of int
      | IAccess of int
      | IOp of op
      | IApply
      | IAppterm of i
      | ICur of i
      | IGrab of i
      | ISeq of i * i
      | IShift of i | IControl of i
      | IShift0 of i | IControl0 of i
      | IReset of i

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

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str