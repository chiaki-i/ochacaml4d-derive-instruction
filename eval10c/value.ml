open Syntax

(* Definitional interpreter for λ-calculus with 4 delimited continuation operations : eval1 *)

(* Value *)
type v = VNum of int
       | VFun of i list * v list
       | VContS of c * s * t
       | VContC of c * s * t
       | VEmpty

and c = (i list * v list) list

and i = IPushmark
      | INum of int | IAccess of int | IOp of op
      | IApply | IAppterm | IReturn
      | ICur of i list | IGrab of i list
      | IShift of i list | IControl of i list
      | IShift0 of i list | IControl0 of i list
      | IReset of i list

and s = v list

and t = TNil | Trail of h

and h = Hold of c * s
      | Append of h * h

and m = MNil | MCons of (c * s * t) * m

(* v_to_string : v -> string *)
let rec v_to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VEmpty -> "<ε>"

(* i_list_to_string : i list -> string *)
let rec i_list_to_string lst = match lst with
    [] -> ""
  | first :: rest ->
    i_to_string first ^
    List.fold_left (fun str i -> str ^ "; " ^ i_to_string i) "" rest

(* i_to_string : i -> string *)
and i_to_string inst = match inst with
    IPushmark -> "Pushmark"
  | INum (n) -> "Num (" ^ string_of_int n ^ ")"
  | IAccess (n) -> "Access (" ^ string_of_int n ^ ")"
  | IOp (op) -> "Op (" ^ Syntax.op_to_string op  ^ ")"
  | IApply -> "Apply"
  | IAppterm -> "Appterm"
  | IReturn -> "Return"
  | ICur (is) -> "Cur (" ^ i_list_to_string is ^ ")"
  | IGrab (is) -> "Grab (" ^ i_list_to_string is ^ ")"
  | IShift (is) -> "Shift (" ^ i_list_to_string is ^ ")"
  | IControl (is) -> "Control (" ^ i_list_to_string is ^ ")"
  | IShift0 (is) -> "Shift0 (" ^ i_list_to_string is ^ ")"
  | IControl0 (is) -> "Control0 (" ^ i_list_to_string is ^ ")"
  | IReset (is) -> "Reset (" ^ i_list_to_string is ^ ")"

(* s_to_string : s -> string *)
let rec s_to_string s =
  "[" ^
  begin match s with
    [] -> ""
  | first :: rest ->
    v_to_string first ^
    List.fold_left (fun str v -> str ^ "; " ^ v_to_string v) "" rest
  end
  ^ "]"

(* Value.print : v -> unit *)
let print exp =
  let str = v_to_string exp in
  print_string str

(* Value.print_inst : i list -> unit *)
let print_inst is = print_string (i_list_to_string is)