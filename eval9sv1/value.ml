open Syntax

(* Interpreter using combinators factored as instructions : eval8sv *)
(* Derived from eval7ds4v *)

(* Value *)
type v = VNum of int
       | VFun of (c -> s -> r -> t -> m -> v)
       | VContS of c * s * r * t
       | VContC of c * s * r * t
       | VArgs of v list

and c = i list

and i = IPush
      | IPushmark
      | INum of int
      | IAccess of int
      | IOp of op
      | IApply
      | IFun of i
      | ISeq of i * i
      | IShift of i | IControl of i
      | IShift0 of i | IControl0 of i
      | IReset of i

and s = v list

and r = rv list

and rv = VS of v list

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


(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
