open Syntax

(* linearize i; derived from eval9s2 *)
(* defunctionalize VFun *)

(* Value *)
type v = VNum of int
       | VFun of i list * v list
       | VContS of c * s * t
       | VContC of c * s * t
       | VArgs of v list

and c = (i list * v list) list

and i = IPush
      | IPushmark
      | INum of int
      | IAccess of int
      | IOp of op
      | IApply
      | IFun of i list
      | IShift of i list | IControl of i list
      | IShift0 of i list | IControl0 of i list
      | IReset of i list

and s = v list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * s * t) * m


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
