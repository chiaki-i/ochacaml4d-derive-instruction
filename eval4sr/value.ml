open Syntax

(* Stack-based interpreter : eval4 (with return stack) *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> s -> r -> t -> m -> v)
       | VContS of c * s * r * t
       | VContC of c * s * r * t
       | VArgs of v list

and f = CApp0
      | CAppS0
      | COp0 of op
      | COp1 of e * string list * op * v list
      | CRet
      | CApp2 of e * string list * v list
      | CAppS1 of e * string list * v list

(*
eval3   : c =   C1 :: C2 :: CRet :: C3 :: C4 :: CRet :: C5 :: []
eval4sr : c =   C1 :: C2 :: CRet :: []
        : r =               (C3 :: C4 :: CRet :: []) :: (C5 :: []) :: []
*)

and c = f list

and s = v list

and r = c list

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
