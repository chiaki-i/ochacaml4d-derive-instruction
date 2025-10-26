open Syntax

(* Defunctionalized interpreter with values passed via stack : eval7d w r.s.*)
(* Introduce return stack.  Derived from eval7ds3 *)

(* Value *)
type v = VNum of int
       | VFun of (c -> s -> r -> t -> m -> v)
       | VContS of c * s * r * t
       | VContC of c * s * r * t
       | VArgs of v list

and c = C0
      | CSeq of c' * c

and c' = CApp0
       | CApp2 of e * string list
       | COp0 of op
       | COp1 of e * string list * op
       | CAppS0
       | CAppS1 of e * string list

(* c before:
(C1, vs)::(C2, vs)::(CRet, [])::(C3, vs)::(C4, vs)::(CRet, [])::(C5, vs)::[]

af_ter splitting c and vs:
 C1     :: C2     :: CRet     :: C3     :: C4     :: CRet     :: C5     ::[]
     vs ::     vs ::       [] ::     vs ::     vs ::       [] ::     vs ::[]

c = C1::C2::CRet::[]
r = vs::vs::(C3::C4::CRet::[], vs::vs::(c5::[], vs::[])
                              (C3)(C4)         (C5)
*)

and s = v list

and r = rv list

and rv = VS of v list
       | VK of c * r

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
