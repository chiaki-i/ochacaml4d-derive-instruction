open Syntax

(* Linearized interpreter : eval3 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> c -> t -> m -> v)
       | VContS of c * t
       | VContC of c * t

(* Frame: new datatype *)
and f = CApp0 of v
      | CApp1 of i * v list
      | COp0 of v * (v -> v -> c -> t -> m -> v)
      | COp1 of i * v list * (v -> v -> c -> t -> m -> v)

(* Continuation becomes a single list of frames *)
and c = f list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * t) * m

and i = v list -> c -> t -> m -> v


(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"


(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str