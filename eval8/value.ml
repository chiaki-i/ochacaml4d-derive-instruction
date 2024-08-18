(* Interpreter using combinators factored as instructions : eval8 *)

(* Value *)
type v = VNum of int
       | VFun of (v -> v list -> c -> s -> t -> m -> v)
       | VContS of c * s * t
       | VContC of c * s * t
       | VEnv of v list
       (* | VK of c *)

and c = v -> s -> t -> m -> v

and s = v list

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil
      | MCons of (c * s * t) * m

type i  = v list -> c -> v -> s -> t -> m -> v
type i' = v list -> v list -> c -> v -> s -> t -> m -> v (* for tail call optimization *)

(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VEnv (_) -> "<VEnv>"
(*   | VK (_) -> "<VK>" *)

let vlist_of_string lst =
  List.fold_left (fun s1 s2 -> s1 ^ " " ^ s2) "" (List.map to_string lst)

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str
