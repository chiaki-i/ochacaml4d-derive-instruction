(* reset を跨ぐ Grab が単独で働く例。 *)
(* reset は fun y の本体という末尾位置（f_t の Reset ケース経由）にあるため、 *)
(* 外側の引数 4 がメタ継続のフレームに残り、reset の中の fun x -> y が *)
(* それを直接束縛する。shift/k は使わない *)
(fun y -> reset (fun x -> y)) 3 4
