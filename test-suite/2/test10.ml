(* <<S0 k. Sh. 0> 1 2 3> *)
reset ((reset (shift0 k -> shift h -> k 0)) 1 2 3)

(* ./interpreter
reset ((reset (shift0 k -> shift h -> k 0)) 1 2 3)
Parsed   : reset ((reset ((shift0 k -> (shift h -> (k 0)))) 1 2 3))
Compiled : Pushmark; Reset (Pushmark; Num (3); Num (2); Num (1); Pushmark; Reset (Shift0 (Shift (Pushmark; Num (0); Access (1); Apply); Return)); Apply)
0 *)
(* eval1e_1 の f_sr の Shift のケースにおいて、app_c0 とすべきところを c としていると、メタ継続に入っているはずの v2s の情報を捨ててしまいエラーになるはず *)
