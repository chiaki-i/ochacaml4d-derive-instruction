(* コミット cb2117a に「State Monad の典型的な例」として書かれている式。 *)
(* state-monad-put と同じく reset がトップレベル App の演算子位置にあるため、 *)
(* eval1b_7 時点では Grab は発火しない *)
(reset ((fun result -> fun x -> result) (shift k -> fun x -> k 2 (x + 1)))) 3
