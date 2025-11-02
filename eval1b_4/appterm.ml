(fun f -> (fun z -> f (z + 4)) 2 3) (fun x -> fun y -> x * y)

  C[(fun x -> ((fun y -> y) 2)) 1]
= Pushmark; C[1]; Push; C[fun x -> ((fun y -> y) 2)]; Apply
= Pushmark; 1; Push; Cur(T[(fun y -> y) 2]; Return); Apply
= Pushmark; 1; Push; Cur(2; Push; C[fun y -> y]; Appterm; Return); Apply
= Pushmark; 1; Push; Cur(2; Push; Cur(T[y]; Return); Appterm; Return); Apply
= Pushmark; 1; Push; Cur(2; Push; Cur(Access y; Return); Appterm; Return); Apply

Pushmark
  s = empty

1; Push;
  s = 1; empty

Cur(2; Push; Cur(Access y; Return); Appterm; Return)
  a = (2; Push; Cur(Access y; Return); Appterm; Return), []
  s = 1; empty

Apply
  i = 2; Push; Cur(Access y; Return); Appterm; Return
  e = 1 :: []
  s = empty
  r = []

2; Push
  e = 1 :: []
  s = 2 :: empty

Cur(Access y; Return)
  i = Appterm; Return
  a = (Access y; Return), 1
  e = 1 :: []
  s = 2 :: empty

Appterm
  i = Access y; Return
  e = 2 :: 1 :: []
  s = empty

Access y
  e = 2 :: 1 :: []
  a = 2
  s = empty

Return
  a = 2

  C[(fun x -> (fun y -> (fun z -> z) (fun w -> w)) 2 3) 1]
= Pushmark; C[1]; Push; C[fun x -> (fun y -> (fun z -> z) (fun w -> w)) 2 3]; Apply
= Pushmark; 1; Push; Cur(T[(fun y -> (fun z -> z) (fun w -> w)) 2 3]; Return); Apply
= Pushmark; 1; Push; Cur(3; Push; 2; Push; C[fun y -> (fun z -> z) (fun w -> w)];
                         Appterm; Return); Apply
= Pushmark; 1; Push; Cur(3; Push; 2; Push; Cur(T[(fun z -> z) (fun w -> w)]; Return);
                         Appterm; Return); Apply
= Pushmark; 1; Push; Cur(3; Push; 2; Push; Cur(C[fun w -> w]; Push; C[fun z -> z];
                                               Appterm; Return);
                         Appterm; Return); Apply
= Pushmark; 1; Push; Cur(3; Push; 2; Push; Cur(Cur(Access w; Return); Push;
                                               Cur(Access z; Return); Appterm; Return);
                         Appterm; Return); Apply

Pushmark; 1; Push
  s = 1 :: empty

Cur ()
  a = (), []
  s = 1 :: empty

Apply
  i = (...)
  e = 1 :: []
  s = empty
  r = ...

3; Push; 2; Push
  e = 1 :: []
  s = 2 :: 3 :: empty

Cur ()
  a = (...), 1 :: []
  e = 1 :: []
  s = 2 :: 3 :: empty

Appterm
  e = 2 :: 1 :: []
  s = 3 :: empty

Cur (Access w; Return)
  a = (Access w; Return), 2:: 1 :: []
  e = 2 :: 1 :: []
  s = 3 :: empty

Push
  a = {(Access w; Return), 2:: 1 :: []}
  e = 2 :: 1 :: []
  s = {(Access w; Return), 2:: 1 :: []} :: 3 :: empty

Cur (Access z; Return)
  a = (Access z; Return), 2:: 1 :: []
  e = 2 :: 1 :: []
  s = {(Access w; Return), 2:: 1 :: []} :: 3 :: empty

Appterm
  i = Access z; Return
  e = {(Access w; Return), 2:: 1 :: []} :: 2 :: 1 :: []
  s = 3 :: empty

Access z
  a = {(Access w; Return), 2:: 1 :: []}
  e = {(Access w; Return), 2:: 1 :: []} :: 2 :: 1 :: []
  s = 3 :: empty

Return
  i = Access w; Return
  e = 3 :: 2 :: 1 :: []
  s = empty

Access w
  a = 3
  e = 3 :: 2 :: 1 :: []
  s = empty

Return
  a = 3

  C[(fun x -> (fun y -> (fun z -> z) (fun w -> w)) 2 3) 1]
= Pushmark; 1; Push; Cur(3; Push; 2; Push; Cur(Cur(Access w; Return); Push;
                                               Cur(Access z; Return); Appterm; Return);
                         Appterm; Return); Apply
