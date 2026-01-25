(* case 1 *)
reset (shift k -> (2 + (k 1)))

$ rlwrap ./interpreter
reset (shift k -> (2 + (k 1)))
Parsed   : reset ((shift k -> (2 + (k 1))))
Compiled : Reset (Shift (Pushmark; Num (1); Access (0); Apply; Num (2); Op (+)))
i: Reset (Shift (Pushmark; Num (1); Access (0); Apply; Num (2); Op (+)))
e: []
s: []
r: ●
t: ●
m: ●
--------------------
i: Shift (Pushmark; Num (1); Access (0); Apply; Num (2); Op (+))
e: []
s: []
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Pushmark; Num (1); Access (0); Apply; Num (2); Op (+)
e: [<VContS>]
s: []
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Num (1); Access (0); Apply; Num (2); Op (+)
e: [<VContS>]
s: [<ε>]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Access (0); Apply; Num (2); Op (+)
e: [<VContS>]
s: [1; <ε>]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Apply; Num (2); Op (+)
e: [<VContS>]
s: [<VContS>; 1; <ε>]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: []
s: [1]
r: ●
t: ●
Return, [<VContS>]) :: (Num (2); Op (+), [<VContS>]), [<ε>], ●), (((●, []), [], ●), ●))
--------------------
i: ●
e: ●
s: [1]
r: ●
t: ●
m: (((Return, [<VContS>]) :: (Num (2); Op (+), [<VContS>]), [<ε>], ●), (((●, []), [], ●), ●))
--------------------
i: Return
e: [<VContS>]
s: [1; <ε>]
r: (Num (2); Op (+), [<VContS>])
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Num (2); Op (+)
e: [<VContS>]
s: [1]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Op (+)
e: [<VContS>]
s: [2; 1]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: [<VContS>]
s: [3]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: ●
s: [3]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: []
s: [3]
r: ●
t: ●
m: ●
--------------------
i: ●
e: ●
s: [3]
r: ●
t: ●
m: ●
--------------------
3

(* case 2 *)
reset (control k -> (2 + (k 1)))

$ rlwrap ./interpreter
reset (control k -> (2 + (k 1)))
Parsed   : reset ((control k -> (2 + (k 1))))
Compiled : Reset (Control (Pushmark; Num (1); Access (0); Apply; Num (2); Op (+)))
i: Reset (Control (Pushmark; Num (1); Access (0); Apply; Num (2); Op (+)))
e: []
s: []
r: ●
t: ●
m: ●
--------------------
i: Control (Pushmark; Num (1); Access (0); Apply; Num (2); Op (+))
e: []
s: []
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Pushmark; Num (1); Access (0); Apply; Num (2); Op (+)
e: [<VContC>]
s: []
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Num (1); Access (0); Apply; Num (2); Op (+)
e: [<VContC>]
s: [<ε>]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Access (0); Apply; Num (2); Op (+)
e: [<VContC>]
s: [1; <ε>]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Apply; Num (2); Op (+)
e: [<VContC>]
s: [<VContC>; 1; <ε>]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: []
s: [1]
r: ●
eturn, [<VContC>]) :: (Num (2); Op (+), [<VContC>]), [<ε>])
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: ●
s: [1]
r: ●
t: ((Return, [<VContC>]) :: (Num (2); Op (+), [<VContC>]), [<ε>])
m: (((●, []), [], ●), ●)
--------------------
i: Return
e: [<VContC>]
s: [1; <ε>]
r: (Num (2); Op (+), [<VContC>])
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Num (2); Op (+)
e: [<VContC>]
s: [1]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Op (+)
e: [<VContC>]
s: [2; 1]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: [<VContC>]
s: [3]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: ●
s: [3]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: []
s: [3]
r: ●
t: ●
m: ●
--------------------
i: ●
e: ●
s: [3]
r: ●
t: ●
m: ●
--------------------
3

(* case 3 *)
reset (shift0 k -> (2 + (k 1)))

$ rlwrap ./interpreter
reset (shift0 k -> (2 + (k 1)))
Parsed   : reset ((shift0 k -> (2 + (k 1))))
Compiled : Reset (Shift0 (Pushmark; Num (1); Access (0); Apply; Num (2); Op (+)))
i: Reset (Shift0 (Pushmark; Num (1); Access (0); Apply; Num (2); Op (+)))
e: []
s: []
r: ●
t: ●
m: ●
--------------------
i: Shift0 (Pushmark; Num (1); Access (0); Apply; Num (2); Op (+))
e: []
s: []
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Pushmark; Num (1); Access (0); Apply; Num (2); Op (+)
e: [<VContS>]
s: []
r: (●, [])
t: ●
m: ●
--------------------
i: Num (1); Access (0); Apply; Num (2); Op (+)
e: [<VContS>]
s: [<ε>]
r: (●, [])
t: ●
m: ●
--------------------
i: Access (0); Apply; Num (2); Op (+)
e: [<VContS>]
s: [1; <ε>]
r: (●, [])
t: ●
m: ●
--------------------
i: Apply; Num (2); Op (+)
e: [<VContS>]
s: [<VContS>; 1; <ε>]
r: (●, [])
t: ●
m: ●
--------------------
i: ●
e: []
s: [1]
r: ●
t: ●
<ε>], ●), ●), [<VContS>]) :: (Num (2); Op (+), [<VContS>]) :: (●, []), [
--------------------
i: ●
e: ●
s: [1]
r: ●
t: ●
m: (((Return, [<VContS>]) :: (Num (2); Op (+), [<VContS>]) :: (●, []), [<ε>], ●), ●)
--------------------
i: Return
e: [<VContS>]
s: [1; <ε>]
r: (Num (2); Op (+), [<VContS>]) :: (●, [])
t: ●
m: ●
--------------------
i: Num (2); Op (+)
e: [<VContS>]
s: [1]
r: (●, [])
t: ●
m: ●
--------------------
i: Op (+)
e: [<VContS>]
s: [2; 1]
r: (●, [])
t: ●
m: ●
--------------------
i: ●
e: [<VContS>]
s: [3]
r: (●, [])
t: ●
m: ●
--------------------
i: ●
e: []
s: [3]
r: ●
t: ●
m: ●
--------------------
i: ●
e: ●
s: [3]
r: ●
t: ●
m: ●
--------------------
3

(* case 4 *)
reset (shift k -> ((k 1) + 2))

$ rlwrap ./interpreter
reset (shift k -> ((k 1) + 2))
Parsed   : reset ((shift k -> ((k 1) + 2)))
Compiled : Reset (Shift (Num (2); Pushmark; Num (1); Access (0); Apply; Op (+)))
i: Reset (Shift (Num (2); Pushmark; Num (1); Access (0); Apply; Op (+)))
e: []
s: []
r: ●
t: ●
m: ●
--------------------
i: Shift (Num (2); Pushmark; Num (1); Access (0); Apply; Op (+))
e: []
s: []
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Num (2); Pushmark; Num (1); Access (0); Apply; Op (+)
e: [<VContS>]
s: []
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Pushmark; Num (1); Access (0); Apply; Op (+)
e: [<VContS>]
s: [2]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Num (1); Access (0); Apply; Op (+)
e: [<VContS>]
s: [<ε>; 2]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Access (0); Apply; Op (+)
e: [<VContS>]
s: [1; <ε>; 2]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Apply; Op (+)
e: [<VContS>]
ε>; 2]ContS>; 1; <
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: []
s: [1]
r: ●
t: ●
m: (((Return, [<VContS>]) :: (Op (+), [<VContS>]), [<ε>; 2], ●), (((●, []), [], ●), ●))
--------------------
i: ●
e: ●
s: [1]
r: ●
t: ●
m: (((Return, [<VContS>]) :: (Op (+), [<VContS>]), [<ε>; 2], ●), (((●, []), [], ●), ●))
--------------------
i: Return
e: [<VContS>]
s: [1; <ε>; 2]
r: (Op (+), [<VContS>])
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: Op (+)
e: [<VContS>]
s: [1; 2]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: [<VContS>]
s: [3]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: ●
s: [3]
r: ●
t: ●
m: (((●, []), [], ●), ●)
--------------------
i: ●
e: []
s: [3]
r: ●
t: ●
m: ●
--------------------
i: ●
e: ●
s: [3]
r: ●
t: ●
m: ●
--------------------
3

