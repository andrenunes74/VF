(*
   var x : integer = 0;

   procedure increment(i : integer);
     var y : integer = 0;
   begin
    0:   y := x; 
    1:   x := y + 1 
    2: end;

   increment(1) || ... || increment(N)
*)
------------------------------ MODULE ex4 ------------------------------

EXTENDS Integers
CONSTANT N
ASSUME N > 0
VARIABLES x, y, pc

vars == <<x,y,pc>>

Increment1(i) == 
    /\ pc[i] = 0 
    /\ UNCHANGED <<x>>
    /\ y' = [y EXCEPT ![i] = x]
    /\ pc' = [pc EXCEPT ![i] = 1]

Increment2(i) == 
    /\ pc[i] = 1
    /\ UNCHANGED <<y>>
    /\ x' = y[i] + 1
    /\ pc' = [pc EXCEPT ![i] = 2]

Init == x = 0 /\ y = [i \in 1..N |-> 0] /\ pc = [i \in 1..N |-> 0]
Next == \E i \in 1..N : Increment1(i) \/ Increment2(i)
Algorithm == Init /\ [][Next]_vars

Finish == \A i \in 1..N : pc[i] = 2
Termination == <> Finish
TypeOK == [] (x \in Int /\ y \in [1..N -> 0..10] /\ pc \in [1..N -> 0..2])

=============================================================================