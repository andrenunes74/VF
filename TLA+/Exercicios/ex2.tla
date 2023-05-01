(*
   var x : integer = 0

   procedure increment;
   begin
    0: x := x + 1
    1: end;

   increment || increment
*)
------------------------------ MODULE ex2 ------------------------------

EXTENDS Integers
VARIABLES x,pc

vars == <<x,pc>>

Increment(i) == 
    /\ pc[i] = 0 
    /\ x' = x + 1 
    /\ pc' = [pc EXCEPT ![i] = 1]

Init == x = 0 /\ pc = [i \in 0..1 |-> 0]
Next == \E i \in 0..1 : Increment(i)
Algorithm == Init /\ [][Next]_vars

Finish == \A i \in 0..1 : pc[i] = 1
Termination == <> Finish
TypeOK == [] (x \in Int /\ pc \in [0..1 -> 0..1])

=============================================================================

