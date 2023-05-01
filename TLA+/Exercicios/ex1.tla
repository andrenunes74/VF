(*
    var r : integer = n;

    0: if r < 0 then 
    1: r := -r
    2:
*)
------------------------------ MODULE ex1 ------------------------------

EXTENDS Integers

CONSTANTS N
VARIABLES r,pc

program == 
    /\ pc = 0
    /\ UNCHANGED <<r>>
    /\ IF r < 0 THEN pc' = 1 
                ELSE pc' = 2 

program1 == 
    /\ pc = 1
    /\ r' = -r
    /\ pc' = 2

vars == <<pc,r>>
Init == r = -10 /\ pc = 0
Next == program \/ program1
Algorithm == Init /\ [][Next]_vars

TypeOK == [] (r \in Int /\ pc \in 0..2)
Termination == <> (pc = 2)

=============================================================================

