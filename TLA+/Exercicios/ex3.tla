(*
   var 
     sem : boolean = true;

   procedure process;
   begin
0:  while true do
     begin

1:      repeat until sem;
        sem := false;

2:      sem := true;
    end
   end;

   process || process
*)
------------------------------ MODULE ex3 ------------------------------

EXTENDS Integers
VARIABLES sem,pc

vars == <<sem,pc>>

WhileT(i) == 
    /\ pc[i] = 0 
    /\ sem = TRUE
    /\ sem' = FALSE 
    /\ pc' = [pc EXCEPT ![i] = 0] 

WhileF(i) == 
    /\ pc[i] = 0 
    /\ sem = FALSE
    /\ sem' = TRUE
    /\ pc' = [pc EXCEPT ![i] = 2] 

Init == sem = TRUE /\ pc = [i \in 0..1 |-> 0]
Next == \E i \in 0..1 : WhileT(i) \/ WhileF(i) 
Algorithm == Init /\ [][Next]_vars

Finish == \A i \in 0..1 : pc[i] = 2 /\ sem = TRUE
Termination == <> Finish
TypeOK == [] (sem \in BOOLEAN /\ pc \in [0..1 -> 0..2])

=============================================================================