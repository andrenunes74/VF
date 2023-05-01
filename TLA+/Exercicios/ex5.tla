(*
   var 
     sem : boolean = true;

   procedure process(i : integer);
   begin
0:   while true do
     begin

1:     repeat until sem;
       sem := false;

2:     sem := true
     end
   end;

   process(0) || ... || process(N-1)

*)
------------------------------ MODULE ex5 ------------------------------
EXTENDS Integers
CONSTANT N
ASSUME N > 0
VARIABLES sem, pc
vars == <<sem,pc>>

process1(i) == 
    /\ pc[i] = 0 
    /\ sem = TRUE
    /\ sem' = FALSE 
    /\ pc' = [pc EXCEPT ![i] = 1]

process2(i) == 
    /\ pc[i] = 1
    /\ sem = FALSE
    /\ sem' = TRUE
    /\ pc' = [pc EXCEPT ![i] = 2]

Init == sem = TRUE /\ pc = [i \in 1..N |-> 0]
Next == \E i \in 1..N : process1(i) \/ process2(i)
Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next)

Finish == \A i \in 1..N : pc[i] = 2
Termination == <> Finish

TypeOK == [] (sem \in BOOLEAN /\ pc \in [1..N -> 0..2])
mutualExclusion == [](\A i,j \in 1..N : i # j => ~((pc[i] = 1) /\ (pc[j] = 1)))
noStarvation == \A i \in 1..N : WF_vars(process2(i)) /\ WF_vars(process1(i))
PartialCorrectness == \A i, j \in 1..N : i # j => pc[i] # 2 \/ pc[j] # 2
=============================================================================
