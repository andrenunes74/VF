(*
 var
     level : array [0..N-1] of -1..N-2 = [N of -1];
     last  : array [0..N-2] of  0..N-1;

   procedure process(i : integer);
     var l : integer = 0;
   begin
     while true do
     begin

0:     while l < N-1 do
       begin
         level[i] := l;
         last[l]  := i;
1:       repeat until (last[l] != i or ∀ k != i . level[k] < l));
         l := l+1
       end

2:     level[i] := -1;
       l := 0
     end
   end;

   process(0) || ... || process(N-1)
*)

------------------------------ MODULE ex6 ------------------------------
EXTENDS Integers
CONSTANT N
ASSUME N > 1
VARIABLES level, last, pc, l
vars == <<pc, l, level, last>>

idleTrue(i) == 
    /\ pc[i] = 0 /\ l[i] < N-1
    /\ level' = [level EXCEPT ![i] = l[i]] /\ last' = [last EXCEPT ![l[i]] = i] 
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<l>>

idleFalse(i) == 
    /\ pc[i] = 0 /\ l[i] >= N-1
    /\ pc' = [pc EXCEPT ![i] = 2]
    /\ UNCHANGED <<l, last, level>>

repeatWhileTrue(i) == 
    /\ pc[i] = 1 /\ (last[l[i]] # i \/ \A k \in 0..(N-1) : k # i => level[k] < l[i]) /\ l[i] < N-1
    /\ l' = [l EXCEPT ![i] = l[i]+1]
    /\ pc' = [pc EXCEPT ![i] = 0]
    /\ UNCHANGED <<last, level>>

repeatWhileFalse(i) == 
    /\ pc[i] = 1 /\ (last[l[i]] # i \/ \A k \in 0..(N-1) : k # i => level[k] < l[i]) /\ l[i] >= N-1
    /\ l' = [l EXCEPT ![i] = l[i]+1]
    /\ pc' = [pc EXCEPT ![i] = 2]
    /\ UNCHANGED <<last, level>>

critical(i) == 
    /\ pc[i] = 2 /\ l[i] >= N-1
    /\ level' = [level EXCEPT ![i] = -1] /\ l' = [l EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = 0]
    /\ UNCHANGED <<last>>


Init == pc = [i \in 0..N-1 |-> 0] /\ l = [i \in 0..N-1 |-> 0] /\ last \in [0..N-2 -> 0..N-1] /\ level = [i \in 0..N-1 |-> -1] 
Next == \E i \in 0..(N-1) : idleTrue(i) \/ idleFalse(i) \/ repeatWhileTrue(i) \/ repeatWhileFalse(i) \/ critical(i)
Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == [] (pc \in [0..(N-1) -> 0..2] /\ l \in [0..(N-1) -> Int] /\ last \in [0..N-2 -> 0..N-1] /\ level \in [0..N-1 -> -1..N-2])
mutualExclusion == [](\A i,j \in 0..(N-1) : i # j => ~((pc[i] = 2) /\ (pc[j] = 2)))
NoStarvation == \A i \in 0..(N-1) : pc[i] = 1 => (l[i] >= N-1 /\ (\E j \in 0..(N-1) : j # i /\ level[j] >= l[i]))
=============================================================================

