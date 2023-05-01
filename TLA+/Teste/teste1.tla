(*Parte1*)
------------------------------ MODULE teste1 ---------------------------------
(*Pergunta 1*)
EXTENDS Naturals, TLC, Sequences
CONSTANT N
ASSUME N>0
VARIABLES n, lock, waiting, pc
vars == <<n, lock, waiting, pc>>

Init == 
    /\ n = 0
    /\ pc = [id \in 1..N |-> 0]
    /\ lock = TRUE
    /\ waiting = [id \in 1..N |-> FALSE]

rUntilLockF(i) == 
    /\ pc[i] = 0
    /\ lock = FALSE
    /\ UNCHANGED <<pc,waiting,n,lock>>

rUntilLock(i) ==
    /\ pc[i] = 0
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ n' = n+1
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<waiting>>

whileT(i) ==
    /\ n < N
    /\ pc[i] = 1
    /\ waiting' = [waiting EXCEPT ![i] = TRUE]
    /\ lock' = TRUE
    /\ pc' = [pc EXCEPT ![i] = 2]
    /\ UNCHANGED <<n>>

whileF(i) ==
    /\ ~(n<N)
    /\ pc[i] = 1
    /\ waiting' = [id \in 1..N |-> FALSE]
    /\ lock' = TRUE
    /\ pc' = [pc EXCEPT ![i] = 3]
    /\ UNCHANGED <<n>>

rUntilLWF(i) == 
    /\ pc[i] = 2
    /\ lock = FALSE
    /\ waiting[i] = TRUE
    /\ UNCHANGED <<pc,waiting,n,lock>>

rUntilLWT(i) == 
    /\ pc[i] = 2
    /\ lock = TRUE
    /\ waiting[i] = FALSE
    /\ lock' = FALSE
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<waiting,n>>

Next == \E i \in 1..N : rUntilLockF(i) \/ rUntilLock(i) \/ whileT(i) \/ whileF(i) \/ rUntilLWF(i) \/ rUntilLWT(i)
Spec == Init /\ [][Next]_vars

(*Pergunta2*)
(*a*)
typeOK == 
    /\ n \in 0..N
    /\ pc \in [1..N -> 0..3]
    /\ lock \in BOOLEAN 
    /\ waiting \in [1..N -> BOOLEAN]

(*b*)
notAllin2 == [] ~(\A x \in 1..N: (pc[x]=2))

(*c*)
Finish == \A i \in 1..N : pc[i] = 3
Termination == <> Finish

(*d*)
barreira == [] (\A x \in 1..N : pc[x] = 3 => \A y \in 1..N\{x}: pc[y] >= 1 )

(*e*)
(*Propriedade de safety, assim proibo o erro...*)
WaitingInvariant == [](\A i \in 1..N : waiting[i]  = FALSE) => ~(lock)
Spec2 == Init /\ [][Next]_vars /\ WaitingInvariant
=============================================================================