(*Parte2*)
------------------------------ MODULE teste2 ---------------------------------
(*Pergunta 2*)
EXTENDS Naturals, TLC, Sequences, Randomization
CONSTANT N
ASSUME N>=0
VARIABLES inbox, result, try, pc
vars == <<inbox, result, try, pc>>

(*Funcao que escolhe um random (ajuda do chatgpt)*)
RandomNumberInRange == RandomElement({n \in 1..2 : 1 <= n /\ n <= 2})

Init == 
    /\ inbox = [id \in 0..N |-> <<>>]
    /\ result = [id \in 0..N |-> 0]
    /\ try = [id \in 0..N |-> RandomNumberInRange]
    /\ pc = [id \in 0..N |-> 0]

procedure1(i) ==
    /\ pc[i] = 0
    /\ inbox' = [inbox EXCEPT ![1-i] = Append(@,try[i])]
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<result,try>>

procedure2(i) ==
    /\ pc[i] = 1
    /\ IF (result[i] = 0 /\ Len(inbox[i]) # 0)
        THEN (IF Tail(inbox[i]) = <<try[i]>> 
                THEN try' = [try EXCEPT ![i] = RandomNumberInRange] /\ inbox' = [inbox EXCEPT ![1-i] = Append(@, try[i]), ![i] = Tail(inbox[i])] 
                ELSE UNCHANGED <<inbox, pc, try,result>>)
        ELSE result' = [result EXCEPT ![i] = try[i]] /\ UNCHANGED <<inbox, pc, try>>

Next == \E i \in 0..N : procedure1(i) \/ procedure2(i)
Spec == Init /\ [][Next]_vars

(*a*)
diferentes == (\A x \in 0..N : result[x] # 0 => \A y \in 0..N\{x} : result[y] # result[x])

(*b*)
MessagesNotOverflow == [](\A i \in 0..N : Len(inbox[i]) <= 2)

(*c*)
propriedade == \A x \in 0..N : result[x] # 0 => \E y \in 0..N\{x} : result[y] # 0 /\ result[y] # result[x]
=============================================================================