(*
   var
     waiter : boolean = true;
     fork   : array [0..N-1] of boolean = [N of true];
   
   function left(i : integer) : integer;
   begin
     left := i;
   end;

   function right(i : integer) : integer;
   begin
     right := mod (i-1) N;
   end;

   procedure phil(i : integer);
   begin
     while true do
     begin
0:         think 
       repeat until waiter; fica a espera ate ser verdade
       waiter := false;
1:     repeat until fork[left(i)];
       fork[left(i)] := false;
2:     repeat until fork[right(i)];
       fork[right(i)] := false;
       waiter := true;
3:          eat 
       fork[left(i)] := true;
       fork[right(i)] := true;       
     end
   end;

   phil(0) || ... || phil(N-1) 
*)

------------------------------ MODULE ex7 ------------------------------
EXTENDS Integers
CONSTANT N
ASSUME N > 1
VARIABLES waiter, fork, pc
vars == <<waiter, fork, pc>>

left(i) == i
right(i) == (i-1) % N

runtilWaiterF(i) ==
    /\ pc[i] = 0
    /\ waiter = FALSE
    /\ UNCHANGED <<fork,pc,waiter>>

runtilWaiterT(i) ==
    /\ pc[i] = 0
    /\ waiter = TRUE
    /\ waiter' = FALSE
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<fork>>

runtilForkLF(i) == 
    /\ pc[i] = 1
    /\ fork[left(i)] = FALSE
    /\ UNCHANGED <<fork,pc,waiter>>

runtilForkLT(i) == 
    /\ pc[i] = 1
    /\ fork[left(i)] = TRUE
    /\ fork' = [fork EXCEPT ![left(i)] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = 2]
    /\ UNCHANGED <<waiter>>

runtilForkRF(i) == 
    /\ pc[i] = 2
    /\ fork[right(i)] = FALSE
    /\ UNCHANGED <<pc,waiter,fork>>

runtilForkRT(i) == 
    /\ pc[i] = 2
    /\ fork[right(i)] = TRUE
    /\ fork' = [fork EXCEPT ![right(i)] = FALSE]
    /\ waiter' = TRUE
    /\ pc' = [pc EXCEPT ![i] = 3]

eat(i) == 
    /\ pc[i] = 3
    /\ fork' = [fork EXCEPT ![left(i)] = TRUE, ![right(i)] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = 0]
    /\ UNCHANGED <<waiter>>

Init == pc = [i \in 0..N-1 |-> 0] /\ waiter = TRUE /\ fork = [i \in 0..N-1 |-> TRUE]
Next == \E i \in 0..(N-1) : runtilWaiterF(i) \/ runtilWaiterT(i) \/ runtilForkLF(i) \/ runtilForkLT(i) \/ runtilForkRF(i) \/ runtilForkRT(i) \/ eat(i)
Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next) (*verificar que qualquer filósofo que já requisitou o empregado vai inevitavelmente comer*)

TypeOK == [] (pc \in [0..(N-1) -> 0..3] /\ waiter \in BOOLEAN /\ fork \in [0..(N-1) -> BOOLEAN])

(*verificar que filósofos vizinhos nunca comem ao mesmo tempo*)
vizinhos ==  [] (\A i \in 0..(N-1) : pc[i]=3 => ~(pc[right(i)]=3)) 
=============================================================================