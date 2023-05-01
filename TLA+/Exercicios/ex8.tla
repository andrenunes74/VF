(*
var 
    outbox : array [1..N] of channel;
    inbox  : array [1..N] of channel;

   procedure node(id : integer);
    var 
       elected : boolean = false;
       msg : integer;
   begin
    send(id,outbox[id]);
0:   while true do
    begin
       msg := receive(inbox[id]);
       if msg >= id then send(msg,outbox[id]);
       if msg =  id then elected := true
    end
   end;

   procedure transmit;
    var 
       msg : integer;
       id : integer; 
   begin
0: while true do
    begin
       repeat id := 1..N until not empty(outbox[id]);
       msg := receive(outbox[id]);
       send(msg,inbox[succ(id)])
    end
   end;

   node(1) || ... || node(N) || transmit
*)
------------------------ MODULE ex8 -------------------------
EXTENDS Naturals, TLC
CONSTANTS N, succ
VARIABLES outbox, inbox, elected

Node == 1..N

func(n) == CHOOSE x \in Node : succ [x] = n

reachable(n) ==
  LET aux[i \in Nat] == 
    IF i = 1 THEN { succ[n] }
    ELSE aux[i-1] \cup { x \in Node : \E y \in aux[i-1] : x = succ[y] }
  IN aux[N]

ASSUME 
    /\ N > 0
    /\ succ \in [Node -> Node]
    /\ \A x \in Node : Node \subseteq reachable(x)
        
node(id) == \E m \in inbox[id] :
    /\ inbox'   = [inbox EXCEPT ![id] = @ \ {m}]
    /\ outbox'  = IF m >= id 
                  THEN [outbox EXCEPT ![id] = @ \cup {m}]
                  ELSE outbox
    /\ elected' = IF m = id
                  THEN [elected EXCEPT ![id] = TRUE]
                  ELSE elected

transmit == \E id \in Node : \E m \in outbox[id] :
    /\ outbox' = [a \in Node |-> {}]
    /\ inbox'  = [a \in Node |-> outbox[func(a)] \cup inbox[a]]
    /\ UNCHANGED elected
    
Init ==
    /\ outbox  = [id \in Node |-> {id}]
    /\ inbox   = [id \in Node |-> {}]
    /\ elected = [id \in Node |-> FALSE]

Next == transmit \/ \E id \in Node : node(id)
vars == <<outbox, inbox, elected>>
Spec == Init /\ [][Next]_vars

TypeOK == [] (outbox \in [Node -> SUBSET Node] /\ inbox \in [Node -> SUBSET Node] /\ elected \in [Node -> BOOLEAN])
AtMostOneLeader == [] (\A x,y \in Node : elected[x] /\ elected[y] => x = y)
LeaderStaysLeader == \A x \in Node : [] (elected[x] => [] (elected[x]))
AtLeastOneLeader == WF_vars(Next) => <> (\E x \in Node : elected[x])

config == 5:> 4 @@ 4:>3 @@ 3:>2 @@ 2:>1 @@ 1:>5

Ex1 == ([] \A x \in Node : elected[x])
Ex1a == ~(<> \E x \in Node : elected[x]) 
==================================================================