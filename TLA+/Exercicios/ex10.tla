(*
   type status = (Working,Prepared,Aborted,Committed);

   type message = record
     from: 0..N;
     type: status;
   end;

   var inbox : array [0..N] of channel;

   procedure worker(id : integer);
     var state : status = Working;
         msg : message; 
   begin
0:   while true do
     begin
          Finish task 
       if state = Working then
       begin 
         state := Prepared; 
         msg.from = id;
         msg.type = Prepared;
         send(msg,inbox[0])
       end
       or else
          Abort task  
       if state = Working then 
       begin
         state := Aborted
       end
       or else
          Receive message 
       if not empty(inbox[id]) then
       begin
         msg := receive(inbox[id]); 
         if msg.type = Aborted or msg.type = Committed then state := msg.type;
       end
     end
   end;

   procedure broadcast(msg : message);
     var id : integer = 1;
   begin
     while id <= N do
     begin
       send(msg,inbox[id]);
       id := id + 1
     end
   end;

   procedure master;
     var state : status = Working;
         prepared : array 1..N of boolean = [N of false];
         msg : message;
     procedure 
   begin
0:   while true do
     begin
          Abort transaction 
       if state = Working then
       begin 
         state := Aborted; 
         msg.from = 0;
         msg.type = Aborted;
         broadcast(msg)
       end
       or else
          Receive message 
       if not empty(inbox[0]) then
       begin
         msg := receive(inbox[0]);
         prepared[msg.from] := true; 
         if state = Working and prepared = [N of true] then 
         begin 
           msg.from = 0;
           msg.type = Committed;
           state := Committed; 
           broadcast(msg) 
         end
       end
     end
   end;

   master || worker(1) || ... || worker(N)
*)
------------------------------ MODULE ex10 ---------------------------------

EXTENDS Naturals, TLC, Sequences
CONSTANT N
ASSUME N>=0
VARIABLES inbox, state, id, prepared, statusMaster
vars == <<inbox, state, id, prepared, statusMaster>>

stat == {"Working","Prepared","Aborted","Committed","init"}

send(a,b) == inbox' = [inbox EXCEPT ![b] = a]

Init == 
    /\ inbox = [x \in 0..N |->[from |-> N+1, type|-> "init"]] (*Estado inicial como se fosse vazio*)
    /\ state = [x \in 1..N |-> "Working"]
    /\ id = 1
    /\ prepared = [x \in 1..N |-> FALSE]
    /\ statusMaster = "Working"

typeOK == 
    /\ prepared \in [0..N -> BOOLEAN]
    /\ statusMaster \in stat
    /\ id \in 1..N
    /\ \A x \in stat: state \in [1..N -> x]
    /\ \A x \in stat: (inbox \in Seq([from: 0..N, type: x ]))

workerFinish(i) ==
    /\ state[i] = "Working" 
    /\ state' = [state EXCEPT ![i] = "Prepared"]
    /\ send([from |-> i, type|-> "Prepared"], 0)
    /\ UNCHANGED <<id,prepared,statusMaster>>

workerAbort(i) ==
    /\ state[i] = "Working" 
    /\ state' = [state EXCEPT ![i] = "Aborted"]
    /\ UNCHANGED <<id,prepared,statusMaster,inbox>>

workerRcv(i) == 
    /\ ~(inbox[i] = [from |-> N+1, type|-> "init"])
    /\ (inbox[i].type = "Aborted" \/ inbox[i].type = "Committed")
    /\ state' = [state EXCEPT ![i] = inbox[i].type]
    /\ UNCHANGED <<id,prepared,statusMaster,inbox>>

broadcast(a,b) ==
    IF (id <= N)
    THEN send([from |-> a, type|-> b], id) /\ id' = id + 1 /\ UNCHANGED <<prepared,state>>
    ELSE id' = 1 /\ UNCHANGED <<prepared,statusMaster,state,inbox>>

masterAbort ==
    /\ statusMaster = "Working"
    /\ statusMaster' = "Aborted"
    /\ broadcast(0,"Aborted")
    /\ UNCHANGED <<prepared,state>>

masterReceive ==
    /\ ~(inbox[0] = [from |-> N+1, type|-> "init"])
    /\ prepared'=[prepared EXCEPT ![inbox[0].from] = TRUE]
    /\ IF statusMaster = "Working" /\ (\A x \in 1..N: prepared[x] = TRUE)
        THEN statusMaster' = "Committed" /\ broadcast(0,"Committed") /\ UNCHANGED <<state>>
        ELSE UNCHANGED <<statusMaster,inbox,id,state>>

Next == masterAbort \/ masterReceive \/ (\E i \in 1..N : workerRcv(i) \/ workerAbort(i) \/ workerFinish(i))
Spec == Init /\ [][Next]_vars

Consistencia == \A x,i \in 1..N: ~(state[i]= "Aborted" /\ state[x]= "Committed")
Estabilidade == \A i \in 1..N: (state[i]= "Aborted" \/ state[i]= "Committed") => [](state[i]= "Aborted" \/ state[i]= "Committed")
Progresso == \A x \in 1..N: state[x]= "Committed" => (<> \A i \in 1..N: state[i]= "Committed")

=============================================================================