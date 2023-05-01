------------------------- MODULE Status -------------------------

EXTENDS Naturals, TLC, Sequences

CONSTANTS N

VARIABLES inbox, worker_status, master_status, prepared

Status == {"Working","Prepared","Aborted","Committed"}

TypeOK == [] (inbox \in [0..N -> Seq([from : 0..N,type : Status ])]
            /\ worker_status \in [1..N -> Status]
            /\ master_status \in Status
            /\ prepared \in [1..N -> BOOLEAN])

Init == /\ inbox = [id \in 0..N |-> <<>>]
        /\ worker_status = [id \in 1..N |-> "Working"]
        /\ master_status = "Working"
        /\ prepared = [id \in 1..N |-> FALSE]

Worker_Finish(id) ==
    /\ worker_status[id] = "Working"
    /\ worker_status' = [worker_status EXCEPT ![id] = "Prepared"]
    /\ inbox' = [inbox EXCEPT ![0] = Append(@,[from |-> id, type |-> "Prepared"])] (*enviar mensagem*)
    /\ prepared' = prepared
    /\ master_status' = master_status

Worker_Abort(id) == 
    /\ worker_status[id] = "Working"
    /\ worker_status' = [worker_status EXCEPT ![id] = "Aborted"]
    /\ inbox' = inbox
    /\ prepared' = prepared
    /\ master_status' = master_status

Worker_Recieve(id) ==
    /\ Len(inbox[id]) # 0
    /\ (Head(inbox[id]).type = "Aborted" \/ Head(inbox[id]).type = "Prepared")
    /\ worker_status' = [worker_status EXCEPT ![id] = Head(inbox[id]).type] (*ir buscar*)
    /\ inbox' = [inbox EXCEPT ![id] = Tail(inbox[id])] (*como se fosse apagar mensagem dps de a usar*)
    /\ prepared' = prepared
    /\ master_status' = master_status

Broadcast(m) == inbox' = [id \in 0..N |-> IF id = 0 THEN inbox[0] ELSE Append(inbox[id],m)] (*enviar mensagem*)
    
Master_Abort_Transction == 
    /\ master_status = "Working"
    /\ master_status' = "Aborted"
    /\ Broadcast([from |-> 0, type |-> "Aborted"])
    /\ prepared' = prepared
    /\ worker_status' = worker_status

Master_Recieve_Message ==
    /\ Len(inbox[0]) # 0
    /\ prepared' = [prepared EXCEPT ![Head(inbox[0]).from] = TRUE]
    /\ (IF /\ prepared' = [id \in 1..N |-> TRUE]
          /\ master_status = "Working"
          THEN master_status' = "Committed"
            /\ Broadcast([from |-> 0, type |-> "Committed"])
          ELSE master_status' = master_status)
    /\ inbox' = [inbox EXCEPT ![0] = Tail(inbox[0])]
    /\ worker_status' = worker_status


Next ==(\E id \in 1..N : Worker_Recieve(id) \/ Worker_Finish(id) \/ Worker_Abort(id)) \/
        Master_Abort_Transction \/ Master_Recieve_Message

vars == <<inbox, worker_status, master_status, prepared>>

Spec == Init /\ [][Next]_vars

=============================================================================