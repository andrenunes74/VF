(*
   type message = record
     msg: 1..N;
     bit: 0..1;
   end;

   var msgs : channel;
       acks : channel;

   procedure transmitter;
     var bit : 0..1 = 0;
         data : 1..N;
         m : message;
   begin
0:   while true do
     begin
          receive ack 
       if not empty(acks) then
       begin
         if receive(acks) = bit then
         begin
           bit := 1 - bit;
           data := 1..N;
         end
       end
       or else
         send msg 
       begin
         m.msg := data;
         m.bit := bit;
         send(m,msgs)
       end;
     end
   end;

   procedure receiver;
     var bit : 0..1 = 1;
         rcvd : 1..N;
         m : message;
   begin
0:   while true do
     begin
           receive msg 
       if not empty(msgs) then
       begin
         m := receive(msgs);
         rcvd := m.msg;
         bit := m.bit;
       end
       or else
          send ack
       begin
         send(bit,acks)
       end;
     end
   end;

   procedure dropper;
   begin
0:   while true do
     begin
          drop msg 
       if not empty(msgs) then receive(msgs)
       or else
          drop ack
       if not empty(drop) then receive(acks)
     end
   end;

   transmitter || received || dropper
*)
------------------------- MODULE ex9 -------------------------

EXTENDS Naturals, TLC, Sequences
CONSTANTS N, K
VARIABLES msgs, acks, bit_rec, bit_trans, data, rcvd
vars == <<msgs, acks, bit_rec, bit_trans, data, rcvd>>

empty(set) == Len(set) = 0
receive(set) == set' = Tail(set)
send(m, set) ==
    IF Len(set) < K THEN
        set' = Append(set, m)
    ELSE
        set' = Append(Tail(set), m)

transmitter_rec_ack ==
    /\ ~empty(acks)
    /\ bit_trans = Head(acks)
    /\ receive(acks)
    /\ bit_trans' = 1 - bit_trans
    /\ data' = 1..N
    /\ bit_rec' = bit_rec
    /\ UNCHANGED <<rcvd,msgs>>

transmitter_snd_msg ==
    /\ send([data |-> data, bit |-> bit_trans], msgs)
    /\ UNCHANGED <<acks,bit_rec,bit_trans,data,rcvd>>

receiver_snd_ack ==
    /\ ~empty(msgs)
    /\ bit_rec' = Head(msgs).bit
    /\ bit_trans' = bit_trans
    /\ data' = Head(msgs).data
    /\ receive(msgs)
    /\ UNCHANGED <<acks,rcvd>>

receiver_rec_msg ==
    /\ send(bit_rec, acks)
    /\ UNCHANGED <<msgs,bit_rec,bit_trans,data,rcvd>>

dropper_msg ==
    /\ ~empty(msgs)
    /\ receive(msgs)
    /\ UNCHANGED <<acks,bit_rec,bit_trans,data,rcvd>>

dropper_ack ==
    /\ ~empty(acks)
    /\ receive(acks)
    /\ UNCHANGED <<msgs,bit_rec,bit_trans,data,rcvd>>

Init == /\ msgs = <<>>
        /\ acks = <<>>
        /\ bit_rec = 0
        /\ bit_trans = 1
        /\ data = 0
        /\ rcvd = 0

Next == transmitter_rec_ack \/ transmitter_snd_msg
    \/  receiver_snd_ack \/ receiver_rec_msg
    \/  dropper_msg \/ dropper_ack

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == [] (msgs \in Seq([data : 1..N, bit : 0..1]))
          /\ acks \in Seq(0..1)
          /\ bit_rec \in 0..1
          /\ bit_trans \in 0..1
          /\ data \in 1..N
          /\ rcvd \in 1..N

MessagesNotOverflow == [](Len(acks) <= K)
MessagesNotLost == []<>(msgs = <<>>)

=============================================================================