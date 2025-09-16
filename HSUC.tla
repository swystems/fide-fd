-------------------------------- MODULE HSUC --------------------------------
EXTENDS Integers
CONSTANT P, V
VARIABLES 
    leader,
    correct,
    proposal,
    acks,
    nw,
    crashed,
    broadcast,
    decision,
    proposer,
    proposed

normalvars ==  <<leader,correct,proposal,acks,nw,broadcast,decision,proposer,proposed>>  
vars == <<leader,correct,proposal,acks,crashed,nw,broadcast,decision,proposer,proposed>>  

    
Min(S) == 
    IF S = {} 
    THEN -1 
    ELSE CHOOSE n \in S : \A k \in S : n \leq k
    
Messages == [type : {"propose"}, v : V] \cup [type : {"ack"}] \cup [type: {"decide"}, v : V]
    
HSUCTypeOK == 
    /\ leader \in [P -> P]
    /\ correct \in [P -> SUBSET P]
    /\ proposal \in [P -> V \cup {-1}]
    /\ acks \in [P -> SUBSET P]
    /\ nw \subseteq ([data: Messages, from: P, to: P] \cup [data: Messages, from: P, delivered: SUBSET P]) 
    /\ crashed \subseteq P
    /\ broadcast \in [P -> {0, 1}]
    /\ decision \in [P -> V \cup {-1}]
    /\ proposer \in [P -> P \cup {-1}]
    /\ proposed \in [P -> {0, 1}]
    
HSUCInit ==
    /\ leader = [p \in P |-> Min(P)] 
    /\ acks = [p \in P |-> {}]
    /\ proposal = [p \in P |-> -1]
    /\ correct = [p \in P |-> P]
    /\ crashed = {}
    /\ broadcast = [p \in P |-> 0]
    /\ decision = [p \in P |-> -1]
    /\ nw = {}
    /\ proposer = [p \in P |-> -1]
    /\ proposed = [p \in P |-> 0]
    
Send(p, m, q) == nw' = nw \cup {[data |-> m, from |-> p, to |-> q]}    
MSend(p, m, ps) == nw' = nw \cup {[data |-> m, from |-> p, to |-> q] : q \in ps}
Recv(p, m, q) == 
    /\ [data |-> m, from |-> q, to |-> p] \in nw
    /\ nw' = nw \ {[data |-> m, from |-> q, to |-> p]}
RecvSend(p, qm, q, rm) ==
    /\ [data |-> qm, from |-> q, to |-> p] \in nw
    /\ nw' = (nw \ {[data |-> qm, from |-> q, to |-> p]}) \cup {[data |-> rm, from |-> p, to |-> q]} 
BCast(p, m) ==
    nw' = nw \cup {[data |-> m, from |-> p, delivered |-> {}]}
Deliver(p, m) ==
    \E q \in P, d \in SUBSET P : 
        /\ p \notin d
        /\ [data |-> m, from |-> q, delivered |-> d] \in nw
        /\ nw' = (nw \ {[data |-> m, from |-> q, delivered |-> d]}) \cup {[data |-> m, from |-> q, delivered |-> d \cup {p}]} 
        
   
Crashed(p) == p \in crashed
        
LoseMessage(p) == 
    \E q \in P, m \in Messages :
        /\ [data |-> m, from |-> p, to |-> q] \in nw
        /\ nw' = nw \ {[data |-> m, from |-> p, to |-> q]}
        /\ UNCHANGED <<leader, correct, proposal, acks, crashed, broadcast, decision, proposer,proposed>>
LoseBCastMessageRB(p) ==
    \E m \in Messages, d \in SUBSET P : 
        /\ [from |-> p, data |-> m, delivered |-> d] \in nw
        /\ d \subseteq crashed
        /\ nw' = nw \ {[from |-> p, data |-> m, delivered |-> d]}
        /\ UNCHANGED <<leader, correct, proposal, acks, crashed, broadcast, decision, proposer, proposed>>

LoseBCastMessageBEB(p) ==
    \E m \in Messages, d \in SUBSET P, q \in P: 
        /\ [from |-> p, data |-> m, delivered |-> d] \in nw
        /\ q \notin d
        /\ nw' = (nw \ {[from |-> p, data |-> m, delivered |-> d]}) \cup {[from |-> p, data |-> m, delivered |-> d \cup {p}]}
        /\ UNCHANGED <<leader, correct, proposal, acks, crashed, broadcast, decision, proposer, proposed>>
    
Propose(p) == 
    /\ proposed[p] = 0
    /\ IF proposal[p] = -1 
        THEN \E v \in V : proposal' = [proposal EXCEPT ![p] = v]
        ELSE UNCHANGED <<proposal>>
    /\ IF p = leader[p]
        THEN 
            /\ MSend(p, [type |-> "propose", v |-> proposal'[p]], correct[p])
        ELSE UNCHANGED <<nw>>
    /\ proposed' = [proposed EXCEPT ![p] = 1]
    /\ UNCHANGED <<leader, correct, acks, crashed, broadcast, decision, proposer>>
    
DetectCrash(p) ==
    /\ \E q \in crashed : 
        /\ q \in correct[p]
        /\ correct' = [correct EXCEPT ![p] = correct[p] \ {q}]
        /\ IF q = leader[p] 
            THEN leader' = [leader EXCEPT ![p] = Min(correct'[p])]
            ELSE UNCHANGED <<leader>>
        /\ IF p = leader'[p] /\ proposal[p] # -1
            THEN MSend(p, [type |-> "propose", v |-> proposal[p]], correct[p])
            ELSE UNCHANGED <<nw>>
    /\ UNCHANGED <<proposal, acks, crashed, broadcast, decision, proposer, proposed>>   
       
Crash(p) == 
    /\ p \notin crashed
    /\ \E q \in P : q \notin crashed /\ q # p
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<leader, correct, proposal, acks, nw, broadcast, decision, proposer, proposed>>

ReceiveProposal(p) == 
    /\ \E q \in P, m \in Messages :
        /\ (proposer[p] = -1 \/ proposer[p] <= q) 
        /\ RecvSend(p, m, q, [type |-> "ack"])
        /\ m.type = "propose"
        /\ proposal' = [proposal EXCEPT ![p] = m.v]
        /\ proposer' = [proposer EXCEPT ![p] = q]
    /\ UNCHANGED <<leader, correct, acks, crashed, broadcast, decision, proposed>>
        
ReceiveAck(p) ==
    /\ \E q \in P, m \in Messages :
        /\ Recv(p, m, q)
        /\ m.type = "ack"
        /\ acks' = [acks EXCEPT ![p] = acks[p] \cup {q}]
    /\ UNCHANGED <<leader, correct, proposal, crashed, broadcast, decision, proposer, proposed>>
        
Decide(p) ==
    /\ decision[p] = -1
    /\ \E m \in Messages : 
        /\ Deliver(p, m)
        /\ m.type = "decide"
        /\ decision' = [decision EXCEPT ![p] = m.v]
        /\ UNCHANGED <<leader, correct, proposal, acks, crashed, broadcast, proposer, proposed>>
        
SendDecision(p) ==
    /\ correct[p] \subseteq acks[p]
    /\ broadcast[p] = 0
    /\ BCast(p, [type |-> "decide", v |-> proposal[p]])
    /\ broadcast' = [broadcast EXCEPT ![p] = 1]
    /\ UNCHANGED <<leader, correct, proposal, acks, crashed, decision, proposer, proposed>>   
    
NonCrash ==
    \/ \E p \in P : 
        \/ ~Crashed(p) /\ Propose(p)
        \/ ~Crashed(p) /\ DetectCrash(p)
        \/ ~Crashed(p) /\ ReceiveProposal(p)
        \/ ~Crashed(p) /\ ReceiveAck(p)
        \/ ~Crashed(p) /\ SendDecision(p)
        \/ ~Crashed(p) /\ Decide(p)
        \/ Crashed(p) /\ LoseMessage(p)
        \/ Crashed(p) /\ LoseBCastMessageRB(p) 
    
HSUCNext ==
    \/ NonCrash
    \/ \E p \in P : Crash(p)
    
HSUCSpec == HSUCInit /\ [][HSUCNext]_vars /\ WF_<<normalvars>>(NonCrash) /\ <> \A p \in P : proposed[p] = 1 \/ p \in crashed

Termination == <> \A p \in P : decision[p] # -1 \/ p \in crashed
    
Agreement ==
    ~ \E p \in P, q \in P : decision[p] # -1 /\ decision[q] # -1 /\ decision[p] # decision[q] 
    

=============================================================================
\* Modification History
\* Last modified Thu Nov 30 21:50:01 CET 2023 by pschuprikov
\* Created Tue Nov 28 10:07:21 CET 2023 by pschuprikov
