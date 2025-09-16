-------------------------------- MODULE HUC --------------------------------
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
    proposed

normalvars ==  <<leader,correct,proposal,acks,nw,broadcast,decision,proposed>>  
vars == <<leader,correct,proposal,acks,crashed,nw,broadcast,decision,proposed>>  

    
Min(S) == 
    IF S = {} 
    THEN -1 
    ELSE CHOOSE n \in S : \A k \in S : n \leq k
    
Messages == [type : {"propose"}, v : V] \cup [type: {"decide"}, v : V]
    
HUCTypeOK == 
    /\ leader \in [P -> P]
    /\ correct \in [P -> SUBSET P] \* powerset of P
    /\ proposal \in [P -> [P -> V \cup {-1}]]
    /\ acks \in [P -> SUBSET P]
    /\ nw \subseteq ([data: Messages, from: P, to: P] \cup [data: Messages, from: P, delivered: SUBSET P]) 
    /\ crashed \subseteq P
    /\ broadcast \in [P -> {0, 1}]
    /\ decision \in [P -> V \cup {-1}]
    /\ proposed \in [P -> {0, 1}]
    
HUCInit ==
    /\ leader = [p \in P |-> Min(P)] 
    /\ acks = [p \in P |-> {}]
    /\ proposal = [p \in P |-> [q \in P |-> -1]]
    /\ correct = [p \in P |-> P]
    /\ crashed = {}
    /\ broadcast = [p \in P |-> 0]
    /\ decision = [p \in P |-> -1]
    /\ nw = {}
    /\ proposed = [p \in P |-> 0]
    
Send(p, m, q) == nw' = nw \cup {[data |-> m, from |-> p, to |-> q]}    
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
        /\ UNCHANGED <<leader, correct, proposal, acks, crashed, broadcast, decision, proposed>>
LoseBCastMessage(p) ==
    \E m \in Messages, d \in SUBSET P : 
        /\ [from |-> p, data |-> m, delivered |-> d] \in nw
        /\ d = {}
        /\ nw' = nw \ {[from |-> p, data |-> m, delivered |-> d]}
        /\ UNCHANGED <<leader, correct, proposal, acks, crashed, broadcast, decision, proposed>>
    
    
Propose(p) == 
    /\ proposed[p] = 0
    /\ proposed' = [proposed EXCEPT ![p] = 1]
    /\ \E v \in  V : proposal' = [proposal EXCEPT ![p][p] = v]
    /\ Send(p, [type |-> "propose", v |-> proposal'[p][p]], leader[p])
    /\ UNCHANGED <<leader, correct, acks, crashed, broadcast, decision>>
    
CanDetectCrash(p, q) == 
    /\ ~\E m \in nw : 
        /\ "delivered" \in DOMAIN m
        /\ m.from = q 
        /\ p \notin m.delivered
    
DetectCrash(p) ==
    /\ \E q \in crashed : 
        /\ CanDetectCrash(p, q)
        /\ q \in correct[p]
        /\ correct' = [correct EXCEPT ![p] = correct[p] \ {q}]
        /\ proposal' = [proposal EXCEPT ![p][q] = -1]
        /\ IF q = leader[p] 
            THEN 
                /\ leader' = [leader EXCEPT ![p] = Min(correct'[p])]
                /\ IF proposal[p][p] # -1
                    THEN Send(p, [type |-> "propose", v |-> proposal[p][p]], leader'[p])
                    ELSE UNCHANGED <<nw>>
            ELSE UNCHANGED <<leader, nw>>
    /\ UNCHANGED <<acks, crashed, broadcast, decision, proposed>>   
       
Crash(p) == 
    /\ p \notin crashed
    /\ \E q \in P : q \notin crashed /\ q # p \* f = n-1 condition
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<leader, correct, proposal, acks, nw, broadcast, decision, proposed>>

ReceiveProposal(p) == 
    /\ \E q \in P, m \in Messages :
        /\ Recv(p, m, q)
        /\ m.type = "propose"
        /\ proposal' = [proposal EXCEPT ![p][q] = m.v]
        /\ acks' = [acks EXCEPT ![p] = acks[p] \cup {q}]
    /\ UNCHANGED <<leader, correct, crashed, broadcast, decision, proposed>>
        
DeliverDecision(p) ==
    /\ decision[p] = -1
    /\ \E m \in Messages : 
        /\ Deliver(p, m)
        /\ m.type = "decide"
        /\ decision' = [decision EXCEPT ![p] = m.v]
        /\ UNCHANGED <<leader, correct, proposal, acks, crashed, broadcast, proposed>>
        
Choose(ps) ==
    ps[Min({p \in P : ps[p] # -1})]
        
SendDecision(p) ==
    /\ correct[p] \subseteq acks[p]
    /\ broadcast[p] = 0
    /\ broadcast' = [broadcast EXCEPT ![p] = 1]
    /\ BCast(p, [type |-> "decide", v |-> Choose(proposal[p])])
    /\ UNCHANGED <<leader, correct, proposal, acks, crashed, decision, proposed>>   
    
NonCrash ==
    \/ \E p \in P : 
        \/ ~Crashed(p) /\ Propose(p)
        \/ ~Crashed(p) /\ DetectCrash(p)
        \/ ~Crashed(p) /\ ReceiveProposal(p)
        \/ ~Crashed(p) /\ SendDecision(p)
        \/ ~Crashed(p) /\ DeliverDecision(p)
        \/ Crashed(p) /\ LoseMessage(p)
        \/ Crashed(p) /\ LoseBCastMessage(p) 
    
HUCNext ==
    \/ NonCrash
    \/ \E p \in P : Crash(p)
    
HUCSpec == HUCInit /\ [][HUCNext]_vars /\ WF_<<normalvars>>(NonCrash) /\ <> \A p \in P : proposed[p] = 1 \/ p \in crashed

Termination == <> \A p \in P : decision[p] # -1 \/ p \in crashed
    
Agreement ==
    ~ \E p \in P, q \in P : decision[p] # -1 /\ decision[q] # -1 /\ decision[p] # decision[q]
=============================================================================
\* Modification History
\* Last modified Thu Nov 30 17:13:43 CET 2023 by pschuprikov
\* Created Tue Nov 28 10:07:21 CET 2023 by pschuprikov
