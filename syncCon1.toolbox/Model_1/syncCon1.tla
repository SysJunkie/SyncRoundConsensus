--------------------------------- MODULE syncCon1 ---------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, FAILNUM
ASSUME N <= 5 /\ 0<=FAILNUM /\ FAILNUM <=4
Nodes == 1..N
 
(*
--algorithm syncCon1
{ variable FailNum = FAILNUM,
           up = [n \in Nodes |-> TRUE];
           pt = [n \in Nodes |-> 0];
           t = [n \in Nodes |-> FALSE];
           d = [n \in Nodes |-> -1];
           mb = [n \in Nodes |-> {}];
  define {
     SetMin(S) ==  CHOOSE i \in S : \A j \in S : i <= j
  }       
  macro MayBeFail(){
     if(FailNum > 0 /\ up[self]){
         either {
                 up[self] := FALSE;
                 FailNum := FailNum - 1;
                }
         or skip;
     };
  }
 
  fair process(n \in Nodes)
  variable v = 0, pv = 0, Q = {};
  {
  P: if(up[self]){
       v := self;
       Q := Nodes;
     
  PS:    while(up[self] /\ Q # {}) {
           with(p \in Q){
             \* Node can fail here, such that up[self] will be set to False
             \* A process can fail anytime during the broadcast
             MayBeFail();
             \* Pop process p from Q
             Q := Q \ {p};
             if(up[self]){
                mb[p] := mb[p] \union {v};  \* Broadcast value of self to each process if self is up
             }  
           };  
         }; 
            
         \* A node may fail after broadcast        
         MayBeFail();
         
        \* Increase the number of rounds that are completed if the node is up   
         if(up[self]){
            pt[self] := pt[self] + 1;
         };
         
         \* To await, a process must be up and every other process should be on the same round
         \* Wait for others to move to next round
         \* If the node is down, exit.
  PR:    await(up[self] = FALSE \/ (up[self] /\ (\A i \in Nodes: IF up[i] THEN pt[i] = pt[self] ELSE TRUE))); \* agreement property is that two variables cannot
                          
         \* Terminate and compute decision if the node is up
         if(up[self]){                         
            d[self] := SetMin(mb[self]);
            t[self] := TRUE;
         }
     };
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES FailNum, up, pt, t, d, mb, pc

(* define statement *)
SetMin(S) ==  CHOOSE i \in S : \A j \in S : i <= j

VARIABLES v, pv, Q

vars == << FailNum, up, pt, t, d, mb, pc, v, pv, Q >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ pt = [n \in Nodes |-> 0]
        /\ t = [n \in Nodes |-> FALSE]
        /\ d = [n \in Nodes |-> -1]
        /\ mb = [n \in Nodes |-> {}]
        (* Process n *)
        /\ v = [self \in Nodes |-> 0]
        /\ pv = [self \in Nodes |-> 0]
        /\ Q = [self \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF up[self]
                 THEN /\ v' = [v EXCEPT ![self] = self]
                      /\ Q' = [Q EXCEPT ![self] = Nodes]
                      /\ pc' = [pc EXCEPT ![self] = "PS"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << v, Q >>
           /\ UNCHANGED << FailNum, up, pt, t, d, mb, pv >>

PS(self) == /\ pc[self] = "PS"
            /\ IF up[self] /\ Q[self] # {}
                  THEN /\ \E p \in Q[self]:
                            /\ IF FailNum > 0 /\ up[self]
                                  THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                             /\ FailNum' = FailNum - 1
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<FailNum, up>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << FailNum, up >>
                            /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                            /\ IF up'[self]
                                  THEN /\ mb' = [mb EXCEPT ![p] = mb[p] \union {v[self]}]
                                  ELSE /\ TRUE
                                       /\ mb' = mb
                       /\ pc' = [pc EXCEPT ![self] = "PS"]
                       /\ pt' = pt
                  ELSE /\ IF FailNum > 0 /\ up[self]
                             THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                        /\ FailNum' = FailNum - 1
                                     \/ /\ TRUE
                                        /\ UNCHANGED <<FailNum, up>>
                             ELSE /\ TRUE
                                  /\ UNCHANGED << FailNum, up >>
                       /\ IF up'[self]
                             THEN /\ pt' = [pt EXCEPT ![self] = pt[self] + 1]
                             ELSE /\ TRUE
                                  /\ pt' = pt
                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                       /\ UNCHANGED << mb, Q >>
            /\ UNCHANGED << t, d, v, pv >>

PR(self) == /\ pc[self] = "PR"
            /\ (up[self] = FALSE \/ (up[self] /\ (\A i \in Nodes: IF up[i] THEN pt[i] = pt[self] ELSE TRUE)))
            /\ IF up[self]
                  THEN /\ d' = [d EXCEPT ![self] = SetMin(mb[self])]
                       /\ t' = [t EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED << t, d >>
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << FailNum, up, pt, mb, v, pv, Q >>

n(self) == P(self) \/ PS(self) \/ PR(self)

Next == (\E self \in Nodes: n(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))

\*Agreement invariant
\* The nodes that have terminated (up nodes) have the same decision values
Agreement == \A i \in Nodes: \A j \in Nodes: IF t[i] /\ t[j] THEN d[i] = d[j] ELSE TRUE

\* Termination property
\* If the node is up, it has terminated (its t is TRUE) otherwise it has not terminated
Termination == <>(\A i \in Nodes: IF up[i] THEN t[i] = TRUE ELSE t[i] = FALSE)
\* END TRANSLATION
 
 
\* END TRANSLATION
 
================================================
Members:
-------- 
Name: Sneha Mehta
UBIT Name: snehameh
Person# - 50245877

Name: Varun Jain
UBIT Name: varunjai 
Person# - 50247176

Explanation:
Agreement Property: The nodes that have terminated (up nodes) have the same decision values

- The agreement property is satisfied when FAILNUM=0

We take 3 Nodes in the system and check for FAILNUM=1 ie 1 node crashes out of the 3 nodes.
In this scenario the final state at which the Agreement Invariant is violated is:

/\  FailNum = 0
/\  Q = <<{3}, {}, {}>>
/\  d = <<-1, 1, 2>>
/\  mb = <<{2, 3}, {1, 2, 3}, {2, 3}>>
/\  pc = <<"PS", "Done", "Done">>
/\  pt = <<0, 1, 1>>
/\  pv = <<0, 0, 0>>
/\  t = <<FALSE, TRUE, TRUE>>
/\  up = <<FALSE, TRUE, TRUE>>
/\  v = <<1, 2, 3>>

1. In this scenario, when Node 1 fails, it was able to broadcast its value to Node 2 but not to Node 3.
2. Node 2 terminates(t=TRUE) with minimum value 1, which was sent by Node 1 (its decision is 1). 
3. Node 3 terminates(t=TRUE) with minimum value 2 (its decision is 2).
4. Since both have different decision values at termination, it violates the Agreement property.
5. Note that Node 1 fails, and we do not set its t[1] to TRUE. It remains FALSE as initially set.
   The decision of the crashed node is not taken into consideration.

   
Nodes: 3 and Crash: 2

/\  FailNum = 1
/\  Q = <<{3}, {}, {}>>
/\  d = <<-1, 1, 2>>
/\  mb = <<{2, 3}, {1, 2, 3}, {2, 3}>>
/\  pc = <<"PS", "Done", "Done">>
/\  pt = <<0, 1, 1>>
/\  pv = <<0, 0, 0>>
/\  t = <<FALSE, TRUE, TRUE>>
/\  up = <<FALSE, TRUE, TRUE>>
/\  v = <<1, 2, 3>>
   
   