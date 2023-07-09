------------------- MODULE System ------------------

EXTENDS Naturals, RealTime

CONSTANTS Data, SENDTIME
CONSTANT BusSend(_)
ASSUME \A m: BusSend(m) \in BOOLEAN 
ASSUME SENDTIME \in Nat /\ SENDTIME > 0

VARIABLES terminals, bus, collision, timers
-----------------------------------------------------
NoData == CHOOSE d: d \notin Data

TypeInv == /\ terminals \in [Nat -> [status: {"rdy", "trying", "fail",
                                             "transmiting", "waiting", "recovering",
                                             "retry", "collision", "restart"},
                                     msg: Data \cup {NoData}]]
           /\ bus, collision \in {0, 1}
           /\ timers = [Nat -> [t, l: Nat, r: {"no", "yes"}]]

Ts == INSTANCE Timers

Init == /\ Ts!Init
        /\ terminals = [n \in Nat -> [status -> "rdy", msg -> NoData]]
        /\ bus = 0
        /\ collision = 0

vars == <<terminals, bus, collision, timers>>
-----------------------------------------------------

SetSend(i) ==  /\ terminals[i].status = "rdy"
               /\ \E d \in data:
                    /\ Ts!Set(i, SENDTIME)
                    /\ terminals' = [terminals EXCEPT 
                                     ![i] = [status -> "trying", msg -> d]]
                    /\ UNCHANGED <<bus, collision>>

SendOk(i) == /\ terminals[i].status = "trying"
             /\ bus = 0
             /\ BusSend(terminals[i].msg)
             /\ Ts!Start(i)
             /\ terminals' = [terminals EXCEPT 
                              ![i] = [status -> "transmiting", msg -> @.msg]]
             /\ bus' = 1
             /\ UNCHANGED <<collision>>




SendFail(i) == /\ terminals[i].status = "trying"
               /\ bus = 1
               /\ \E r \in Nat:
                    /\ r > 0
                    /\ Ts!Set(i, r)
                    /\ terminals' = [terminals EXCEPT 
                                     ![i] = [status -> "fail", msg -> @.msg]]
                    /\ UNCHANGED <<bus, collision>>

Fail(i) == /\ terminals[i].status = "fail"
           /\ Ts!Start(i)
           /\ terminals' = [terminals EXCEPT 
                            ![i] = [status -> "waiting", msg -> @.msg]]
           /\ UNCHANGED <<bus, collision>

WaitAfterFail(i) == /\ terminals[i].status = "waiting"
                    /\ Ts!Timeout(i)
                    /\ terminals' = [terminals EXCEPT 
                                     ![i] = [status -> "retry", msg -> @.msg]]
                    /\ UNCHANGED <<bus, collision>>

Retry(i) == /\ terminals[i].status = "retry"
            /\ Ts!Set(i, SENDTIME)
            /\ terminals' = [terminals EXCEPT 
                             ![i] = [status -> "trying", msg -> @.msg]]
            /\ UNCHANGED <<bus, collision>>

WaitAfterCollision(i) == /\ terminals[i].status = "recovering"
                         /\ Ts!Timeout(i)
                         /\ terminals' = [terminals EXCEPT 
                                          ![i] = [status -> "rdy", msg -> @.msg]]
                         /\ UNCHANGED <<bus, collision>>

Deliver(i) == /\ terminals[i].status = "transmiting"
              /\ Ts!Timeout(i)
              /\ bus = 1
              /\ terminals' = [terminals EXCEPT 
                               ![i] = [status -> "rdy", msg -> NoData]]
              /\ bus' = 0
              /\ UNCHANGED <<collision>>

DetectCollision == \E i,j \in Nat /\ i /= j: /\ terminals[i] = "transmiting"
                                             /\ terminals[j] = "transmiting"
                                             /\ collision' = 1
                                             /\ UNCHANGED <<bus, timers, terminals>>



Collision == /\ collision = 1
             /\ terminals' = [n \in Nat -> [status -> "collision", msg -> NoData]]
             /\ timers' = [n \in Nat -> [t -> 0, l -> 0, r -> "no"]]
             /\ bus' = 0
             /\ collision' = 0

SetAfterCollision(i) == /\ terminals[i].status = "collision"
                        /\ \E r \in Nat /\ r > 0:
                            /\ Ts!Set(i, r)
                            /\ terminals' = [terminals EXCEPT 
                                             ![i] = [status -> "restart", msg -> @.msg]]
                            /\ UNCHANGED <<bus, collision>>

Restart(i) == /\ terminals[i].status = "restart"
              /\ Ts!Start(i)
              /\ terminals' = [terminals EXCEPT 
                               ![i] = [status -> "recovering", msg -> @.msg]]
              /\ UNCHANGED <<bus, collision>>


Next == \/ Collision
        \/ DetectCollision
        \/ (\E i \in Nat: \/ SetSend(i) \/ SendOk(i) \/ SendFail(i)
                          \/ Fail(i) \/ Retry(i) \/ Deliver(i)
                          \/ WaitAfterFail(i) \/ WaitAfterCollision(i)
                          \/ SetAfterCollision(i) \/ Restart(i))
                      
Fairness == /\ WF_vars(DetectCollision)
            /\ \E i \in Nat: WF_vars( \/ SendFail(i) \/ Retry(i) 
                                      \/ Fail(i) \/ SetAfterCollision(i)
                                      \/ Restart(i))
            /\ \E i \in Nat: SF_vars(SendOk(i))

Spec == /\ Init 
        /\ [][Next]_vars 
        /\ Fairness 
        /\ RTBound(Collision, vars, 0, 1) 
        /\ RTBound(DetectCollision, vars, 0, 1)
----
THEOREM Spec => TypeInv

======================================================