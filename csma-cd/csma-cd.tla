------------------- MODULE System ------------------

EXTENDS Naturals, RealTime

CONSTANTS Data, L
ASSUME L \in Nat /\ L > 0

VARIABLES terminals

-----------------------------------------------------
NoData == CHOOSE d: d \notin Data

TypeInv == terminals \in [Nat -> [status: {"rdy", "transmiting", "waiting"},
                                  msg: Data \cup {NoData}]]

Bus == INSTANCE BusInterface
Ts == INSTANCE Timers

Init == terminals = [Nat -> [status -> "rdy", msg -> NoData]]
-----------------------------------------------------

Send(i) ==  /\ terminals[i].status = "rdy"
            /\ \E d \in data:
                /\ Bus!Free
                /\ Bus!Send(d)
                /\ Ts!Set(i, L)
                /\ Ts!Start(i)
                /\ terminals' = [terminals EXCEPT ![i].status = "transmiting", ![i].msg = d]
NotFree(i) == /\ terminals[i].status = "rdy"
              /\ \E d \in data:
                /\ \neg Bus!Free
                /\ LET t = CHOOSE v: v \in Nat /\ v > 0
                   IN /\ Ts!Set(i, t)
                      /\ Ts!Start(i)
                      /\ terminals' = [terminals EXCEPT ![i].status = "waiting", ![i].msg = d]

Wait(i) == /\ terminals[i].status = "waiting"
           /\ Ts!Timeout(i)
           /\ terminals' = [terminals EXCEPT ![i].status = "rdy"]

Deliver(i) == /\ terminals[i].status = "transmiting"
              /\ Ts!Timeout(i)
              /\ Bus!Deliver
              /\ terminals' = [terminals EXCEPT ![i].status = "rdy", ![i].msg = NoData]

Collision == /\ Bus!Collision
             /\ terminals' = [Nat -> [status -> "waiting", msg -> NoData]]
             /\ Ts!

======================================================