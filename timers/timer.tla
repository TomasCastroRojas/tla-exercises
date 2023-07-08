------------- MODULE Timer ----------------------
EXTENDS Naturals, DK_RealTime, RealTime

VARIABLES time, running, limit
-------------------------------------------------
TTypeInv == time, limit \in Nat /\ running \in {"no", "yes"}
sv == <<limit, running, time>>
av == <<limit, running, time, now>>
-------------------------------------------------
TInit == limit = 0 /\ running = "no"

Set(l) == /\ l > 0
          /\ running = "no"
          /\ limit' = l
          /\ UNCHANGED <<time, now, running>>

Start == /\ running = "no"
         /\ limit > 0
         /\ time' = now
         /\ running' = "yes"
         /\ UNCHANGED <<now, limit>>

Timeout == /\ running = "yes"
           /\ now - time >= limit
           /\ running' = "no"
           /\ UNCHANGED <<time, now, limit>>

Stop == /\ running = "yes"
        /\ running' = "no"
        /\ UNCHANGED <<time, now, limit>>

TNext == Start \/ Stop \/ Timeout \/ (\E t \in Nat: Set(t))
TSpec == TInit /\ [][TNext]_sv /\ RTBound(Timeout, av, 0, 1)
-------------------------------------------------
THEOREM TSpec => []TTypeInv
=================================================




