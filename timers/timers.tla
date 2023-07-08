------------- MODULE Timer ----------------------
EXTENDS Naturals, DK_RealTime, RealTime

VARIABLES timers
-------------------------------------------------
TTypeInv == timers \in [Nat -> [t, l: Nat, r: {"no", "yes"}]]
-------------------------------------------------
TInit == timers = [n \in Nat -> [t -> now, l -> 0, r -> "no"]]

Set(i, lim) == /\ lim > 0
               /\ timers[i].r = "no"
               /\ timers' = [timers EXCEPT ![i] = [t -> @.t, l -> lim, r -> @.r]]
               /\ UNCHANGED <<now>>

Start(i) == /\ timers[i].r = "no"
            /\ timers[i].l > 0
            /\ timers' = [timers EXCEPT ![i] = [t -> now, l -> @.l, r -> "yes"]]
            /\ UNCHANGED <<now>>    

Timeout(i) == /\ timers[i].r = "yes"
              /\ now - timers[i].t >= timers[i].l
              /\ timers' = [timers EXCEPT ![i] = [t -> @.t, l -> @.l, r -> "no"]]
              /\ UNCHANGED <<now>>
Stop(i) == /\ timers[i].r = "yes"
           /\ timers' = [timers EXCEPT ![i] = [t -> @.t, l -> @.l, r -> "no"]]
           /\ UNCHANGED <<now>>

TNext == \E i \in Nat: Start(i) \/ Stop(i) \/ Timeout(i) \/ (\E t \in Nat: Set(i, t))
TSpec == TInit /\ [][TNext]_timers /\ (\A i \in Nat: RTBound(Timeout(i), <<timers, now>>, 0, 1))
-------------------------------------------------
THEOREM TSpec => []TTypeInv
=================================================