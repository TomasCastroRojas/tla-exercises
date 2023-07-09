---- MODULE crond2 ----
EXTENDS Naturals, FiniteSets

CONSTANTS MAXAPROGS, PROGS
ASSUME MAXAPROGS \in Nat /\ MAXAPROGS > 0

VARIABLES crontab, timers, now, aprocs
------
nullp == CHOOSE x: x \notin PROGS
TypeInv == /\ timers = [n \in Nat -> [t -> now, l -> 0, r -> "no"]]
           /\ IsFiniteSet(aprocs)
           /\ crontab \in [Nat -> [time:Nat,
                                   prog: PROGS \cup nullp,
                                   status: {"none", "set", "no", "yes", "run"}]]
           /\ now \in Nat
Ts == INSTANCE Timers
av == <<crontab, timers, aprocs, now>>
sv == <<crontab, timers, aprocs>>                       
------
Init == Ts!TInit

AddJob(t, p) == LET i = CHOOSE w: w \in Nat /\ crontab[w].status = "none"
                IN /\ p \in PROGS
                   /\ t > 0
                   /\ crontab' = [crontab EXCEPT 
                                 ![i] = [time -> t, prog -> p, status -> "set"]]
                   /\ UNCHANGED <<now, aprocs>>

SetJob(i) == /\ crontab[i].status = "set"
             /\ Ts!Set(i, crontab[i].time)
             /\ crontab' = [crontab EXCEPT 
                            ![i] = [time -> @.t, prog -> @.prog, status -> "no"]]
             /\ UNCHANGED <<now, aprocs>>

Start(i) == /\ crontab[i].status = "no"
            /\ Ts!Start(i)
            /\ crontab' = [crontab EXCEPT 
                          ![i] = [time -> @.time, prog -> @.prog, status -> "yes"]]
            /\ UNCHANGED <<aprocs, now>>

Sched(i) == /\ crontab[i].status = "yes"
            /\ Ts!Timeout(i)
            /\ crontab' = [crontab EXCEPT 
                          ![i] = [time -> @.time, prog -> @.prog, status -> "run"]]
            /\ UNCHANGED <<aprocs, now>>

Exec(i) == /\ crontab[i].status = "run"
           /\ Cardinality(aprocs) < MAXAPROGS
           /\ crontab' = [crontab EXCEPT 
                         ![i] = [time -> @.time, prog -> @.prog, status -> "no"]]
           /\ aprocs' = aprocs \cup {crontab[i].prog}
           /\ UNCHANGED <<timers, now>>

RemoveJob(i) == /\ \/ /\ crontab[i].status = "yes"
                      /\ Ts!Stop(i)
                      /\ UNCHANGED <<aprocs, now>>
                   \/ /\ crontab[i].status = "no"
                      /\ UNCHANGED <<aprocs, now, timers>>
                /\ crontab' = [crontab EXCEPT 
                              ![i] = [time -> 0, prog -> nullp, status -> "none"]]
-----
Next == \/ (\E t \in Nat, p \in PROGS: AddJob(t, p))
        \/ (\E i \in Nat: \/ Start(i) \/ Sched(i) \/ Exec(i) \/ RemoveJob(i) \/ SetJob(i)) 
Spec == Init /\ [][Next]_sv /\ (\A i \in Nat: WF_av(Start(i)) /\ SF_av(Exec(i)))
-----
THEOREM Spec => []TypeInv
====