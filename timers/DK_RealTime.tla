------------- MODULE DK_RealTime ---------------
EXTENDS Naturals

VARIABLE now
------------------------------------------------
RTTypeInv == now \in Nat

RTInit == now = 0

Tick == now' = now + 1

RTSpec == RTInit /\ [][Tick]_now /\ WF_now(Tick)
-----------------------------------------------
THEOREM RTSpec => []RTTypeInv
================================================