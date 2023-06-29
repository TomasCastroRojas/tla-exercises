------------------------------- MODULE Alarma -------------------------------

EXTENDS Naturals, Sequences
CONSTANTS SecCode, Sector, Sensor
ASSUME SecCode \in Seq(0..9)
VARIABLES keyPresses, armed, bocina

KeypadButton == {n : n \in 0..9} \cup Sector

TypeInv == /\ keyPresses \in Seq(KeypadButton)
           /\ armed \in [Sector -> BOOLEAN]
           /\ bocina \in BOOLEAN

Init == /\ keyPresses = <<>>
        /\ armed = [s \in Sector |-> FALSE]
        /\ bocina = FALSE

ToggleAll == /\ armed' = [s \in Sector |-> ~\E x \in Sector : armed[x]]
             /\ UNCHANGED bocina

Deactivate == /\ bocina' = FALSE
              /\ UNCHANGED armed

SecCodeEntered == /\ keyPresses = SecCode
                  /\ IF bocina THEN Deactivate ELSE ToggleAll

SectorSecCodeEntered(s) == /\ keyPresses = <<s>> \o SecCode
                           /\ armed' = [armed EXCEPT ![s] = ~@[s]]
                           /\ UNCHANGED bocina

RespondToCommand(cmd) == \/ /\ cmd = SecCode
                            /\ SecCodeEntered
                         \/ \E s \in Sector :
                             /\ cmd = <<s>> \o SecCode
                             /\ SectorSecCodeEntered(s)

PossibleCommands == {<<s>> \o SecCode : s \in Sector} \cup { SecCode }
KeyPress(i) == IF Append(keyPresses, i) \in PossibleCommands
               THEN /\ keyPresses' = <<>>
                    /\ RespondToCommand(Append(keyPresses, i))
               ELSE /\ keyPresses' = Append(keyPresses, i)
                    /\ UNCHANGED <<armed, bocina>>

Signal(m, s) == /\ bocina' = armed[s]
                /\ UNCHANGED <<keyPresses, armed>>

Next == \/ \E i \in KeypadButton : KeyPress(i)
        \/ \E m \in Sensor, s \in Sector : Signal(m, s)

Spec == Init /\ [][Next]_<<keyPresses, armed, bocina>>

THEOREM Spec => []TypeInv

=============================================================================
\* Modification History
\* Last modified Sun Feb 26 22:01:36 ART 2023 by lautarog
\* Created Sun Feb 26 21:09:14 ART 2023 by lautarog
