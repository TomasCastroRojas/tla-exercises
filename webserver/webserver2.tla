----------------------------- MODULE WebServer -----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Clients, LoginInfo, FileId, FileData, M, NoFile, Inactive
CONSTANTS AuthClient(_, _), Reply(_, _)

ASSUME M \in Nat /\ M > 0
ASSUME \A c, l : AuthClient(c, l) \in BOOLEAN
ASSUME \A c, m : Reply(c, m) \in BOOLEAN 

VARIABLES buffer, connections, files, auths, control

vars == << buffer, connections, files, auths >>

File == [data:FileData, access: SUBSET Clients]

Request ==  [type: {"GET"}, fid: FileId] \cup [type: {"AUTH"}, data: LoginInfo] \cup 
            [type: {"POST"}, f: File, fid: FileId]

Msg == {"Succesful login", "Invalid Login", "File Not Found",
        "Succesful file upload", "File stored"}

Respond == MSG \cup File

NoFile == CHOOSE f: f \notin File

Inactive == CHOOSE x: x \notin Request \cup Respond
---------------------------------------------------------------------------

TypeInv == /\ connections \subseteq Clients
           /\ auths \subseteq Clients
           /\ IsFiniteSet(connections)
           /\ buffer \in [c \in Clients |-> Request \cup Respond \cup {Inactive}]
           /\ files \in [fid \in FileId |-> File \cup {NoFile}]
           /\ control \in [c \in Clients |-> {"rdy", "working", "done"}]

Init == /\ buffer = [c \in Clients |-> Inactive]
        /\ control = [c \in Clients |-> "rdy"]
        /\ connections = {}
        /\ auths = {}
        /\ files = [fid \in FileId |-> NoFile]

Connect(c) == /\ Cardinality(connections) < M
              /\ control[c] = "rdy"
              /\ connections' = connections \cup {c}
              /\ UNCHANGED <<buffer, files, auths, control>>

Req(c) == /\ c \in connections
          /\ \E req \in Request:
                /\ buffer' = [buffer EXCEPT ![c] = req]
                /\ control' = [control EXCEPT  ![c] = "working"]
                /\ connections' = connections \ c
          /\ UNCHANGED << files, auths >>

DoGet(c) == 
    LET req = buffer[c]
    IN  /\ control[c] = "working"
        /\ req.type = "GET"
        /\ buffer' = [buffer EXCEPT ![c] = IF files[req.fid] = NoFile
                                            THEN "File not found"
                                            ELSE IF files[req.fid].access = {}
                                                THEN files[req.fid]
                                                ELSE IF c \in auths \cap files[req.fid].access
                                                    THEN files[req.fid]
                                                    ELSE "Unauthorized access"]
        /\ control' = [control EXCEPT ![c] = "done"]
        /\ UNCHANGED << files, auths, connections>

DoAuth(c) ==
    LET req = buffer[c]
    IN /\ control[c] = "working"
       /\ req.type = "AUTH"
       /\ buffer' = [buffer EXCEPT ![c] = IF AuthClient(c, req.data)
                                          THEN "Succesful login"
                                          ELSE "Invalid login"]
       /\ auths' = IF AuthClient(c, req.data)
                   THEN auths \cup {c}
                   ELSE auths
       /\ control' = [control EXCEPT ![c] = "done"]
       /\ UNCHANGED << files, connections >>

DoPost(c) ==
    LET req = buffer[c]
    IN /\ control[c] = "working"
       /\ req.type = "POST"
       /\ buffer' = [buffer EXCEPT ![c] = IF files[req.fid] = NoFile
                                          THEN "Succesful upload"
                                          ELSE "File already stored"]
       /\ files' = [files EXCEPT ![req.fid] = IF @ = NoFile
                                              THEN req.f
                                              ELSE @]
       /\ control' = [control EXCEPT ![c] = "done"]
       /\ UNCHANGED << auths, connections >>

Rsp(c) == /\ control[c] = "done"
          /\ Reply(c, buffer[c])
          /\ buffer' = [buffer EXCEPT ![c] = Inactive]
          /\ control' = [control EXCEPT ![c] = "rdy"]
          /\ UNCHANGED << files, auth, connections >>

Next == \E c \in Clients: Connect(c) \/ Req(c) \/ DoGet(c)
                          \/ DoPost(c) \/ DoAuth(c) \/ Rsp(c)

Fairness == 
    \A c \in Clients : WF_vars(DoGet(c) \/ DoPost(c) \/ DoAuth(c) \/ Rsp(c))

Spec == Init /\ [][Next]_vars /\ Fairness
----------------------------------------------------------------------------
THEOREM Spec => []TypeInv
=============================================================================
