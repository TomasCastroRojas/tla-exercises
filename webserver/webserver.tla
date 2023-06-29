----------------------------- MODULE WebServer -----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Clients, LoginInfo, FileId, FileData, M, NoFile, Inactive
CONSTANTS AuthClient(_, _), Reply(_, _)

ASSUME M \in Nat /\ M > 0
ASSUME \A c, l : AuthClient(c, l) \in BOOLEAN
ASSUME \A c, m : Reply(c, m) \in BOOLEAN 

VARIABLES pendingReqs, connections, files, auths, attending

vars == << pendingReqs, connections, files, auths, attending >>

File == [data:FileData, access: SUBSET Clients]

Request ==  [type: {"GET"}, fid: FileId] \cup [type: {"AUTH"}, data: LoginInfo] \cup 
            [type: {"POST"}, f: File, fid: FileId]

Msg == {"Succesful login", "Invalid Login", "File Not Found", "Succesful file upload", "File stored"}

Respond == MSG \cup File

NoFile == CHOOSE f: f \notin File

Inactive == CHOOSE x: x \notin [c: Clients, r: Request]
---------------------------------------------------------------------------

TypeInv == /\ connections \subseteq Clients
           /\ auths \subseteq Clients
           /\ IsFiniteSet(connections)
           /\ pendingReqs \in Seq([c: Clients, req: Request])
           /\ files \in [fid \in FileId |-> File \cup NoFile]
           /\ attending \in [c: Clients, r: Request] \cup Inactive

Init == /\ pendingReqs = << >>
        /\ connections = {}
        /\ auths = {}
        /\ files = [fid \in FileId |-> NoFile]
        /\ attending = Inactive

Connect(c) == /\ Cardinality(connections) < M
              /\ connections' = connections \cup c
              /\ UNCHANGED <<pendingReqs, files, auths, attending>>

Req(c) == /\ c \in connections
          /\ \E r \in Request:
                /\ pendingReqs' = pendingReqs \cup <<c, r>>
                /\ connections' = connections \ c
          /\ UNCHANGED << files, auths, attending >>

SelectNextReq == /\ attending = Inactive
                 /\ pendingReqs /= << >>
                 /\ attending' = Head(pendingReqs)
                 /\ pendingReqs' = Tail(pendingReqs)
                 /\ UNCHANGED <<connections, files, auth>>

GetFile ==     /\ attending /= Inactive
               /\ attending.req.type = "GET"
               /\ files[attending.req.fid] /= NoFile
               /\ files[attending.req.fid].access = {}
               /\ Reply(attending.c, files[attending.req.fid].data)
               /\ attending' = Inactive
               /\ UNCHANGED << connections, pendingReqs, auth, files >>

GetFileRestricted ==/\ attending /= Inactive
                    /\ attending.req.type = "GET"
                    /\ files[attending.req.fid] /= NoFile
                    /\ files[attending.req.fid].access /= {}
                    /\ attending.c \in auths \cap files[attending.req.fid].access
                    /\ Reply(attending.c, files[attending.req.fid].data)
                    /\ attending' = Inactive
                    /\ UNCHANGED << connections, pendingReqs, auth, files >>

GetFileNotAuth == /\ attending /= Inactive
                  /\ attending.req.type = "GET"
                  /\ files[attending.req.fid] /= NoFile
                  /\ files[attending.req.fid].access /= {}
                  /\ attending.c \notin auths \cap files[attending.req.fid].access
                  /\ Reply(attending.c, "Unauthorized Access")
                  /\ attending' = Inactive
                  /\ UNCHANGED << connections, pendingReqs, auth, files >>

GetFileError == /\ attending /= Inactive
                /\ attending.req.type = "GET"
                /\ files[attending.req.fid] = NoFile
                /\ Reply(attending.c, "File not founded")
                /\ attending' = Inactive
                /\ UNCHANGED << connections, pendingReqs, auth, files >>

Get == \/ GetFileFree
       \/ GetFileRestricted
       \/ GetFileNotAuth
       \/ GetFileError

AuthOk == /\ attending /= Inactive
          /\ attending.req.type = "AUTH"
          /\ AuthClient(attending.c, attending.req.data)
          /\ auths' = auths \cup attending.c
          /\ Reply(attending.c, "Succesful login")
          /\ attending' = Inactive
          /\ UNCHANGED << files, connections, pendingReqs >>

AuthError == /\ attending /= Inactive
             /\ attending.req.type = "AUTH"
             /\ \lnot AuthClient(attending.c, attending.req.data)
             /\ Reply(attending.c, "Invalid Login")
             /\ attending' = Inactive
             /\ UNCHANGED << auth, files, connections, pendingReqs >>

Auth == \/ AuthOk
        \/ AuthError

PostOk == /\ attending /= Inactive
          /\ attending.req.type = "POST"
          /\ files[attending.req.fid] = NoFile
          /\ files' = [files EXCEPT ![attending.req.fid] = attending.req.f]
          /\ Reply(attending.c, "Successful upload")
          /\ attending' = Inactive
          /\ UNCHANGED << connections, auths, pendingReqs >>

PostError == /\ attending /= Inactive
             /\ attending.req.type = "POST"
             /\ files[attending.req.fid] /= NoFile
             /\ Reply(attending.c, "File already stored")
             /\ attending' = Inactive
             /\ UNCHANGED << files, connections, auths, pendingReqs >>

Post == \/ PostOk
        \/ PostError

Next == \/ \E c \in Clients: Connect(c)
        \/ \E c \in Clients: Req(c)
        \/ SelectNextReq
        \/ Get
        \/ Auth
        \/ Post

Spec == Init /\ [][Next]_vars /\ WF_vars(SelectNextReq \/ Get \/ Auth \/ Post)
----------------------------------------------------------------------------
THEOREM Spec => TypeInv
=============================================================================
