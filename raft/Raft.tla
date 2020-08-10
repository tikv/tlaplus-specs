---------------------------- MODULE Raft -------------------------------
(**********************************************************************)
(* Copyright 2020 TiKV Project Authors. Licensed under Apache-2.0.    *)
(*                                                                    *)
(* Tla specifications for tikv/raft-rs.                               *)
(*                                                                    *)
(* Different from raft-rs actual implements, the spec omits ticks and *)
(* messages. Instead, it makes nodes to fetch logs and change between *)
(* roles randomly. The good side is a lot of states are reduced.      *)
(* Unsynchronous tick and heartbeat lost are still simulated as roles *)
(* are changed randomly. Append lost are simulated limitedly by       *)
(* randomly pause fetching logs. Out of order messages are not taken  *)
(* into account however.                                              *)
(**********************************************************************)

EXTENDS Integers, FiniteSets
------------------------------------------------------------------------

CONSTANTS Value, InitVoters, InitTerm, InitIndex, MaxTerm

(* Struct HardState: term, vote, commit. *)

VARIABLES voters, (* Nodes that can vote. *)
          hardState, (* term, voteFor, commit. *)
          softState, (* leaderId, role. *)
          logs, (* Logs sequence of each node. *)
          leaderHistory, (* A history of all leaders. *)
          commitHistory (* A history of all committed logs. *)

history == <<leaderHistory, commitHistory>>
vars == <<voters, hardState, softState, logs, history>>

Term == { t: t \in 0..MaxTerm }
Voter == Nat

NoValue == CHOOSE v: v \notin Value
None == CHOOSE v: v \notin Voter

Roles == { "Leader", "Follower", "Candidate" }
ConfChange == [type: {"Add", "Remove"}, id: Voter]
Entry == [index: Nat, term: Term, data: Value \union { NoValue } \union ConfChange]
HardState == [term: Term, voteFor: Voter \union { None }, commit: Nat]
SoftState == [leader: Voter \union { None }, role: Roles]
LeaderHistoryEntry == [leader: Voter, term: Term]

(* Make sure all varint match types. *)
TypeInvarint == /\ voters \subseteq Voter
                /\ leaderHistory \subseteq LeaderHistoryEntry
                /\ commitHistory \subseteq Entry
                /\ \A v \in voters: /\ hardState[v] \in HardState
                                    /\ softState[v] \in SoftState
                                    /\ logs[v] \subseteq Entry

Init == /\ voters = InitVoters
        /\ hardState = [v \in InitVoters |-> [term |-> InitTerm, voteFor |-> None, commit |-> InitIndex]]
        /\ softState = [v \in InitVoters |-> [leader |-> None, role |-> "Follower"]]
        /\ logs = [v \in InitVoters |-> {[index |-> InitIndex, term |-> InitTerm, data |-> NoValue]}]
        /\ leaderHistory = {}
        /\ commitHistory = {[index |-> InitIndex, term |-> InitTerm, data |-> NoValue]}

(* Gets the last log from given entries. *)
LastLog(entries) == CHOOSE log \in entries: \A e \in entries: e.index <= log.index 

(* Gets the last log of given node. *)
LastLogOf(v) == LastLog(logs[v])

Campaign(v) == /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.term = @ + 1, !.voteFor = v]]
               /\ softState' = [softState EXCEPT ![v] = [leader |-> None, role |-> "Candidate"]]

(* When follower ticks, it either do nothing or starts campaign. *)
(* We skip blindly ticking to reduce useless states.             *)
TickFollower(v) == IF hardState[v].term = MaxTerm
                   THEN (* Don't campain when reach MaxTerm, otherwise the possible states are infinite. *)
                        UNCHANGED <<hardState, softState>>
                   ELSE Campaign(v)

(* When candidate ticks, it either do nothing or conclude campaign *)
(* failure and step down as follower.                              *)
TickCandidate(v) == /\ softState' = [softState EXCEPT ![v] = [@ EXCEPT !.role = "Follower"]]
                    /\ UNCHANGED <<hardState>>

(* When leader ticks, it should broadcast heartbeats. We omit the message *)
(* queue to make less states, so in theory it should do nothing. Here we  *)
(* make it step down to simulate the effect of check quorum.              *)
TickLeader(v) == /\ softState' = [softState EXCEPT ![v] = [leader |-> None, role |-> "Follower"]]
                 /\ UNCHANGED <<hardState>>

(* Simuates state machine ticks.                                          *)
Tick(v) == /\ CASE softState[v].role = "Follower" -> TickFollower(v)
              [] softState[v].role = "Candidate" -> TickCandidate(v)
              [] softState[v].role = "Leader" -> TickLeader(v)
           /\ UNCHANGED <<voters, logs, history>>

------------------------------------------------------------------------

(* Help operators. *)
Min(a, b) == IF a > b
             THEN b
             ELSE a

Max(a, b) == IF a < b
             THEN b
             ELSE a

------------------------------------------------------------------------

(* Checks if there is any new leader. It's the same as handling MsgHeartbeat. *)
CheckLeader(v) ==
    /\ \E l \in voters: /\ softState[l].role = "Leader"
                        /\ \/ /\ hardState[l].term > hardState[v].term
                              /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.term = hardState[l].term, !.voteFor = None]]
                           \/ /\ hardState[l].term = hardState[v].term
                              /\ softState[v].leader # l
                              /\ UNCHANGED <<hardState>>
                        /\ softState' = [softState EXCEPT ![v] = [role |-> "Follower", leader |-> l]]
    /\ UNCHANGED <<voters, logs, history>>

(* Fetches logs from leader. It's the same as handling MsgAppend.        *)
FetchLog(v) ==
    LET leader == softState[v].leader
    IN /\ leader # None
       /\ softState[leader].role = "Leader"
       /\ hardState[leader].term = hardState[v].term
       /\ LET lastLog == LastLogOf(v)
          IN IF lastLog \in logs[leader]
             THEN (* Leader's log matches Follower's. Fetch logs or commit index randomly. *)
                  \/ \E fetchLastLog \in logs[leader]:
                        /\ fetchLastLog.index > lastLog.index
                        /\ logs' = [logs EXCEPT ![v] = @ \union {
                                      l \in logs[leader]: /\ l.index > lastLog.index
                                                          /\ l.index <= fetchLastLog.index
                                   }]
                        /\ \/ /\ hardState[v].commit # hardState[leader].commit
                              /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.commit = Min(fetchLastLog.index, hardState[leader].commit)]]
                           \/ /\ hardState[v].commit = hardState[leader].commit
                              /\ UNCHANGED <<hardState>>
                  \/ /\ hardState[v].commit # lastLog.index
                     /\ hardState[v].commit < hardState[leader].commit
                     /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.commit = Min(hardState[leader].commit, lastLog.index)]]
                     /\ UNCHANGED <<logs>>
             ELSE (* Overwrites mismatch logs. *)
                  /\ lastLog.index > hardState[v].commit
                  /\ logs' = [logs EXCEPT ![v] = @ \ { lastLog }]
                  /\ UNCHANGED <<hardState>>
       /\ UNCHANGED <<voters, softState, history>>

(* Checks if logs of c are up to date. *)
LogsUpToDate(v, c) == LET lastLog == LastLogOf(v)
                          candidateLastLog == LastLogOf(c)
                      IN \/ candidateLastLog.term > lastLog.term
                         \/ /\ candidateLastLog.term = lastLog.term
                            /\ candidateLastLog.index >= lastLog.index

(* Votes for any suitable cnadidate. It's the same as handling MsgRequestVote. *)
Vote(v) ==
    /\ \E l \in voters: /\ softState[l].role = "Candidate"
                        /\ \/ hardState[l].term > hardState[v].term
                           \/ /\ hardState[l].term = hardState[v].term
                              /\ hardState[v].voteFor = None
                        /\ LogsUpToDate(v, l)
                        /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.voteFor = l, !.term = hardState[l].term]]
                        /\ softState' = [softState EXCEPT ![v] = [leader |-> None, role |-> "Follower"]]
    /\ UNCHANGED <<voters, logs, history>>

(* Proposes data as a log entry. *)
AppendLog(v, data) ==
    logs' = [logs EXCEPT ![v] = @ \union { [index |-> LastLogOf(v).index + 1, term |-> hardState[v].term, data |-> data] }]

(* Becomes leader if possible. It's the same as handling RequestVoteResponse. *)
ClaimLeadership(v) ==
    /\ LET met == { l \in voters: /\ hardState[l].term = hardState[v].term
                                  /\ hardState[l].voteFor = v }
       IN Cardinality(met) * 2 > Cardinality(voters)
    /\ softState' = [softState EXCEPT ![v] = [leader |-> v, role |-> "Leader"]]
    /\ AppendLog(v, NoValue)
    /\ leaderHistory' = leaderHistory \union { [leader |-> v, term |-> hardState[v].term] }
    /\ UNCHANGED <<voters, hardState, commitHistory>>

(* Checks if it's possible to commit logs. It's the same as handling MsgAppendResponse. *)
Commit(v) ==
    /\ LastLogOf(v).index # hardState[v].commit
    /\ LET quorumLogs == { l \in logs[v]: /\ l.index > hardState[v].commit
                                          /\ LET met == { o \in voters: l \in logs[o] }
                                             IN Cardinality(met) * 2 > Cardinality(voters)}
       IN /\ quorumLogs # {}
          /\ LET quorumLastLog == LastLog(quorumLogs)
             IN /\ quorumLastLog.term = hardState[v].term
                /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.commit = quorumLastLog.index]]
                /\ commitHistory' = commitHistory \union { l \in logs[v]: /\ l.index <= quorumLastLog.index
                                                                          /\ l.index > hardState[v].commit }
                /\ UNCHANGED <<voters, softState, logs, leaderHistory>>

StepFollower(v) == \/ CheckLeader(v)
                   \/ FetchLog(v)
                   \/ Vote(v)

StepCandidate(v) == \/ CheckLeader(v)
                    \/ Vote(v)
                    \/ ClaimLeadership(v)

StepLeader(v) == \/ CheckLeader(v)
                 \/ Commit(v)
                 \/ Vote(v)

Step(v) == CASE softState[v].role = "Leader" -> StepLeader(v)
           [] softState[v].role = "Candidate" -> StepCandidate(v)
           [] softState[v].role = "Follower" -> StepFollower(v)

-----------------------------------------------------------------------

Next == \E v \in voters: \/ Step(v)
                         \/ Tick(v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------

(* Election Safety: at most one leader can be elected in a given term. *)
ElectionSafety ==
    \A h1, h2 \in leaderHistory: \/ h1.term # h2.term
                                 \/ h1.leader = h2.leader

CommittedLog(v) ==
    { l \in logs[v]: l.index <= hardState[v].commit }

(* State Machine Safety: if a server has applied a log entry  *)
(* at a given index to its state machine, no other server     *)
(* will ever apply a different log entry for the same index.  *)
StateMachineSafety ==
    (* Log Matching: if two logs contain an entry with the same    *)
    (* index and term, then the logs are identical in all entries  *)
    (* up through the given index.                                 *)
    /\ \A l1, l2 \in commitHistory: \/ l1.index # l2.index
                                    \/ l1 = l2
    (* Leader Completeness: if a log entry is committed in a given *)
    (* term, then that entry will be present in the logs of the    *)
    (* leaders for all higher-numbered terms.                      *)
    /\ \A v \in voters: \/ /\ softState[v].role = "Leader"
                           /\ CommittedLog(v) = { l \in commitHistory: l.index <= hardState[v].commit }
                        \/ softState[v].role # "Leader"

Safety == TypeInvarint /\ ElectionSafety /\ StateMachineSafety

------------------------------------------------------------------------

THEOREM Spec => []Safety

========================================================================
