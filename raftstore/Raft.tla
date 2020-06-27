---- MODULE Raft ----
(**********************************************************************)
(* Copyright 2020 TiKV Project Authors. Licensed under Apache-2.0.    *)
(*                                                                    *)
(* Tla specifications for tikv/raft-rs.                               *)
(**********************************************************************)

EXTENDS Integers, FiniteSets
------------------------------------------------------------------------

CONSTANTS Value, InitVoters, InitTerm, InitIndex, MaxTerm

(* Struct HardState: term, vote, commit. *)

VARIABLES voters, (* Nodes that can vote. *)
          hardState, (* term, voteFor, commit. *)
          softState, (* leaderId, role. *)
          logs, (* Logs sequence of each node. *)
          leaderHistory,
          commitHistory

history == <<leaderHistory, commitHistory>>

Term == { t: t \in 0..MaxTerm }
Voter == Nat

NoValue == CHOOSE v: v \notin Value
None == CHOOSE v: v \notin Voter

Entry == [index: Nat, term: Term, data: Value \union { NoValue }]
HardState == [term: Term, voteFor: Voter \union { None }, commit: Nat]
Roles == { "Leader", "Follower", "Candidate" }
SoftState == [leader: Voter \union { None }, role: Roles]
LeaderLog == [leader: Voter, term: Term]

TypeInvarint == /\ voters \subseteq Voter
                /\ leaderHistory \subseteq LeaderLog
                /\ commitHistory \subseteq Entry
                /\ \A v \in voters: /\ hardState[v].term <= MaxTerm
                                    /\ hardState[v] \in HardState
                                    /\ softState[v] \in SoftState
                                    /\ logs[v] \subseteq Entry

Quorum == { S \in SUBSET voters: Cardinality(S) * 2 > Cardinality(voters) }

Init == /\ voters = InitVoters
        /\ hardState = [v \in InitVoters |-> [term |-> InitTerm, voteFor |-> None, commit |-> InitIndex]]
        /\ logs = [v \in InitVoters |-> {[index |-> InitIndex, term |-> InitTerm, data |-> NoValue]}]
        /\ softState = [v \in InitVoters |-> [leader |-> None, role |-> "Follower"]]
        /\ leaderHistory = {}
        /\ commitHistory = {[index |-> InitIndex, term |-> InitTerm, data |-> NoValue]}

LastLog(entries) == CHOOSE log \in entries: \A e \in entries: e.index <= log.index 

LastLogOf(v) == LastLog(logs[v])

Campaign(v) == /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.term = @ + 1, !.voteFor = v]]
               /\ softState' = [softState EXCEPT ![v] = [leader |-> None, role |-> "Candidate"]]

TickFollower(v) == IF hardState[v].term = MaxTerm
                   THEN UNCHANGED <<hardState, softState>>
                   ELSE Campaign(v)

TickCandidate(v) == /\ softState' = [softState EXCEPT ![v] = [@ EXCEPT !.role = "Follower"]]
                    /\ UNCHANGED <<hardState>>

TickLeader(v) == /\ softState' = [softState EXCEPT ![v] = [leader |-> None, role |-> "Follower"]]
                 /\ UNCHANGED <<hardState>>

Tick(v) == /\ CASE softState[v].role = "Follower" -> TickFollower(v)
              [] softState[v].role = "Candidate" -> TickCandidate(v)
              [] softState[v].role = "Leader" -> TickLeader(v)
           /\ UNCHANGED <<voters, logs, history>>

------------------------------------------------------------------------

Min(a, b) == IF a > b
             THEN b
             ELSE a

Max(a, b) == IF a < b
             THEN b
             ELSE a

FetchLeader(v) ==
    /\ \E l \in voters: /\ softState[l].role = "Leader"
                        /\ \/ /\ hardState[l].term > hardState[v].term
                              /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.term = hardState[l].term, !.voteFor = None]]
                           \/ /\ hardState[l].term = hardState[v].term
                              /\ softState[v].leader # l
                              /\ UNCHANGED <<hardState>>
                        /\ softState' = [softState EXCEPT ![v] = [role |-> "Follower", leader |-> l]]
    /\ UNCHANGED <<voters, logs, history>>

FetchLog(v) ==
    LET leader == softState[v].leader
    IN /\ leader # None
       /\ softState[leader].role = "Leader"
       /\ hardState[leader].term = hardState[v].term
       /\ LET lastLog == LastLogOf(v)
          IN IF lastLog \in logs[leader]
             THEN \/ \E fetchLastLog \in logs[leader]:
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
             ELSE /\ lastLog.index > hardState[v].commit
                  /\ logs' = [logs EXCEPT ![v] = @ \ { lastLog }]
                  /\ UNCHANGED <<hardState>>
       /\ UNCHANGED <<voters, softState, history>>

LogsUpToDate(v, c) == LET lastLog == LastLogOf(v)
                          lastCandidateLog == LastLogOf(c)
                      IN \/ lastCandidateLog.term > lastLog.term
                         \/ /\ lastCandidateLog.term = lastLog.term
                            /\ lastCandidateLog.index >= lastLog.index

Vote(v) ==
    /\ \E l \in voters: /\ softState[l].role = "Candidate"
                        /\ \/ hardState[l].term > hardState[v].term
                           \/ /\ hardState[l].term = hardState[v].term
                              /\ hardState[v].voteFor = None
                        /\ LogsUpToDate(v, l)
                        /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.voteFor = l, !.term = hardState[l].term]]
                        /\ softState' = [softState EXCEPT ![v] = [leader |-> None, role |-> "Follower"]]
    /\ UNCHANGED <<voters, logs, history>>

AppendLog(v, data) ==
    logs' = [logs EXCEPT ![v] = @ \union { [index |-> LastLogOf(v).index + 1, term |-> hardState[v].term, data |-> data] }]

ClaimLeadership(v) ==
    /\ \E q \in Quorum: \A l \in q: /\ hardState[l].term = hardState[v].term
                                    /\ hardState[l].voteFor = v
    /\ softState' = [softState EXCEPT ![v] = [leader |-> v, role |-> "Leader"]]
    /\ AppendLog(v, NoValue)
    /\ leaderHistory' = leaderHistory \union { [leader |-> v, term |-> hardState[v].term] }
    /\ UNCHANGED <<voters, hardState, commitHistory>>

Commit(v) ==
    /\ LastLogOf(v).index # hardState[v].commit
    /\ LET prs == [ l \in voters |-> LastLog(logs[v] \intersect logs[l]).index ]
           commitCandidate == { l \in voters: \E q \in Quorum: \A v2 \in q: prs[v2] >= prs[l] }
           committed == { prs[l]: l \in commitCandidate }
           commitIndex == CHOOSE c \in committed: \A o \in committed: c >= o
       IN /\ \E l \in logs[v]: /\ l.index = commitIndex
                               /\ l.term = hardState[v].term
          /\ hardState' = [hardState EXCEPT ![v] = [@ EXCEPT !.commit = commitIndex]]
          /\ commitHistory' = commitHistory \union { l \in logs[v]: l.index <= commitIndex }
          /\ UNCHANGED <<voters, softState, logs, leaderHistory>>

StepFollower(v) == \/ FetchLeader(v)
                   \/ FetchLog(v)
                   \/ Vote(v)

StepCandidate(v) == \/ FetchLeader(v)
                    \/ Vote(v)
                    \/ ClaimLeadership(v)

StepLeader(v) == \/ FetchLeader(v)
                 \/ Commit(v)
                 \/ Vote(v)

Step(v) == CASE softState[v].role = "Leader" -> StepLeader(v)
           [] softState[v].role = "Candidate" -> StepCandidate(v)
           [] softState[v].role = "Follower" -> StepFollower(v)

-----------------------------------------------------------------------

Next == \E v \in voters: \/ Step(v)
                         \/ Tick(v)

-----------------------------------------------------------------------

ElectionSafety ==
    \A h1, h2 \in leaderHistory: \/ h1.term # h2.term
                                 \/ h1.leader = h2.leader

CommittedLog(v) ==
    { l \in logs[v]: l.index <= hardState[v].commit }

LogSafety ==
    /\ \A l1, l2 \in commitHistory: \/ l1.index # l2.index
                                    \/ l1.term = l2.term
    /\ \A v \in voters: CommittedLog(v) = { l \in commitHistory: l.index <= hardState[v].commit }

========================================================================