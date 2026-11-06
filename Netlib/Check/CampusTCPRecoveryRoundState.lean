import Netlib.Check.CampusTCPRecoveryRoundAdmission
import Netlib.Check.CampusTCPRecoveryRoundSender
import Netlib.Check.CampusTCPRecoveryRoundReceiver
import Netlib.Check.CampusTCPRecoveryRoundSend
import Netlib.Check.CampusTCPRecoveryRoundDrop
import Netlib.Check.CampusTCPRecoveryRoundNetwork
import Netlib.Check.CampusTCPRecoveryRoundHistory
import Netlib.Check.CampusTCPRecoveryRoundRetire

/-!
# Current state of one actual recovery range

Sender flight, receiver release, and gateway observation are separate facts.
Clock and drop transitions retain their actual current report.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundState

noncomputable section

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRecoveryRoundPhaseBase (At Anchor)

namespace S
export CampusTCPRecoveryRoundSender (Flight)
end S
namespace R
export CampusTCPRecoveryRoundReceiver (Facts)
end R
namespace A
export CampusTCPRecoveryRoundAdmission (Observed RangeState)
end A

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request}

structure GatewayState (initial : Initial report complete request) (current : CampusTCPService.Before) where
  valid : current.tracker.Valid
  records : current.tracker.records = [⟨initial.entry, true⟩]
  admission : A.RangeState initial.session request.bytes current.admission

def GatewayState.ofInitial (initial : Initial report complete request) : GatewayState initial initial.beforeService :=
  ⟨initial.valid, initial.records, CampusTCPRecoveryRoundAdmission.initial_actualphase initial⟩

def GatewayState.frame (gateway : GatewayState initial before) (same : before = after) : GatewayState initial after :=
  same ▸ gateway

structure Live (initial : Initial report complete request) (current : Cut input complete)
    (sentAt retries : Nat) (released : Bool) where
  anchor : Anchor initial current
  sender : S.Flight initial sentAt (endpoint current.endpoints .client) retries
  receiver : R.Facts initial (endpoint current.endpoints .server) released
  gateway : GatewayState initial (beforeService input current.report.final .primary)
  history : CampusTCPRecoveryRoundHistory.History initial current released
  observed : released = true → Nonempty (A.Observed initial.session request.bytes
    (beforeService input current.report.final .primary).admission)

variable {current after : Cut input complete} {sentAt retries : Nat} {released : Bool}
variable {id : Nat} {actual : Step input}

theorem clock_time (frame : Endpoint.ClockFrame before next) (prepared : Endpoint.AckPrepared next) :
    Endpoint.AckTimeReady before next.now := by
  intro reaction selected
  have present : next.ackReaction = some reaction := frame.ackReaction.trans selected
  have guards := prepared.2
  rw [present] at guards
  exact guards.1

def Live.reindex (live : Live initial current sentAt retries released) (anchor : Anchor initial after)
    (client : endpoint after.endpoints .client = endpoint current.endpoints .client)
    (server : endpoint after.endpoints .server = endpoint current.endpoints .server)
    (operations : applicationSteps after.endpoints .server = applicationSteps current.endpoints .server)
    (gateway : beforeService input current.report.final .primary = beforeService input after.report.final .primary) :
    Live initial after sentAt retries released where
  anchor := anchor
  sender := by rw [client]; exact live.sender
  receiver := by rw [server]; exact live.receiver
  gateway := live.gateway.frame gateway
  history := live.history.same operations
  observed released := by
    obtain ⟨seen⟩ := live.observed released
    exact ⟨seen.frame (congrArg CampusTCPService.Before.admission gateway)⟩

def Live.frame (live : Live initial current sentAt retries released) (placement : At current after)
    (anchor : Anchor initial after) : Live initial after sentAt retries released where
  anchor := anchor
  sender := live.sender.tick (placement.frame.endpointFrame .client)
  receiver := live.receiver.clock (placement.frame.endpointFrame .server)
    (clock_time (placement.frame.endpointFrame .server) (anchor.guards .server).prepared)
  gateway := live.gateway.frame (placement.frame.beforeService .primary).symm
  history := live.history.clock placement
  observed released := by
    obtain ⟨seen⟩ := live.observed released
    exact ⟨seen.frame (congrArg CampusTCPService.Before.admission (placement.frame.beforeService .primary).symm)⟩

theorem Live.clock (live : Live initial current sentAt retries released) (actual : Step input)
    (before : actual.before = current.report.final) (actor : Actor) (millis : Nat)
    (event : actual.event = .advanceClock actor millis)
    (recovery : Recovery.State) (runtime : (endpoint current.endpoints actor).recovery = some recovery)
    (monotone : recovery.now ≤ millis)
    (timely : Endpoint.AckTimeReady (endpoint current.endpoints actor) millis) :
    ∃ move : CampusTCPRoundPhaseBase.Move current actual, At current move.after ∧
      Nonempty (Live initial move.after sentAt retries released) := by
  obtain ⟨move, placement, anchor⟩ := live.anchor.clock actual before actor millis event recovery runtime monotone timely
  exact ⟨move, placement, ⟨live.frame placement anchor⟩⟩

def Live.drop (live : Live initial current sentAt retries released)
    (appended : CampusTCPRecoveryRoundDrop.Append current id actual) :
    Live initial appended.move.after sentAt retries released :=
  live.reindex (appended.anchor live.anchor)
    (congrArg (fun endpoints => endpoint endpoints .client) appended.endpoints)
    (congrArg (fun endpoints => endpoint endpoints .server) appended.endpoints)
    (congrArg (fun endpoints => applicationSteps endpoints .server) appended.endpoints)
    (by rw [appended.move.final, appended.facts.beforeService])

def Live.assign (live : Live initial current sentAt retries released)
    (assignment : CampusTCPRecoveryRoundNetwork.AssignmentMove initial current index ingress produced actual) :
    Live initial assignment.move.after sentAt retries released :=
  live.reindex assignment.anchor
    (congrArg (fun endpoints => endpoint endpoints .client) assignment.endpoints)
    (congrArg (fun endpoints => endpoint endpoints .server) assignment.endpoints)
    (congrArg (fun endpoints => applicationSteps endpoints .server) assignment.endpoints)
    (assignment.gateway .primary).symm

def Live.ofSend (sent : CampusTCPRecoveryRoundSend.Sent initial native current quantum actual)
    (placement : At (Cut.ofPrepared initial.start) current) :
    Live initial sent.move.after (endpoint current.endpoints .client).now 0 false where
  anchor := sent.anchor
  sender := sent.flight
  receiver := (CampusTCPRecoveryRoundReceiver.initial_facts initial).clock sent.receiver
    (clock_time sent.receiver (sent.anchor.guards .server).prepared)
  gateway := (GatewayState.ofInitial initial).frame sent.gateway.symm
  history := ((CampusTCPRecoveryRoundHistory.initial_history initial).clock placement).client_local
    sent.move (.send request.bytes.length true) (by rw [sent.event]; exact .send _ _)
    sent.application.operation sent.application.recorded
  observed impossible := by cases impossible

structure Retired (initial : Initial report complete request) (current : Cut input complete) (retries : Nat) where
  anchor : Anchor initial current
  retirement : CampusTCPRecoveryRoundRetire.Retirement retries (endpoint current.endpoints .client)
  receiver : R.Facts initial (endpoint current.endpoints .server) true
  gateway : GatewayState initial (beforeService input current.report.final .primary)
  history : CampusTCPRecoveryRoundHistory.History initial current true
  bound : retries ≤ 2

def Live.retire (live : Live initial current sentAt retries true)
    (ack : CampusTCPRecoveryRoundRetire.AckMove initial current retries index served emission emitted actual)
    (actor : served.ticket.value.produced.actor = .server) : Retired initial ack.move.after retries where
  anchor := ack.anchor
  retirement := ack.retirement
  receiver := ack.receiver
  gateway := live.gateway.frame (ack.gateway .primary).symm
  history := live.history.same (by
    have operations := CampusTCPRoundPhaseHistory.Move.delivery_history ack.move ack.delivery.toDelivery ack.actualEq .server
    simpa only [actor, Actor.other, reduceCtorEq, ite_false, List.append_nil] using operations)
  bound := live.sender.bound

def Retired.frame (retired : Retired initial current retries) (placement : At current after)
    (anchor : Anchor initial after) : Retired initial after retries where
  anchor := anchor
  retirement := retired.retirement.clock (placement.frame.endpointFrame .client)
    (clock_time (placement.frame.endpointFrame .client) (anchor.guards .client).prepared)
  receiver := retired.receiver.clock (placement.frame.endpointFrame .server)
    (clock_time (placement.frame.endpointFrame .server) (anchor.guards .server).prepared)
  gateway := retired.gateway.frame (placement.frame.beforeService .primary).symm
  history := retired.history.clock placement
  bound := retired.bound

structure Completed (initial : Initial report complete request) (current : Cut input complete) (retries : Nat) where
  anchor : Anchor initial current
  reader : Step input
  member : reader ∈ current.report.steps
  event : reader.event = .read .server request.bytes.length
  bytes : reader.result.read = request.bytes
  operation : T.Step
  recorded : reader.result.application = some (.server, operation)
  history : CampusTCPRecoveryRoundHistory.Complete initial current operation
  retirement : CampusTCPRecoveryRoundRetire.Retirement retries (endpoint current.endpoints .client)
  gateway : GatewayState initial (beforeService input current.report.final .primary)
  empty : (endpoint current.endpoints .server).core.received = []
  held : (endpoint current.endpoints .server).receiveStore.held = []
  bound : retries ≤ 2

def Retired.read (retired : Retired initial current retries)
    (read : CampusTCPRecoveryRoundRetire.ReadMove initial current retries actual) : Completed initial read.move.after retries where
  anchor := read.anchor
  reader := actual
  member := read.move.member
  event := read.event
  bytes := read.returned
  operation := read.operation
  recorded := read.recorded
  history := retired.history.read read.move read.operation (by rw [read.event]; exact .read _)
    read.recorded read.localEvent read.localRead
  retirement := read.retirement
  gateway := retired.gateway.frame (read.gateway .primary).symm
  empty := read.empty
  held := read.held
  bound := retired.bound

def Completed.frame (done : Completed initial current retries) (placement : At current after)
    (anchor : Anchor initial after) : Completed initial after retries where
  anchor := anchor
  reader := done.reader
  member := placement.member done.member
  event := done.event
  bytes := done.bytes
  operation := done.operation
  recorded := done.recorded
  history := done.history.clock placement
  retirement := done.retirement.clock (placement.frame.endpointFrame .client)
    (clock_time (placement.frame.endpointFrame .client) (anchor.guards .client).prepared)
  gateway := done.gateway.frame (placement.frame.beforeService .primary).symm
  empty := by rw [(placement.frame.endpointFrame .server).core]; exact done.empty
  held := by rw [(placement.frame.endpointFrame .server).receiveStore]; exact done.held
  bound := done.bound

end

end Netlib.Check.CampusTCPRecoveryRoundState
