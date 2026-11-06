import Netlib.Check.CampusTCPTwoProgressPhaseBase
import Netlib.Check.CampusTCPTwoProgressPathsAssign
import Netlib.Check.CampusTCPTwoProgressPathsService
import Netlib.Check.CampusTCPTwoProgressPathsAckService
import Netlib.Check.CampusTCPTwoProgressGatewayRanges

namespace Netlib.Check.CampusTCPTwoProgressPhaseNetwork

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core Arrived)
open CampusTCPTwoProgressPathsReady (rangeAt)
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressServiceState (processingAt processingAt_admission processingAt_attachment)

namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace M
export CampusTCPTwoProgressMonitor (Monitor observe Allowed observeOrdinary)
end M
namespace P
export CampusTCPTwoProgressPaths (Ingress DataIngress AckIngress DataTicket AckTicket)
end P
namespace A
export CampusTCPTwoProgressPathsAssign (Assigned DataAssigned AckAssigned)
end A
namespace D
export CampusTCPTwoProgressPathsService (DataServed)
end D
namespace K
export CampusTCPTwoProgressPathsAckService (AckServed)
end K

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current after : Cut input complete} {sender actor : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {part : S.Part} {lane : CampusTCPTwoProgressMonitor.Lane} {count : Nat} {actual : Step input}
variable {fields : Produced input.active input.passive → Prop}

structure Advance (core : Core initial native quantum allowance current monitor sent received)
    (actual : Step input) (move : Move current actual) where
  nextCore : Core initial native quantum allowance move.after
    (M.observe (config initial native quantum allowance) monitor actual) sent received
  book : nextCore.losses.book = core.losses.book
  ordinary : M.observe (config initial native quantum allowance) monitor actual =
    M.observeOrdinary (config initial native quantum allowance) monitor actual

private def finish (core : Core initial native quantum allowance current monitor sent received)
    (move : Move current actual) (endpoints : move.after.endpoints = current.endpoints)
    (jointBefore : CampusTCPTwoProgressState.Live initial move.after sent monitor.retries received)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint move.after.endpoints sender) sent)
    (covered : ∀ role, Arrived received role → (rangeAt jointBefore.gatewayState role).isSome = true)
    (acknowledged : (jointBefore.gatewayState.gateway.session.lane sender.direction).acknowledged ≤
      initial.geometry.«prefix» + (received.bytes lower upper).length)
    (peerSettled : CampusTCPTwoProgressGatewayPeerSettled.Settled jointBefore.gatewayState)
    (peerWindow : CampusTCPTwoProgressGatewayPeerWindow.Reserved jointBefore.gatewayState)
    (action : CampusTCPRoundMonitor.Action) (event : actual.event = action.event)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor action.event) :
    Advance core actual move := by
  let cfg := config initial native quantum allowance
  have allowedActual : M.Allowed cfg actual.before monitor actual.event := by
    rw [move.beforeEq, event]
    exact allowed
  have observed := CampusTCPTwoProgressMonitorFacts.observe_action cfg monitor actual move.supported move.passed allowedActual action event
  have counters : CampusTCPTwoProgressMonitorFacts.counters (M.observe cfg monitor actual) =
      CampusTCPTwoProgressMonitorFacts.counters monitor := by
    rw [observed]
    exact CampusTCPTwoProgressMonitorFacts.ordinary_counters cfg monitor actual
  have retries := congrArg Prod.fst counters
  have drops := congrArg Prod.snd counters
  change (M.observe cfg monitor actual).retries = monitor.retries at retries
  change (M.observe cfg monitor actual).drops = monitor.drops at drops
  let updated := M.observe cfg monitor actual
  let joint : CampusTCPTwoProgressState.Live initial move.after sent updated.retries received := {
    anchor := jointBefore.anchor
    senderFlight := by rw [retries]; exact jointBefore.senderFlight
    receiverFacts := jointBefore.receiverFacts
    gatewayState := jointBefore.gatewayState
    gatewayWindow := jointBefore.gatewayWindow
    history := jointBefore.history }
  have sameRuntime : joint.senderFlight.recovery = core.live.senderFlight.recovery := by
    have slots := congrArg (fun value => (endpoint value sender).recovery) endpoints
    exact Option.some.inj (joint.senderFlight.runtime.symm.trans (slots.trans core.live.senderFlight.runtime))
  exact {
    nextCore := {
      live := joint
      senderWindow := space
      originals := core.originals.retain_steps move.retained
      originalTimes := core.originalTimes
      writer := core.writer.same (by rw [endpoints])
      losses := core.losses.append move
        (by cases action <;> simp only [CampusTCPTwoProgressLossHistory.isDrop, event, CampusTCPRoundMonitor.Action.event])
        (by cases action <;> simp only [CampusTCPTwoProgressLossHistory.isTimeout, event, CampusTCPRoundMonitor.Action.event]) drops retries
      lossBound := by rw [drops]; exact core.lossBound
      retired := core.retired
      gatewayAck := acknowledged
      peerSettled, peerWindow
      covered
      duplicates := by rw [sameRuntime]; exact core.duplicates
      deadline := by rw [sameRuntime]; exact core.deadline
      estimatorBeforeRetire := by rw [sameRuntime]; exact core.estimatorBeforeRetire
      rtoBeforeRetire := by rw [sameRuntime, retries]; exact core.rtoBeforeRetire
      rtoPending := by rw [sameRuntime, retries]; exact core.rtoPending
      emptyDuplicate := fun empty => sameRuntime.symm ▸ core.emptyDuplicate empty }
    book := rfl
    ordinary := observed }

private theorem session_same (before : CampusTCPTwoProgressGatewayState.View initial current)
    (next : CampusTCPTwoProgressGatewayState.View initial after)
    (same : beforeService input after.report.final gateway = beforeService input current.report.final gateway) :
    next.gateway.session = before.gateway.session := by
  have phase := next.gateway.phase
  rw [same, before.gateway.phase] at phase
  exact (Admission.Phase.data.inj phase).symm

private def assignment_advance (core : Core initial native quantum allowance current monitor sent received)
    (path : P.Ingress current actor fields) (assigned : A.Assigned core.live path native actual)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor
      (.assign path.output.index (native.ingress path.output.produced.actor))) :
    Advance core actual assigned.value.move := by
  have ranges := core.live.gatewayState.ranges_same assigned.next.gatewayState (assigned.value.serviceFrame gateway)
  have covered : ∀ role, Arrived received role → (rangeAt assigned.next.gatewayState role).isSome = true := by
    intro role arrived
    have old := core.covered role arrived
    cases role with
    | lower => change assigned.next.gatewayState.ranges.lowerRun.isSome = true; rw [ranges.1]; exact old
    | upper => change assigned.next.gatewayState.ranges.upperRun.isSome = true; rw [ranges.2]; exact old
  have acknowledged : (assigned.next.gatewayState.gateway.session.lane sender.direction).acknowledged ≤
      initial.geometry.«prefix» + (received.bytes lower upper).length := by
    rw [session_same core.live.gatewayState assigned.next.gatewayState (assigned.value.serviceFrame gateway)]
    exact core.gatewayAck
  have peerSettled := CampusTCPTwoProgressGatewayPeerSettled.same_service core.live.gatewayState assigned.next.gatewayState
    core.peerSettled (assigned.value.serviceFrame gateway)
  have peerWindow : CampusTCPTwoProgressGatewayPeerWindow.Reserved assigned.next.gatewayState := by
    change CampusTCPTwoProgressGatewayPeerWindow.floor initial ≤ _
    rw [session_same core.live.gatewayState assigned.next.gatewayState (assigned.value.serviceFrame gateway)]
    exact core.peerWindow
  exact finish core assigned.value.move assigned.value.endpoints assigned.next assigned.reserve covered acknowledged
    peerSettled peerWindow
    (.assign path.output.index (native.ingress path.output.produced.actor)) assigned.value.facts.event allowed

private theorem data_acknowledged (core : Core initial native quantum allowance current monitor sent received)
    (path : P.DataTicket initial native current part lane) (served : D.DataServed core.live path actual) :
    (served.next.gatewayState.gateway.session.lane sender.direction).acknowledged =
      (core.live.gatewayState.gateway.session.lane sender.direction).acknowledged := by
  obtain ⟨processing, present, _, _, attached, _⟩ := served.value.facts.processing
  have previous : served.served.before = beforeService input current.report.final gateway := by
    rw [served.value.facts.current, served.value.selected]
  let selected := processingAt processing previous
  have direction : selected.prepared.attachment.direction = sender.direction := by
    rw [processingAt_attachment]
    exact attached
  have phase : selected.admitted.state.phase = .data served.next.gatewayState.gateway.session := by
    have phase := served.next.gatewayState.gateway.phase
    rw [served.value.after_before processing present] at phase
    change processing.nextAdmission.phase = .data served.next.gatewayState.gateway.session at phase
    rw [← processingAt_admission processing previous,
      CampusTCPRoundAdmission.Processing.committed_data selected core.live.gatewayState.gateway.session core.live.gatewayState.gateway.phase] at phase
    exact phase
  have frame := (CampusTCPTwoProgressGatewayWindow.result_window_fields selected.admitted core.live.gatewayState.gateway.phase phase).1
  simpa only [direction, CampusTCPTwoProgressGatewayState.sender_lane] using frame

structure DataAssigned (core : Core initial native quantum allowance current monitor sent received)
    (path : P.DataIngress initial current part lane) (actual : Step input) where
  value : A.DataAssigned core.live path native actual
  advance : Advance core actual value.value.move
  gateway : advance.nextCore.live.gatewayState = value.next.gatewayState

structure AckAssigned (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckIngress initial current count lane) (actual : Step input) where
  value : A.AckAssigned core.live path native actual
  advance : Advance core actual value.value.move
  gateway : advance.nextCore.live.gatewayState = value.next.gatewayState

structure DataServed (core : Core initial native quantum allowance current monitor sent received)
    (path : P.DataTicket initial native current part lane) (actual : Step input) where
  value : D.DataServed core.live path actual
  advance : Advance core actual value.value.move
  gateway : advance.nextCore.live.gatewayState = value.next.gatewayState

structure AckServed (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckTicket initial native current (received.bytes lower upper).length lane) (actual : Step input) where
  value : K.AckServed core.live path actual
  advance : Advance core actual value.value.move
  gateway : advance.nextCore.live.gatewayState = value.next.gatewayState

theorem assign_data_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.DataIngress initial current part lane)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor
      (.assign path.output.index (native.ingress sender))) :
    ∃ actual, Nonempty (DataAssigned core path actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPathsAssign.assign_data_at core.live core.senderWindow native path
  have permit : M.Allowed (config initial native quantum allowance) current.report.final monitor
      (.assign path.output.index (native.ingress path.output.produced.actor)) := by simpa only [path.output.actor] using allowed
  exact ⟨actual, ⟨⟨value, assignment_advance core path.toIngress value.toAssigned permit, rfl⟩⟩⟩

theorem assign_ack_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckIngress initial current count lane)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor
      (.assign path.output.index (native.ingress sender.other))) :
    ∃ actual, Nonempty (AckAssigned core path actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPathsAssign.assign_ack_at core.live core.senderWindow native path
  have permit : M.Allowed (config initial native quantum allowance) current.report.final monitor
      (.assign path.output.index (native.ingress path.output.produced.actor)) := by simpa only [path.output.actor] using allowed
  exact ⟨actual, ⟨⟨value, assignment_advance core path.toIngress value.toAssigned permit, rfl⟩⟩⟩

theorem serve_data_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.DataTicket initial native current part lane)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor (.serve path.ticket.id none)) :
    ∃ actual, Nonempty (DataServed core path actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPathsService.serve_data_at core.live core.senderWindow path
  have covered : ∀ role, Arrived received role → (rangeAt value.next.gatewayState role).isSome = true :=
    fun role arrived => value.preserved role (core.covered role arrived)
  have acknowledged : (value.next.gatewayState.gateway.session.lane sender.direction).acknowledged ≤
      initial.geometry.«prefix» + (received.bytes lower upper).length := by
    rw [data_acknowledged core path value]
    exact core.gatewayAck
  have fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper)
      value.served.ticket.value.produced := by
    rw [value.value.facts.ticket, path.produced]
    exact path.output.fields
  have peerSettled := CampusTCPTwoProgressGatewayPeerSettled.sender_service_settled core.live.gatewayState value.value
    value.next.gatewayState rfl fields.acknowledgment
  have peerWindow := CampusTCPTwoProgressGatewayPeerWindow.sender_service_reserved core.live.gatewayState core.peerWindow
    value.value value.next.gatewayState rfl
    (show CampusTCPTwoProgressGatewayPeerWindow.floor initial ≤ value.served.ticket.value.source.packet.segment.window.val from
      Nat.le_trans (Nat.min_le_right _ _) fields.window)
  exact ⟨actual, ⟨⟨value, finish core value.value.move value.value.endpoints value.next value.reserve covered acknowledged
    peerSettled peerWindow
    (.serve path.ticket.id) value.value.facts.event allowed, rfl⟩⟩⟩

theorem serve_ack_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckTicket initial native current (received.bytes lower upper).length lane)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor (.serve path.ticket.id none)) :
    ∃ actual, Nonempty (AckServed core path actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPathsAckService.serve_ack_at core.live core.senderWindow path core.gateway_observed core.gatewayAck
  have covered : ∀ role, Arrived received role → (rangeAt value.next.gatewayState role).isSome = true := by
    intro role arrived
    have old := core.covered role arrived
    cases role with
    | lower => change value.next.gatewayState.ranges.lowerRun.isSome = true; rw [value.lowerRun]; exact old
    | upper => change value.next.gatewayState.ranges.upperRun.isSome = true; rw [value.upperRun]; exact old
  have acknowledged : (value.next.gatewayState.gateway.session.lane sender.direction).acknowledged ≤
      initial.geometry.«prefix» + (received.bytes lower upper).length := by rw [value.acknowledged]; exact Nat.le_refl _
  have peerSettled := CampusTCPTwoProgressGatewayPeerSettled.receiver_service_settled core.live.gatewayState core.peerSettled
    value.value value.next.gatewayState rfl value.lowerRun value.upperRun
  have peerWindow := CampusTCPTwoProgressGatewayPeerWindow.receiver_service_reserved core.live.gatewayState core.peerWindow
    value.value value.next.gatewayState rfl
  exact ⟨actual, ⟨⟨value, finish core value.value.move value.value.endpoints value.next value.reserve covered acknowledged
    peerSettled peerWindow
    (.serve path.ticket.id) value.value.facts.event allowed, rfl⟩⟩⟩

theorem DataServed.covered {core : Core initial native quantum allowance current monitor sent received}
    {path : P.DataTicket initial native current part lane} (served : DataServed core path actual) :
    (rangeAt served.advance.nextCore.live.gatewayState part).isSome = true := by
  rw [served.gateway]
  exact served.value.covered

end Netlib.Check.CampusTCPTwoProgressPhaseNetwork
