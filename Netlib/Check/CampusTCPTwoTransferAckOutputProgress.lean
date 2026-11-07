import Netlib.Check.CampusTCPTwoTransferLocatedAckOutput
import Netlib.Check.CampusTCPTwoTransferServiceObserve
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase
import Netlib.Check.CampusTCPTwoTransferServiceProgress

/-!
# Current ACK emission on the same transfer task

The actual receiver queue supplies the ACK output.
Its new ingress retains the same data paths and loss book.
-/

namespace Netlib.Check.CampusTCPTwoTransferAckOutputProgress

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferPhaseState (Active Debt)
open CampusTCPTwoTransferWork (Work DataWork OriginalLane RetryLane AckWork AckState)
open CampusTCPTwoTransferPaths (AckIngress)
open CampusTCPTwoTransferLocatedAckOutput (Acked)
open CampusTCPTwoTransferServiceObserve (afterService)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe controlDemand drainTicket)
end W
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane)
end M
namespace X
export CampusTCPTwoExchangeMonitor (allowed observe)
end X
namespace F
export CampusTCPTwoProgressMonitorFacts (observe_action observe_ack phase_beq mode_beq)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {lane : M.Lane} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper


def ingressLane (lane : M.Lane) (index packetID : Nat) : M.Lane :=
  ⟨.ackIngress, { lane.refs with ackOutput := some index, ackIngressPacket := some packetID }⟩

theorem allowed_output (allowed : W.Allowed cfg current.report.final monitor (.emitAck sender.other true)) :
    W.drainTicket current.report.final monitor = none ∧ W.controlDemand monitor = none := by
  by_cases invalid : monitor.mode = .invalid
  · simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  · cases drain : W.drainTicket current.report.final monitor with
    | some ticket => simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain,
        CampusTCPTwoTransferMonitor.drainServes] at allowed
    | none =>
      cases selected : W.controlDemand monitor with
      | none => exact ⟨rfl, rfl⟩
      | some kind =>
        cases kind <;> simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain, selected,
          CampusTCPTwoTransferMonitor.Control.serves] at allowed

private theorem observe_output (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (active : Active core)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished) (control : W.controlDemand monitor = none)
    (value : Acked core.live actual) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (selected : monitor.exchange.forward.ack = some lane) (phase : lane.phase = .needAck) (packetID : Nat)
    (custody : actual.result.state.custody.pendingID (Transit.ingressAt current.report.final.outputs.length) = some packetID) :
    W.observe cfg monitor actual = afterService monitor
      { monitor.exchange.forward with ack := some (ingressLane lane current.report.final.outputs.length packetID) } := by
  have localAllowed := CampusTCPTwoTransferServiceObserve.local_allowed ordinary control active.exchange allowed
  have localObserved : CampusTCPTwoProgressMonitor.observe ((cfg).at actual.before).forward monitor.exchange.forward actual =
      { monitor.exchange.forward with ack := some (ingressLane lane current.report.final.outputs.length packetID) } := by
    rw [F.observe_action _ _ _ value.move.supported value.move.passed
      (by rw [value.move.beforeEq]; exact localAllowed) (.emitAck sender.other true) value.facts.event,
      F.observe_ack _ _ _ lane active.mode active.lower_not_needSend active.upper_not_needSend selected]
    have actor : value.facts.produced.actor = sender.other := by rw [value.facts.production]; rfl
    have self : (sender.other == sender.other) = true := by cases sender <;> rfl
    have cfgSender : ((cfg).at current.report.final).forward.sender = sender := rfl
    simp only [CampusTCPTwoProgressMonitor.observeAck, CampusTCPTwoProgressMonitor.ackLane,
      phase, CampusTCPGapProgressMonitor.observeOutput, value.facts.output, actor, cfgSender,
      ite_false, ite_true, self, value.move.beforeEq, custody,
      CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap, F.phase_beq,
      reduceCtorEq, decide_false, Bool.false_eq_true, ingressLane]
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [value.move.supported, value.move.passed, value.move.beforeEq]
    exact allowed
  have innerChecked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [value.move.supported, value.move.passed]
    simpa only [Bool.true_and, X.allowed, active.exchange, value.move.beforeEq, CampusTCPTwoProgressMonitor.Allowed] using localAllowed
  have drainless : W.drainTicket current.report.final monitor = none := by
    apply CampusTCPTwoTransferControlObserve.noDrain_of_non_capture
    rcases ordinary with mode | mode <;> rw [mode] <;> decide
  rw [W.observe, ite_eq_left checked, value.move.beforeEq, drainless, control]
  unfold CampusTCPTwoTransferMonitor.ordinary
  rw [X.observe, ite_eq_left innerChecked, active.exchange, localObserved]
  have healthy : monitor.exchange.forward.mode ≠ .invalid := by rcases active.mode with mode | mode <;> rw [mode] <;> decide
  have unfinished : monitor.exchange.forward.mode ≠ .done := by rcases active.mode with mode | mode <;> rw [mode] <;> decide
  simp only [F.mode_beq, healthy, unfinished, decide_false, Bool.false_eq_true, ite_false]
  change (if decide (monitor.exchange.mode = .invalid) then _ else _) = _
  rw [active.exchange]
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]
  unfold afterService
  congr 2
  · change (match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops) = _
    rw [value.facts.event]
  · change (match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) = _
    rw [value.facts.event]

structure AckSent (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (lane : M.Lane) (actual : Step input) where
  value : Acked core.live actual
  pending : core.live.receiverFacts.reaction.work.pending ≠ []
  allowed : W.Allowed cfg current.report.final monitor actual.event
  packetID : Nat
  custody : value.move.after.report.final.custody.pendingID (Transit.ingressAt current.report.final.outputs.length) = some packetID
  observed : W.observe cfg monitor actual = afterService monitor
    { monitor.exchange.forward with ack := some (ingressLane lane current.report.final.outputs.length packetID) }
  next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after
    (W.observe cfg monitor actual) location sent received
  gateway : next.live.gatewayState = core.live.gatewayState.reframe (value.gateway location)
  book : next.losses.book = core.losses.book
  path : AckIngress initial value.move.after (received.bytes lower upper).length
    (ingressLane lane current.report.final.outputs.length packetID)

theorem ack_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (selected : monitor.exchange.forward.ack = some lane) (phase : lane.phase = .needAck)
    (pending : core.live.receiverFacts.reaction.work.pending ≠ [])
    (allowed : W.Allowed cfg current.report.final monitor (.emitAck sender.other true)) :
    ∃ actual, Nonempty (AckSent core lane actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoTransferLocatedAckOutput.ack_at core.live core.senderWindow pending
  have allowedActual : W.Allowed cfg current.report.final monitor actual.event := by rw [value.facts.event]; exact allowed
  have control := (allowed_output allowed).2
  have ordinary := controls.ordinary_modes control
  obtain ⟨packetID, custody⟩ := CampusTCPRoundMonitorFacts.output_pending actual value.facts.produced value.facts.output
  rw [value.move.beforeEq] at custody
  have observed := observe_output core active ordinary control value allowedActual selected phase packetID custody
  have retries : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries := by rw [observed]; rfl
  have drops : (W.observe cfg monitor actual).exchange.forward.drops = monitor.exchange.forward.drops := by rw [observed]; rfl
  have wholeDrops : (W.observe cfg monitor actual).exchange.drops = monitor.exchange.drops := by rw [observed]; rfl
  have timeouts : (W.observe cfg monitor actual).exchange.timeouts = monitor.exchange.timeouts := by rw [observed]; rfl
  let live : LiveAt initial value.move.after location sent (W.observe cfg monitor actual).exchange.forward.retries received := {
    value.next with
      senderFlight := by rw [retries]; exact value.next.senderFlight
      gatewayState := core.live.gatewayState.reframe (value.gateway location)
      gatewayWindow := core.live.gatewayWindow }
  have recovery : live.senderFlight.recovery = core.live.senderFlight.recovery := by
    exact Option.some.inj (live.senderFlight.runtime.symm.trans
      ((congrArg (fun state : Endpoint.State => state.recovery) value.peer).trans core.live.senderFlight.runtime))
  have queue : CampusTCPTwoTransferQueue.Closed value.move.after.report.final (W.observe cfg monitor actual).exchange.forward := by
    rw [observed]
    apply (core.primaryQueue.work_same ?_).reframe <;> try rfl
    rw [value.move.final, CampusTCPTwoProgressPathRetain.Step.work_quiet actual (by rw [value.facts.event]; trivial), value.move.beforeEq]
  let next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after
      (W.observe cfg monitor actual) location sent received := {
    live, senderWindow := value.reserve
    originals := core.originals.retain_steps value.move.retained
    originalTimes := core.originalTimes
    writer := core.writer.same value.senderSteps
    losses := core.losses.append value.move
      (by rw [CampusTCPTwoProgressLossHistory.isDrop, value.facts.event])
      (by rw [CampusTCPTwoExchangeLoss.isTimeoutOutput, value.facts.event]) drops retries wholeDrops timeouts
    lossBound := by rw [drops]; exact core.lossBound
    primaryQueue := queue
    retired := core.retired, gatewayAck := core.gatewayAck, peerSettled := core.peerSettled, peerWindow := core.peerWindow
    covered := core.covered
    duplicates := by rw [recovery]; exact core.duplicates
    emptyDuplicate := by rw [recovery]; exact core.emptyDuplicate
    deadline := by rw [recovery]; exact core.deadline
    estimatorBeforeRetire := by rw [recovery]; exact core.estimatorBeforeRetire
    rtoBeforeRetire := by rw [recovery, retries]; exact core.rtoBeforeRetire
    rtoPending := by rw [recovery, retries]; exact core.rtoPending }
  let path : AckIngress initial value.move.after (received.bytes lower upper).length
      (ingressLane lane current.report.final.outputs.length packetID) := {
    output := {
      index := current.report.final.outputs.length, produced := value.facts.produced
      stored := by rw [value.move.final]; exact value.facts.source
      actor := by rw [value.facts.production]; rfl
      application := by rw [value.facts.production]; trivial
      fields := value.fields }
    packetID, custody := by
      change value.move.after.report.final.custody.pendingID (Transit.ingressAt current.report.final.outputs.length) = some packetID
      rw [value.move.final]
      exact custody
    phase := rfl, outputRef := rfl, packetRef := rfl }
  exact ⟨actual, ⟨⟨value, pending, allowedActual, packetID, by rw [value.move.final]; exact custody,
    observed, next, rfl, rfl, path⟩⟩⟩

theorem AckSent.sender_recovery {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} (value : AckSent core lane actual) :
    value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
  exact Option.some.inj (value.next.live.senderFlight.runtime.symm.trans
    ((congrArg (fun state : Endpoint.State => state.recovery) value.value.peer).trans core.live.senderFlight.runtime))

private def data_after {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} (value : AckSent core lane actual)
    {part : CampusTCPTwoProgressSender.Part} {other : M.Lane}
    (work : DataWork initial checks current core.live.gatewayState part other) :
    DataWork initial checks value.value.move.after value.next.live.gatewayState part other := by
  rw [value.gateway]
  have nonconsuming (id : Nat) : CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some id := by
    simp only [value.value.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket, ne_eq, reduceCtorEq, not_false_eq_true]
  cases work with
  | ingress path source => exact .ingress (path.after_move value.value.move (nonconsuming _)) (source.retain_steps value.value.move.retained)
  | ticket path selected source =>
    exact .ticket (path.after_quiet value.value.move (by rw [value.value.facts.event]; trivial)) selected
      (source.retain_steps value.value.move.retained)
  | link path source covered =>
    exact .link (path.after_move value.value.move (nonconsuming _))
      (source.retain_steps value.value.move.retained) covered

private def original_after {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} (value : AckSent core lane actual)
    {part : CampusTCPTwoProgressSender.Part} {other : M.Lane}
    (work : OriginalLane initial checks current core.live.gatewayState received part other) :
    OriginalLane initial checks value.value.move.after value.next.live.gatewayState received part other := by
  cases work with
  | active work missing => exact .active (data_after value work) missing
  | done phase => exact .done phase


def AckSent.active {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} (value : AckSent core lane actual) (active : Active core)
    (selected : monitor.exchange.forward.ack = some lane) : Active value.next := by
  have lowerEq := congrArg (fun whole : W.Monitor => whole.exchange.forward.lower) value.observed
  have upperEq := congrArg (fun whole : W.Monitor => whole.exchange.forward.upper) value.observed
  have retryEq := congrArg (fun whole : W.Monitor => whole.exchange.forward.retry) value.observed
  have ackEq := congrArg (fun whole : W.Monitor => whole.exchange.forward.ack) value.observed
  have modeEq := congrArg (fun whole : W.Monitor => whole.exchange.forward.mode) value.observed
  have waitingEq := congrArg (fun whole : W.Monitor => whole.exchange.forward.waiting) value.observed
  have retryDone := active.serial (by rw [selected]; rfl)
  let afterLane := ingressLane lane current.report.final.outputs.length value.packetID
  have nextAck : (W.observe cfg monitor actual).exchange.forward.ack = some afterLane := ackEq
  have lowerLane : OriginalLane initial checks value.value.move.after value.next.live.gatewayState received .lower
      (W.observe cfg monitor actual).exchange.forward.lower := by rw [lowerEq]; exact original_after value active.lowerLane
  have upperLane : OriginalLane initial checks value.value.move.after value.next.live.gatewayState received .upper
      (W.observe cfg monitor actual).exchange.forward.upper := by rw [upperEq]; exact original_after value active.upperLane
  refine {
    exchange := by rw [value.observed]; exact active.exchange
    mode := by rw [modeEq]; exact active.mode
    preparing := active.preparing, nonempty := active.nonempty
    lowerLane, upperLane
    retry := by rw [retryEq]; exact .done retryDone
    ack := by rw [nextAck]; exact .ingress value.path
    originals := by rw [value.observed]; exact active.originals
    recovery := by rw [value.observed]; exact active.recovery
    recoveryHead := by rw [modeEq, waitingEq]; exact active.recoveryHead
    serial := by rw [retryEq]; intro _; exact retryDone
    ackNonempty := fun _ => active.ackNonempty (by rw [selected]; rfl)
    ackGateway := ?_
    waiting := ?_, runnable := ?_, originalOpen := ?_, debt := ?_
    upperMissing := ?_
    zeroAck := ?_
    sources := active.sources.non_delivery value.value.move (by rw [value.value.facts.event]; trivial) }
  · intro other pending phase
    have same := Option.some.inj (nextAck.symm.trans pending)
    rw [← same] at phase
    cases phase
  · intro waiting
    have none := (active.waiting (waitingEq ▸ waiting)).1
    rw [selected] at none
    cases none
  · intro _ _ none
    rw [nextAck] at none
    cases none
  · intro _ none _
    rw [nextAck] at none
    cases none
  · intro part head rest currentHead
    obtain ⟨debt⟩ := active.debt part head rest currentHead
    cases debt with
    | cause position chosen => exact ⟨.cause position (by rw [value.book]; exact chosen)⟩
    | lower same work => exact ⟨.lower same (lowerLane.work (by rw [lowerEq]; exact work.not_done))⟩
    | upper same work => exact ⟨.upper same (upperLane.work (by rw [upperEq]; exact work.not_done))⟩
    | retry work => exact False.elim (work.not_done retryDone)
    | ack old _ _ covered => exact ⟨.ack afterLane nextAck (.ingress value.path) covered⟩
  · intro retired missing done
    obtain ⟨position, chosen⟩ := active.upperMissing retired missing (by rw [upperEq] at done; exact done)
    exact ⟨position, by rw [value.book]; exact chosen⟩
  · intro _ _ retired
    rw [value.sender_recovery]
    exact active.zeroAck lane selected retired


theorem AckSent.phase {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} (value : AckSent core lane actual)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location) :
    CampusTCPTwoTransferControlState.Phase value.value.move.after.report.final (W.observe cfg monitor actual).mode location := by
  have nextMode := congrArg (fun whole : W.Monitor => whole.mode) value.observed
  rw [nextMode]
  have control := (allowed_output (by rw [← value.value.facts.event]; exact value.allowed)).2
  exact controls.nonservice control value.value.move (by rw [value.value.facts.event]; trivial)


theorem Step.emit_ack (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (active : Active core)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (selected : monitor.exchange.forward.ack = some lane) (phase : lane.phase = .needAck)
    (pending : core.live.receiverFacts.reaction.work.pending ≠ [])
    (allowed : W.Allowed cfg current.report.final monitor (.emitAck sender.other true))
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .emitAck sender.other true) :
    Nonempty (AckSent core lane actual) := by
  obtain ⟨chosen, ⟨value⟩⟩ := ack_at core active controls selected phase pending allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
    (value.value.move.beforeEq.trans before.symm) (value.value.facts.event.trans event.symm)
  exact same ▸ ⟨value⟩


theorem AckSent.ack_state {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} (value : AckSent core lane actual) :
    value.value.facts.localStep.result.state.ackReaction = some
      (AckReaction.outputState core.live.receiverFacts.reaction (endpoint current.endpoints sender.other).now
        (endpoint current.endpoints sender.other).core.receiveNext (endpoint current.endpoints sender.other).core.capacity
        (endpoint current.endpoints sender.other).core.window (endpoint current.endpoints sender.other).effectiveMSS) := by
  have state := value.value.facts.origin.ack_state
  rw [value.value.facts.localBefore, core.live.receiverFacts.ackRuntime, Option.map_some] at state
  exact state

end Netlib.Check.CampusTCPTwoTransferAckOutputProgress
