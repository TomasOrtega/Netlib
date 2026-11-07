import Netlib.Check.CampusTCPTwoTransferTimeoutObserve
import Netlib.Check.CampusTCPTwoTransferTimeoutSources
import Netlib.Check.CampusTCPTwoTransferPhaseState
import Netlib.Check.CampusTCPTwoProgressTimer

namespace Netlib.Check.CampusTCPTwoTransferTimeoutProgress

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferWork
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoProgressPhaseBase (OriginalTimes emitted Arrived)
open CampusTCPTwoProgressRetry (HeadRange)

namespace M
export CampusTCPTwoProgressMonitor (timerTarget timerDemand nextDemand Allowed)
end M
namespace W
export CampusTCPTwoTransferMonitor (observe Allowed)
end W
namespace T
export CampusTCPTwoTransferLocatedTimeout (Retry)
end T
namespace O
export CampusTCPTwoTransferTimeoutObserve (afterTimeout ingressLane)
end O
namespace L
export CampusTCPTwoTransferLoss (Loss Book Spent Supports)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {actual : Step input}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {part : CampusTCPTwoProgressSender.Part} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}
variable {position target : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def currentHead (selected : HeadRange sent part head rest) : CampusTCPTwoProgressLossHistory.Head initial current part where
  recovery := core.live.senderFlight.recovery
  runtime := core.live.senderFlight.runtime
  entry := head
  tail := rest
  ledger := core.live.senderFlight.ledger.trans selected.ledger
  identity := selected.identity core.live.senderFlight
  position := by cases selected <;> exact congrArg Recovery.Outstanding.start core.live.senderFlight.headFixed
  count := selected.count core.live.senderFlight

theorem timer_fields (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (selected : HeadRange sent part head rest) (timer : M.timerTarget core.live.senderFlight.recovery = some target)
    (due : target ≤ core.live.senderFlight.recovery.now) :
    ∃ deadline, core.live.senderFlight.recovery.deadline = some deadline ∧
      deadline ≤ core.live.senderFlight.recovery.now ∧ head.lastAt + core.live.senderFlight.recovery.rto ≤ core.live.senderFlight.recovery.now := by
  obtain ⟨entry, tail, deadline, ledger, armed, _⟩ := CampusTCPTwoProgressTimer.target_some timer
  obtain ⟨sameHead, sameTail⟩ := List.cons.inj ((core.live.senderFlight.ledger.trans selected.ledger).symm.trans ledger)
  subst entry tail
  exact ⟨deadline, armed, CampusTCPTwoProgressTimer.due_fields (core.live.senderFlight.ledger.trans selected.ledger) armed timer due⟩

def spentEntry (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (value : T.Retry core.live part head rest actual) (loss : L.Loss initial cfg)
    (cause : core.losses.book.cause part = some position) (found : core.losses.book.losses[position]? = some loss)
    (phase : monitor.exchange.mode = .forward) (allowed : W.Allowed cfg current.report.final monitor actual.event) : L.Spent initial cfg :=
  core.losses.spentEntry part position loss cause found (currentHead (core := core) value.selection) value.move value.facts.event phase allowed

def updatedBook (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (value : T.Retry core.live part head rest actual) (loss : L.Loss initial cfg)
    (cause : core.losses.book.cause part = some position) (found : core.losses.book.losses[position]? = some loss)
    (phase : monitor.exchange.mode = .forward) (allowed : W.Allowed cfg current.report.final monitor actual.event) : L.Book initial cfg :=
  core.losses.book.spendCause (spentEntry core value loss cause found phase allowed)

private theorem retry_recovery (value : T.Retry core.live part head rest actual) :
    value.next.senderFlight.recovery = Recovery.timeoutState core.live.senderFlight.recovery head rest := by
  have runtime : (endpoint value.move.after.endpoints sender).recovery = some (Recovery.timeoutState core.live.senderFlight.recovery head rest) := by
    rw [value.endpointsEq]
    exact value.facts.runtime
  exact Option.some.inj (value.next.senderFlight.runtime.symm.trans runtime)

structure Retried (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (part : CampusTCPTwoProgressSender.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (position : Nat) (actual : Step input) where
  value : T.Retry core.live part head rest actual
  loss : L.Loss initial cfg
  cause : core.losses.book.cause part = some position
  found : core.losses.book.losses[position]? = some loss
  support : L.Supports loss part
  earlier : loss.move.after.report.steps <+: current.report.steps
  phase : monitor.exchange.mode = .forward
  allowed : W.Allowed cfg current.report.final monitor actual.event
  observed : W.observe cfg monitor actual = O.afterTimeout monitor current.report.final.outputs.length value.packetID
  next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after (W.observe cfg monitor actual)
    location (sent.retry core.live.senderFlight.recovery.now) received
  book : next.losses.book = updatedBook core value loss cause found phase allowed
  path : CampusTCPTwoProgressPaths.DataIngress initial value.move.after part (W.observe cfg monitor actual).exchange.forward.retry
  produced : path.output.produced = value.facts.produced
  source : CampusTCPTwoProgressReadWriter.SelectedOutput initial value.move.after path.output.produced

theorem finish (value : T.Retry core.live part head rest actual)
    (cause : core.losses.book.cause part = some position)
    (phase : monitor.exchange.mode = .forward) (mode : monitor.exchange.forward.mode = .recovery)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Retried core part head rest position actual) := by
  obtain ⟨loss, found, support, _⟩ := core.losses.valid.cause position cause
  have earlier := core.losses.lossesPast loss (List.mem_of_getElem? found)
  have observed := CampusTCPTwoTransferTimeoutObserve.observe_timeout value phase mode allowed
  have frame := CampusTCPTwoTransferTimeoutObserve.frame value phase mode allowed
  let losses := core.losses.consume part position loss cause found (currentHead (core := core) value.selection) value.move value.facts.event phase allowed frame
  let live : CampusTCPTwoTransferState.LiveAt initial value.move.after location (sent.retry core.live.senderFlight.recovery.now)
      (W.observe cfg monitor actual).exchange.forward.retries received := {
    anchor := value.next.anchor
    senderFlight := by rw [frame.retries]; exact value.next.senderFlight
    receiverFacts := value.next.receiverFacts
    gatewayState := core.live.gatewayState.reframe (value.serviceFrame location)
    gatewayWindow := core.live.gatewayWindow
    history := value.next.history }
  have recovery : live.senderFlight.recovery = Recovery.timeoutState core.live.senderFlight.recovery head rest := by
    have runtime : (endpoint value.move.after.endpoints sender).recovery = some (Recovery.timeoutState core.live.senderFlight.recovery head rest) := by
      rw [value.endpointsEq]
      exact value.facts.runtime
    exact Option.some.inj (live.senderFlight.runtime.symm.trans runtime)
  have quiet := CampusTCPTwoProgressWriteHistory.timeout_quiet value.facts.localStep value.facts.localEvent
  have emittedEq : emitted initial (sent.retry core.live.senderFlight.recovery.now) = emitted initial sent := by cases sent <;> rfl
  let next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after
      (W.observe cfg monitor actual) location (sent.retry core.live.senderFlight.recovery.now) received := {
    live
    senderWindow := value.reserve
    originals := (core.originals.retry _).retain_steps value.move.retained
    originalTimes := by cases value.selection <;> exact core.originalTimes
    writer := emittedEq.symm ▸ core.writer.quiet value.facts.localStep value.selectedSteps quiet.1 quiet.2
    losses
    lossBound := by rw [frame.dropIDs]; exact core.lossBound
    primaryQueue := by
      rw [observed]
      exact core.primaryQueue.work_same (by rw [value.move.final]; exact value.facts.work)
    retired := by rw [← value.selection.retired]; exact core.retired
    gatewayAck := core.gatewayAck
    peerSettled := core.peerSettled
    peerWindow := core.peerWindow
    covered := core.covered
    duplicates := by rw [recovery]; exact Nat.zero_le _
    emptyDuplicate := fun _ => by rw [recovery]; rfl
    deadline := by rw [recovery]; exact RecoveryDeadline.timeout _ _ _
    estimatorBeforeRetire := fun retired => by
      rw [recovery]
      exact core.estimatorBeforeRetire ((value.selection.retired core.live.senderFlight.recovery.now).trans retired)
    rtoBeforeRetire := fun retired => by
      rw [recovery, frame.retries]
      change 2 * core.live.senderFlight.recovery.rto = _
      rw [core.rtoBeforeRetire ((value.selection.retired core.live.senderFlight.recovery.now).trans retired), Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    rtoPending := fun _ => by
      rw [recovery, frame.retries]
      exact RTOEnvelope.timeout head rest (core.rtoPending (by rw [value.selection.ledger]; simp)) }
  let beforePath : CampusTCPTwoProgressPaths.DataIngress initial value.move.after part
      (O.ingressLane monitor.exchange.forward.retry current.report.final.outputs.length value.packetID) := {
    output := {
      index := current.report.final.outputs.length
      produced := value.facts.produced
      stored := value.source
      actor := by rw [value.facts.production]; rfl
      application := by rw [value.facts.production]; trivial
      fields := value.fields }
    packetID := value.packetID
    custody := value.custody
    phase := rfl, outputRef := rfl, packetRef := rfl }
  let path := beforePath.reindex (congrArg (fun state => state.exchange.forward.retry) observed)
  have book : next.losses.book = updatedBook core value loss cause found phase allowed := by cases part <;> rfl
  exact ⟨{
    value, loss, cause, found, support, earlier, phase, allowed, observed, next, book, path
    produced := rfl
    source := CampusTCPTwoTransferTimeoutSources.source core value }⟩

private theorem selection_retry (selected : HeadRange sent part head rest) (now : Nat) :
    HeadRange (sent.retry now) part { head with lastAt := now, retried := true } rest := by
  cases selected <;> constructor

private theorem same_role (before : HeadRange sent part head rest)
    (after : HeadRange (sent.retry now) role nextHead nextRest) : role = part := by
  cases before <;> cases after <;> rfl

private theorem upper_missing (active : Active core) (value : Retried core part head rest position actual) :
    (sent.retry core.live.senderFlight.recovery.now).retiredBytes = 0 → ¬Arrived received .upper →
      (W.observe cfg monitor actual).exchange.forward.upper.phase = .done →
      ∃ position, value.next.losses.book.cause .upper = some position := by
  intro zero missing done
  cases selected : value.value.selection with
  | lower first second head =>
    obtain ⟨position, chosen⟩ := active.upperMissing rfl missing (by simpa only [value.observed, O.afterTimeout] using done)
    exact ⟨position, by rw [value.book]; exact chosen⟩
  | upper first second head =>
    have positive := List.length_pos_iff.mpr initial.lowerNonempty
    change lower.length = 0 at zero
    omega

def after_retry (active : Active core) (value : Retried core part head rest position actual)
    (waiting : monitor.exchange.forward.waiting = true) : Active value.next := by
  have mode := active.waiting_mode waiting
  obtain ⟨lowerDone, upperDone⟩ := active.recovery mode
  obtain ⟨ackNone, _⟩ := active.waiting waiting
  have nextAck : (W.observe cfg monitor actual).exchange.forward.ack = none := by
    rw [value.observed]
    exact ackNone
  exact {
    exchange := by rw [value.observed]; exact active.exchange
    mode := Or.inr (by rw [value.observed]; exact mode)
    preparing := by cases value.value.selection <;> rfl
    nonempty := by cases value.value.selection <;> intro impossible <;> cases impossible
    lowerLane := .done (by rw [value.observed]; exact lowerDone)
    upperLane := .done (by rw [value.observed]; exact upperDone)
    retry := .active part { head with lastAt := core.live.senderFlight.recovery.now, retried := true } rest
      (selection_retry value.value.selection _) (.ingress value.path value.source)
    ack := by unfold AckState; rw [nextAck]; exact PUnit.unit
    originals := by intro impossible; rw [value.observed] at impossible; change monitor.exchange.forward.mode = .originals at impossible; rw [mode] at impossible; cases impossible
    recovery := fun _ => by simpa only [value.observed, O.afterTimeout] using And.intro lowerDone upperDone
    recoveryHead := by
      intro _ _ role nextHead nextRest chosen
      have same := CampusTCPTwoProgressRecoveryHead.head_eq (selection_retry value.value.selection _) chosen
      rw [← same]
    serial := by intro impossible; rw [nextAck] at impossible; cases impossible
    ackNonempty := by intro impossible; rw [nextAck] at impossible; cases impossible
    ackGateway := by intro _ impossible; rw [nextAck] at impossible; cases impossible
    waiting := by intro impossible; rw [value.observed] at impossible; cases impossible
    runnable := by intro _ _ _; rw [value.path.phase]; decide
    originalOpen := by intro impossible; rw [value.observed] at impossible; change monitor.exchange.forward.mode = .originals at impossible; rw [mode] at impossible; cases impossible
    debt := by
      intro role nextHead nextRest selected
      have roleEq := same_role value.value.selection selected
      cases roleEq
      exact ⟨.retry (.ingress value.path)⟩
    upperMissing := upper_missing active value
    zeroAck := by intro _ impossible; rw [nextAck] at impossible; cases impossible
    sources := active.sources.non_delivery value.value.move (by rw [value.value.facts.event]; trivial) }

theorem due_of_allowed (active : Active core) (waiting : monitor.exchange.forward.waiting = true)
    (allowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward (.timeout sender true)) :
    ∃ target, M.timerTarget core.live.senderFlight.recovery = some target ∧ target ≤ core.live.senderFlight.recovery.now := by
  have mode := active.waiting_mode waiting
  have ackNone := (active.waiting waiting).1
  obtain ⟨_, chosen | dropped | free, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, next, served⟩ := chosen
    simp only [M.nextDemand, mode, ackNone, waiting, ite_true] at next
    cases pending : M.timerDemand ((cfg).at current.report.final).forward current.report.final with
    | none => simp only [pending, Option.map_none] at next; cases next
    | some timer =>
      simp only [pending, Option.map_some] at next
      cases next
      obtain ⟨recovery, entry, tail, deadline, target, runtime, ledger, armed, targetEq, selected⟩ :=
        CampusTCPTwoProgressTimer.timerDemand_some pending
      have current : CampusTCPGapProgressMonitor.senderRecovery ((cfg).at current.report.final).forward.toConfig current.report.final =
          some core.live.senderFlight.recovery := by
        simp only [CampusTCPGapProgressMonitor.senderRecovery, current.connection, config,
          CampusTCPTwoTransferNative.Checks.monitorConfig, CampusTCPTwoTransferMonitor.Config.at,
          CampusTCPTwoExchangeSetup.config, CampusTCPTwoProgressSetup.config, core.live.senderFlight.runtime]
      have same := Option.some.inj (runtime.symm.trans current)
      subst recovery
      have targetAt : M.timerTarget core.live.senderFlight.recovery = some target :=
        (CampusTCPTwoProgressTimer.target_of_fields ledger armed).trans (congrArg some targetEq.symm)
      change CampusTCPGapProgressMonitor.serves timer (.timeout sender true) = true at served
      rw [selected] at served
      split at served
      · have impossible := (CampusTCPGapProgressMonitorFacts.serves_tick _ _ _).mp served
        cases impossible
      · rename_i late
        exact ⟨target, targetAt, Nat.le_of_not_gt late⟩
  · obtain ⟨_, _, impossible, _⟩ := dropped
    cases impossible
  · obtain ⟨_, _, impossible, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ free
    cases impossible

structure Advanced (active : Active core) (actual : Step input) where
  part : CampusTCPTwoProgressSender.Part
  head : Recovery.Outstanding
  rest : List Recovery.Outstanding
  position : Nat
  value : Retried core part head rest position actual
  next : Active value.next

theorem timeout_at (active : Active core) (waiting : monitor.exchange.forward.waiting = true) (budget : allowance ≤ 2)
    (allowed : W.Allowed cfg current.report.final monitor (.timeout sender true)) :
    ∃ actual, Nonempty (Advanced active actual) := by
  have mode := active.waiting_mode waiting
  obtain ⟨part, head, rest, selected⟩ := active.current_head
  obtain ⟨position, cause⟩ := active.waiting_cause waiting part head rest selected
  have credit := Nat.lt_of_lt_of_le (core.timeout_credit part position cause) budget
  have localAllowed := (CampusTCPTwoTransferTimeoutObserve.allowed_timeout_fields cfg current.report.final monitor sender allowed active.exchange).2.2.2
  obtain ⟨target, timer, due⟩ := due_of_allowed active waiting localAllowed
  obtain ⟨deadline, armed, deadlineDue, elapsed⟩ := timer_fields core selected timer due
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoTransferLocatedTimeout.retry_at core.live core.senderWindow selected credit armed deadlineDue elapsed
  obtain ⟨record⟩ := finish value cause active.exchange mode (by rw [value.facts.event]; exact allowed)
  exact ⟨actual, ⟨⟨part, head, rest, position, record, after_retry active record waiting⟩⟩⟩

theorem Step.timeout (active : Active core) (waiting : monitor.exchange.forward.waiting = true) (budget : allowance ≤ 2)
    (allowed : W.Allowed cfg current.report.final monitor (.timeout sender true))
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .timeout sender true) :
    Nonempty (Advanced active actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := timeout_at active waiting budget allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.value.value.move.beforeEq.trans before.symm) (value.value.value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

end Netlib.Check.CampusTCPTwoTransferTimeoutProgress
