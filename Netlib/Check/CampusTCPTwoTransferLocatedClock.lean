import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoTransferClockBound

/-!
# Actual clocks preserve the located forward task

The same clock step appends to the full loss history and keeps its cause book.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedClock

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {actor : Actor} {millis : Nat} {actual : Step input}

private theorem local_mode_beq (left right : CampusTCPTwoProgressMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem local_allowed (cfg : CampusTCPTwoTransferMonitor.Config) (state : State input) (monitor : W.Monitor)
    (phase : monitor.exchange.mode = .forward)
    (allowed : W.Allowed cfg state monitor (.advanceClock actor millis)) :
    CampusTCPTwoProgressMonitor.Allowed (cfg.at state).forward state monitor.exchange.forward (.advanceClock actor millis) := by
  have ordinary := CampusTCPTwoTransferClockBound.allowed_clock cfg state monitor actor millis allowed
  simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed,
    phase, CampusTCPTwoProgressMonitor.Allowed] using ordinary

theorem observe_clock (cfg : CampusTCPTwoTransferMonitor.Config) (monitor : W.Monitor)
    (phase : monitor.exchange.mode = .forward) (active : monitor.exchange.forward.mode ≠ .done)
    (actual : Step input) (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (event : actual.event = .advanceClock actor millis)
    (allowed : W.Allowed cfg actual.before monitor actual.event) :
    W.observe cfg monitor actual = { monitor with exchange := { monitor.exchange with slots := monitor.exchange.slots + 1 } } := by
  cases actual with
  | mk before selected result computed =>
    dsimp only at event supported passed allowed ⊢
    subst selected
    let actual : Step input := ⟨before, .advanceClock actor millis, result, computed⟩
    have currentAllowed := local_allowed cfg before monitor phase allowed
    have valid := ((CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp currentAllowed).1
    have localStep := CampusTCPTwoProgressMonitorFacts.observe_clock (cfg.at before).forward monitor.exchange.forward
      actual supported passed currentAllowed rfl
    have exchangeAllowed := CampusTCPTwoTransferClockBound.allowed_clock cfg before monitor actor millis allowed
    have exchangeChecked : (result.supported && result.passed &&
        CampusTCPTwoExchangeMonitor.allowed (cfg.at before) before monitor.exchange (.advanceClock actor millis)) = true := by
      rw [supported, passed]
      exact exchangeAllowed
    have nextExchange : CampusTCPTwoExchangeMonitor.observe (cfg.at before) monitor.exchange actual =
        { monitor.exchange with slots := monitor.exchange.slots + 1 } := by
      change (actual.result.supported && actual.result.passed &&
        CampusTCPTwoExchangeMonitor.allowed (cfg.at before) actual.before monitor.exchange actual.event) = true at exchangeChecked
      rw [CampusTCPTwoExchangeMonitor.observe, ite_eq_left exchangeChecked]
      simp only [phase, localStep, local_mode_beq, valid, active, decide_false, Bool.false_eq_true, ite_false]
      congr 1 <;> exact phase
    have ordinary : CampusTCPTwoTransferMonitor.ordinary cfg monitor actual =
        { monitor with exchange := { monitor.exchange with slots := monitor.exchange.slots + 1 } } := by
      rw [CampusTCPTwoTransferMonitor.ordinary, nextExchange]
      simp only [phase, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]
    have checked : (result.supported && result.passed &&
        CampusTCPTwoTransferMonitor.allowed cfg before monitor (.advanceClock actor millis)) = true := by
      rw [supported, passed]
      exact allowed
    change W.observe cfg monitor actual = _
    rw [W.observe, ite_eq_left checked]
    cases drain : CampusTCPTwoTransferMonitor.drainTicket before monitor with
    | some ticket => simpa only [drain, actual] using ordinary
    | none =>
      cases selected : CampusTCPTwoTransferMonitor.controlDemand monitor <;>
        simpa only [drain, selected, actual] using ordinary

structure Clocked (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (actor : Actor) (millis : Nat) (actual : Step input) where
  move : Move current actual
  event : actual.event = .advanceClock actor millis
  placement : CampusTCPRecoveryRoundPhaseBase.At current move.after
  next : Core initial checks routing quantum allowance reverseLower reverseUpper move.after
    (W.observe (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual) location sent received
  observed : W.observe (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual =
    { monitor with exchange := { monitor.exchange with slots := monitor.exchange.slots + 1 } }
  healthy : (W.observe (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual).mode ≠ .invalid
  book : next.losses.book = core.losses.book
  nowBound : ∀ selected, (endpoint move.after.endpoints selected).now ≤ (endpoint current.endpoints selected).now + quantum

theorem Step.clock (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (active : monitor.exchange.forward.mode ≠ .done)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .advanceClock actor millis)
    (allowed : W.Allowed (config initial checks routing quantum allowance reverseLower reverseUpper)
      current.report.final monitor (.advanceClock actor millis)) : Nonempty (Clocked core actor millis actual) := by
  let cfg := config initial checks routing quantum allowance reverseLower reverseUpper
  have currentAllowed := local_allowed cfg current.report.final monitor phase allowed
  let anchor := CampusTCPGapProgressPhaseBase.Anchor.refl current core.live.anchor.guards
  obtain ⟨clocked⟩ := CampusTCPTwoProgressClock.Step.clock actual anchor (cfg.at current.report.final).forward
    monitor.exchange.forward actor millis before event currentAllowed
  have observed := observe_clock cfg monitor phase active actual clocked.move.supported clocked.move.passed event
    (by rw [before, event]; exact allowed)
  have healthy : (W.observe cfg monitor actual).mode ≠ .invalid := by
    have valid : monitor.mode ≠ .invalid := by
      intro invalid
      simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
    rw [observed]
    exact valid
  let joint := core.live.clock clocked.placement
    (CampusTCPTwoProgressNetworkState.clock_time clocked core.live.anchor.guards currentAllowed sender)
    (CampusTCPTwoProgressNetworkState.clock_time clocked core.live.anchor.guards currentAllowed sender.other)
  have monotone : core.live.senderFlight.recovery.now ≤ (endpoint clocked.move.after.endpoints sender).now := by
    have oldNow : (endpoint current.endpoints sender).now = core.live.senderFlight.recovery.now := by
      simp only [Endpoint.State.now, core.live.senderFlight.runtime, Option.map_some, Option.getD_some]
    rw [← oldNow]
    exact (clocked.placement.frame.endpointFrame sender).monotone
  let appended : CampusTCPTwoTransferLossHistory.History initial cfg clocked.move.after (W.observe cfg monitor actual) :=
    core.losses.append clocked.move
    (by simp only [CampusTCPTwoProgressLossHistory.isDrop, event])
    (by simp only [CampusTCPTwoExchangeLoss.isTimeoutOutput, event])
    (by rw [observed]) (by rw [observed]) (by rw [observed]) (by rw [observed])
  have lossesWitness : ∃ losses : CampusTCPTwoTransferLossHistory.History initial cfg clocked.move.after
      (W.observe cfg monitor actual), losses.book = core.losses.book := ⟨appended, rfl⟩
  rw [observed] at lossesWitness
  obtain ⟨losses, lossBook⟩ := lossesWitness
  have updated : ∃ next : Core initial checks routing quantum allowance reverseLower reverseUpper clocked.move.after
      (W.observe cfg monitor actual) location sent received, next.losses.book = core.losses.book := by
    rw [observed]
    refine ⟨{
      live := joint
      senderWindow := CampusTCPTwoProgressSenderWindow.clock core.senderWindow (clocked.placement.frame.endpointFrame sender)
      originals := core.originals.clock clocked.placement
      originalTimes := core.originalTimes
      writer := core.writer.clock clocked.placement
      losses := losses
      lossBound := core.lossBound
      primaryQueue := core.primaryQueue.work_same clocked.placement.frame.work
      retired := core.retired
      gatewayAck := core.gatewayAck
      peerSettled := core.peerSettled
      peerWindow := core.peerWindow
      covered := core.covered
      duplicates := core.duplicates
      emptyDuplicate := core.emptyDuplicate
      deadline := RecoveryDeadline.advance _ _ core.deadline monotone
      estimatorBeforeRetire := core.estimatorBeforeRetire
      rtoBeforeRetire := core.rtoBeforeRetire
      rtoPending := fun nonempty => RTOEnvelope.advance _ (core.rtoPending nonempty) monotone }, ?_⟩
    exact lossBook
  obtain ⟨next, book⟩ := updated
  refine ⟨⟨clocked.move, event, clocked.placement, next, observed, healthy, book, ?_⟩⟩
  intro selected
  have bound := CampusTCPTwoTransferClockBound.Move.actor_now_le clocked.move (by rw [event]; exact allowed) selected
  exact bound

end Netlib.Check.CampusTCPTwoTransferLocatedClock
