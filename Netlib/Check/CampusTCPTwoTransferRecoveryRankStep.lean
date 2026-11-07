import Netlib.Check.CampusTCPTwoTransferRecoveryRankBounds
import Netlib.Check.CampusTCPTwoTransferRecoveryRankClockStep
import Netlib.Check.CampusTCPTwoTransferRecoveryCap
import Netlib.Check.CampusTCPTwoTransferEvidenceEvents
import Netlib.Check.CampusTCPTwoTransferEvidenceTimeout
import Netlib.Check.CampusTCPTwoTransferEvidenceDrop
import Netlib.Check.CampusTCPTwoProgressRecoveryRankWork

namespace Netlib.Check.CampusTCPTwoTransferRecoveryRankStep

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferEvidence (Evidence)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferHandoffRTO (PendingCap)

namespace R
export CampusTCPTwoTransferRecoveryRank (rank boundSlots)
end R
namespace K
export CampusTCPTwoProgressRecoveryRank (timerSlots)
end K
namespace M
export CampusTCPTwoProgressMonitor (Allowed nextDemand dropTarget exposedPacket)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe nextDemand serves)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "packetCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)

private theorem after_healthy
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (budget : allowance ≤ 2) (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    (W.observe cfg monitor actual).mode ≠ .invalid := by
  rcases value.step budget actual move.beforeEq allowed with running | terminal
  · obtain ⟨advance⟩ := running
    exact advance.next.healthy
  · obtain ⟨read⟩ := terminal
    exact read.value.healthy

private theorem observed_rank
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (budget : allowance ≤ 2)
    (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event) (bound : Nat) :
    R.rank cfg bound allowance move.after.report.final (W.observe cfg monitor actual) =
      CampusTCPTwoProgressRecoveryRank.rank packetCfg bound allowance actual.result.state
        (CampusTCPTwoProgressMonitor.observe packetCfg monitor.exchange.forward actual) := by
  obtain ⟨control, drained⟩ := CampusTCPTwoTransferNonoriginal.ordinary value nonoriginal
  have healthy := after_healthy value budget move allowed
  rcases CampusTCPTwoTransferOriginalRank.ordinary_frame move value.healthy value.forward.exchange drained control allowed with
    invalid | ⟨_, observed⟩
  · exact False.elim (healthy invalid)
  · unfold R.rank
    rw [observed, move.final, move.beforeEq]
    rfl

private theorem successor_slots_le
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (cap : PendingCap cfg capacity current.report.final monitor)
    (budget : allowance ≤ 2) (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    K.timerSlots (cfg).exchange.forward actual.result.state ≤ R.boundSlots cfg capacity allowance := by
  have bounded := CampusTCPTwoTransferRecoveryCap.step value nonoriginal cap budget move allowed
  rcases value.step budget actual move.beforeEq allowed with running | terminal
  · obtain ⟨advance⟩ := running
    have nextCap : PendingCap cfg capacity advance.move.after.report.final (W.observe cfg monitor actual) := by
      rw [advance.move.final, ← move.final]
      exact bounded
    have slots := CampusTCPTwoTransferRecoveryRank.evidence_slots_le advance.next
      (CampusTCPTwoTransferNonoriginal.advanced_nonoriginal advance nonoriginal allowed) nextCap
    rw [advance.move.final] at slots
    exact slots
  · obtain ⟨read⟩ := terminal
    have senderEq : (cfg).exchange.forward.sender = sender := rfl
    have runtime : CampusTCPGapProgressMonitor.senderRecovery (cfg).exchange.forward.toConfig read.value.finalCut.report.final =
        some read.value.value.senderFlight.recovery := by
      simp only [CampusTCPGapProgressMonitor.senderRecovery, read.value.finalCut.connection, senderEq]
      exact read.value.value.senderFlight.runtime
    have slots := CampusTCPTwoTransferRecoveryRank.empty_slots _ _ _ runtime read.value.value.senderFlight.ledger
    change K.timerSlots (cfg).exchange.forward read.value.value.move.after.report.final = 0 at slots
    rw [read.value.value.move.final] at slots
    rw [slots]
    exact Nat.zero_le _

variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

private theorem action_running (active : Active core) (mode : monitor.exchange.forward.mode = .recovery)
    (allowed : M.Allowed packetCfg current.report.final monitor.exchange.forward actual.event)
    (action : CampusTCPRoundMonitor.Action) (event : actual.event = action.event) : monitor.exchange.forward.waiting = false := by
  cases waiting : monitor.exchange.forward.waiting with
  | false => rfl
  | true =>
    have ack := (active.waiting waiting).1
    obtain ⟨_, selected | dropped | free, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
    · obtain ⟨demand, next, served⟩ := selected
      simp only [M.nextDemand, mode, ack, waiting, ite_true] at next
      cases pending : CampusTCPTwoProgressMonitor.timerDemand packetCfg current.report.final with
      | none => simp only [pending, Option.map_none] at next; cases next
      | some timer =>
        simp only [pending, Option.map_some] at next
        cases next
        obtain ⟨_, _, _, _, _, _, _, _, _, chosen⟩ := CampusTCPTwoProgressTimer.timerDemand_some pending
        change CampusTCPGapProgressMonitor.serves timer actual.event = true at served
        rw [chosen] at served
        split at served
        · have impossible := event.symm.trans ((CampusTCPGapProgressMonitorFacts.serves_tick _ _ _).mp served)
          cases action <;> cases impossible
        · have impossible := event.symm.trans ((CampusTCPGapProgressMonitorFacts.serves_timeout _ _).mp served)
          cases action <;> cases impossible
    · obtain ⟨_, _, same, _⟩ := dropped
      have impossible := event.symm.trans same
      cases action <;> cases impossible
    · obtain ⟨_, _, same, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ free
      have impossible := event.symm.trans same
      cases action <;> cases impossible

private theorem drop_running (active : Active core) (mode : monitor.exchange.forward.mode = .recovery) (id : Nat)
    (selected : M.dropTarget packetCfg current.report.final monitor.exchange.forward id = some target) :
    monitor.exchange.forward.waiting = false := by
  cases waiting : monitor.exchange.forward.waiting with
  | false => rfl
  | true =>
    obtain ⟨ack, retry⟩ := active.waiting waiting
    obtain ⟨lowerDone, upperDone⟩ := active.recovery mode
    simp [M.dropTarget, mode, M.exposedPacket, CampusTCPGapProgressMonitor.nextAction,
      CampusTCPTwoProgressMonitor.Lane.toGap, lowerDone, upperDone, retry, ack] at selected

private theorem action_strict
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (active : Active value.core) (nonoriginal : monitor.exchange.forward.mode ≠ .originals)
    (cap : PendingCap cfg capacity current.report.final monitor) (budget : allowance ≤ 2)
    (positive : 0 < quantum) (capacityPositive : 0 < capacity) (move : Move current actual)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) (action : CampusTCPRoundMonitor.Action)
    (event : actual.event = action.event) :
    R.rank cfg (R.boundSlots cfg capacity allowance) allowance move.after.report.final (W.observe cfg monitor actual) <
      R.rank cfg (R.boundSlots cfg capacity allowance) allowance current.report.final monitor := by
  have mode := active.mode.resolve_left nonoriginal
  have localAllowed := CampusTCPTwoTransferNonoriginal.local_allowed value nonoriginal allowed
  have running := action_running active mode localAllowed action event
  have slots := successor_slots_le value nonoriginal cap budget move allowed
  have time := CampusTCPTwoTransferRecoveryRank.boundSlots_positive cfg capacity allowance positive capacityPositive
  have strict := CampusTCPTwoProgressRecoveryRankWork.action_strict packetCfg _ allowance current.report.final monitor.exchange.forward
    actual mode running (CampusTCPTwoTransferRecoveryRank.active_rank_shape active mode) time slots
    move.supported move.passed (by rw [move.beforeEq]; exact localAllowed) action event
  rw [observed_rank value nonoriginal budget move allowed]
  exact strict

private theorem active_nonclock_strict
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (active : Active value.core) (nonoriginal : monitor.exchange.forward.mode ≠ .originals)
    (cap : PendingCap cfg capacity current.report.final monitor) (budget : allowance ≤ 2)
    (positive : 0 < quantum) (capacityPositive : 0 < capacity) (move : Move current actual)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (nonClock : ∀ actor millis, actual.event ≠ .advanceClock actor millis) :
    R.rank cfg (R.boundSlots cfg capacity allowance) allowance move.after.report.final (W.observe cfg monitor actual) <
      R.rank cfg (R.boundSlots cfg capacity allowance) allowance current.report.final monitor := by
  have mode := active.mode.resolve_left nonoriginal
  obtain ⟨control, drained⟩ := CampusTCPTwoTransferNonoriginal.ordinary value nonoriginal
  cases CampusTCPTwoTransferEvidenceEvents.classify value drained control allowed with
  | send count event => exact action_strict value active nonoriginal cap budget positive capacityPositive move allowed (.send sender count true) event
  | assign index ingress event => exact action_strict value active nonoriginal cap budget positive capacityPositive move allowed (.assign index ingress) event
  | serve ticket event => exact action_strict value active nonoriginal cap budget positive capacityPositive move allowed (.serve ticket) event
  | deliver index bytes event => exact action_strict value active nonoriginal cap budget positive capacityPositive move allowed (.deliver index bytes true) event
  | ack event => exact action_strict value active nonoriginal cap budget positive capacityPositive move allowed (.emitAck sender.other true) event
  | read ready _ => rw [mode] at ready; cases ready
  | clock actor millis event => exact False.elim (nonClock actor millis event)
  | timeout event =>
    have currentAllowed : W.Allowed cfg current.report.final monitor (.timeout sender true) := by rw [← event]; exact allowed
    have waiting := (value.timeout_fields currentAllowed).2.1
    obtain ⟨record⟩ := CampusTCPTwoTransferTimeoutProgress.Step.timeout active waiting budget currentAllowed actual move.beforeEq event
    have decrease := CampusTCPTwoTransferRecoveryRankTimer.timeout_exact active (R.boundSlots cfg capacity allowance) record.value waiting
    rw [record.value.value.move.final, ← move.final] at decrease
    omega
  | drop id event =>
    obtain ⟨target, selected⟩ := value.drop_target (by rw [← event]; exact allowed)
    have localAllowed := CampusTCPTwoTransferNonoriginal.local_allowed value nonoriginal allowed
    have slots := successor_slots_le value nonoriginal cap budget move allowed
    have time := CampusTCPTwoTransferRecoveryRank.boundSlots_positive cfg capacity allowance positive capacityPositive
    obtain ⟨lowerDone, upperDone⟩ := active.recovery mode
    have strict := CampusTCPTwoProgressRecoveryRankWork.observed_drop_strict packetCfg _ allowance current.report.final
      monitor.exchange.forward actual id mode (drop_running active mode id selected)
      (CampusTCPTwoTransferRecoveryRank.active_rank_shape active mode) lowerDone upperDone
      (by rw [move.beforeEq]; exact selected) time slots move.supported move.passed
      (by rw [move.beforeEq]; exact localAllowed) event
    rw [observed_rank value nonoriginal budget move allowed]
    exact strict

private theorem ready_nonclock_strict
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (ready : monitor.exchange.forward.mode = .needRead) (bound : Nat) (move : Move current actual)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (nonClock : ∀ actor millis, actual.event ≠ .advanceClock actor millis) :
    R.rank cfg bound allowance move.after.report.final (W.observe cfg monitor actual) <
      R.rank cfg bound allowance current.report.final monitor := by
  have nonoriginal : monitor.exchange.forward.mode ≠ .originals := by rw [ready]; decide
  have localAllowed := CampusTCPTwoTransferNonoriginal.local_allowed value nonoriginal allowed
  obtain ⟨_, selected | dropped | free, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp localAllowed
  · obtain ⟨demand, pending, served⟩ := selected
    simp only [M.nextDemand, ready] at pending
    cases pending
    have event := (CampusTCPTwoProgressMonitorFacts.serves_operation _ actual.event).mp served
    obtain ⟨read⟩ := value.read_step ready actual move.beforeEq event
    rw [read.value.observed]
    simp only [R.rank, CampusTCPTwoTransferLocatedRead.afterRead, CampusTCPTwoProgressRecoveryRank.rank, ready]
    decide
  · obtain ⟨_, _, _, target⟩ := dropped
    simp only [M.dropTarget, ready] at target
    cases target
  · obtain ⟨actor, millis, event, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ free
    exact False.elim (nonClock actor millis event)

theorem nonclock_strict
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (cap : PendingCap cfg capacity current.report.final monitor)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (nonClock : ∀ actor millis, actual.event ≠ .advanceClock actor millis) :
    R.rank cfg (R.boundSlots cfg capacity allowance) allowance move.after.report.final (W.observe cfg monitor actual) <
      R.rank cfg (R.boundSlots cfg capacity allowance) allowance current.report.final monitor := by
  rcases value with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (nonoriginal state.mode)
  | pending state => exact False.elim (nonoriginal state.mode)
  | active active =>
    exact active_nonclock_strict ⟨_, _, _, .active active, controls, scope, armed, recorded⟩ active nonoriginal
      cap budget positive capacityPositive move allowed nonClock
  | readable core exchange ready sources duplicate mainAck =>
    exact ready_nonclock_strict ⟨_, _, _, .readable core exchange ready sources duplicate mainAck, controls, scope, armed, recorded⟩
      ready _ move allowed nonClock

theorem nonincrease
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (cap : PendingCap cfg capacity current.report.final monitor)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    R.rank cfg (R.boundSlots cfg capacity allowance) allowance move.after.report.final (W.observe cfg monitor actual) ≤
      R.rank cfg (R.boundSlots cfg capacity allowance) allowance current.report.final monitor := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    obtain ⟨clocked⟩ := CampusTCPTwoTransferLocatedClock.Step.clock value.core value.forward.exchange value.forward.not_done
      actual move.beforeEq event (by rw [← event]; exact allowed)
    have decrease := CampusTCPTwoTransferRecoveryRankClock.nonincrease value nonoriginal (R.boundSlots cfg capacity allowance) clocked
    rw [clocked.move.final, ← move.final] at decrease
    exact decrease
  · exact Nat.le_of_lt (nonclock_strict value nonoriginal cap budget positive capacityPositive move allowed
      (fun actor millis same => clock ⟨actor, millis, same⟩))

theorem served_strict
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (cap : PendingCap cfg capacity current.report.final monitor)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (demand : CampusTCPTwoTransferMonitor.Demand) (pending : W.nextDemand cfg current.report.final monitor = some demand)
    (served : W.serves cfg demand actual.event = true) :
    R.rank cfg (R.boundSlots cfg capacity allowance) allowance move.after.report.final (W.observe cfg monitor actual) <
      R.rank cfg (R.boundSlots cfg capacity allowance) allowance current.report.final monitor := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    obtain ⟨clocked⟩ := CampusTCPTwoTransferLocatedClock.Step.clock value.core value.forward.exchange value.forward.not_done
      actual move.beforeEq event (by rw [← event]; exact allowed)
    have decrease := CampusTCPTwoTransferRecoveryRankClockStep.served_strict value nonoriginal (R.boundSlots cfg capacity allowance)
      positive clocked (by rw [← event]; exact allowed) demand pending served
    rw [clocked.move.final, ← move.final] at decrease
    exact decrease
  · exact nonclock_strict value nonoriginal cap budget positive capacityPositive move allowed
      (fun actor millis same => clock ⟨actor, millis, same⟩)

theorem persistent
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (cap : PendingCap cfg capacity current.report.final monitor)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (equal : R.rank cfg (R.boundSlots cfg capacity allowance) allowance move.after.report.final (W.observe cfg monitor actual) =
      R.rank cfg (R.boundSlots cfg capacity allowance) allowance current.report.final monitor)
    (demand : CampusTCPTwoTransferMonitor.Demand) (pending : W.nextDemand cfg current.report.final monitor = some demand) :
    W.nextDemand cfg move.after.report.final (W.observe cfg monitor actual) = some demand := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    obtain ⟨clocked⟩ := CampusTCPTwoTransferLocatedClock.Step.clock value.core value.forward.exchange value.forward.not_done
      actual move.beforeEq event (by rw [← event]; exact allowed)
    have atClock : R.rank cfg (R.boundSlots cfg capacity allowance) allowance clocked.move.after.report.final (W.observe cfg monitor actual) =
        R.rank cfg (R.boundSlots cfg capacity allowance) allowance current.report.final monitor := by
      rw [clocked.move.final, ← move.final]
      exact equal
    have same := CampusTCPTwoTransferRecoveryRankClockStep.equal_pending value nonoriginal (R.boundSlots cfg capacity allowance)
      positive clocked (by rw [← event]; exact allowed) atClock
    rw [clocked.move.final, ← move.final] at same
    exact same.trans pending
  · have strict := nonclock_strict value nonoriginal cap budget positive capacityPositive move allowed
      (fun actor millis same => clock ⟨actor, millis, same⟩)
    rw [equal] at strict
    exact False.elim (Nat.lt_irrefl _ strict)

end Netlib.Check.CampusTCPTwoTransferRecoveryRankStep
