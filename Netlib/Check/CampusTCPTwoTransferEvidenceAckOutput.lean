import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoTransferAckOutputProgress

/-!
# The selected actual ACK output extends current evidence

Current typed ACK work supplies the queued response.
The same recorded step retains every unselected data path.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferWork (DataWork OriginalLane RetryLane AckWork AckState)

namespace L
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand nextDemand laneDemand servesOption serves)
end L
namespace G
export CampusTCPGapProgressMonitor (Demand nextAction serves)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (phase_beq_false servesOption_iff serves_originalChoice)
end F
namespace O
export CampusTCPTwoTransferAckOutputProgress (AckSent allowed_output)
end O

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input}
variable {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "localCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at
    (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)

private theorem output_demand (allowed : CampusTCPTwoProgressMonitor.Allowed localCfg current.report.final
    monitor.exchange.forward (.emitAck sender.other true)) :
    ∃ demand, L.nextDemand localCfg current.report.final monitor.exchange.forward = some demand ∧
      L.serves demand (.emitAck sender.other true) = true := by
  obtain ⟨_, chosen | dropped | clocked, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
  · exact chosen
  · obtain ⟨_, _, impossible, _⟩ := dropped
    cases impossible
  · obtain ⟨_, _, impossible, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ clocked
    cases impossible

private theorem output_action {lane : L.Lane} {demand : G.Demand}
    (next : L.laneDemand localCfg current.report.final monitor.exchange.forward lane = some demand)
    (served : G.serves demand (.emitAck sender.other true) = true) :
    ∃ action, G.nextAction (localCfg).toConfig current.report.final lane.toGap = some action ∧
      Event.emitAck sender.other true = action.event := by
  obtain ⟨action, next, kind⟩ := CampusTCPTwoProgressMonitorFacts.laneDemand_action _ _ _ _ next
  refine ⟨action, next, ?_⟩
  rcases kind with operation | ⟨id, resolution⟩
  · exact (CampusTCPGapProgressMonitorFacts.serves_operation action _).mp (operation ▸ served)
  · rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action id _).mp (resolution ▸ served) with selected | impossible
    · exact selected
    · cases impossible

private theorem data_not_output {part : CampusTCPTwoProgressSender.Part} {lane : L.Lane}
    (work : DataWork initial checks current core.live.gatewayState part lane) :
    L.servesOption (L.laneDemand localCfg current.report.final monitor.exchange.forward lane) (.emitAck sender.other true) = false := by
  apply Bool.eq_false_iff.mpr
  intro served
  obtain ⟨_, next, served⟩ := (F.servesOption_iff _ _).mp served
  obtain ⟨action, next, event⟩ := output_action next served
  have same := Option.some.inj (next.symm.trans (work.command_next localCfg))
  rw [same] at event
  cases underlying : work.work with
  | ingress path =>
    simp only [CampusTCPTwoTransferWork.DataWork.command, underlying, CampusTCPTwoTransferWork.Work.command,
      CampusTCPRoundMonitor.Action.event] at event
    cases event
  | ticket path _ =>
    simp only [CampusTCPTwoTransferWork.DataWork.command, underlying, CampusTCPTwoTransferWork.Work.command,
      CampusTCPRoundMonitor.Action.event] at event
    cases event
  | link path =>
    simp only [CampusTCPTwoTransferWork.DataWork.command, underlying, CampusTCPTwoTransferWork.Work.command,
      CampusTCPRoundMonitor.Action.event] at event
    cases event

private theorem original_not_output {part : CampusTCPTwoProgressSender.Part} {lane : L.Lane}
    (work : OriginalLane initial checks current core.live.gatewayState received part lane) :
    L.servesOption (L.laneDemand localCfg current.report.final monitor.exchange.forward lane) (.emitAck sender.other true) = false := by
  cases work with
  | active work _ => exact data_not_output work
  | done phase => simp only [L.laneDemand, G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase,
      bind, Option.bind, L.servesOption]

private theorem retry_not_output {lane : L.Lane}
    (work : RetryLane initial checks current core.live.gatewayState sent lane) :
    L.servesOption (L.laneDemand localCfg current.report.final monitor.exchange.forward lane) (.emitAck sender.other true) = false := by
  cases work with
  | active _ _ _ _ work => exact data_not_output work
  | done phase => simp only [L.laneDemand, G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase,
      bind, Option.bind, L.servesOption]

private theorem timer_not_output {demand : G.Demand}
    (next : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final = some demand)
    (served : G.serves demand (.emitAck sender.other true) = true) : False := by
  obtain ⟨recovery, head, rest, deadline, target, _, _, _, _, selected⟩ := CampusTCPTwoProgressTimer.timerDemand_some next
  by_cases early : recovery.now < target
  · rw [ite_eq_left early] at selected
    have impossible := (CampusTCPGapProgressMonitorFacts.serves_tick _ _ _).mp (selected ▸ served)
    cases impossible
  · rw [ite_eq_right early] at selected
    have impossible := (CampusTCPGapProgressMonitorFacts.serves_timeout _ _).mp (selected ▸ served)
    cases impossible

private theorem ack_pending {lane : L.Lane} {demand : G.Demand} (work : AckWork checks core.live lane)
    (next : L.laneDemand localCfg current.report.final monitor.exchange.forward lane = some demand)
    (served : G.serves demand (.emitAck sender.other true) = true) :
    lane.phase = .needAck ∧ core.live.receiverFacts.reaction.work.pending ≠ [] := by
  obtain ⟨action, next, event⟩ := output_action next served
  have same := Option.some.inj (next.symm.trans (work.command_next localCfg))
  rw [same] at event
  cases work with
  | pending phase queue => exact ⟨phase, queue⟩
  | ingress path => cases event
  | ticket path _ => cases event
  | link path => cases event

private theorem current_ack (active : Active core)
    (allowed : CampusTCPTwoProgressMonitor.Allowed localCfg current.report.final monitor.exchange.forward (.emitAck sender.other true)) :
    ∃ lane, monitor.exchange.forward.ack = some lane ∧ lane.phase = .needAck ∧
      core.live.receiverFacts.reaction.work.pending ≠ [] := by
  obtain ⟨demand, next, served⟩ := output_demand allowed
  have first := active.lower_not_needSend
  have second := active.upper_not_needSend
  cases ack : monitor.exchange.forward.ack with
  | some lane =>
    have selected := next
    rcases active.mode with mode | mode
    all_goals simp only [L.nextDemand, mode, (F.phase_beq_false _ _).mpr first, (F.phase_beq_false _ _).mpr second,
      Bool.false_eq_true, ite_false, ack] at selected
    all_goals cases pending : L.laneDemand localCfg current.report.final monitor.exchange.forward lane with
      | none => simp only [pending, Option.map_none] at selected; cases selected
      | some chosen =>
        have same : (.single chosen : L.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
        subst demand
        have current : AckWork checks core.live lane := by simpa only [AckState, ack] using active.ack
        exact ⟨lane, rfl, ack_pending current pending served⟩
  | none =>
    rcases active.mode with mode | mode
    · have selected := next
      simp only [L.nextDemand, mode, (F.phase_beq_false _ _).mpr first, (F.phase_beq_false _ _).mpr second,
        Bool.false_eq_true, ite_false, ack] at selected
      split at selected
      · have same := Option.some.inj selected
        subst demand
        rcases (F.serves_originalChoice _ _ _).mp served with lower | upper
        · rw [original_not_output active.lowerLane] at lower
          cases lower
        · rw [original_not_output active.upperLane] at upper
          cases upper
      · cases selected
    · have selected := next
      simp only [L.nextDemand, mode, ack] at selected
      cases waiting : monitor.exchange.forward.waiting with
      | false =>
        simp only [waiting, Bool.false_eq_true, ite_false] at selected
        cases pending : L.laneDemand localCfg current.report.final monitor.exchange.forward monitor.exchange.forward.retry with
        | none => simp only [pending, Option.map_none] at selected; cases selected
        | some chosen =>
          have same : (.single chosen : L.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
          subst demand
          have served : L.servesOption (L.laneDemand localCfg current.report.final monitor.exchange.forward monitor.exchange.forward.retry)
              (.emitAck sender.other true) = true := by rw [pending]; exact served
          rw [retry_not_output active.retry] at served
          cases served
      | true =>
        simp only [waiting, ite_true] at selected
        cases pending : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final with
        | none => simp only [pending, Option.map_none] at selected; cases selected
        | some chosen =>
          have same : (.single chosen : L.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
          subst demand
          exact False.elim (timer_not_output pending served)

private theorem active_output_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (active : Active evidence.core) (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .emitAck sender.other true) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    Nonempty (Advanced evidence actual) := by
  have canonicalAllowed : W.Allowed cfg current.report.final monitor (.emitAck sender.other true) := by rw [← event]; exact allowed
  obtain ⟨_, control⟩ := O.allowed_output canonicalAllowed
  have ordinary := evidence.controls.ordinary_modes control
  have localAllowed := CampusTCPTwoTransferServiceObserve.local_allowed ordinary control active.exchange canonicalAllowed
  obtain ⟨lane, selected, phase, pending⟩ := current_ack active localAllowed
  obtain ⟨value⟩ := CampusTCPTwoTransferAckOutputProgress.Step.emit_ack evidence.core active evidence.controls
    selected phase pending canonicalAllowed actual before event
  have nextMode := congrArg (fun whole : W.Monitor => whole.mode) value.observed
  have forwardMode := congrArg (fun whole : W.Monitor => whole.exchange.forward.mode) value.observed
  exact ⟨{
    move := value.value.move, location
    next := {
      sent := evidence.sent, received := evidence.received, core := value.next, forward := .active (value.active active selected)
      controls := value.phase evidence.controls
      scope := by
        intro unarmed unfinished
        rcases ordinary with armed | finished
        · exact False.elim (unarmed (nextMode.trans armed))
        · exact False.elim (unfinished (nextMode.trans finished))
      armed := fun armed => forwardMode.trans (evidence.armed (nextMode.symm ▸ armed))
      recorded := evidence.recorded.snoc value.value.move allowed } }⟩

theorem Evidence.ack_output_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .emitAck sender.other true)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced evidence actual) := by
  have canonicalAllowed : W.Allowed cfg current.report.final monitor (.emitAck sender.other true) := by rw [← event]; exact allowed
  obtain ⟨_, control⟩ := O.allowed_output canonicalAllowed
  have ordinary := evidence.controls.ordinary_modes control
  have localAllowed := CampusTCPTwoTransferServiceObserve.local_allowed ordinary control evidence.forward.exchange canonicalAllowed
  obtain ⟨demand, next, served⟩ := output_demand localAllowed
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    simp only [L.nextDemand, state.mode, state.lowerPending,
      show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.emitAck sender.other true)).mp served
    cases impossible
  | pending state =>
    have lowerNotPending : monitor.exchange.forward.lower.phase ≠ .needSend := by
      rcases state.lowerPath.phase with atIngress | done
      · rw [atIngress]; decide
      · rw [done]; decide
    simp only [L.nextDemand, state.mode, (F.phase_beq_false _ _).mpr lowerNotPending, Bool.false_eq_true, ite_false,
      state.upperPending, show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.emitAck sender.other true)).mp served
    cases impossible
  | active state => exact active_output_step ⟨_, _, _, .active state, controls, scope, armed, recorded⟩ state actual before event allowed
  | readable core exchange mode sources _ _ =>
    simp only [L.nextDemand, mode] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.emitAck sender.other true)).mp served
    cases impossible

end Netlib.Check.CampusTCPTwoTransferEvidence
