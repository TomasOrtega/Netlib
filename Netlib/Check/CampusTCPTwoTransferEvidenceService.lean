import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoTransferServiceProgress
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase

/-!
# Ordinary service on the same recorded transfer trace

Current typed work identifies the supplied service ticket.
Its actual service retains the located phase and recorded history.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferWork (DataWork OriginalLane RetryLane AckWork AckState)
open CampusTCPTwoTransferPaths (DataTicket AckTicket)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoProgressReadWriter (SelectedOutput)

namespace L
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand nextDemand laneDemand servesOption serves)
end L
namespace G
export CampusTCPGapProgressMonitor (Demand nextAction serves)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (phase_beq_false servesOption_iff serves_originalChoice)
end F
namespace V
export CampusTCPTwoTransferLocatedService (DataServiced AckServiced lower_at upper_at retry_at ack_at)
end V
namespace Q
export CampusTCPTwoTransferServiceProgress (active_lower active_upper active_retry active_ack)
end Q

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {ticket : Nat}
variable {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "localCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at
    (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)

private theorem ordinary_service (allowed : W.Allowed cfg current.report.final monitor (.serve ticket none))
    (drainless : W.drainTicket current.report.final monitor = none) : W.controlDemand monitor = none := by
  by_cases invalid : monitor.mode = .invalid
  · simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  · cases selected : W.controlDemand monitor with
    | none => rfl
    | some kind =>
      cases kind <;> simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drainless, selected,
        CampusTCPTwoTransferMonitor.Control.serves] at allowed

private theorem served_demand (allowed : CampusTCPTwoProgressMonitor.Allowed localCfg current.report.final
    monitor.exchange.forward (.serve ticket none)) :
    ∃ demand, L.nextDemand localCfg current.report.final monitor.exchange.forward = some demand ∧
      L.serves demand (.serve ticket none) = true := by
  obtain ⟨_, chosen | dropped | clocked, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
  · exact chosen
  · obtain ⟨_, _, impossible, _⟩ := dropped
    cases impossible
  · obtain ⟨_, _, impossible, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ clocked
    cases impossible

private theorem served_lane {lane : L.Lane} {demand : G.Demand}
    (next : L.laneDemand localCfg current.report.final monitor.exchange.forward lane = some demand)
    (served : G.serves demand (.serve ticket none) = true) :
    G.nextAction (localCfg).toConfig current.report.final lane.toGap = some (.serve ticket) := by
  obtain ⟨action, next, kind⟩ := CampusTCPTwoProgressMonitorFacts.laneDemand_action _ _ _ _ next
  have event : Event.serve ticket none = action.event := by
    rcases kind with operation | ⟨id, resolution⟩
    · exact (CampusTCPGapProgressMonitorFacts.serves_operation action _).mp (operation ▸ served)
    · rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action id _).mp (resolution ▸ served) with event | impossible
      · exact event
      · cases impossible
  have same := congrArg CampusTCPRoundMonitor.actionOf event
  rw [CampusTCPRoundMonitor.Action.actionOf_event] at same
  have actionEq : CampusTCPRoundMonitor.Action.serve ticket = action := Option.some.inj same
  rwa [← actionEq] at next

private theorem timer_not_service {demand : G.Demand}
    (next : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final = some demand)
    (served : G.serves demand (.serve ticket none) = true) : False := by
  obtain ⟨recovery, head, rest, deadline, target, _, _, _, _, selected⟩ := CampusTCPTwoProgressTimer.timerDemand_some next
  by_cases early : recovery.now < target
  · rw [ite_eq_left early] at selected
    have impossible := (CampusTCPGapProgressMonitorFacts.serves_tick _ _ _).mp (selected ▸ served)
    cases impossible
  · rw [ite_eq_right early] at selected
    have impossible := (CampusTCPGapProgressMonitorFacts.serves_timeout _ _).mp (selected ▸ served)
    cases impossible

private inductive ServiceSelection (config : L.Config) (state : State input) (monitor : L.Monitor) (ticket : Nat) : Prop where
  | lower (mode : monitor.mode = .originals) (ack : monitor.ack = none)
      (next : G.nextAction config.toConfig state monitor.lower.toGap = some (.serve ticket))
  | upper (mode : monitor.mode = .originals) (ack : monitor.ack = none)
      (next : G.nextAction config.toConfig state monitor.upper.toGap = some (.serve ticket))
  | ack (lane : L.Lane) (pending : monitor.ack = some lane)
      (next : G.nextAction config.toConfig state lane.toGap = some (.serve ticket))
  | retry (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = false)
      (next : G.nextAction config.toConfig state monitor.retry.toGap = some (.serve ticket))

private theorem service_selection (active : Active core)
    (allowed : CampusTCPTwoProgressMonitor.Allowed localCfg current.report.final monitor.exchange.forward (.serve ticket none)) :
    ServiceSelection localCfg current.report.final monitor.exchange.forward ticket := by
  obtain ⟨demand, next, served⟩ := served_demand allowed
  have first := active.lower_not_needSend
  have second := active.upper_not_needSend
  rcases active.mode with mode | mode
  · have selected := next
    simp only [L.nextDemand, mode, (F.phase_beq_false _ _).mpr first, (F.phase_beq_false _ _).mpr second,
      Bool.false_eq_true, ite_false] at selected
    cases ack : monitor.exchange.forward.ack with
    | some lane =>
      simp only [ack] at selected
      cases pending : L.laneDemand localCfg current.report.final monitor.exchange.forward lane with
      | none => simp only [pending, Option.map_none] at selected; cases selected
      | some chosen =>
        have same : (.single chosen : L.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
        subst demand
        exact .ack lane ack (served_lane pending served)
    | none =>
      simp only [ack] at selected
      split at selected
      · have same := Option.some.inj selected
        subst demand
        rcases (F.serves_originalChoice _ _ _).mp served with lower | upper
        · obtain ⟨_, pending, served⟩ := (F.servesOption_iff _ _).mp lower
          exact .lower mode ack (served_lane pending served)
        · obtain ⟨_, pending, served⟩ := (F.servesOption_iff _ _).mp upper
          exact .upper mode ack (served_lane pending served)
      · cases selected
  · have selected := next
    simp only [L.nextDemand, mode] at selected
    cases ack : monitor.exchange.forward.ack with
    | some lane =>
      simp only [ack] at selected
      cases pending : L.laneDemand localCfg current.report.final monitor.exchange.forward lane with
      | none => simp only [pending, Option.map_none] at selected; cases selected
      | some chosen =>
        have same : (.single chosen : L.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
        subst demand
        exact .ack lane ack (served_lane pending served)
    | none =>
      simp only [ack] at selected
      cases waiting : monitor.exchange.forward.waiting with
      | false =>
        simp only [waiting, Bool.false_eq_true, ite_false] at selected
        cases pending : L.laneDemand localCfg current.report.final monitor.exchange.forward monitor.exchange.forward.retry with
        | none => simp only [pending, Option.map_none] at selected; cases selected
        | some chosen =>
          have same : (.single chosen : L.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
          subst demand
          exact .retry mode ack waiting (served_lane pending served)
      | true =>
        simp only [waiting, ite_true] at selected
        cases pending : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final with
        | none => simp only [pending, Option.map_none] at selected; cases selected
        | some chosen =>
          have same : (.single chosen : L.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
          subst demand
          exact False.elim (timer_not_service pending served)

private theorem data_ticket {part : CampusTCPTwoProgressSender.Part} {lane : L.Lane}
    (work : DataWork initial checks current core.live.gatewayState part lane)
    (next : G.nextAction (localCfg).toConfig current.report.final lane.toGap = some (.serve ticket)) :
    ∃ path : DataTicket initial checks current part lane,
      ∃ _source : SelectedOutput initial current path.output.produced,
        path.assignedGateway = location ∧ path.ticket.id = ticket := by
  have same := Option.some.inj ((work.command_next localCfg).symm.trans next)
  cases work with
  | ingress path _ => cases same
  | ticket path selected source => exact ⟨path, source, selected, CampusTCPRoundMonitor.Action.serve.inj same⟩
  | link path _ _ => cases same

private theorem ack_ticket {lane : L.Lane} (work : AckWork checks core.live lane)
    (next : G.nextAction (localCfg).toConfig current.report.final lane.toGap = some (.serve ticket)) :
    ∃ path : AckTicket initial checks current (received.bytes lower upper).length lane,
      path.assignedGateway = location ∧ path.ticket.id = ticket := by
  have same := Option.some.inj ((work.command_next localCfg).symm.trans next)
  cases work with
  | pending phase queue => cases same
  | ingress path => cases same
  | ticket path selected => exact ⟨path, selected, CampusTCPRoundMonitor.Action.serve.inj same⟩
  | link path => cases same

private theorem original_ticket {part : CampusTCPTwoProgressSender.Part} {lane : L.Lane}
    (work : OriginalLane initial checks current core.live.gatewayState received part lane)
    (next : G.nextAction (localCfg).toConfig current.report.final lane.toGap = some (.serve ticket)) :
    ∃ path : DataTicket initial checks current part lane,
      ∃ _source : SelectedOutput initial current path.output.produced,
        path.assignedGateway = location ∧ path.ticket.id = ticket := by
  cases work with
  | active work _ => exact data_ticket work next
  | done phase => simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next; cases next

private theorem retry_ticket {lane : L.Lane}
    (work : RetryLane initial checks current core.live.gatewayState sent lane)
    (next : G.nextAction (localCfg).toConfig current.report.final lane.toGap = some (.serve ticket)) :
    ∃ part head rest, CampusTCPTwoProgressRetry.HeadRange sent part head rest ∧
      ∃ path : DataTicket initial checks current part lane,
        ∃ _source : SelectedOutput initial current path.output.produced,
          path.assignedGateway = location ∧ path.ticket.id = ticket := by
  cases work with
  | active part head rest selected work =>
    obtain ⟨path, source, located, id⟩ := data_ticket work next
    exact ⟨part, head, rest, selected, path, source, located, id⟩
  | done phase => simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next; cases next

private def extend_service
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (move : CampusTCPRoundPhaseBase.Move current actual)
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper move.after (W.observe cfg monitor actual)
      location evidence.sent evidence.received) (active : Active next)
    (controls : C.Phase move.after.report.final (W.observe cfg monitor actual).mode location)
    (mode : (W.observe cfg monitor actual).mode = monitor.mode)
    (forwardMode : (W.observe cfg monitor actual).exchange.forward.mode = monitor.exchange.forward.mode)
    (ordinary : W.controlDemand monitor = none) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    Advanced evidence actual := {
  move, location
  next := {
    sent := evidence.sent, received := evidence.received, core := next, forward := .active active, controls
    scope := by
      intro unarmed unfinished
      rcases evidence.controls.ordinary_modes ordinary with armed | finished
      · exact False.elim (unarmed (mode.trans armed))
      · exact False.elim (unfinished (mode.trans finished))
    armed := fun armed => forwardMode.trans (evidence.armed (mode.symm ▸ armed))
    recorded := evidence.recorded.snoc move allowed } }

private theorem active_service_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (active : Active evidence.core) (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .serve ticket none) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (drainless : W.drainTicket current.report.final monitor = none) : Nonempty (Advanced evidence actual) := by
  have canonicalAllowed : W.Allowed cfg current.report.final monitor (.serve ticket none) := by rw [← event]; exact allowed
  have control := ordinary_service canonicalAllowed drainless
  have ordinary := evidence.controls.ordinary_modes control
  have localAllowed := CampusTCPTwoTransferServiceObserve.local_allowed ordinary control active.exchange canonicalAllowed
  cases service_selection active localAllowed with
  | lower mode ack next =>
    obtain ⟨path, source, selected, id⟩ := original_ticket active.lowerLane next
    have pathAllowed : W.Allowed cfg current.report.final monitor (.serve path.ticket.id none) := by rw [id]; exact canonicalAllowed
    obtain ⟨chosen, ⟨value⟩⟩ := V.lower_at evidence.core active evidence.controls ordinary path selected source pathAllowed mode ack
    have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
      (value.value.value.move.beforeEq.trans before.symm) (by rw [value.value.value.facts.event, id, event])
    exact same ▸ ⟨extend_service evidence value.value.value.move value.next (Q.active_lower active value mode ack)
      (CampusTCPTwoTransferServiceProgress.DataServiced.phase value evidence.controls ordinary selected)
      (by rw [value.observed]; rfl) (by rw [value.observed]; rfl) control
      (by rw [value.value.value.facts.event]; exact pathAllowed)⟩
  | upper mode ack next =>
    obtain ⟨path, source, selected, id⟩ := original_ticket active.upperLane next
    have pathAllowed : W.Allowed cfg current.report.final monitor (.serve path.ticket.id none) := by rw [id]; exact canonicalAllowed
    obtain ⟨chosen, ⟨value⟩⟩ := V.upper_at evidence.core active evidence.controls ordinary path selected source pathAllowed mode ack
    have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
      (value.value.value.move.beforeEq.trans before.symm) (by rw [value.value.value.facts.event, id, event])
    exact same ▸ ⟨extend_service evidence value.value.value.move value.next (Q.active_upper active value mode ack)
      (CampusTCPTwoTransferServiceProgress.DataServiced.phase value evidence.controls ordinary selected)
      (by rw [value.observed]; rfl) (by rw [value.observed]; rfl) control
      (by rw [value.value.value.facts.event]; exact pathAllowed)⟩
  | retry mode ack waiting next =>
    obtain ⟨part, head, rest, headRange, path, source, selected, id⟩ := retry_ticket active.retry next
    have pathAllowed : W.Allowed cfg current.report.final monitor (.serve path.ticket.id none) := by rw [id]; exact canonicalAllowed
    obtain ⟨chosen, ⟨value⟩⟩ := V.retry_at evidence.core active evidence.controls ordinary path selected source pathAllowed mode ack waiting
    have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
      (value.value.value.move.beforeEq.trans before.symm) (by rw [value.value.value.facts.event, id, event])
    exact same ▸ ⟨extend_service evidence value.value.value.move value.next
      (Q.active_retry active value mode ack head rest headRange)
      (CampusTCPTwoTransferServiceProgress.DataServiced.phase value evidence.controls ordinary selected)
      (by rw [value.observed]; rfl) (by rw [value.observed]; rfl) control
      (by rw [value.value.value.facts.event]; exact pathAllowed)⟩
  | ack lane pending next =>
    have currentAck : AckWork checks evidence.core.live lane := by simpa only [AckState, pending] using active.ack
    obtain ⟨path, selected, id⟩ := ack_ticket currentAck next
    have pathAllowed : W.Allowed cfg current.report.final monitor (.serve path.ticket.id none) := by rw [id]; exact canonicalAllowed
    obtain ⟨chosen, ⟨value⟩⟩ := V.ack_at evidence.core active evidence.controls ordinary path selected pathAllowed pending
    have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
      (value.value.value.move.beforeEq.trans before.symm) (by rw [value.value.value.facts.event, id, event])
    exact same ▸ ⟨extend_service evidence value.value.value.move value.next (Q.active_ack active value pending)
      (CampusTCPTwoTransferServiceProgress.AckServiced.phase value evidence.controls ordinary selected)
      (by rw [value.observed]; rfl) (by rw [value.observed]; rfl) control
      (by rw [value.value.value.facts.event]; exact pathAllowed)⟩

theorem Evidence.service_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .serve ticket none)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (drainless : W.drainTicket current.report.final monitor = none) : Nonempty (Advanced evidence actual) := by
  have canonicalAllowed : W.Allowed cfg current.report.final monitor (.serve ticket none) := by rw [← event]; exact allowed
  have control := ordinary_service canonicalAllowed drainless
  have ordinary := evidence.controls.ordinary_modes control
  have localAllowed := CampusTCPTwoTransferServiceObserve.local_allowed ordinary control evidence.forward.exchange canonicalAllowed
  obtain ⟨demand, next, served⟩ := served_demand localAllowed
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    simp only [L.nextDemand, state.mode, state.lowerPending,
      show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.serve ticket none)).mp served
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
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.serve ticket none)).mp served
    cases impossible
  | active state =>
    exact active_service_step ⟨_, _, _, .active state, controls, scope, armed, recorded⟩ state actual before event allowed drainless
  | readable core exchange mode sources _ _ =>
    simp only [L.nextDemand, mode] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.serve ticket none)).mp served
    cases impossible

end Netlib.Check.CampusTCPTwoTransferEvidence
