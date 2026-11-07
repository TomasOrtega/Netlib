import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoTransferAssignProgress

/-!
# Actual assignment steps extend the same transfer evidence

The current selector identifies one typed ingress path. Current lifecycle facts
select primary or standby routing before the same supplied step is enabled.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferWork (DataWork OriginalLane RetryLane AckWork AckState)
open CampusTCPTwoTransferPaths (DataIngress AckIngress)
open CampusTCPTwoProgressPhaseBase (Arrived)

namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand Allowed nextDemand laneDemand servesOption)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand nextAction serves)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff freeClock_event phase_beq_false laneDemand_action
  serves_operation serves_resolution serves_timeout serves_tick servesOption_iff serves_originalChoice)
end F
namespace N
export CampusTCPTwoTransferLocatedAssign (allowed_assign)
end N
namespace P
export CampusTCPTwoTransferAssignProgress (active_lower active_upper active_retry active_ack)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {index : Nat} {ingress : I.InterfaceRef}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : R.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {localCfg : M.Config} {demand : M.Demand} {laneDemand : G.Demand} {lane : M.Lane}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "forwardCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)

private theorem assigned_demand (allowed : M.Allowed localCfg current.report.final monitor.exchange.forward (.assign index ingress)) :
    ∃ demand, M.nextDemand localCfg current.report.final monitor.exchange.forward = some demand ∧
      CampusTCPTwoProgressMonitor.serves demand (.assign index ingress) = true := by
  obtain ⟨_, chosen | dropped | clocked, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
  · exact chosen
  · obtain ⟨_, _, impossible, _⟩ := dropped
    cases impossible
  · obtain ⟨_, _, impossible, _⟩ := F.freeClock_event _ _ _ _ clocked
    cases impossible

private inductive AssignmentSelection (config : M.Config) (state : State input)
    (monitor : M.Monitor) (index : Nat) (ingress : I.InterfaceRef) : Prop where
  | lower (demand : G.Demand) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
      (selected : M.laneDemand config state monitor monitor.lower = some demand)
      (served : G.serves demand (.assign index ingress) = true)
  | upper (demand : G.Demand) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
      (first : M.servesOption (M.laneDemand config state monitor monitor.lower) (.assign index ingress) = false)
      (selected : M.laneDemand config state monitor monitor.upper = some demand)
      (served : G.serves demand (.assign index ingress) = true)
  | ack (lane : M.Lane) (demand : G.Demand) (pending : monitor.ack = some lane)
      (selected : M.laneDemand config state monitor lane = some demand)
      (served : G.serves demand (.assign index ingress) = true)
  | retry (demand : G.Demand) (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = false)
      (selected : M.laneDemand config state monitor monitor.retry = some demand)
      (served : G.serves demand (.assign index ingress) = true)

private theorem timer_not_assign
    (pending : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final = some laneDemand)
    (served : G.serves laneDemand (.assign index ingress) = true) : False := by
  obtain ⟨recovery, head, rest, deadline, target, _, _, _, _, demand⟩ := CampusTCPTwoProgressTimer.timerDemand_some pending
  by_cases early : recovery.now < target
  · rw [ite_eq_left early] at demand
    have impossible := (CampusTCPGapProgressMonitorFacts.serves_tick _ _ (.assign index ingress)).mp (demand ▸ served)
    cases impossible
  · rw [ite_eq_right early] at demand
    have impossible := (CampusTCPGapProgressMonitorFacts.serves_timeout _ (.assign index ingress)).mp (demand ▸ served)
    cases impossible

private theorem assignment_selection (active : Active core)
    (next : M.nextDemand localCfg current.report.final monitor.exchange.forward = some demand)
    (served : CampusTCPTwoProgressMonitor.serves demand (.assign index ingress) = true) :
    AssignmentSelection localCfg current.report.final monitor.exchange.forward index ingress := by
  have first := active.lower_not_needSend
  have second := active.upper_not_needSend
  rcases active.mode with mode | mode
  · have selected := next
    simp only [M.nextDemand, mode, (F.phase_beq_false _ _).mpr first, (F.phase_beq_false _ _).mpr second,
      Bool.false_eq_true, ite_false] at selected
    cases ack : monitor.exchange.forward.ack with
    | some lane =>
      simp only [ack] at selected
      cases pending : M.laneDemand localCfg current.report.final monitor.exchange.forward lane with
      | none => simp only [pending, Option.map_none] at selected; cases selected
      | some chosen =>
        have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
        subst demand
        exact .ack lane chosen ack pending served
    | none =>
      simp only [ack] at selected
      split at selected
      · have same := Option.some.inj selected
        subst demand
        have choices := (F.serves_originalChoice _ _ _).mp served
        by_cases lower : M.servesOption (M.laneDemand localCfg current.report.final monitor.exchange.forward monitor.exchange.forward.lower)
            (.assign index ingress) = true
        · obtain ⟨chosen, pending, served⟩ := (F.servesOption_iff _ _).mp lower
          exact .lower chosen mode ack pending served
        · obtain ⟨chosen, pending, served⟩ := (F.servesOption_iff _ _).mp (choices.resolve_left lower)
          exact .upper chosen mode ack (Bool.eq_false_iff.mpr lower) pending served
      · cases selected
  · have selected := next
    simp only [M.nextDemand, mode] at selected
    cases ack : monitor.exchange.forward.ack with
    | some lane =>
      simp only [ack] at selected
      cases pending : M.laneDemand localCfg current.report.final monitor.exchange.forward lane with
      | none => simp only [pending, Option.map_none] at selected; cases selected
      | some chosen =>
        have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
        subst demand
        exact .ack lane chosen ack pending served
    | none =>
      simp only [ack] at selected
      cases waiting : monitor.exchange.forward.waiting with
      | false =>
        simp only [waiting, Bool.false_eq_true, ite_false] at selected
        cases pending : M.laneDemand localCfg current.report.final monitor.exchange.forward monitor.exchange.forward.retry with
        | none => simp only [pending, Option.map_none] at selected; cases selected
        | some chosen =>
          have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
          subst demand
          exact .retry chosen mode ack waiting pending served
      | true =>
        simp only [waiting, ite_true] at selected
        cases pending : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final with
        | none => simp only [pending, Option.map_none] at selected; cases selected
        | some chosen =>
          have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
          subst demand
          exact False.elim (timer_not_assign pending served)

private theorem assignment_action
    (selected : M.laneDemand localCfg current.report.final monitor.exchange.forward lane = some laneDemand)
    (served : G.serves laneDemand (.assign index ingress) = true) :
    ∃ action, G.nextAction localCfg.toConfig current.report.final lane.toGap = some action ∧
      Event.assign index ingress = action.event := by
  obtain ⟨action, next, operation | ⟨id, resolution⟩⟩ := F.laneDemand_action _ _ _ _ selected
  · exact ⟨action, next, (CampusTCPGapProgressMonitorFacts.serves_operation action (.assign index ingress)).mp (operation ▸ served)⟩
  · rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action id (.assign index ingress)).mp (resolution ▸ served) with same | impossible
    · exact ⟨action, next, same⟩
    · cases impossible

private theorem original_ingress {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    {part : CampusTCPTwoProgressSender.Part} (work : OriginalLane initial checks current view received part lane)
    (selected : M.laneDemand localCfg current.report.final monitor.exchange.forward lane = some laneDemand)
    (served : G.serves laneDemand (.assign index ingress) = true) :
    ∃ path : DataIngress initial current part lane,
      Event.assign index ingress = .assign path.output.index (localCfg.toConfig.ingress localCfg.sender) := by
  obtain ⟨action, next, event⟩ := assignment_action selected served
  cases work with
  | active work _ =>
    cases work with
    | ingress path _ =>
      rw [path.action localCfg] at next
      have same := Option.some.inj next
      subst action
      exact ⟨path, event⟩
    | ticket path _ _ => rw [path.action localCfg] at next; cases Option.some.inj next; cases event
    | link path _ _ => rw [path.action localCfg] at next; cases Option.some.inj next; cases event
  | done phase => simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next; cases next

private theorem ack_ingress (work : AckWork checks core.live lane)
    (selected : M.laneDemand localCfg current.report.final monitor.exchange.forward lane = some laneDemand)
    (served : G.serves laneDemand (.assign index ingress) = true) :
    ∃ path : AckIngress initial current (received.bytes lower upper).length lane,
      Event.assign index ingress = .assign path.output.index (localCfg.toConfig.ingress localCfg.sender.other) := by
  obtain ⟨action, next, event⟩ := assignment_action selected served
  have command := work.command_next localCfg
  have same := Option.some.inj (command.symm.trans next)
  subst action
  cases work with
  | pending phase _ => cases event
  | ingress path => exact ⟨path, event⟩
  | ticket path _ => cases event
  | link path => cases event

private theorem retry_ingress {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    (work : RetryLane initial checks current view sent lane)
    (selected : M.laneDemand localCfg current.report.final monitor.exchange.forward lane = some laneDemand)
    (served : G.serves laneDemand (.assign index ingress) = true) :
    ∃ part head rest, ∃ _chosen : CampusTCPTwoProgressRetry.HeadRange sent part head rest,
      ∃ path : DataIngress initial current part lane,
        Event.assign index ingress = .assign path.output.index (localCfg.toConfig.ingress localCfg.sender) := by
  obtain ⟨action, next, event⟩ := assignment_action selected served
  cases work with
  | active part head rest chosen work =>
    cases work with
    | ingress path _ =>
      rw [path.action localCfg] at next
      have same := Option.some.inj next
      subst action
      exact ⟨part, head, rest, chosen, path, event⟩
    | ticket path _ _ => rw [path.action localCfg] at next; cases Option.some.inj next; cases event
    | link path _ _ => rw [path.action localCfg] at next; cases Option.some.inj next; cases event
  | done phase => simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next; cases next

private theorem arrived_done {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    {part : CampusTCPTwoProgressSender.Part} (work : OriginalLane initial checks current view received part lane)
    (arrived : Arrived received part) : lane.phase = .done := by
  cases work with
  | active _ missing => exact False.elim (missing arrived)
  | done phase => exact phase

private theorem ack_finished
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (active : Active evidence.core) (pending : monitor.exchange.forward.ack = some lane)
    (ordinary : W.controlDemand monitor = none) : monitor.mode = .finished := by
  rcases evidence.controls.ordinary_modes ordinary with armed | finished
  · have mode := evidence.armed armed
    have nonempty := active.ackNonempty (by rw [pending]; rfl)
    have resolved : monitor.exchange.forward.lower.phase = .done ∨ monitor.exchange.forward.upper.phase = .done := by
      cases stage : evidence.received with
      | empty => exact False.elim (nonempty stage)
      | upperHeld => exact Or.inr (arrived_done active.upperLane (by rw [stage]; trivial))
      | lowerReleased => exact Or.inl (arrived_done active.lowerLane (by rw [stage]; trivial))
      | allReleased => exact Or.inl (arrived_done active.lowerLane (by rw [stage]; trivial))
    have due : CampusTCPTwoTransferMonitor.transferDue monitor.exchange = true := by
      rcases resolved with lowerDone | upperDone
      · simp only [CampusTCPTwoTransferMonitor.transferDue, active.exchange, mode, lowerDone,
          show (CampusTCPTwoExchangeMonitor.Mode.forward == .forward) = true by rfl,
          show (CampusTCPTwoProgressMonitor.Mode.originals == .originals) = true by rfl,
          show (CampusTCPRoundMonitor.Phase.done == .done) = true by rfl, Bool.true_and, Bool.true_or]
      · simp only [CampusTCPTwoTransferMonitor.transferDue, active.exchange, mode, upperDone,
          show (CampusTCPTwoExchangeMonitor.Mode.forward == .forward) = true by rfl,
          show (CampusTCPTwoProgressMonitor.Mode.originals == .originals) = true by rfl,
          show (CampusTCPRoundMonitor.Phase.done == .done) = true by rfl, Bool.true_and, Bool.or_true]
    simp only [W.controlDemand, armed, due, ite_true] at ordinary
    cases ordinary
  · exact finished

private def extend_active
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

private theorem active_assign_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (active : Active evidence.core) (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .assign index ingress) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    Nonempty (Advanced evidence actual) := by
  obtain ⟨_, control, ordinary⟩ := N.allowed_assign cfg current.report.final monitor (by rw [← event]; exact allowed)
  have localAllowed : M.Allowed forwardCfg current.report.final monitor.exchange.forward (.assign index ingress) := by
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, active.exchange] using ordinary
  obtain ⟨demand, next, served⟩ := assigned_demand localAllowed
  cases assignment_selection active next served with
  | lower demand mode ack selected served =>
    obtain ⟨path, selectedEvent⟩ := original_ingress active.lowerLane selected served
    have canonical : actual.event = .assign path.output.index (checks.ingress (current.report.final.owner sender) sender) :=
      event.trans (by cases sender <;> exact selectedEvent)
    obtain ⟨value⟩ := CampusTCPTwoTransferLocatedAssign.Step.lower_assign actual evidence.core active evidence.controls path mode ack allowed before canonical
    exact ⟨extend_active evidence value.value.move value.next (P.active_lower active value mode ack)
      (CampusTCPTwoTransferAssignProgress.DataAssigned.phase value evidence.controls allowed)
      (by rw [value.observed]; rfl) (by rw [value.observed]; rfl) control allowed⟩
  | upper demand mode ack lowerServes selected served =>
    obtain ⟨path, selectedEvent⟩ := original_ingress active.upperLane selected served
    have canonical : actual.event = .assign path.output.index (checks.ingress (current.report.final.owner sender) sender) :=
      event.trans (by cases sender <;> exact selectedEvent)
    obtain ⟨value⟩ := CampusTCPTwoTransferLocatedAssign.Step.upper_assign actual evidence.core active evidence.controls path mode ack
      (by rw [event]; exact lowerServes) allowed before canonical
    exact ⟨extend_active evidence value.value.move value.next (P.active_upper active value mode ack)
      (CampusTCPTwoTransferAssignProgress.DataAssigned.phase value evidence.controls allowed)
      (by rw [value.observed]; rfl) (by rw [value.observed]; rfl) control allowed⟩
  | ack lane demand pending selected served =>
    have currentAck : AckWork checks evidence.core.live lane := by simpa only [AckState, pending] using active.ack
    obtain ⟨path, selectedEvent⟩ := ack_ingress currentAck selected served
    have canonical : actual.event = .assign path.output.index (checks.ingress (current.report.final.owner sender.other) sender.other) :=
      event.trans (by cases sender <;> exact selectedEvent)
    have finished := ack_finished evidence active pending control
    obtain ⟨value⟩ := CampusTCPTwoTransferLocatedAssign.Step.ack_assign actual evidence.core active evidence.controls finished path pending allowed before canonical
    exact ⟨extend_active evidence value.value.move value.next (P.active_ack active value pending)
      (CampusTCPTwoTransferAssignProgress.AckAssigned.phase value evidence.controls allowed)
      (by rw [value.observed]; rfl) (by rw [value.observed]; rfl) control allowed⟩
  | retry demand mode ack waiting selected served =>
    obtain ⟨part, head, rest, chosen, path, selectedEvent⟩ := retry_ingress active.retry selected served
    have canonical : actual.event = .assign path.output.index (checks.ingress (current.report.final.owner sender) sender) :=
      event.trans (by cases sender <;> exact selectedEvent)
    have finished := evidence.recovery_finished mode
    obtain ⟨value⟩ := CampusTCPTwoTransferLocatedAssign.Step.retry_assign actual evidence.core active evidence.controls finished path mode ack waiting allowed before canonical
    exact ⟨extend_active evidence value.value.move value.next (P.active_retry active value mode ack head rest chosen)
      (CampusTCPTwoTransferAssignProgress.RetryAssigned.phase value evidence.controls allowed)
      (by rw [value.observed]; rfl) (by rw [value.observed]; rfl) control allowed⟩

theorem Evidence.assign_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .assign index ingress)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced evidence actual) := by
  obtain ⟨_, _, ordinary⟩ := N.allowed_assign cfg current.report.final monitor (by rw [← event]; exact allowed)
  have localAllowed : M.Allowed forwardCfg current.report.final monitor.exchange.forward (.assign index ingress) := by
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, evidence.forward.exchange] using ordinary
  obtain ⟨demand, next, served⟩ := assigned_demand localAllowed
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    simp only [M.nextDemand, state.mode, state.lowerPending,
      show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (F.serves_operation _ (.assign index ingress)).mp served
    cases impossible
  | pending state =>
    have lowerNotPending : monitor.exchange.forward.lower.phase ≠ .needSend := by
      rcases state.lowerPath.phase with atIngress | done
      · rw [atIngress]; decide
      · rw [done]; decide
    simp only [M.nextDemand, state.mode, (F.phase_beq_false _ _).mpr lowerNotPending, Bool.false_eq_true, ite_false,
      state.upperPending, show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (F.serves_operation _ (.assign index ingress)).mp served
    cases impossible
  | active state => exact active_assign_step ⟨_, _, _, .active state, controls, scope, armed, recorded⟩ state actual before event allowed
  | readable core exchange mode sources _ _ =>
    simp only [M.nextDemand, mode] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (F.serves_operation _ (.assign index ingress)).mp served
    cases impossible

end Netlib.Check.CampusTCPTwoTransferEvidence
