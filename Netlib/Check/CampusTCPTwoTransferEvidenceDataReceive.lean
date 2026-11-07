import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoTransferDataReceiveProgress
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase

/-!
# Actual data delivery extends the same recorded evidence

Current ACK absence selects the data branch. The actual selected lane supplies
its stored link, original writer, and receiver-stage case.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferWork (DataWork OriginalLane RetryLane)
open CampusTCPTwoTransferPaths (DataLink)

namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand Allowed nextDemand laneDemand servesOption)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand nextAction serves)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff freeClock_event phase_beq_false laneDemand_action
  servesOption_iff serves_originalChoice)
end F
namespace P
export CampusTCPTwoTransferDataReceiveProgress (Result lower_at upper_at retry_at)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {index : Nat} {bytes : List UInt8}
variable {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {localCfg : M.Config} {demand : M.Demand} {laneDemand : G.Demand} {lane : M.Lane}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "localConfig" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)

private theorem delivered_demand (allowed : M.Allowed localCfg current.report.final monitor.exchange.forward (.deliver index bytes true)) :
    ∃ demand, M.nextDemand localCfg current.report.final monitor.exchange.forward = some demand ∧
      CampusTCPTwoProgressMonitor.serves demand (.deliver index bytes true) = true := by
  obtain ⟨_, chosen | dropped | clocked, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
  · exact chosen
  · obtain ⟨_, _, impossible, _⟩ := dropped; cases impossible
  · obtain ⟨_, _, impossible, _⟩ := F.freeClock_event _ _ _ _ clocked; cases impossible

private inductive Selection (config : M.Config) (state : State input) (monitor : M.Monitor) (index : Nat) (bytes : List UInt8) : Prop where
  | lower (demand : G.Demand) (mode : monitor.mode = .originals)
      (selected : M.laneDemand config state monitor monitor.lower = some demand)
      (served : G.serves demand (.deliver index bytes true) = true)
  | upper (demand : G.Demand) (mode : monitor.mode = .originals)
      (selected : M.laneDemand config state monitor monitor.upper = some demand)
      (served : G.serves demand (.deliver index bytes true) = true)
  | retry (demand : G.Demand) (mode : monitor.mode = .recovery) (waiting : monitor.waiting = false)
      (selected : M.laneDemand config state monitor monitor.retry = some demand)
      (served : G.serves demand (.deliver index bytes true) = true)

private theorem timer_not_data
    (pending : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final = some laneDemand)
    (served : G.serves laneDemand (.deliver index bytes true) = true) : False := by
  obtain ⟨recovery, head, rest, deadline, target, _, _, _, _, demand⟩ := CampusTCPTwoProgressTimer.timerDemand_some pending
  by_cases early : recovery.now < target
  · rw [ite_eq_left early] at demand
    have impossible := (CampusTCPGapProgressMonitorFacts.serves_tick _ _ (.deliver index bytes true)).mp (demand ▸ served)
    cases impossible
  · rw [ite_eq_right early] at demand
    have impossible := (CampusTCPGapProgressMonitorFacts.serves_timeout _ (.deliver index bytes true)).mp (demand ▸ served)
    cases impossible

private theorem selection (active : Active core) (ack : monitor.exchange.forward.ack = none)
    (next : M.nextDemand localCfg current.report.final monitor.exchange.forward = some demand)
    (served : CampusTCPTwoProgressMonitor.serves demand (.deliver index bytes true) = true) :
    Selection localCfg current.report.final monitor.exchange.forward index bytes := by
  have first := active.lower_not_needSend
  have second := active.upper_not_needSend
  rcases active.mode with mode | mode
  · simp only [M.nextDemand, mode, (F.phase_beq_false _ _).mpr first, (F.phase_beq_false _ _).mpr second,
      Bool.false_eq_true, ite_false, ack] at next
    split at next
    · have same := Option.some.inj next
      subst demand
      rcases (F.serves_originalChoice _ _ _).mp served with lower | upper
      · obtain ⟨chosen, pending, served⟩ := (F.servesOption_iff _ _).mp lower
        exact .lower chosen mode pending served
      · obtain ⟨chosen, pending, served⟩ := (F.servesOption_iff _ _).mp upper
        exact .upper chosen mode pending served
    · cases next
  · simp only [M.nextDemand, mode, ack] at next
    cases waiting : monitor.exchange.forward.waiting with
    | false =>
      simp only [waiting, Bool.false_eq_true, ite_false] at next
      cases pending : M.laneDemand localCfg current.report.final monitor.exchange.forward monitor.exchange.forward.retry with
      | none => simp only [pending, Option.map_none] at next; cases next
      | some chosen =>
        have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
        subst demand
        exact .retry chosen mode waiting pending served
    | true =>
      simp only [waiting, ite_true] at next
      cases pending : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final with
      | none => simp only [pending, Option.map_none] at next; cases next
      | some chosen =>
        have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
        subst demand
        exact False.elim (timer_not_data pending served)

private theorem delivered_action
    (selected : M.laneDemand localCfg current.report.final monitor.exchange.forward lane = some laneDemand)
    (served : G.serves laneDemand (.deliver index bytes true) = true) :
    ∃ action, G.nextAction localCfg.toConfig current.report.final lane.toGap = some action ∧
      Event.deliver index bytes true = action.event := by
  obtain ⟨action, next, operation | ⟨id, resolution⟩⟩ := F.laneDemand_action _ _ _ _ selected
  · exact ⟨action, next, (CampusTCPGapProgressMonitorFacts.serves_operation action _).mp (operation ▸ served)⟩
  · rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action id _).mp (resolution ▸ served) with same | impossible
    · exact ⟨action, next, same⟩
    · cases impossible

private theorem original_link {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    {part : CampusTCPTwoProgressSender.Part} (work : OriginalLane initial checks current view received part lane)
    (selected : M.laneDemand localCfg current.report.final monitor.exchange.forward lane = some laneDemand)
    (served : G.serves laneDemand (.deliver index bytes true) = true) :
    ∃ path : DataLink initial current part lane, Event.deliver index bytes true = .deliver path.index path.emission.bytes true := by
  obtain ⟨action, next, event⟩ := delivered_action selected served
  cases work with
  | active work _ =>
    cases work with
    | ingress path _ => rw [path.action localCfg] at next; cases Option.some.inj next; cases event
    | ticket path _ _ => rw [path.action localCfg] at next; cases Option.some.inj next; cases event
    | link path _ _ =>
      rw [path.action localCfg] at next
      have same := Option.some.inj next
      subst action
      exact ⟨path, event⟩
  | done phase => simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next; cases next

private theorem retry_link {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    (work : RetryLane initial checks current view sent lane)
    (selected : M.laneDemand localCfg current.report.final monitor.exchange.forward lane = some laneDemand)
    (served : G.serves laneDemand (.deliver index bytes true) = true) :
    ∃ part head rest, ∃ _chosen : CampusTCPTwoProgressRetry.HeadRange sent part head rest,
      ∃ path : DataLink initial current part lane, Event.deliver index bytes true = .deliver path.index path.emission.bytes true := by
  obtain ⟨action, next, event⟩ := delivered_action selected served
  cases work with
  | active part head rest chosen work =>
    cases work with
    | ingress path _ => rw [path.action localCfg] at next; cases Option.some.inj next; cases event
    | ticket path _ _ => rw [path.action localCfg] at next; cases Option.some.inj next; cases event
    | link path _ _ =>
      rw [path.action localCfg] at next
      have same := Option.some.inj next
      subst action
      exact ⟨part, head, rest, chosen, path, event⟩
  | done phase => simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next; cases next

private theorem extend_data
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    {part : CampusTCPTwoProgressSender.Part} {target : CampusTCPTwoProgressMonitor.DropTarget}
    {path : DataLink initial current part lane} (value : P.Result evidence.core path target) (notAck : target ≠ .ack)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .deliver path.index path.emission.bytes true)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced evidence actual) := by
  have allowedHere : W.Allowed cfg current.report.final monitor value.value.value.value.delivery.step.event := by
    rw [value.value.value.value.delivery.event, ← event]
    exact allowed
  have control := (CampusTCPTwoTransferReceiveObserve.allowed_receipt cfg current.report.final monitor path.index path.emission.bytes
    (by rw [← event]; exact allowed)).2.1
  have ordinary := evidence.controls.ordinary_modes control
  have modeEq : (W.observe cfg monitor value.value.value.value.delivery.step).mode = monitor.mode := by rw [value.value.observed]; rfl
  have forwardMode : (W.observe cfg monitor value.value.value.value.delivery.step).exchange.forward.mode = monitor.exchange.forward.mode := by
    rw [value.value.observed]
    cases target <;> first | rfl | exact False.elim (notAck rfl)
  let advance : Advanced evidence value.value.value.value.delivery.step := {
    move := value.value.value.value.move, location
    next := {
      sent := evidence.sent, received := value.stage, core := value.value.next, forward := .active value.active
      controls := by
        rw [modeEq]
        exact evidence.controls.nonservice control value.value.value.value.move (by rw [value.value.value.value.delivery.event]; trivial)
      scope := by
        intro unarmed unfinished
        rcases ordinary with armed | finished
        · exact False.elim (unarmed (modeEq.trans armed))
        · exact False.elim (unfinished (modeEq.trans finished))
      armed := fun armed => forwardMode.trans (evidence.armed (modeEq.symm ▸ armed))
      recorded := evidence.recorded.snoc value.value.value.value.move allowedHere } }
  exact (value.value.step_eq actual before event) ▸ ⟨advance⟩

private theorem active_data_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (active : Active evidence.core) (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .deliver index bytes true) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (ack : monitor.exchange.forward.ack = none) : Nonempty (Advanced evidence actual) := by
  have ordinary := (CampusTCPTwoTransferReceiveObserve.allowed_receipt cfg current.report.final monitor index bytes
    (by rw [← event]; exact allowed)).2.2
  have localAllowed : M.Allowed localConfig current.report.final monitor.exchange.forward (.deliver index bytes true) := by
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, active.exchange] using ordinary
  obtain ⟨demand, next, served⟩ := delivered_demand localAllowed
  cases selection active ack next served with
  | lower demand mode selected served =>
    obtain ⟨path, selectedEvent⟩ := original_link active.lowerLane selected served
    have canonical := event.trans selectedEvent
    obtain ⟨value⟩ := P.lower_at active path mode ack (by rw [← canonical]; exact allowed)
    exact extend_data evidence value (by decide) actual before canonical allowed
  | upper demand mode selected served =>
    obtain ⟨path, selectedEvent⟩ := original_link active.upperLane selected served
    have canonical := event.trans selectedEvent
    obtain ⟨value⟩ := P.upper_at active path mode ack (by rw [← canonical]; exact allowed)
    exact extend_data evidence value (by decide) actual before canonical allowed
  | retry demand mode waiting selected served =>
    obtain ⟨part, head, rest, chosen, path, selectedEvent⟩ := retry_link active.retry selected served
    have canonical := event.trans selectedEvent
    obtain ⟨value⟩ := P.retry_at active path chosen mode ack waiting (by rw [← canonical]; exact allowed)
    exact extend_data evidence value (by decide) actual before canonical allowed

theorem Evidence.data_receive_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .deliver index bytes true)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) (ack : monitor.exchange.forward.ack = none) :
    Nonempty (Advanced evidence actual) := by
  have ordinary := (CampusTCPTwoTransferReceiveObserve.allowed_receipt cfg current.report.final monitor index bytes
    (by rw [← event]; exact allowed)).2.2
  have localAllowed : M.Allowed localConfig current.report.final monitor.exchange.forward (.deliver index bytes true) := by
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, evidence.forward.exchange] using ordinary
  obtain ⟨demand, next, served⟩ := delivered_demand localAllowed
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    simp only [M.nextDemand, state.mode, state.lowerPending,
      show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.deliver index bytes true)).mp served
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
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.deliver index bytes true)).mp served
    cases impossible
  | active state => exact active_data_step ⟨_, _, _, .active state, controls, scope, armed, recorded⟩ state actual before event allowed ack
  | readable core exchange mode sources senderDuplicate mainAck =>
    simp only [M.nextDemand, mode] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.deliver index bytes true)).mp served
    cases impossible

end Netlib.Check.CampusTCPTwoTransferEvidence
