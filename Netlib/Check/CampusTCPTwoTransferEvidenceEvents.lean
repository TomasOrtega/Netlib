import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoTransferServiceObserve
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase

/-!
# Canonical ordinary events from current evidence

The current demand and typed work determine actor, policy, and operation shape.
The read case also identifies the current read phase.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidenceEvents

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferEvidence (Evidence)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferWork (DataWork OriginalLane RetryLane AckWork AckState)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed drainTicket controlDemand)
end W
namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand nextDemand laneDemand servesOption)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand nextAction serves)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff freeClock_event phase_beq_false laneDemand_action serves_originalChoice servesOption_iff)
end F

inductive EventShape (sender : Actor) (total : Nat) (mode : CampusTCPTwoProgressMonitor.Mode) (event : Event) : Prop where
  | send (count : Nat) (selected : event = .send sender count true)
  | assign (index : Nat) (ingress : I.InterfaceRef) (selected : event = .assign index ingress)
  | serve (ticket : Nat) (selected : event = .serve ticket none)
  | deliver (index : Nat) (bytes : List UInt8) (selected : event = .deliver index bytes true)
  | ack (selected : event = .emitAck sender.other true)
  | read (current : mode = .needRead) (selected : event = .read sender.other total)
  | clock (actor : Actor) (millis : Nat) (selected : event = .advanceClock actor millis)
  | timeout (selected : event = .timeout sender true)
  | drop (id : Nat) (selected : event = .dropPacket id)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {event : Event} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {packetConfig : M.Config} {demand : M.Demand} {selectedDemand : G.Demand} {lane : M.Lane}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "packetCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)
local notation "Shape" => EventShape sender (List.length (lower ++ upper))
  (CampusTCPTwoProgressMonitor.Monitor.mode
    (CampusTCPTwoExchangeMonitor.Monitor.forward (CampusTCPTwoTransferMonitor.Monitor.exchange monitor))) event

private theorem lane_event
    (selected : M.laneDemand packetConfig current.report.final monitor.exchange.forward lane = some selectedDemand)
    (served : G.serves selectedDemand event = true) :
    ∃ action, G.nextAction packetConfig.toConfig current.report.final lane.toGap = some action ∧
      (event = action.event ∨ ∃ id, event = .dropPacket id) := by
  obtain ⟨action, next, operation | ⟨id, resolution⟩⟩ := F.laneDemand_action _ _ _ _ selected
  · exact ⟨action, next, .inl ((CampusTCPGapProgressMonitorFacts.serves_operation action event).mp (operation ▸ served))⟩
  · rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action id event).mp (resolution ▸ served) with ordinary | drop
    · exact ⟨action, next, .inl ordinary⟩
    · exact ⟨action, next, .inr ⟨id, drop⟩⟩

private theorem data_shape {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    {part : CampusTCPTwoProgressSender.Part} (work : DataWork initial checks current view part lane)
    (selected : M.laneDemand packetConfig current.report.final monitor.exchange.forward lane = some selectedDemand)
    (served : G.serves selectedDemand event = true) : Shape := by
  obtain ⟨action, next, ordinary | ⟨id, drop⟩⟩ := lane_event selected served
  · have same := Option.some.inj (next.symm.trans (work.command_next packetConfig))
    rw [same] at ordinary
    cases work with
    | ingress path _ => exact .assign _ _ ordinary
    | ticket path _ _ => exact .serve _ ordinary
    | link path _ _ => exact .deliver _ _ ordinary
  · exact .drop id drop

private theorem original_shape {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    {part : CampusTCPTwoProgressSender.Part} (work : OriginalLane initial checks current view received part lane)
    (selected : M.laneDemand packetConfig current.report.final monitor.exchange.forward lane = some selectedDemand)
    (served : G.serves selectedDemand event = true) : Shape := by
  cases work with
  | active work _ => exact data_shape work selected served
  | done phase =>
    obtain ⟨_, next, _⟩ := F.laneDemand_action _ _ _ _ selected
    simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next
    cases next

private theorem retry_shape {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    (work : RetryLane initial checks current view sent lane)
    (selected : M.laneDemand packetConfig current.report.final monitor.exchange.forward lane = some selectedDemand)
    (served : G.serves selectedDemand event = true) : Shape := by
  cases work with
  | active _ _ _ _ work => exact data_shape work selected served
  | done phase =>
    obtain ⟨_, next, _⟩ := F.laneDemand_action _ _ _ _ selected
    simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next
    cases next

private theorem ack_shape (work : AckWork checks core.live lane) (senderEq : packetConfig.sender = sender)
    (selected : M.laneDemand packetConfig current.report.final monitor.exchange.forward lane = some selectedDemand)
    (served : G.serves selectedDemand event = true) : Shape := by
  obtain ⟨action, next, ordinary | ⟨id, drop⟩⟩ := lane_event selected served
  · have same := Option.some.inj (next.symm.trans (work.command_next packetConfig))
    rw [same] at ordinary
    cases work with
    | pending _ _ =>
      change event = .emitAck packetConfig.sender.other true at ordinary
      rw [senderEq] at ordinary
      exact .ack ordinary
    | ingress path => exact .assign _ _ ordinary
    | ticket path _ => exact .serve _ ordinary
    | link path => exact .deliver _ _ ordinary
  · exact .drop id drop

private theorem timer_shape (senderEq : packetConfig.sender = sender)
    (pending : CampusTCPTwoProgressMonitor.timerDemand packetConfig current.report.final = some selectedDemand)
    (served : G.serves selectedDemand event = true) : Shape := by
  obtain ⟨recovery, head, rest, deadline, target, _, _, _, _, demand⟩ := CampusTCPTwoProgressTimer.timerDemand_some pending
  by_cases early : recovery.now < target
  · rw [ite_eq_left early] at demand
    exact .clock _ _ ((CampusTCPGapProgressMonitorFacts.serves_tick _ _ event).mp (demand ▸ served))
  · rw [ite_eq_right early] at demand
    have same := (CampusTCPGapProgressMonitorFacts.serves_timeout _ event).mp (demand ▸ served)
    rw [senderEq] at same
    exact .timeout same

private theorem active_selected (active : Active core)
    (next : M.nextDemand packetCfg current.report.final monitor.exchange.forward = some demand)
    (served : CampusTCPTwoProgressMonitor.serves demand event = true) : Shape := by
  have first := active.lower_not_needSend
  have second := active.upper_not_needSend
  rcases active.mode with mode | mode
  · simp only [M.nextDemand, mode, (F.phase_beq_false _ _).mpr first, (F.phase_beq_false _ _).mpr second,
      Bool.false_eq_true, ite_false] at next
    cases ack : monitor.exchange.forward.ack with
    | some lane =>
      simp only [ack] at next
      cases pending : M.laneDemand packetCfg current.report.final monitor.exchange.forward lane with
      | none => simp only [pending, Option.map_none] at next; cases next
      | some chosen =>
        have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
        subst demand
        exact ack_shape (by simpa only [AckState, ack] using active.ack) rfl pending served
    | none =>
      simp only [ack] at next
      split at next
      · have same := Option.some.inj next
        subst demand
        rcases (F.serves_originalChoice _ _ _).mp served with lower | upper
        · obtain ⟨chosen, pending, served⟩ := (F.servesOption_iff _ _).mp lower
          exact original_shape active.lowerLane pending served
        · obtain ⟨chosen, pending, served⟩ := (F.servesOption_iff _ _).mp upper
          exact original_shape active.upperLane pending served
      · cases next
  · simp only [M.nextDemand, mode] at next
    cases ack : monitor.exchange.forward.ack with
    | some lane =>
      simp only [ack] at next
      cases pending : M.laneDemand packetCfg current.report.final monitor.exchange.forward lane with
      | none => simp only [pending, Option.map_none] at next; cases next
      | some chosen =>
        have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
        subst demand
        exact ack_shape (by simpa only [AckState, ack] using active.ack) rfl pending served
    | none =>
      simp only [ack] at next
      cases waiting : monitor.exchange.forward.waiting with
      | false =>
        simp only [waiting, Bool.false_eq_true, ite_false] at next
        cases pending : M.laneDemand packetCfg current.report.final monitor.exchange.forward monitor.exchange.forward.retry with
        | none => simp only [pending, Option.map_none] at next; cases next
        | some chosen =>
          have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
          subst demand
          exact retry_shape active.retry pending served
      | true =>
        simp only [waiting, ite_true] at next
        cases pending : CampusTCPTwoProgressMonitor.timerDemand packetCfg current.report.final with
        | none => simp only [pending, Option.map_none] at next; cases next
        | some chosen =>
          have same : (.single chosen : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
          subst demand
          exact timer_shape rfl pending served

theorem classify
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (_drainless : W.drainTicket current.report.final monitor = none) (control : W.controlDemand monitor = none)
    (allowed : W.Allowed cfg current.report.final monitor event) : Shape := by
  have ordinary := evidence.controls.ordinary_modes control
  have localAllowed := CampusTCPTwoTransferServiceObserve.local_allowed ordinary control evidence.forward.exchange allowed
  obtain ⟨_, chosen | dropped | clocked, _⟩ := (F.allowed_iff _ _ _ _).mp localAllowed
  · obtain ⟨demand, next, served⟩ := chosen
    rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
    cases forward with
    | written state =>
      simp only [M.nextDemand, state.mode, state.lowerPending,
        show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true] at next
      have same := Option.some.inj next
      subst demand
      exact .send _ ((CampusTCPTwoProgressMonitorFacts.serves_operation _ event).mp served)
    | pending state =>
      have first : monitor.exchange.forward.lower.phase ≠ .needSend := by
        rcases state.lowerPath.phase with ingress | done
        · rw [ingress]; decide
        · rw [done]; decide
      simp only [M.nextDemand, state.mode, (F.phase_beq_false _ _).mpr first, Bool.false_eq_true, ite_false,
        state.upperPending, show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true] at next
      have same := Option.some.inj next
      subst demand
      exact .send _ ((CampusTCPTwoProgressMonitorFacts.serves_operation _ event).mp served)
    | active active => exact active_selected active next served
    | readable core exchange mode sources senderDuplicate mainAck =>
      simp only [M.nextDemand, mode] at next
      have same := Option.some.inj next
      subst demand
      exact .read mode ((CampusTCPTwoProgressMonitorFacts.serves_operation _ event).mp served)
  · obtain ⟨id, _, selected, _⟩ := dropped
    exact .drop id selected
  · obtain ⟨actor, millis, selected, _⟩ := F.freeClock_event _ _ _ _ clocked
    exact .clock actor millis selected

end Netlib.Check.CampusTCPTwoTransferEvidenceEvents
