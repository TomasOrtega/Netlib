import Netlib.Check.CampusTCPTwoTransferRecoveryCapAck
import Netlib.Check.CampusTCPTwoTransferRecoveryCapBasic
import Netlib.Check.CampusTCPTwoTransferNonoriginal

/-!
# Fixed cap through selected recovery application work

Current typed work identifies the actual emission or serviced data link.
The supplied step is the same operation as the enabled receipt or ACK output.
-/

namespace Netlib.Check.CampusTCPTwoTransferRecoveryCap

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferWork (DataWork AckWork AckState)
open CampusTCPTwoTransferHandoffRTO (PendingCap same_core)
open CampusTCPTwoTransferEvidence (Evidence)

namespace W
export CampusTCPTwoTransferMonitor (Monitor observe Allowed)
end W
namespace M
export CampusTCPTwoProgressMonitor (Lane Demand nextDemand laneDemand serves)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand nextAction serves)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff freeClock_event laneDemand_action)
end F

def ApplicationEvent : Event → Prop
  | .deliver .. | .emitAck .. => True
  | _ => False

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {actual : Step input} {event : Event}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "localCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at
    (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)

private theorem lane_action {lane : M.Lane} {demand : G.Demand}
    (selected : M.laneDemand localCfg current.report.final monitor.exchange.forward lane = some demand)
    (served : G.serves demand event = true) (application : ApplicationEvent event) :
    ∃ action, G.nextAction (localCfg).toConfig current.report.final lane.toGap = some action ∧ event = action.event := by
  obtain ⟨action, next, operation | ⟨id, resolution⟩⟩ := F.laneDemand_action _ _ _ _ selected
  · exact ⟨action, next, (CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp (operation ▸ served)⟩
  · rcases (CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _).mp (resolution ▸ served) with selected | dropped
    · exact ⟨action, next, selected⟩
    · rw [dropped] at application; cases application

private inductive Choice (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (event : Event) : Prop where
  | ack (lane : M.Lane) (selected : monitor.exchange.forward.ack = some lane)
      (work : AckWork checks core.live lane) (action : CampusTCPRoundMonitor.Action)
      (next : G.nextAction (localCfg).toConfig current.report.final lane.toGap = some action) (event : event = action.event)
  | retry (part : CampusTCPTwoProgressSender.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
      (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
      (work : DataWork initial checks current core.live.gatewayState part monitor.exchange.forward.retry)
      (none : monitor.exchange.forward.ack = none) (waiting : monitor.exchange.forward.waiting = false)
      (action : CampusTCPRoundMonitor.Action)
      (next : G.nextAction (localCfg).toConfig current.report.final monitor.exchange.forward.retry.toGap = some action)
      (event : event = action.event)

private theorem timer_not_application {demand : G.Demand}
    (pending : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final = some demand)
    (served : G.serves demand event = true) (application : ApplicationEvent event) : False := by
  obtain ⟨recovery, head, rest, deadline, target, _, _, _, _, selected⟩ := CampusTCPTwoProgressTimer.timerDemand_some pending
  by_cases early : recovery.now < target
  · rw [ite_eq_left early] at selected
    have clock := (CampusTCPGapProgressMonitorFacts.serves_tick _ _ _).mp (selected ▸ served)
    rw [clock] at application
    cases application
  · rw [ite_eq_right early] at selected
    have timeout := (CampusTCPGapProgressMonitorFacts.serves_timeout _ _).mp (selected ▸ served)
    rw [timeout] at application
    cases application

private theorem choice (active : Active core) (mode : monitor.exchange.forward.mode = .recovery)
    (allowed : CampusTCPTwoProgressMonitor.Allowed localCfg current.report.final monitor.exchange.forward event)
    (application : ApplicationEvent event) : Choice core event := by
  have chosen : ∃ demand, M.nextDemand localCfg current.report.final monitor.exchange.forward = some demand ∧
      M.serves demand event = true := by
    obtain ⟨_, selected | dropped | clocked, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
    · exact selected
    · obtain ⟨id, _, eventEq, _⟩ := dropped; rw [eventEq] at application; cases application
    · obtain ⟨actor, millis, eventEq, _⟩ := F.freeClock_event _ _ _ _ clocked
      rw [eventEq] at application; cases application
  obtain ⟨demand, pending, served⟩ := chosen
  simp only [M.nextDemand, mode] at pending
  cases ack : monitor.exchange.forward.ack with
  | some lane =>
    simp only [ack] at pending
    cases selected : M.laneDemand localCfg current.report.final monitor.exchange.forward lane with
    | none => rw [selected] at pending; cases pending
    | some raw =>
      simp only [selected, Option.map_some] at pending
      cases pending
      obtain ⟨action, next, eventEq⟩ := lane_action selected served application
      exact .ack lane ack (by simpa only [AckState, ack] using active.ack) action next eventEq
  | none =>
    simp only [ack] at pending
    cases waiting : monitor.exchange.forward.waiting with
    | true =>
      simp only [waiting, ite_true] at pending
      cases selected : CampusTCPTwoProgressMonitor.timerDemand localCfg current.report.final with
      | none => rw [selected] at pending; cases pending
      | some raw =>
        simp only [selected, Option.map_some] at pending
        cases pending
        exact False.elim (timer_not_application selected served application)
    | false =>
      simp only [waiting, Bool.false_eq_true, ite_false] at pending
      cases selected : M.laneDemand localCfg current.report.final monitor.exchange.forward monitor.exchange.forward.retry with
      | none => rw [selected] at pending; cases pending
      | some raw =>
        simp only [selected, Option.map_some] at pending
        cases pending
        obtain ⟨action, next, eventEq⟩ := lane_action selected served application
        cases active.retry with
        | done done => simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, done] at next; cases next
        | active part head rest selected work => exact .retry part head rest selected work ack waiting action next eventEq

theorem data_cap {part : CampusTCPTwoProgressSender.Part} {lane : M.Lane} {target : CampusTCPTwoProgressMonitor.DropTarget}
    {stage : CampusTCPTwoProgressReceiver.Stage} {chunk : List UInt8}
    {path : CampusTCPTwoTransferPaths.DataLink initial current part lane}
    (value : CampusTCPTwoTransferLocatedDataReceive.Received core path target stage chunk)
    (prior : PendingCap cfg capacity current.report.final monitor) :
    PendingCap cfg capacity value.value.value.move.after.report.final (W.observe cfg monitor value.value.value.delivery.step) := by
  apply same_core core value.next prior
  · exact congrArg Recovery.State.rto value.sender_recovery
  · exact fun pending => pending
  · rw [value.observed]; cases target <;> rfl

theorem output_cap {lane : M.Lane} (value : CampusTCPTwoTransferAckOutputProgress.AckSent core lane actual)
    (prior : PendingCap cfg capacity current.report.final monitor) :
    PendingCap cfg capacity value.value.move.after.report.final (W.observe cfg monitor actual) := by
  apply same_core core value.next prior
  · exact congrArg Recovery.State.rto value.sender_recovery
  · exact fun pending => pending
  · rw [value.observed]; rfl

theorem application_cap (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (active : Active evidence.core) (mode : monitor.exchange.forward.mode = .recovery)
    (prior : PendingCap cfg capacity current.report.final monitor) (move : Move current actual)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) (application : ApplicationEvent actual.event) :
    PendingCap cfg capacity move.after.report.final (W.observe cfg monitor actual) := by
  have localAllowed := CampusTCPTwoTransferNonoriginal.local_allowed evidence (by rw [mode]; decide) allowed
  cases choice active mode localAllowed application with
  | ack lane selected work action next event =>
    have same := Option.some.inj (next.symm.trans (work.command_next localCfg))
    rw [same] at event
    cases work with
    | pending phase queue =>
      change actual.event = .emitAck sender.other true at event
      obtain ⟨value⟩ := CampusTCPTwoTransferAckOutputProgress.Step.emit_ack evidence.core active evidence.controls selected phase queue
        (by rw [← event]; exact allowed) actual move.beforeEq event
      have bounded := output_cap value prior
      rw [value.value.move.final, ← move.final] at bounded
      exact bounded
    | ingress path => rw [event] at application; cases application
    | ticket path assigned => rw [event] at application; cases application
    | link path =>
      change actual.event = .deliver path.index path.emission.bytes true at event
      obtain ⟨value, same⟩ := CampusTCPTwoTransferAckRetire.Step.receive_ack active evidence.controls path selected
        (by rw [← event]; exact allowed) actual move.beforeEq event
      have bounded := received_cap active value (by rw [mode]; decide) selected prior
      rw [value.move.final, same, ← move.final] at bounded
      exact bounded
  | retry part head rest selected work ack waiting action next event =>
    have same := Option.some.inj (next.symm.trans (work.command_next localCfg))
    rw [same] at event
    cases work with
    | ingress path source => rw [event] at application; cases application
    | ticket path assigned source => rw [event] at application; cases application
    | link path source known =>
      change actual.event = .deliver path.index path.emission.bytes true at event
      obtain ⟨value⟩ := CampusTCPTwoTransferDataReceiveProgress.retry_at active path selected mode ack waiting
        (by rw [← event]; exact allowed)
      have bounded := data_cap value.value prior
      rw [value.value.value.value.move.final, value.value.step_eq actual move.beforeEq event, ← move.final] at bounded
      exact bounded

end Netlib.Check.CampusTCPTwoTransferRecoveryCap
