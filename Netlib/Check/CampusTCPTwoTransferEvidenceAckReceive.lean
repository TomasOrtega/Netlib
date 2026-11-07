import Netlib.Check.CampusTCPTwoTransferAckRetire

/-!
# The selected actual ACK receipt extends current evidence

Current ACK work identifies the stored link and its literal bytes.
The same delivery retains active work or derives the readable boundary.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferWork (OriginalLane AckWork AckState)
open CampusTCPTwoTransferPaths (AckLink)
open CampusTCPTwoProgressPhaseBase (Arrived)

namespace L
export CampusTCPTwoProgressMonitor (Lane Demand nextDemand laneDemand servesOption serves)
end L
namespace G
export CampusTCPGapProgressMonitor (Demand nextAction serves)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (phase_beq_false)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {index : Nat} {bytes : List UInt8} {lane : L.Lane}
variable {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "localCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at
    (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)

private theorem delivery_demand
    (allowed : CampusTCPTwoProgressMonitor.Allowed localCfg current.report.final monitor.exchange.forward (.deliver index bytes true)) :
    ∃ demand, L.nextDemand localCfg current.report.final monitor.exchange.forward = some demand ∧
      L.serves demand (.deliver index bytes true) = true := by
  obtain ⟨_, chosen | dropped | clocked, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
  · exact chosen
  · obtain ⟨_, _, impossible, _⟩ := dropped
    cases impossible
  · obtain ⟨_, _, impossible, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ clocked
    cases impossible

private theorem ack_link {demand : G.Demand} (work : AckWork checks core.live lane)
    (next : L.laneDemand localCfg current.report.final monitor.exchange.forward lane = some demand)
    (served : G.serves demand (.deliver index bytes true) = true) :
    ∃ path : AckLink initial current (received.bytes lower upper).length lane,
      Event.deliver index bytes true = .deliver path.index path.emission.bytes true := by
  obtain ⟨action, next, kind⟩ := CampusTCPTwoProgressMonitorFacts.laneDemand_action _ _ _ _ next
  have event : Event.deliver index bytes true = action.event := by
    rcases kind with operation | ⟨id, resolution⟩
    · exact (CampusTCPGapProgressMonitorFacts.serves_operation action _).mp (operation ▸ served)
    · rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action id _).mp (resolution ▸ served) with selected | impossible
      · exact selected
      · cases impossible
  have same := Option.some.inj (next.symm.trans (work.command_next localCfg))
  rw [same] at event
  cases work with
  | pending phase queue => cases event
  | ingress path => cases event
  | ticket path _ => cases event
  | link path => exact ⟨path, event⟩

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

private theorem active_ack_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (active : Active evidence.core) (pending : monitor.exchange.forward.ack = some lane)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .deliver index bytes true)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced evidence actual) := by
  have canonicalAllowed : W.Allowed cfg current.report.final monitor (.deliver index bytes true) := by rw [← event]; exact allowed
  have control := (CampusTCPTwoTransferAckReceiveObserve.ordinary_delivery canonicalAllowed).2
  have ordinary := evidence.controls.ordinary_modes control
  have localAllowed := CampusTCPTwoTransferServiceObserve.local_allowed ordinary control active.exchange canonicalAllowed
  obtain ⟨demand, next, served⟩ := delivery_demand localAllowed
  have selected := next
  have first := active.lower_not_needSend
  have second := active.upper_not_needSend
  have chosen : ∃ demand, L.laneDemand localCfg current.report.final monitor.exchange.forward lane = some demand ∧
      G.serves demand (.deliver index bytes true) = true := by
    rcases active.mode with mode | mode
    all_goals simp only [L.nextDemand, mode, (F.phase_beq_false _ _).mpr first, (F.phase_beq_false _ _).mpr second,
      Bool.false_eq_true, ite_false, pending] at selected
    all_goals cases found : L.laneDemand localCfg current.report.final monitor.exchange.forward lane with
      | none => simp only [found, Option.map_none] at selected; cases selected
      | some chosen =>
        have same : (.single chosen : L.Demand) = demand := by simpa only [found, Option.map_some, Option.some.injEq] using selected
        subst demand
        exact ⟨chosen, rfl, served⟩
  obtain ⟨demand, next, served⟩ := chosen
  have currentAck : AckWork checks evidence.core.live lane := by simpa only [AckState, pending] using active.ack
  obtain ⟨path, canonical⟩ := ack_link currentAck next served
  have pathAllowed : W.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true) := by
    rw [← canonical]; exact canonicalAllowed
  have finished := ack_finished evidence active pending control
  obtain ⟨record, same⟩ := CampusTCPTwoTransferAckRetire.Step.receive_ack active evidence.controls path pending pathAllowed
    actual before (event.trans canonical)
  have advance : Advanced evidence record.actual := {
    move := record.move, location
    next := {
      sent := record.nextStage, received := evidence.received, core := record.nextCore, forward := record.forward
      controls := record.phase evidence.controls pathAllowed
      scope := by intro _ unfinished; exact False.elim (unfinished (record.outer_mode.trans finished))
      armed := by rw [record.outer_mode, finished]; intro impossible; cases impossible
      recorded := evidence.recorded.snoc record.move (by rw [record.event]; exact pathAllowed) } }
  exact same ▸ ⟨advance⟩


theorem Evidence.ack_receive_step
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (pending : monitor.exchange.forward.ack = some lane)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .deliver index bytes true)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced evidence actual) := by
  have canonicalAllowed : W.Allowed cfg current.report.final monitor (.deliver index bytes true) := by rw [← event]; exact allowed
  have control := (CampusTCPTwoTransferAckReceiveObserve.ordinary_delivery canonicalAllowed).2
  have ordinary := evidence.controls.ordinary_modes control
  have localAllowed := CampusTCPTwoTransferServiceObserve.local_allowed ordinary control evidence.forward.exchange canonicalAllowed
  obtain ⟨demand, next, served⟩ := delivery_demand localAllowed
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => rw [state.ack] at pending; cases pending
  | pending state => rw [state.ack] at pending; cases pending
  | active state => exact active_ack_step ⟨_, _, _, .active state, controls, scope, armed, recorded⟩ state pending actual before event allowed
  | readable core exchange mode sources duplicate mainAck =>
    simp only [L.nextDemand, mode] at next
    have same := Option.some.inj next
    subst demand
    have impossible := (CampusTCPTwoProgressMonitorFacts.serves_operation _ (.deliver index bytes true)).mp served
    cases impossible

end Netlib.Check.CampusTCPTwoTransferEvidence
