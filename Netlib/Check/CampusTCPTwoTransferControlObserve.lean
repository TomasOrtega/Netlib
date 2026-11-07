import Netlib.Check.CampusTCPTwoTransferMonitor
import Netlib.Check.CampusTCPTransferEnabled
import Netlib.Check.CampusTCPTwoTransferNetwork
import Netlib.Check.CampusTCPTwoProgressMonitorFacts

/-!
# Exact observation of current transfer operations

Stored controls supply their own supported and passed facts.
Their observer updates retain every local and global exchange counter.
-/

namespace Netlib.Check.CampusTCPTwoTransferControlObserve

open CampusTCPModel (Input State Step Event Served Ticket Transit)
open CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoTransferMonitor

local notation "Config" => CampusTCPTwoTransferMonitor.Config

namespace N
export CampusTCPTwoTransferNetwork (Service)
end N

variable {input : Input} {complete : TCPHandshake.Completed input.active input.passive}
variable {current : Cut input complete} {config : Config} {monitor : Monitor} {kind : Control}
variable {actual : Step input}

private theorem mode_beq (left right : Mode) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> rfl

theorem noDrain_of_non_capture (state : State input) (monitor : Monitor) (mode : monitor.mode ≠ .capture) :
    drainTicket state monitor = none := by simp [drainTicket, mode_beq, mode]

theorem noDrain_of_primary_zero (state : State input) (monitor : Monitor) (zero : state.outstanding .primary = 0) :
    drainTicket state monitor = none := by
  have empty : state.work.pending.filter (fun item => decide (item.value.gateway = .primary)) = [] :=
    List.length_eq_zero_iff.mp zero
  have absent : state.work.pending.find? (fun item => decide (item.value.gateway = .primary)) = none := by
    apply List.find?_eq_none.mpr
    intro item member primary
    have selected : item ∈ state.work.pending.filter (fun item => decide (item.value.gateway = .primary)) :=
      List.mem_filter.mpr ⟨member, primary⟩
    rw [empty] at selected
    cases selected
  simp only [drainTicket, absent, Option.map_none, ite_self]

theorem noDrain_of_selected (state : State input) (selected : controlDemand monitor = some kind)
    (notCapture : kind ≠ .capture) : drainTicket state monitor = none := by
  apply noDrain_of_non_capture
  intro capture
  have same : kind = .capture := by simpa only [controlDemand, capture, Option.some.injEq] using selected.symm
  exact notCapture same

private theorem selected_valid (selected : controlDemand monitor = some kind) : monitor.mode ≠ .invalid := by
  intro invalid
  rw [controlDemand, invalid] at selected
  cases selected

private theorem control_serves_self (kind : Control) (config : Config) : kind.serves config (kind.event config) = true := by
  cases kind <;> simp only [Control.serves, Control.event, beq_self_eq_true]

def afterControl (monitor : Monitor) (kind : Control) : Monitor :=
  { mode := kind.after
    exchange := { monitor.exchange with slots := monitor.exchange.slots + 1 }
    controls := monitor.controls ++ [(kind, monitor.exchange.slots)] }

theorem control_allowed (value : CampusTCPTransferEnabled.Control current (kind.event config) actual)
    (selected : controlDemand monitor = some kind) (drainless : drainTicket current.report.final monitor = none) :
    Allowed config current.report.final monitor actual.event := by
  have valid := selected_valid selected
  rw [Allowed, allowed, ite_eq_right (by simpa only [decide_eq_true_eq] using valid), drainless, selected, value.eventEq]
  cases kind <;> exact control_serves_self _ _

theorem control_observe (value : CampusTCPTransferEnabled.Control current (kind.event config) actual)
    (selected : controlDemand monitor = some kind) (drainless : drainTicket current.report.final monitor = none) :
    observe config monitor actual = afterControl monitor kind := by
  have allowed := control_allowed value selected drainless
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed config actual.before monitor actual.event) = true := by
    rw [value.move.supported, value.move.passed, value.move.beforeEq]
    exact allowed
  rw [observe, ite_eq_left checked, value.move.beforeEq, drainless, selected, value.eventEq]
  cases kind <;> rfl

theorem control_healthy (value : CampusTCPTransferEnabled.Control current (kind.event config) actual)
    (selected : controlDemand monitor = some kind) (drainless : drainTicket current.report.final monitor = none) :
    (observe config monitor actual).mode ≠ .invalid := by
  rw [control_observe value selected drainless]
  cases kind <;> simp only [afterControl, Control.after, ne_eq, reduceCtorEq, not_false_eq_true]

theorem control_fields (value : CampusTCPTransferEnabled.Control current (kind.event config) actual)
    (selected : controlDemand monitor = some kind) (drainless : drainTicket current.report.final monitor = none) :
    (observe config monitor actual).exchange.forward = monitor.exchange.forward ∧
      (observe config monitor actual).exchange.reverse = monitor.exchange.reverse ∧
      (observe config monitor actual).exchange.drops = monitor.exchange.drops ∧
      (observe config monitor actual).exchange.timeouts = monitor.exchange.timeouts ∧
      (observe config monitor actual).exchange.slots = monitor.exchange.slots + 1 ∧
      (observe config monitor actual).exchange.forwardReadSlot = monitor.exchange.forwardReadSlot ∧
      (observe config monitor actual).exchange.writeSlot = monitor.exchange.writeSlot ∧
      (observe config monitor actual).exchange.reverseReadSlot = monitor.exchange.reverseReadSlot ∧
      (observe config monitor actual).controls = monitor.controls ++ [(kind, monitor.exchange.slots)] := by
  rw [control_observe value selected drainless]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Netlib.Check.CampusTCPTwoTransferControlObserve
