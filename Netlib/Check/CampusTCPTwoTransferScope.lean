import Netlib.Check.CampusTCPTwoTransferLocatedDrain
import Netlib.Check.CampusTCPTwoTransferLocatedClock

namespace Netlib.Check.CampusTCPTwoTransferScope

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

namespace W
export CampusTCPTwoTransferMonitor (Monitor transferDue controlDemand drainTicket observe)
end W
namespace Q
export CampusTCPTwoTransferQueue (Closed TicketAt)
end Q

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {actor : Actor} {millis : Nat}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {kind : CampusTCPTwoTransferMonitor.Control}

structure TransferScope (monitor : W.Monitor) : Prop where
  exchange : monitor.exchange.mode = .forward
  mode : monitor.exchange.forward.mode = .originals
  resolved : monitor.exchange.forward.lower.phase = .done ∨ monitor.exchange.forward.upper.phase = .done

private theorem exchange_mode_beq (left right : CampusTCPTwoExchangeMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem TransferScope.of_due (due : W.transferDue monitor.exchange = true) : TransferScope monitor := by
  simp only [W.transferDue, exchange_mode_beq, CampusTCPTwoProgressMonitorFacts.mode_beq,
    CampusTCPTwoProgressMonitorFacts.phase_beq, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at due
  exact ⟨due.1.1, due.1.2, due.2⟩

theorem TransferScope.due (scope : TransferScope monitor) : W.transferDue monitor.exchange = true := by
  simp only [W.transferDue, exchange_mode_beq, CampusTCPTwoProgressMonitorFacts.mode_beq,
    CampusTCPTwoProgressMonitorFacts.phase_beq, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨⟨scope.exchange, scope.mode⟩, scope.resolved⟩

theorem TransferScope.of_pause (armed : monitor.mode = .armed)
    (selected : W.controlDemand monitor = some .pause) : TransferScope monitor := by
  apply TransferScope.of_due
  simp only [W.controlDemand, armed] at selected
  split at selected
  · assumption
  · cases selected

theorem TransferScope.control (scope : TransferScope monitor)
    (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none) :
    TransferScope (W.observe cfg monitor actual) := by
  rw [CampusTCPTwoTransferControlObserve.control_observe value selected drainless]
  exact ⟨scope.exchange, scope.mode, scope.resolved⟩

theorem TransferScope.pause
    (value : CampusTCPTransferEnabled.Control current (CampusTCPTwoTransferMonitor.Control.pause.event cfg) actual)
    (armed : monitor.mode = .armed) (selected : W.controlDemand monitor = some .pause) :
    TransferScope (W.observe cfg monitor actual) :=
  (TransferScope.of_pause armed selected).control value selected
    (CampusTCPTwoTransferControlObserve.noDrain_of_selected current.report.final selected (by decide))

theorem TransferScope.clock
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
    (scope : TransferScope monitor) (value : CampusTCPTwoTransferLocatedClock.Clocked core actor millis actual) :
    TransferScope (W.observe (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual) := by
  rw [value.observed]
  exact ⟨scope.exchange, scope.mode, scope.resolved⟩

theorem TransferScope.upper_done (scope : TransferScope monitor)
    (lower : monitor.exchange.forward.lower.phase = .dataTicket) : monitor.exchange.forward.upper.phase = .done := by
  rcases scope.resolved with first | second
  · rw [lower] at first
    cases first
  · exact second

theorem TransferScope.lower_done (scope : TransferScope monitor)
    (upper : monitor.exchange.forward.upper.phase = .dataTicket) : monitor.exchange.forward.lower.phase = .done := by
  rcases scope.resolved with first | second
  · exact first
  · rw [upper] at second
    cases second

theorem TransferScope.lower_drain
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    {path : CampusTCPTwoTransferPaths.DataTicket initial checks current .lower monitor.exchange.forward.lower}
    (scope : TransferScope monitor) (value : CampusTCPTwoTransferLocatedDrain.Drained core path actual) :
    TransferScope (W.observe (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual) := by
  rw [value.observed]
  exact ⟨scope.exchange, scope.mode, Or.inr (scope.upper_done path.phase)⟩

theorem TransferScope.upper_drain
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    {path : CampusTCPTwoTransferPaths.DataTicket initial checks current .upper monitor.exchange.forward.upper}
    (scope : TransferScope monitor) (value : CampusTCPTwoTransferLocatedDrain.Drained core path actual) :
    TransferScope (W.observe (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual) := by
  rw [value.observed]
  exact ⟨scope.exchange, scope.mode, Or.inl (scope.lower_done path.phase)⟩

theorem TransferScope.primary_count (scope : TransferScope monitor)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received) :
    current.report.final.outstanding .primary ≤ 1 :=
  core.primaryQueue.resolved_count_le_one (CampusTCPOrigins.Report.work_valid current.report) scope.resolved

theorem TransferScope.selected_drain (scope : TransferScope monitor)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (selected : W.drainTicket current.report.final monitor = some ticket) :
    (Q.TicketAt monitor.exchange.forward.lower ticket ∧ monitor.exchange.forward.upper.phase = .done) ∨
      (Q.TicketAt monitor.exchange.forward.upper ticket ∧ monitor.exchange.forward.lower.phase = .done) := by
  rcases core.primaryQueue.drain_selected selected with lower | upper
  · exact Or.inl ⟨lower, scope.upper_done lower.1⟩
  · exact Or.inr ⟨upper, scope.lower_done upper.1⟩

theorem TransferScope.selected_primary_count (scope : TransferScope monitor)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (selected : W.drainTicket current.report.final monitor = some ticket) :
    current.report.final.outstanding .primary = 1 := by
  have upper := scope.primary_count core
  obtain ⟨item, _, _, member, primary, _⟩ := core.primaryQueue.drain_head selected
  have present : item ∈ current.report.final.work.pending.filter (fun value => decide (value.value.gateway = .primary)) :=
    List.mem_filter.mpr ⟨member, decide_eq_true primary⟩
  have positive := List.length_pos_iff.mpr (List.ne_nil_of_mem present)
  change 0 < current.report.final.outstanding .primary at positive
  omega

end Netlib.Check.CampusTCPTwoTransferScope
