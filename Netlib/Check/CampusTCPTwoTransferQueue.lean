import Netlib.Check.CampusTCPTwoTransferNetwork
import Netlib.Check.CampusTCPTwoTransferMonitor
import Netlib.Check.CampusTCPPrimaryDrain
import Netlib.Check.CampusTCPTwoProgressMonitorFacts

/-!
# Current primary tickets and their original lanes

Every pending primary ticket names a current lower or upper ticket lane.
The initial empty primary queue is an explicit operational condition.
-/

namespace Netlib.Check.CampusTCPTwoTransferQueue

open CampusTCPModel
open CampusTCPRound (Cut)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane)
end M
namespace T
export CampusTCPTwoTransferMonitor (Monitor drainTicket transferDue)
end T

variable {input : Input} {state after : State input} {monitor updated : M.Monitor}
variable {actual : Step input} {id : Nat} {whole : T.Monitor} {exchange : CampusTCPTwoExchangeMonitor.Monitor}

def TicketAt (lane : M.Lane) (id : Nat) : Prop :=
  lane.phase = .dataTicket ∧ lane.refs.dataTicket = some id

def Closed (state : State input) (monitor : M.Monitor) : Prop :=
  ∀ item ∈ state.work.pending, item.value.gateway = .primary →
    TicketAt monitor.lower item.id ∨ TicketAt monitor.upper item.id

def laneIDs (lane : M.Lane) : List Nat :=
  if lane.phase = .dataTicket then lane.refs.dataTicket.toList else []

theorem ticketAt_iff_mem (lane : M.Lane) (id : Nat) : TicketAt lane id ↔ id ∈ laneIDs lane := by
  unfold TicketAt laneIDs
  by_cases phase : lane.phase = .dataTicket
  · simp only [phase, ite_true, true_and]
    cases lane.refs.dataTicket <;> simp [eq_comm]
  · simp [phase]

theorem laneIDs_length (lane : M.Lane) : (laneIDs lane).length ≤ 1 := by
  unfold laneIDs
  split
  · cases lane.refs.dataTicket <;> simp
  · simp

theorem laneIDs_done (lane : M.Lane) (done : lane.phase = .done) : laneIDs lane = [] := by
  simp [laneIDs, done]

theorem Closed.of_zero (zero : state.outstanding .primary = 0) : Closed state monitor := by
  intro item member primary
  have empty : state.work.pending.filter (fun item => decide (item.value.gateway = .primary)) = [] :=
    List.length_eq_zero_iff.mp zero
  have inside : item ∈ state.work.pending.filter (fun item => decide (item.value.gateway = .primary)) :=
    List.mem_filter.mpr ⟨member, decide_eq_true primary⟩
  rw [empty] at inside
  cases inside

theorem Closed.count_le_ids (closed : Closed state monitor) (valid : state.work.Valid) :
    state.outstanding .primary ≤ (laneIDs monitor.lower ++ laneIDs monitor.upper).length := by
  let items := state.work.pending.filter (fun item => decide (item.value.gateway = .primary))
  have pending : (state.work.pending.map (·.id)).Nodup := by
    have unique := valid.1
    simp only [Theory.Outstanding.State.ids, List.map_append] at unique
    exact (List.nodup_append.mp unique).2.1
  have filtered : items.Sublist state.work.pending := List.filter_sublist
  have unique : (items.map (·.id)).Nodup := pending.sublist (filtered.map (·.id))
  have subset : items.map (·.id) ⊆ laneIDs monitor.lower ++ laneIDs monitor.upper := by
    intro id member
    obtain ⟨item, inside, same⟩ := List.mem_map.mp member
    obtain ⟨stored, primary⟩ := List.mem_filter.mp inside
    have lanes := closed item stored (of_decide_eq_true primary)
    rw [← same]
    rcases lanes with lower | upper
    · exact List.mem_append_left _ ((ticketAt_iff_mem _ _).mp lower)
    · exact List.mem_append_right _ ((ticketAt_iff_mem _ _).mp upper)
  simpa only [items, State.outstanding, List.length_map] using unique.length_le_of_subset subset

theorem Closed.count_le_two (closed : Closed state monitor) (valid : state.work.Valid) :
    state.outstanding .primary ≤ 2 := by
  have counted := closed.count_le_ids valid
  have lower := laneIDs_length monitor.lower
  have upper := laneIDs_length monitor.upper
  rw [List.length_append] at counted
  omega

theorem Closed.no_tickets_zero (closed : Closed state monitor) (valid : state.work.Valid)
    (lower : monitor.lower.phase ≠ .dataTicket) (upper : monitor.upper.phase ≠ .dataTicket) :
    state.outstanding .primary = 0 := by
  have counted := closed.count_le_ids valid
  simpa only [laneIDs, lower, upper, ite_false, List.nil_append, List.length_nil, Nat.le_zero] using counted

theorem Closed.lower_done_before_upper (closed : Closed state monitor) (valid : state.work.Valid)
    (lower : monitor.lower.phase = .done) (upper : monitor.upper.phase = .needSend) :
    state.outstanding .primary = 0 := by
  apply closed.no_tickets_zero valid
  · rw [lower]
    decide
  · rw [upper]
    decide

theorem Closed.resolved_count_le_one (closed : Closed state monitor) (valid : state.work.Valid)
    (resolved : monitor.lower.phase = .done ∨ monitor.upper.phase = .done) : state.outstanding .primary ≤ 1 := by
  have counted := closed.count_le_ids valid
  rcases resolved with lower | upper
  · rw [laneIDs_done _ lower, List.nil_append] at counted
    exact Nat.le_trans counted (laneIDs_length _)
  · rw [laneIDs_done _ upper, List.append_nil] at counted
    exact Nat.le_trans counted (laneIDs_length _)

theorem Closed.transfer_due_count_le_one (closed : Closed state exchange.forward) (valid : state.work.Valid)
    (due : T.transferDue exchange = true) : state.outstanding .primary ≤ 1 := by
  have resolved : exchange.forward.lower.phase = .done ∨ exchange.forward.upper.phase = .done := by
    have phases := (Bool.and_eq_true_iff.mp due).2
    simpa only [CampusTCPTwoProgressMonitorFacts.phase_beq, Bool.or_eq_true, decide_eq_true_eq] using phases
  exact closed.resolved_count_le_one valid resolved

variable {complete : H.Completed input.active input.passive} {current : Cut input complete}

theorem Closed.count_le_two_at (closed : Closed current.report.final monitor) :
    current.report.final.outstanding .primary ≤ 2 :=
  closed.count_le_two (CampusTCPOrigins.Report.work_valid current.report)

theorem Closed.transfer_due_count_le_one_at (closed : Closed current.report.final exchange.forward)
    (due : T.transferDue exchange = true) : current.report.final.outstanding .primary ≤ 1 :=
  closed.transfer_due_count_le_one (CampusTCPOrigins.Report.work_valid current.report) due

theorem Closed.drain_head (closed : Closed state whole.exchange.forward)
    (selected : T.drainTicket state whole = some id) :
    ∃ item, state.work.pending.find? (fun ticket => decide (ticket.value.gateway = .primary)) = some item ∧
      item.id = id ∧ item ∈ state.work.pending ∧ item.value.gateway = .primary ∧
      (TicketAt whole.exchange.forward.lower id ∨ TicketAt whole.exchange.forward.upper id) := by
  unfold T.drainTicket at selected
  split at selected
  · cases found : state.work.pending.find? (fun ticket => decide (ticket.value.gateway = .primary)) with
    | none => simp only [found, Option.map_none] at selected; cases selected
    | some item =>
      have same : item.id = id := by simpa only [found, Option.map_some, Option.some.injEq] using selected
      have member := List.mem_of_find?_eq_some found
      have primary : item.value.gateway = .primary := of_decide_eq_true
        (List.find?_some (p := fun ticket : Theory.Outstanding.Item (Ticket input.active input.passive) =>
          decide (ticket.value.gateway = .primary)) found)
      exact ⟨item, rfl, same, member, primary, same ▸ closed item member primary⟩
  · cases selected

theorem Closed.drain_selected (closed : Closed state whole.exchange.forward)
    (selected : T.drainTicket state whole = some id) :
    TicketAt whole.exchange.forward.lower id ∨ TicketAt whole.exchange.forward.upper id :=
  (closed.drain_head selected).choose_spec.2.2.2.2

theorem Closed.work_same (closed : Closed state monitor) (work : after.work = state.work) : Closed after monitor := by
  intro item member primary
  rw [work] at member
  exact closed item member primary

theorem Closed.reframe (closed : Closed state monitor)
    (lowerPhase : updated.lower.phase = monitor.lower.phase) (lowerTicket : updated.lower.refs.dataTicket = monitor.lower.refs.dataTicket)
    (upperPhase : updated.upper.phase = monitor.upper.phase) (upperTicket : updated.upper.refs.dataTicket = monitor.upper.refs.dataTicket) :
    Closed state updated := by
  intro item member primary
  simpa only [TicketAt, lowerPhase, lowerTicket, upperPhase, upperTicket] using closed item member primary

theorem Closed.clock (closed : Closed actual.before monitor) (actor : Actor) (now : Nat)
    (event : actual.event = .advanceClock actor now) : Closed actual.result.state monitor :=
  closed.work_same (CampusTCPPrimaryDrain.clock_work actual actor now event)

theorem Closed.control (closed : Closed actual.before monitor) (control : CampusTCPPrimaryDrain.isControl actual.event) :
    Closed actual.result.state monitor := closed.work_same (CampusTCPPrimaryDrain.control_work actual control)

theorem Closed.assign_lower (closed : Closed current.report.final monitor)
    (value : CampusTCPTwoTransferNetwork.Assignment current index ingress produced actual)
    (phase : monitor.lower.phase = .dataIngress) :
    Closed value.move.after.report.final { monitor with lower :=
      { monitor.lower with phase := .dataTicket, refs := { monitor.lower.refs with dataTicket := some value.ticket.id } } } := by
  intro item member primary
  rw [value.move.final, value.facts.work] at member
  rcases List.mem_append.mp member with old | fresh
  · rcases closed item old primary with lower | upper
    · rw [TicketAt, phase] at lower
      cases lower.1
    · exact Or.inr upper
  · have same : item = value.ticket := List.mem_singleton.mp fresh
    subst item
    exact Or.inl ⟨rfl, rfl⟩

theorem Closed.assign_upper (closed : Closed current.report.final monitor)
    (value : CampusTCPTwoTransferNetwork.Assignment current index ingress produced actual)
    (phase : monitor.upper.phase = .dataIngress) :
    Closed value.move.after.report.final { monitor with upper :=
      { monitor.upper with phase := .dataTicket, refs := { monitor.upper.refs with dataTicket := some value.ticket.id } } } := by
  intro item member primary
  rw [value.move.final, value.facts.work] at member
  rcases List.mem_append.mp member with old | fresh
  · rcases closed item old primary with lower | upper
    · exact Or.inl lower
    · rw [TicketAt, phase] at upper
      cases upper.1
  · have same : item = value.ticket := List.mem_singleton.mp fresh
    subst item
    exact Or.inr ⟨rfl, rfl⟩

theorem Closed.serve_lower (closed : Closed current.report.final monitor)
    (value : CampusTCPTwoTransferNetwork.Service current item hit session actual served emission emitted)
    (selected : TicketAt monitor.lower item.id) :
    Closed value.move.after.report.final { monitor with lower := { monitor.lower with phase := .dataLink } } := by
  obtain ⟨completed, _, _, work⟩ := value.facts.completed
  have valid : actual.before.work.Valid := by rw [value.move.beforeEq]; exact CampusTCPOrigins.Report.work_valid current.report
  intro pending member primary
  have afterMember : pending ∈ completed.state.pending := by simpa only [value.move.final, work] using member
  have beforeMember : pending ∈ current.report.final.work.pending := by
    rw [← value.move.beforeEq]
    exact completed.pendingPerm.mem_iff.mpr (List.mem_cons_of_mem _ afterMember)
  rcases closed pending beforeMember primary with lower | upper
  · have idEq : pending.id = item.id := Option.some.inj (lower.2.symm.trans selected.2)
    have absent := completed.no_pending_id valid pending afterMember
    exact False.elim (absent idEq)
  · exact Or.inr upper

theorem Closed.serve_upper (closed : Closed current.report.final monitor)
    (value : CampusTCPTwoTransferNetwork.Service current item hit session actual served emission emitted)
    (selected : TicketAt monitor.upper item.id) :
    Closed value.move.after.report.final { monitor with upper := { monitor.upper with phase := .dataLink } } := by
  obtain ⟨completed, _, _, work⟩ := value.facts.completed
  have valid : actual.before.work.Valid := by rw [value.move.beforeEq]; exact CampusTCPOrigins.Report.work_valid current.report
  intro pending member primary
  have afterMember : pending ∈ completed.state.pending := by simpa only [value.move.final, work] using member
  have beforeMember : pending ∈ current.report.final.work.pending := by
    rw [← value.move.beforeEq]
    exact completed.pendingPerm.mem_iff.mpr (List.mem_cons_of_mem _ afterMember)
  rcases closed pending beforeMember primary with lower | upper
  · exact Or.inl lower
  · have idEq : pending.id = item.id := Option.some.inj (upper.2.symm.trans selected.2)
    have absent := completed.no_pending_id valid pending afterMember
    exact False.elim (absent idEq)

end Netlib.Check.CampusTCPTwoTransferQueue
