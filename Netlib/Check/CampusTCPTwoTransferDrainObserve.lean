import Netlib.Check.CampusTCPTwoTransferControlObserve

/-!
# Exact observation of stored primary drain services

Each tracked ticket advances its same original lane to the actual new link.
The queued ACK and every loss and retry counter stay attached to the task.
-/

namespace Netlib.Check.CampusTCPTwoTransferDrainObserve

open Protocol Protocol.TCP CampusTCPEnabled
open CampusTCPModel (Input State Step Event Served Ticket Transit)
open CampusTCPRound (Cut)
open CampusTCPTwoTransferMonitor

local notation "Config" => CampusTCPTwoTransferMonitor.Config

namespace N
export CampusTCPTwoTransferNetwork (Service)
end N
namespace L
export CampusTCPTwoProgressMonitor (Monitor Lane dataLane observeData)
end L

variable {input : Input} {complete : TCPHandshake.Completed input.active input.passive}
variable {current : Cut input complete} {config : Config} {monitor : Monitor} {actual : Step input}
variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)}
variable {hit : FlowNAT.Hit} {session : Admission.Session} {served : Served input}
variable {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

private theorem mode_beq (left right : Mode) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> rfl

theorem drain_mode (selected : drainTicket state monitor = some ticket) : monitor.mode = .capture := by
  cases mode : monitor.mode <;> simp_all [drainTicket, mode_beq]

theorem drain_allowed (value : N.Service current item hit session actual served emission emitted)
    (selected : drainTicket current.report.final monitor = some item.id) :
    Allowed config current.report.final monitor actual.event := by
  have valid : monitor.mode ≠ .invalid := by rw [drain_mode selected]; decide
  rw [Allowed, allowed, ite_eq_right (by simpa only [decide_eq_true_eq] using valid), selected, value.facts.event]
  simp [drainServes]

theorem drain_observe (value : N.Service current item hit session actual served emission emitted)
    (selected : drainTicket current.report.final monitor = some item.id) :
    observe config monitor actual = observeDrain config monitor actual item.id := by
  have allowed := drain_allowed (config := config) value selected
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed config actual.before monitor actual.event) = true := by
    rw [value.move.supported, value.move.passed, value.move.beforeEq]
    exact allowed
  rw [observe, ite_eq_left checked, value.move.beforeEq, selected, value.facts.event]

def linkLane (lane : L.Lane) (index packet : Nat) : L.Lane :=
  ⟨.dataLink, { lane.refs with dataService := some index, dataLinkPacket := some packet }⟩

def afterDrain (monitor : Monitor) (next : L.Monitor) : Monitor :=
  { monitor with exchange := { monitor.exchange with forward := next, slots := monitor.exchange.slots + 1 } }

theorem afterDrain_healthy (selected : drainTicket state monitor = some ticket) (next : L.Monitor) :
    (afterDrain monitor next).mode ≠ .invalid := by
  change monitor.mode ≠ .invalid
  rw [drain_mode selected]
  decide

private theorem service_lane (value : N.Service current item hit session actual served emission emitted)
    (config : CampusTCPTwoProgressMonitor.Config) (lane : L.Lane) (phase : lane.phase = .dataTicket) (packet : Nat)
    (pending : actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packet) :
    L.dataLane config lane actual = linkLane lane current.report.final.services.length packet := by
  simp only [L.dataLane, phase, CampusTCPGapProgressMonitor.observeService, value.facts.recorded, emitted,
    value.move.beforeEq, pending, CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap]
  rfl

theorem lower_observe (value : N.Service current item hit session actual served emission emitted)
    (selected : drainTicket current.report.final monitor = some item.id) (primary : item.value.gateway = .primary)
    (phase : monitor.exchange.forward.lower.phase = .dataTicket)
    (ticket : monitor.exchange.forward.lower.refs.dataTicket = some item.id)
    (healthy : monitor.exchange.forward.mode ≠ .invalid) :
    ∃ packet, actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packet ∧
      observe config monitor actual = afterDrain monitor
        { monitor.exchange.forward with
          lower := linkLane monitor.exchange.forward.lower current.report.final.services.length packet
          lastOriginal := some .lower } := by
  obtain ⟨packet, pending⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at pending
  have decoded := service_lane value (config.at actual.before).forward _ phase packet pending
  have observed : L.observeData (config.at actual.before).forward monitor.exchange.forward actual .lower =
      { monitor.exchange.forward with
        lower := linkLane monitor.exchange.forward.lower current.report.final.services.length packet
        lastOriginal := some .lower } := by
    simp only [L.observeData, decoded]
    rfl
  refine ⟨packet, pending, ?_⟩
  rw [drain_observe value selected]
  simp only [observeDrain, value.facts.recorded, value.facts.ticket, primary, and_self, decide_true, ite_true,
    phase, ticket, beq_self_eq_true, CampusTCPTwoProgressMonitorFacts.phase_beq_self, Bool.true_and, observed]
  simp only [healthy, decide_false, Bool.false_eq_true, ite_false]
  rfl

theorem upper_observe (value : N.Service current item hit session actual served emission emitted)
    (selected : drainTicket current.report.final monitor = some item.id) (primary : item.value.gateway = .primary)
    (phase : monitor.exchange.forward.upper.phase = .dataTicket)
    (ticket : monitor.exchange.forward.upper.refs.dataTicket = some item.id)
    (other : ¬(monitor.exchange.forward.lower.phase = .dataTicket ∧
      monitor.exchange.forward.lower.refs.dataTicket = some item.id))
    (healthy : monitor.exchange.forward.mode ≠ .invalid) :
    ∃ packet, actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packet ∧
      observe config monitor actual = afterDrain monitor
        { monitor.exchange.forward with
          upper := linkLane monitor.exchange.forward.upper current.report.final.services.length packet
          lastOriginal := some .upper } := by
  obtain ⟨packet, pending⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at pending
  have decoded := service_lane value (config.at actual.before).forward _ phase packet pending
  have observed : L.observeData (config.at actual.before).forward monitor.exchange.forward actual .upper =
      { monitor.exchange.forward with
        upper := linkLane monitor.exchange.forward.upper current.report.final.services.length packet
        lastOriginal := some .upper } := by
    simp only [L.observeData, decoded]
    rfl
  have lower : (monitor.exchange.forward.lower.phase == .dataTicket &&
      monitor.exchange.forward.lower.refs.dataTicket == some item.id) = false := by
    apply Bool.eq_false_iff.mpr
    intro chosen
    obtain ⟨phase, ticket⟩ := Bool.and_eq_true_iff.mp chosen
    apply other
    exact ⟨of_decide_eq_true (by simpa only [CampusTCPTwoProgressMonitorFacts.phase_beq] using phase), beq_iff_eq.mp ticket⟩
  refine ⟨packet, pending, ?_⟩
  rw [drain_observe value selected]
  simp only [observeDrain, value.facts.recorded, value.facts.ticket, primary, and_self, decide_true, ite_true,
    lower, Bool.false_eq_true, ite_false, phase, ticket, beq_self_eq_true, CampusTCPTwoProgressMonitorFacts.phase_beq_self, Bool.true_and, observed]
  simp only [healthy, decide_false, Bool.false_eq_true, ite_false]
  rfl

end Netlib.Check.CampusTCPTwoTransferDrainObserve
