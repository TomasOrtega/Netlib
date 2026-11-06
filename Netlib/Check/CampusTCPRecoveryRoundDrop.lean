import Netlib.Check.CampusTCPRecoveryRoundPhaseBase
import Netlib.Check.CampusTCPCustodyFacts

/-!
# Actual packet drops in a recovery round

A drop consumes one current custody identity.
It retains endpoint state and gateway work.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundDrop

open CampusTCPModel CampusTCPRound
open CampusTCPRecoveryRoundPhaseBase (Anchor)
namespace C
export Theory.PacketCustody (Item Resolved resolve resolve_completes)
end C

variable {input : Input} {before : State input} {id : Nat} {actual : Step input}

structure Facts (before : State input) (id : Nat) (actual : Step input) where
  beforeEq : actual.before = before
  event : actual.event = .dropPacket id
  resolved : C.Resolved before.custody id .dropped
  computed : C.resolve before.custody id .dropped = .ok resolved
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  final : actual.result.state = { before with custody := resolved.state, time := before.time + 1 }
  output : actual.result.output = none
  service : actual.result.service = none
  receipt : actual.result.receipt = none
  application : actual.result.application = none
  read : actual.result.read = []

theorem enabled (before : State input) (item : C.Item (Transit input)) (member : item ∈ before.custody.pending) :
    ∃ actual : Step input, Nonempty (Facts before item.id actual) := by
  obtain ⟨resolved, computed⟩ := C.resolve_completes before.custody item member .dropped
  let effect : Effect input := { state := { before with custody := resolved.state, time := before.time + 1 } }
  let actual : Step input := ⟨before, .dropPacket item.id, effect, by
    simp only [step, process, processCore, prepareCustody, computed, Except.mapError,
      bind, Except.bind, pure, Except.pure, finishCustody]
    rfl⟩
  exact ⟨actual, ⟨rfl, rfl, resolved, computed, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem Facts.custody (facts : Facts before id actual) : actual.result.state.custody = facts.resolved.state := by
  rw [facts.final]

theorem Facts.dropped (facts : Facts before id actual) :
    actual.result.state.custody.dropped = before.custody.dropped + 1 := by
  rw [facts.custody]
  exact facts.resolved.dropped_of_drop

theorem Facts.work (facts : Facts before id actual) : actual.result.state.work = before.work := by rw [facts.final]
theorem Facts.outputs (facts : Facts before id actual) : actual.result.state.outputs = before.outputs := by rw [facts.final]
theorem Facts.services (facts : Facts before id actual) : actual.result.state.services = before.services := by rw [facts.final]
theorem Facts.receipts (facts : Facts before id actual) : actual.result.state.receipts = before.receipts := by rw [facts.final]
theorem Facts.connection (facts : Facts before id actual) : actual.result.state.connection = before.connection := by rw [facts.final]

theorem Facts.environment (facts : Facts before id actual) :
    CampusTCPRoundEnvironment.environment actual.result.state = CampusTCPRoundEnvironment.environment before := by
  rw [facts.final]
  rfl

theorem Facts.beforeService (facts : Facts before id actual) (gateway : Gateway) :
    beforeService input actual.result.state gateway = beforeService input before gateway := by
  rw [facts.final]
  rfl

theorem Facts.no_repeat (facts : Facts before id actual) (history : Theory.PacketCustody.History before.custody) :
    C.resolve actual.result.state.custody id .dropped = .error .notPending := by
  rw [facts.custody]
  exact facts.resolved.no_repeat history.valid .dropped

theorem Step.facts (actual : Step input) (item : C.Item (Transit input))
    (member : item ∈ actual.before.custody.pending) (event : actual.event = .dropPacket item.id) :
    Nonempty (Facts actual.before item.id actual) := by
  obtain ⟨chosen, ⟨facts⟩⟩ := enabled actual.before item member
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual facts.beforeEq
    (facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

theorem Facts.observe (facts : Facts before id actual) (config : CampusTCPRecoveryRoundMonitor.Config)
    (monitor : CampusTCPRecoveryRoundMonitor.Monitor) (action : CampusTCPRoundMonitor.Action)
    (next : CampusTCPRecoveryRoundMonitor.nextDemand config before monitor = some (.resolution action id)) :
    CampusTCPRecoveryRoundMonitor.observe config monitor actual =
      CampusTCPRecoveryRoundMonitor.observeDrop monitor id := by
  simp only [CampusTCPRecoveryRoundMonitor.observe, facts.supported, facts.passed, Bool.and_self,
    facts.event, facts.beforeEq, next, beq_self_eq_true, ite_true]

variable {events : List Event} {report : Report input events}
variable {complete : TCPHandshake.Completed input.active input.passive}
variable {current : Cut input complete}
variable {request : CampusTCPRoundStart.Request input}
variable {initial : CampusTCPRoundStart.Initial report complete request}

structure Append (current : Cut input complete) (id : Nat) (actual : Step input) where
  facts : Facts current.report.final id actual
  move : CampusTCPRoundPhaseBase.Move current actual
  endpoints : move.after.endpoints = current.endpoints

theorem Facts.append (facts : Facts current.report.final id actual) : Nonempty (Append current id actual) := by
  let report := CampusTCPSchedule.Report.appendStep current.report current.supported current.finished
    actual facts.beforeEq facts.supported
  let next : Cut input complete := ⟨_, report,
    CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl, current.endpoints,
    facts.connection.trans current.connection⟩
  let move : CampusTCPRoundPhaseBase.Move current actual :=
    ⟨next, facts.beforeEq, facts.supported, facts.passed, rfl, rfl⟩
  exact ⟨facts, move, rfl⟩

theorem append (current : Cut input complete) (item : C.Item (Transit input))
    (member : item ∈ current.report.final.custody.pending) :
    ∃ actual : Step input, Nonempty (Append current item.id actual) := by
  obtain ⟨actual, ⟨facts⟩⟩ := enabled current.report.final item member
  exact ⟨actual, facts.append⟩

theorem Append.anchor (appended : Append current id actual) (anchor : Anchor initial current) :
    Anchor initial appended.move.after := by
  refine ⟨?_, anchor.retained.trans appended.move.retained, ?_⟩
  · rw [appended.endpoints]
    exact anchor.guards
  · rw [appended.move.final, appended.facts.environment]
    exact anchor.environment

end Netlib.Check.CampusTCPRecoveryRoundDrop
