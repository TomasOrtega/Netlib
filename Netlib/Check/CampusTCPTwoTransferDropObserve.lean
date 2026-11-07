import Netlib.Check.CampusTCPTwoTransferLossUpdate
import Netlib.Check.CampusTCPTwoProgressMonitorFacts

namespace Netlib.Check.CampusTCPTwoTransferDropObserve

open Protocol.TCP CampusTCPModel CampusTCPEnabled

namespace W
export CampusTCPTwoTransferMonitor (Config Monitor Allowed allowed observe ordinary controlDemand drainTicket)
end W
namespace M
export CampusTCPTwoProgressMonitor (DropTarget dropTarget observeDrop normalize Allowed)
end M
namespace X
export CampusTCPTwoExchangeMonitor (allowed observe)
end X
namespace G
export CampusTCPGapProgressMonitor (senderRecovery)
end G

variable {input : Input} {cfg : W.Config} {monitor : W.Monitor} {actual : Step input}
variable {state : State input} {id : Nat} {target : M.DropTarget} {recovery : Recovery.State}

private theorem local_mode_beq (left right : CampusTCPTwoProgressMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem allowed_drop_fields (allowed : W.Allowed cfg state monitor (.dropPacket id))
    (phase : monitor.exchange.mode = .forward) :
    monitor.mode ≠ .invalid ∧ W.drainTicket state monitor = none ∧ W.controlDemand monitor = none ∧
      M.Allowed (cfg.at state).forward state monitor.exchange.forward (.dropPacket id) := by
  have valid : monitor.mode ≠ .invalid := by
    intro invalid
    simp only [W.Allowed, W.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  have drainless : W.drainTicket state monitor = none := by
    cases found : W.drainTicket state monitor with
    | none => rfl
    | some ticket =>
      simp only [W.Allowed, W.allowed, valid, decide_false, Bool.false_eq_true, ite_false, found,
        CampusTCPTwoTransferMonitor.drainServes] at allowed
  have controls : W.controlDemand monitor = none := by
    cases found : W.controlDemand monitor with
    | none => rfl
    | some kind =>
      cases kind <;>
        simp only [W.Allowed, W.allowed, valid, decide_false, Bool.false_eq_true, ite_false, drainless,
          found, CampusTCPTwoTransferMonitor.Control.serves] at allowed
  refine ⟨valid, drainless, controls, ?_⟩
  simpa only [W.Allowed, W.allowed, valid, decide_false, Bool.false_eq_true, ite_false, drainless, controls,
    X.allowed, phase, M.Allowed] using allowed

theorem drop_mode (selected : M.dropTarget config state value id = some target) :
    value.mode = .originals ∨ value.mode = .recovery := by
  cases mode : value.mode <;> simp_all [M.dropTarget, local_mode_beq]

private theorem normalize_modes (config : CampusTCPTwoProgressMonitor.Config) (state : State input)
    (value : CampusTCPTwoProgressMonitor.Monitor) (runtime : G.senderRecovery config.toConfig state = some recovery)
    (valid : value.mode ≠ .invalid) (unfinished : value.mode ≠ .done) :
    (M.normalize config state value).mode ≠ .invalid ∧ (M.normalize config state value).mode ≠ .done := by
  generalize computed : M.normalize config state value = after
  unfold M.normalize at computed
  simp only [runtime] at computed
  repeat' first
    | split at computed
    | dsimp only at computed
  all_goals cases computed
  all_goals first
    | exact ⟨valid, unfinished⟩
    | (constructor <;> intro impossible <;> cases impossible)

theorem local_drop_modes (facts : CampusTCPRecoveryRoundDrop.Facts state id actual)
    (selected : M.dropTarget config state value id = some target)
    (runtime : G.senderRecovery config.toConfig state = some recovery) :
    (M.observeDrop config value actual id).mode ≠ .invalid ∧
      (M.observeDrop config value actual id).mode ≠ .done := by
  have mode := drop_mode selected
  have nextRuntime : G.senderRecovery config.toConfig actual.result.state = some recovery := by
    rw [facts.final]
    exact runtime
  rw [M.observeDrop, facts.beforeEq, selected]
  cases target <;> apply normalize_modes _ _ _ nextRuntime
  all_goals rcases mode with mode | mode <;> rw [mode] <;> decide

def afterDrop (cfg : W.Config) (monitor : W.Monitor) (actual : Step input) (id : Nat) : W.Monitor :=
  { monitor with exchange := { monitor.exchange with
    forward := M.observeDrop (cfg.at actual.before).forward monitor.exchange.forward actual id
    drops := monitor.exchange.drops ++ [id]
    slots := monitor.exchange.slots + 1 } }

theorem observe_drop (facts : CampusTCPRecoveryRoundDrop.Facts state id actual)
    (phase : monitor.exchange.mode = .forward) (allowed : W.Allowed cfg state monitor (.dropPacket id))
    (selected : M.dropTarget (cfg.at state).forward state monitor.exchange.forward id = some target)
    (runtime : G.senderRecovery (cfg.at state).forward.toConfig state = some recovery) :
    W.observe cfg monitor actual = afterDrop cfg monitor actual id := by
  obtain ⟨valid, drainless, controls, localAllowed⟩ := allowed_drop_fields allowed phase
  have afterModes := local_drop_modes facts selected runtime
  have localStep := CampusTCPTwoProgressMonitorFacts.observe_drop (cfg.at state).forward monitor.exchange.forward actual
    facts.supported facts.passed (by rw [facts.beforeEq, facts.event]; exact localAllowed) facts.event
  have exchangeAllowed : X.allowed (cfg.at actual.before) actual.before monitor.exchange actual.event = true := by
    simpa only [X.allowed, phase, M.Allowed, facts.beforeEq, facts.event] using localAllowed
  have exchangeChecked : (actual.result.supported && actual.result.passed &&
      X.allowed (cfg.at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [facts.supported, facts.passed]
    exact exchangeAllowed
  have exchangeStep : X.observe (cfg.at actual.before) monitor.exchange actual = (afterDrop cfg monitor actual id).exchange := by
    rw [X.observe, ite_eq_left exchangeChecked]
    simp only [phase, facts.beforeEq]
    rw [localStep]
    simp only [local_mode_beq, afterModes.1, afterModes.2, decide_false, Bool.false_eq_true, ite_false]
    congr 1
    · rw [facts.beforeEq]
    · change (match actual.event with | .dropPacket selected => monitor.exchange.drops ++ [selected] | _ => monitor.exchange.drops) = _
      rw [facts.event]
    · change (match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) = _
      rw [facts.event]
  have checked : (actual.result.supported && actual.result.passed && W.allowed cfg actual.before monitor actual.event) = true := by
    rw [facts.supported, facts.passed, facts.beforeEq, facts.event]
    exact allowed
  rw [W.observe, ite_eq_left checked, facts.beforeEq, drainless, controls, W.ordinary, exchangeStep]
  simp only [afterDrop, phase, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]

theorem healthy (facts : CampusTCPRecoveryRoundDrop.Facts state id actual)
    (phase : monitor.exchange.mode = .forward) (allowed : W.Allowed cfg state monitor (.dropPacket id))
    (selected : M.dropTarget (cfg.at state).forward state monitor.exchange.forward id = some target)
    (runtime : G.senderRecovery (cfg.at state).forward.toConfig state = some recovery) :
    (W.observe cfg monitor actual).mode ≠ .invalid := by
  rw [observe_drop facts phase allowed selected runtime]
  exact (allowed_drop_fields allowed phase).1

theorem counters (facts : CampusTCPRecoveryRoundDrop.Facts state id actual)
    (phase : monitor.exchange.mode = .forward) (allowed : W.Allowed cfg state monitor (.dropPacket id))
    (selected : M.dropTarget (cfg.at state).forward state monitor.exchange.forward id = some target)
    (runtime : G.senderRecovery (cfg.at state).forward.toConfig state = some recovery) :
    CampusTCPTwoTransferLossHistory.DropFrame cfg monitor actual id := by
  have observed := observe_drop facts phase allowed selected runtime
  have countFields := Prod.mk.inj (CampusTCPTwoProgressMonitorFacts.drop_counters (cfg.at state).forward
    monitor.exchange.forward actual id (by rw [facts.beforeEq]; exact selected))
  exact ⟨by rw [observed]; simpa only [afterDrop, facts.beforeEq] using countFields.2,
    by rw [observed]; simpa only [afterDrop, facts.beforeEq] using countFields.1,
    by rw [observed]; rfl, by rw [observed]; rfl⟩

end Netlib.Check.CampusTCPTwoTransferDropObserve
