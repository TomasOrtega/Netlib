import Netlib.Check.CampusTCPRevocationControl

/-!
# One physical loss allowance through revocation

Every drop uses the preceding custody counter.
The shutdown suffix retains all losses in its initial state.
-/

namespace Netlib.Check.CampusTCPRevocationLoss

open CampusTCPModel
open CampusTCPRevocationMonitor (Installation)

theorem Step.loss_budget (actual : Step input) (allowance : Nat)
    (gate : CampusTCPRevocationControl.lossAllowed allowance actual.before actual.event = true)
    (prior : actual.before.custody.dropped ≤ allowance) : actual.result.state.custody.dropped ≤ allowance := by
  have count := CampusTCPCustodyFacts.Step.drop_count actual
  cases event : actual.event with
  | dropPacket id =>
    have available : actual.before.custody.dropped < allowance := by
      simpa only [event, CampusTCPRevocationControl.lossAllowed, decide_eq_true_eq] using gate
    simp only [event, CampusTCPCustodyFacts.dropEvent, ↓reduceIte] at count
    omega
  | _ =>
    all_goals simp only [event, CampusTCPCustodyFacts.dropEvent, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at count
    all_goals omega

theorem Step.budget (actual : Step input) (names : Installation → String) (allowance : Nat)
    (checked : CampusTCPRevocationControl.allowed names allowance actual.before actual.event = true)
    (prior : actual.before.custody.dropped ≤ allowance) : actual.result.state.custody.dropped ≤ allowance := by
  have count := CampusTCPCustodyFacts.Step.drop_count actual
  cases event : actual.event with
  | dropPacket id =>
    have permitted : CampusTCPRevocationControl.allowed names allowance actual.before (.dropPacket id) = true := by
      simpa only [event] using checked
    have available := CampusTCPRevocationControl.allowed_drop names allowance actual.before id permitted
    simp only [event, CampusTCPCustodyFacts.dropEvent, ↓reduceIte] at count
    omega
  | _ =>
    all_goals simp only [event, CampusTCPCustodyFacts.dropEvent, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at count
    all_goals omega

theorem Trace.budget (trace : Trace input initial events steps final remaining)
    (names : Installation → String) (allowance : Nat)
    (checked : CampusTCPRevocationControl.actions names allowance steps = true)
    (prior : initial.custody.dropped ≤ allowance) : final.custody.dropped ≤ allowance := by
  induction trace with
  | done state => exact prior
  | stop head blocked tail =>
    have first : CampusTCPRevocationControl.allowed names allowance head.before head.event = true := by
      simpa only [CampusTCPRevocationControl.actions, Bool.and_true] using checked
    exact Step.budget head names allowance first prior
  | next head supported rest ih =>
    simp only [CampusTCPRevocationControl.actions, Bool.and_eq_true] at checked
    exact ih checked.2 (Step.budget head names allowance checked.1 prior)

theorem Trace.loss_budget (trace : Trace input initial events steps final remaining) (allowance : Nat)
    (gates : ∀ actual ∈ steps, CampusTCPRevocationControl.lossAllowed allowance actual.before actual.event = true)
    (prior : initial.custody.dropped ≤ allowance) : final.custody.dropped ≤ allowance := by
  induction trace with
  | done state => exact prior
  | stop head blocked tail => exact Step.loss_budget head allowance (gates head (by simp)) prior
  | next head supported rest ih =>
    exact ih (fun actual member => gates actual (List.mem_cons_of_mem _ member))
      (Step.loss_budget head allowance (gates head (by simp)) prior)

end Netlib.Check.CampusTCPRevocationLoss
