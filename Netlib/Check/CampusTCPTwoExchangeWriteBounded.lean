import Netlib.Check.CampusTCPTwoExchangeMonitor

/-!
# The current reverse write exits within its service window

One persistent write demand selects an actual stored write step.
That step leaves needWrite even when its checks fail.
-/

namespace Netlib.Check.CampusTCPTwoExchangeWriteBounded

open CampusTCPModel

namespace X
export CampusTCPTwoExchangeMonitor
  (Config Monitor Demand observe monitorAt nextDemand pendingAt writeDemand serves Serviced)
end X
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {cfg : X.Config} {monitor : X.Monitor}

theorem serves_write_event {event : Event} (served : X.serves (X.writeDemand cfg) event = true) :
    ∃ actor bytes, event = .write actor bytes := by
  cases event <;> simp only [X.writeDemand, X.serves, Bool.false_eq_true] at served
  rename_i actor bytes
  exact ⟨actor, bytes, rfl⟩

theorem observe_write_exits (mode : monitor.mode = .needWrite) (actual : Step input)
    {actor : Actor} {bytes : List UInt8} (event : actual.event = .write actor bytes) :
    (X.observe cfg monitor actual).mode ≠ .needWrite := by
  unfold X.observe
  split
  · simp only [mode, event]
    intro impossible
    cases impossible
  · intro impossible
    cases impossible

variable {initial final : State input} {events remaining : List Event} {steps : List (Step input)} {bound : Nat}

theorem first_exit (found : ∃ slot, slot ≤ bound ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .needWrite) :
    ∃ slot, slot ≤ bound ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .needWrite ∧
      ∀ prior, prior < slot → (X.monitorAt cfg monitor steps prior).mode = .needWrite := by
  induction bound with
  | zero =>
    obtain ⟨slot, within, exited⟩ := found
    have zero : slot = 0 := by omega
    subst slot
    exact ⟨0, Nat.le_refl _, exited, by intro prior impossible; omega⟩
  | succ bound ih =>
    by_cases earlier : ∃ slot, slot ≤ bound ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .needWrite
    · obtain ⟨slot, within, exited, first⟩ := ih earlier
      exact ⟨slot, by omega, exited, first⟩
    · obtain ⟨slot, within, exited⟩ := found
      have last : slot = bound + 1 := by
        by_cases before : slot ≤ bound
        · exact False.elim (earlier ⟨slot, before, exited⟩)
        · omega
      refine ⟨slot, within, exited, ?_⟩
      intro prior before
      by_cases mode : (X.monitorAt cfg monitor steps prior).mode = .needWrite
      · exact mode
      · exact False.elim (earlier ⟨prior, by omega, mode⟩)

theorem exits_by (mode : monitor.mode = .needWrite) (trace : Trace input initial events steps final remaining)
    (service : X.Serviced cfg initial monitor steps bound) (enough : bound ≤ steps.length) :
    ∃ slot, slot ≤ bound ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .needWrite := by
  by_cases exits : ∃ slot, slot ≤ bound ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .needWrite
  · exact exits
  · have stays : ∀ slot, slot ≤ bound → (X.monitorAt cfg monitor steps slot).mode = .needWrite := by
      intro slot within
      by_cases mode : (X.monitorAt cfg monitor steps slot).mode = .needWrite
      · exact mode
      · exact False.elim (exits ⟨slot, within, mode⟩)
    have pending : X.pendingAt cfg initial monitor steps 0 = some (X.writeDemand cfg) := by
      simp only [X.pendingAt, CampusTCPTwoExchangeMonitor.monitorAt_zero, X.nextDemand, mode]
    have persistent : ∀ slot, slot < bound → X.pendingAt cfg initial monitor steps slot = some (X.writeDemand cfg) := by
      intro slot inside
      simp only [X.pendingAt, X.nextDemand, stays slot (by omega)]
    obtain ⟨offset, inside, served⟩ := service 0 (by omega) (X.writeDemand cfg) pending (by
      simpa only [Nat.zero_add] using persistent)
    obtain ⟨actual, found, _, event, _⟩ := CampusTCPSchedule.Trace.at trace offset (by omega)
    have selected : X.serves (X.writeDemand cfg) actual.event = true := by
      rw [event]
      simpa only [Nat.zero_add] using served
    obtain ⟨actor, bytes, write⟩ := serves_write_event selected
    have exited := observe_write_exits (cfg := cfg) (stays offset (by omega)) actual write
    have stayed := stays (offset + 1) (by omega)
    rw [CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found] at stayed
    exact False.elim (exited stayed)

theorem first_exit_by (mode : monitor.mode = .needWrite) (trace : Trace input initial events steps final remaining)
    (service : X.Serviced cfg initial monitor steps bound) (enough : bound ≤ steps.length) :
    ∃ slot, slot ≤ bound ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .needWrite ∧
      ∀ prior, prior < slot → (X.monitorAt cfg monitor steps prior).mode = .needWrite :=
  first_exit (exits_by mode trace service enough)

end Netlib.Check.CampusTCPTwoExchangeWriteBounded
