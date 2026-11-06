import Netlib.Check.CampusTCPRoundMonitor
import Netlib.Check.CampusTCPRoundServiceBound

/-!
# Read origin in the actual monitored suffix

Only the selected application read can enter the done phase.
The fold and prefix results retain its actual stored operation.
-/

namespace Netlib.Check.CampusTCPRoundMonitorRead

open CampusTCPModel CampusTCPRoundMonitor

variable {input : Input}

private theorem advance_done (config : CampusTCPRoundMonitor.Config) (monitor : Monitor) (actual : Step input)
    (done : (advance config monitor actual).phase = .done) :
    monitor.phase = .needRead ∧ actual.result.read = config.bytes := by
  cases old : monitor.phase <;>
    simp only [advance, old, observeOutput, observeAssignment, observeService, observeReceipt, Monitor.invalid] at done
  all_goals repeat' first
    | (solve | cases done)
    | (solve | exact ⟨rfl, eq_of_beq (by assumption)⟩)
    | (split at done)

theorem observe_done (config : CampusTCPRoundMonitor.Config) (monitor : Monitor) (actual : Step input)
    (prior : monitor.phase ≠ .done) (done : (CampusTCPRoundMonitor.observe config monitor actual).phase = .done) :
    actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
  unfold CampusTCPRoundMonitor.observe at done
  split at done
  · split at done
    · exact False.elim (prior done)
    · split at done
      · split at done
        · rename_i expectedAction actualAction nextFound actionFound matching
          obtain ⟨phase, read⟩ := advance_done config monitor actual done
          have expected : nextAction config actual.before monitor = some (.read .server config.bytes.length) := by
            simp only [nextAction, phase]
          have same := Option.some.inj (nextFound.symm.trans expected)
          subst expectedAction
          subst actualAction
          exact ⟨CampusTCPRoundServiceBound.action_event actual.event _ actionFound, read⟩
        · cases done
      · cases done
  · cases done

theorem fold_done_read (config : CampusTCPRoundMonitor.Config) (prior : Monitor) (steps : List (Step input))
    (notDone : prior.phase ≠ .done)
    (done : (steps.foldl (CampusTCPRoundMonitor.observe config) prior).phase = .done) :
    ∃ actual ∈ steps, actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
  induction steps generalizing prior with
  | nil => exact False.elim (notDone done)
  | cons head tail ih =>
    by_cases entered : (CampusTCPRoundMonitor.observe config prior head).phase = .done
    · obtain ⟨event, read⟩ := observe_done config prior head notDone entered
      exact ⟨head, List.mem_cons_self, event, read⟩
    · obtain ⟨actual, member, event, read⟩ := ih (CampusTCPRoundMonitor.observe config prior head) entered done
      exact ⟨actual, List.mem_cons_of_mem head member, event, read⟩

theorem monitorAt_take (config : CampusTCPRoundMonitor.Config) (prior : Monitor) (steps : List (Step input)) (index : Nat) :
    monitorAt config prior steps index = (steps.take index).foldl (CampusTCPRoundMonitor.observe config) prior := by
  induction steps generalizing prior index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index =>
      simpa only [monitorAt, List.take_succ_cons, List.foldl_cons] using
        ih (CampusTCPRoundMonitor.observe config prior head) index

theorem monitorAt_done_read (config : CampusTCPRoundMonitor.Config) (steps : List (Step input)) (index : Nat)
    (done : (monitorAt config Monitor.initial steps index).phase = .done) :
    ∃ actual ∈ steps.take index, actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
  rw [monitorAt_take] at done
  exact fold_done_read config Monitor.initial (steps.take index) (by decide) done

theorem monitorAt_done_member (config : CampusTCPRoundMonitor.Config) (steps : List (Step input)) (index : Nat)
    (done : (monitorAt config Monitor.initial steps index).phase = .done) :
    ∃ actual ∈ steps, actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
  obtain ⟨actual, member, event, read⟩ := monitorAt_done_read config steps index done
  exact ⟨actual, List.mem_of_mem_take member, event, read⟩

end Netlib.Check.CampusTCPRoundMonitorRead
