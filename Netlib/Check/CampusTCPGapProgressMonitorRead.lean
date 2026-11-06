import Netlib.Check.CampusTCPGapProgressMonitor
import Netlib.Check.CampusTCPGapProgressServiceBound
import Netlib.Check.CampusTCPGapProgressMonitorFacts

namespace Netlib.Check.CampusTCPGapProgressMonitorRead

open CampusTCPModel CampusTCPGapProgressMonitor

variable {input : Input}

private theorem advance_done (config : CampusTCPGapProgressMonitor.Config) (monitor : Monitor) (actual : Step input)
    (done : (advance config monitor actual).phase = .done) :
    monitor.phase = .needRead ∧ actual.result.read = config.bytes := by
  cases old : monitor.phase <;>
    simp only [advance, old, observeOutput, observeAssignment, observeService, observeReceipt, Monitor.invalid] at done
  all_goals repeat' first
    | (solve | cases done)
    | (split at done)
  all_goals
    refine ⟨rfl, ?_⟩
    have checked : (actual.result.read == config.bytes) = true := (Bool.and_eq_true_iff.mp (by assumption)).2
    exact eq_of_beq checked

theorem observe_done (config : CampusTCPGapProgressMonitor.Config) (monitor : Monitor) (actual : Step input)
    (prior : monitor.phase ≠ .done) (done : (CampusTCPGapProgressMonitor.observe config monitor actual).phase = .done) :
    actual.event = .read config.sender.other config.bytes.length ∧ actual.result.read = config.bytes := by
  unfold CampusTCPGapProgressMonitor.observe at done
  split at done
  · split at done
    · exact False.elim (prior done)
    · simp only [Monitor.invalid] at done
      repeat' first | (solve | exact False.elim (prior done)) | (solve | cases done) | split at done
    · simp only [observeOutput, Monitor.invalid] at done
      repeat' first | (solve | exact False.elim (prior done)) | (solve | cases done) | split at done
    · split at done
      · cases done
      · split at done
        · split at done
          · rename_i expectedAction actualAction nextFound actionFound matching
            obtain ⟨phase, read⟩ := advance_done config monitor actual done
            have expected : nextAction config actual.before monitor = some (.read config.sender.other config.bytes.length) := by
              simp only [nextAction, phase]
            have same := Option.some.inj (nextFound.symm.trans expected)
            subst expectedAction
            subst actualAction
            exact ⟨(CampusTCPGapProgressMonitorFacts.actionOf_iff actual.event _).mp actionFound, read⟩
          · cases done
        · cases done
  · cases done

theorem fold_done_read (config : CampusTCPGapProgressMonitor.Config) (prior : Monitor) (steps : List (Step input))
    (notDone : prior.phase ≠ .done) (done : (steps.foldl (CampusTCPGapProgressMonitor.observe config) prior).phase = .done) :
    ∃ actual ∈ steps, actual.event = .read config.sender.other config.bytes.length ∧ actual.result.read = config.bytes := by
  induction steps generalizing prior with
  | nil => exact False.elim (notDone done)
  | cons head tail ih =>
    by_cases entered : (CampusTCPGapProgressMonitor.observe config prior head).phase = .done
    · obtain ⟨event, read⟩ := observe_done config prior head notDone entered
      exact ⟨head, List.mem_cons_self, event, read⟩
    · obtain ⟨actual, member, event, read⟩ := ih (CampusTCPGapProgressMonitor.observe config prior head) entered done
      exact ⟨actual, List.mem_cons_of_mem head member, event, read⟩

theorem monitorAt_take (config : CampusTCPGapProgressMonitor.Config) (prior : Monitor) (steps : List (Step input)) (index : Nat) :
    monitorAt config prior steps index = (steps.take index).foldl (CampusTCPGapProgressMonitor.observe config) prior := by
  induction steps generalizing prior index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index => simpa only [monitorAt, List.take_succ_cons, List.foldl_cons] using ih (CampusTCPGapProgressMonitor.observe config prior head) index

theorem monitorAt_done_read_from (config : CampusTCPGapProgressMonitor.Config) (prior : Monitor) (steps : List (Step input)) (index : Nat)
    (notDone : prior.phase ≠ .done) (done : (monitorAt config prior steps index).phase = .done) :
    ∃ actual ∈ steps.take index, actual.event = .read config.sender.other config.bytes.length ∧ actual.result.read = config.bytes := by
  rw [monitorAt_take] at done
  exact fold_done_read config prior (steps.take index) notDone done

theorem monitorAt_done_read (config : CampusTCPGapProgressMonitor.Config) (steps : List (Step input)) (index output service packet : Nat)
    (done : (monitorAt config (Monitor.initial output service packet) steps index).phase = .done) :
    ∃ actual ∈ steps.take index, actual.event = .read config.sender.other config.bytes.length ∧ actual.result.read = config.bytes :=
  monitorAt_done_read_from config (Monitor.initial output service packet) steps index (by intro impossible; cases impossible) done

theorem monitorAt_done_member (config : CampusTCPGapProgressMonitor.Config) (steps : List (Step input)) (index output service packet : Nat)
    (done : (monitorAt config (Monitor.initial output service packet) steps index).phase = .done) :
    ∃ actual ∈ steps, actual.event = .read config.sender.other config.bytes.length ∧ actual.result.read = config.bytes := by
  obtain ⟨actual, member, event, read⟩ := monitorAt_done_read config steps index output service packet done
  exact ⟨actual, List.mem_of_mem_take member, event, read⟩

end Netlib.Check.CampusTCPGapProgressMonitorRead
