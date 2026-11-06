import Netlib.Check.CampusTCPRecoveryRoundMonitor
import Netlib.Check.CampusTCPRoundMonitorRead

namespace Netlib.Check.CampusTCPRecoveryRoundMonitorRead

open CampusTCPModel CampusTCPRecoveryRoundMonitor

variable {input : Input}

theorem observe_done (config : CampusTCPRecoveryRoundMonitor.Config) (monitor : Monitor) (actual : Step input)
    (prior : monitor.round.phase ≠ .done)
    (done : (CampusTCPRecoveryRoundMonitor.observe config monitor actual).round.phase = .done) :
    actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
  unfold CampusTCPRecoveryRoundMonitor.observe at done
  split at done
  · split at done
    · exact False.elim (prior done)
    · simp only [observeDrop, Monitor.invalid, CampusTCPRoundMonitor.Monitor.invalid] at done
      repeat' first
        | (solve | exact False.elim (prior done))
        | (solve | cases done)
        | (split at done)
    · simp only [observeTimeout, Monitor.invalid, CampusTCPRoundMonitor.observeOutput,
        CampusTCPRoundMonitor.Monitor.invalid] at done
      repeat' first
        | (solve | cases done)
        | (split at done)
    · split at done
      · cases done
      · exact CampusTCPRoundMonitorRead.observe_done config.toConfig monitor.round actual prior done
  · cases done

theorem fold_done_read (config : CampusTCPRecoveryRoundMonitor.Config) (prior : Monitor) (steps : List (Step input))
    (notDone : prior.round.phase ≠ .done)
    (done : (steps.foldl (CampusTCPRecoveryRoundMonitor.observe config) prior).round.phase = .done) :
    ∃ actual ∈ steps, actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
  induction steps generalizing prior with
  | nil => exact False.elim (notDone done)
  | cons head tail ih =>
    by_cases entered : (CampusTCPRecoveryRoundMonitor.observe config prior head).round.phase = .done
    · obtain ⟨event, read⟩ := observe_done config prior head notDone entered
      exact ⟨head, List.mem_cons_self, event, read⟩
    · obtain ⟨actual, member, event, read⟩ := ih (CampusTCPRecoveryRoundMonitor.observe config prior head) entered done
      exact ⟨actual, List.mem_cons_of_mem head member, event, read⟩

theorem monitorAt_take (config : CampusTCPRecoveryRoundMonitor.Config) (prior : Monitor) (steps : List (Step input)) (index : Nat) :
    monitorAt config prior steps index = (steps.take index).foldl (CampusTCPRecoveryRoundMonitor.observe config) prior := by
  induction steps generalizing prior index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index =>
      simpa only [monitorAt, List.take_succ_cons, List.foldl_cons] using
        ih (CampusTCPRecoveryRoundMonitor.observe config prior head) index

theorem monitorAt_done_read_from (config : CampusTCPRecoveryRoundMonitor.Config) (prior : Monitor)
    (steps : List (Step input)) (index : Nat) (notDone : prior.round.phase ≠ .done)
    (done : (monitorAt config prior steps index).round.phase = .done) :
    ∃ actual ∈ steps.take index, actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
  rw [monitorAt_take] at done
  exact fold_done_read config prior (steps.take index) notDone done

theorem monitorAt_done_read (config : CampusTCPRecoveryRoundMonitor.Config) (steps : List (Step input)) (index : Nat)
    (done : (monitorAt config Monitor.initial steps index).round.phase = .done) :
    ∃ actual ∈ steps.take index, actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes :=
  monitorAt_done_read_from config Monitor.initial steps index (by decide) done

theorem monitorAt_done_member (config : CampusTCPRecoveryRoundMonitor.Config) (steps : List (Step input)) (index : Nat)
    (done : (monitorAt config Monitor.initial steps index).round.phase = .done) :
    ∃ actual ∈ steps, actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
  obtain ⟨actual, member, event, read⟩ := monitorAt_done_read config steps index done
  exact ⟨actual, List.mem_of_mem_take member, event, read⟩

end Netlib.Check.CampusTCPRecoveryRoundMonitorRead
