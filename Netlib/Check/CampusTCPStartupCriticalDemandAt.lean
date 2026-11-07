import Netlib.Check.CampusTCPStartupCriticalDemand

/-!
# A drive cut retains the actual OPEN

An observed drive cut contains the opening SYN in its unchanged recovery history.
-/

namespace Netlib.Check.CampusTCPStartupCriticalDemandAt

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace P
export CampusTCPStartupSelection (phaseRank)
end P
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace U
export CampusTCPStartupJobUnique (Linear)
end U
namespace M
export CampusTCPStartupMonitor (Monitor observe)
end M
namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions)
end E
namespace O
export CampusTCPStartupOpening (preparation_before opening_event mode_at drive_at)
end O

variable {input : Input} {events : List Event} {report : Report input events}
variable {state : State input} {current : TCPHandshakeRecovery.State input.active input.passive}
variable {config : CampusTCPStartupTransferMonitor.Config}

theorem phase_rank (connected : state.connection = .recovering current) :
    P.phaseRank state = TCPHandshakeRecovery.phaseLevel current.phase := by
  simp only [P.phaseRank, connected]
  cases current.phase <;> rfl

theorem source_nonidle (connected : report.final.connection = .recovering current)
    (origin : CampusTCPRecoveryStartupCurrentSources.ProducedAt report source) :
    0 < P.phaseRank report.final := by
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected
  have member := origin.recovering_member connected
  have floor := reachable.output_phase member
  have positive : 0 < source.occurrence.kind.phaseFloor := by cases source.occurrence.kind <;> decide
  rw [phase_rank connected]
  omega

theorem zero_complete (connected : state.connection = .recovering current) (linear : U.Linear state)
    (nonidle : 0 < P.phaseRank state) (zero : R.rank quantum state held = 0) : P.phaseRank state = 4 := by
  cases phase : current.phase with
  | idle => simp only [P.phaseRank, connected, phase] at nonidle; omega
  | opened value =>
    have lower := CampusTCPStartupCriticalDemand.rank_phase_one connected linear
      (by simp only [P.phaseRank, connected, phase]) (held := held) (quantum := quantum)
    omega
  | answered value =>
    have lower := CampusTCPStartupCriticalDemand.rank_phase_two connected linear
      (by simp only [P.phaseRank, connected, phase]) (held := held) (quantum := quantum)
    omega
  | acknowledged value client =>
    have lower := CampusTCPStartupCriticalDemand.rank_phase_three connected linear
      (by simp only [P.phaseRank, connected, phase]) (held := held) (quantum := quantum)
    omega
  | complete complete client server => simp only [P.phaseRank, connected, phase]

theorem complete_of_four (connected : state.connection = .recovering current) (four : P.phaseRank state = 4) :
    ∃ certificate client server, current.phase = .complete certificate client server := by
  cases phase : current.phase with
  | idle | opened _ | answered _ | acknowledged _ _ =>
    simp only [P.phaseRank, connected, phase] at four
    omega
  | complete certificate client server => exact ⟨certificate, client, server, rfl⟩

private theorem open_connection_idle (computed : openRecovering input before remote policy = .ok effect)
    (supported : effect.supported = true) : ∃ pending, before.connection = .startup .idle pending := by
  unfold openRecovering at computed
  repeat' first
    | (solve | exact ⟨_, by assumption⟩)
    | (solve | cases computed; change false = true at supported; cases supported)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem Step.open_idle (actual : Step input) (event : actual.event = .openRecovering remote policy)
    (supported : actual.result.supported = true) : ∃ pending, actual.before.connection = .startup .idle pending := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  have accepted : effect.supported = true := by simpa only [final] using supported
  rw [event] at computed
  exact open_connection_idle computed accepted

private theorem observed_supported (prior : M.Monitor) (actual : Step input)
    (drive : (M.observe config prior actual).mode = .drive) : actual.result.supported = true := by
  by_cases checked : (actual.result.supported && actual.result.passed &&
      CampusTCPStartupMonitor.allowed config actual.before prior actual.event) = true
  · simp only [Bool.and_eq_true] at checked
    exact checked.1.1
  · simp only [M.observe, checked, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at drive

section Drive

variable {whole : Report input events} {count : Nat} {within : count ≤ whole.steps.length}
variable {monitor : M.Monitor}
variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (CampusTCPSchedule.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote)}

theorem at_nonidle (value : CampusTCPStartupCurrentAt.At whole config count within profile)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive) : 0 < P.phaseRank (CampusTCPSchedule.Report.cut whole count within).final := by
  have available := O.preparation_before within ending drive
  obtain ⟨opening, found, _, event, _⟩ := O.opening_event actions within ending drive
  obtain ⟨prior, priorAt, _⟩ := O.mode_at within ending drive
    (by omega : config.startup.preparation.length ≤ count)
  obtain ⟨later, laterAt, laterMode⟩ := O.drive_at within ending drive
    (by omega : config.startup.preparation.length < config.startup.preparation.length + 1)
    (by omega : config.startup.preparation.length + 1 ≤ count)
  have observed := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found
  rw [priorAt] at observed
  have same := CampusTCPStartupEntry.observe_startup_eq prior opening later (observed.symm.trans laterAt)
  have supported := observed_supported prior opening (by rw [same]; exact laterMode)
  obtain ⟨pending, idle⟩ := Step.open_idle opening event supported
  obtain ⟨opened⟩ := CampusTCPRecoveryStartupOpened.Step.opened opening idle event
  have member : opening ∈ (CampusTCPSchedule.Report.cut whole count within).steps := List.mem_of_getElem? (by
    change (whole.steps.take count)[config.startup.preparation.length]? = some opening
    rw [List.getElem?_take_of_lt available]
    exact found)
  obtain ⟨origin⟩ := opened.source_at (CampusTCPSchedule.Report.cut whole count within) member
  exact source_nonidle value.value.connected origin

theorem at_zero_complete (value : CampusTCPStartupCurrentAt.At whole config count within profile)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive)
    (prep : CampusTCPStartupProfile.Prep config.startup)
    (zero : R.rank config.transfer.quantum (CampusTCPSchedule.Report.cut whole count within).final monitor.protection = 0) :
    P.phaseRank (CampusTCPSchedule.Report.cut whole count within).final = 4 :=
  zero_complete value.value.connected
    (CampusTCPStartupJobUnique.Report.linear (CampusTCPSchedule.Report.cut whole count within)
      (CampusTCPStartupProfileFacts.Report.cut_no_copy whole prep actions within ending))
    (at_nonidle value actions ending drive) zero

theorem incomplete_phases (connected : state.connection = .recovering current)
    (nonidle : 0 < P.phaseRank state) (incomplete : P.phaseRank state ≠ 4) :
    P.phaseRank state = 1 ∨ P.phaseRank state = 2 ∨ P.phaseRank state = 3 := by
  cases phase : current.phase with
  | idle => simp only [P.phaseRank, connected, phase] at nonidle; omega
  | opened value => exact Or.inl (by simp only [P.phaseRank, connected, phase])
  | answered value => exact Or.inr (Or.inl (by simp only [P.phaseRank, connected, phase]))
  | acknowledged value client => exact Or.inr (Or.inr (by simp only [P.phaseRank, connected, phase]))
  | complete complete client server => exact False.elim (incomplete (by simp only [P.phaseRank, connected, phase]))

theorem at_positive (value : CampusTCPStartupCurrentAt.At whole config count within profile)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive) (prep : CampusTCPStartupProfile.Prep config.startup)
    (incomplete : P.phaseRank (CampusTCPSchedule.Report.cut whole count within).final ≠ 4) :
    0 < R.rank config.transfer.quantum (CampusTCPSchedule.Report.cut whole count within).final monitor.protection := by
  apply CampusTCPStartupCriticalDemand.rank_positive value.value.connected
    (CampusTCPStartupJobUnique.Report.linear (CampusTCPSchedule.Report.cut whole count within)
      (CampusTCPStartupProfileFacts.Report.cut_no_copy whole prep actions within ending))
  exact incomplete_phases value.value.connected (at_nonidle value actions ending drive) incomplete

theorem at_pending (value : CampusTCPStartupCurrentAt.At whole config count within profile)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive) (prep : CampusTCPStartupProfile.Prep config.startup)
    (positive : 0 < R.rank config.transfer.quantum (CampusTCPSchedule.Report.cut whole count within).final monitor.protection) :
    ∃ event, CampusTCPStartupMonitor.nextDemand config (CampusTCPSchedule.Report.cut whole count within).final monitor = some event := by
  have incomplete : P.phaseRank (CampusTCPSchedule.Report.cut whole count within).final ≠ 4 := by
    intro complete
    simp only [R.rank, complete, ite_true] at positive
    omega
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable
    (CampusTCPSchedule.Report.cut whole count within) value.value.connected
  have linear := CampusTCPStartupJobUnique.Report.linear (CampusTCPSchedule.Report.cut whole count within)
    (CampusTCPStartupProfileFacts.Report.cut_no_copy whole prep actions within ending)
  have phase := incomplete_phases value.value.connected (at_nonidle value actions ending drive) incomplete
  obtain ⟨event, selected⟩ := CampusTCPStartupCriticalDemand.demand_exists value.value.connected reachable linear phase
    (config := config) (held := monitor.protection)
  exact ⟨event, by simpa only [CampusTCPStartupMonitor.nextDemand, drive] using selected⟩

end Drive

end Netlib.Check.CampusTCPStartupCriticalDemandAt
