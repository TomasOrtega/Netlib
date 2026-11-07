import Netlib.Check.CampusTCPStartupEntry

/-!
# Five actual setup slots reach the data entry

The following whole action rules out a rejected step or a missing handoff snapshot.
-/

namespace Netlib.Check.CampusTCPStartupSetupBound

open CampusTCPModel

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt observe allowed actions actions_correct)
end E
namespace P
export CampusTCPStartupMonitor (Monitor Setup observe allowed nextDemand)
end P
namespace T
export CampusTCPStartupTransferConfig (snapshot)
end T
namespace S
export CampusTCPSchedule (stateAt)
end S

variable {input : Input} {events : List Event} {config : CampusTCPStartupTransferMonitor.Config}
variable {whole : Report input events}

structure Taken (config : CampusTCPStartupTransferMonitor.Config) (whole : Report input events)
    (slot : Nat) (stage : P.Setup) where
  actual : Step input
  selected : whole.steps[slot]? = some actual
  event : actual.event = CampusTCPStartupMonitor.Setup.event config stage
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  before : actual.before = S.stateAt input.initial whole.steps slot
  after : actual.result.state = S.stateAt input.initial whole.steps (slot + 1)

private theorem taken_at (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (available : slot + 1 < whole.steps.length) (prior : P.Monitor)
    (atSlot : E.monitorAt config (E.initial config) whole.steps slot = .startup prior)
    (mode : prior.mode = .setup stage) :
    ∃ taken : Taken config whole slot stage, P.observe config prior taken.actual = ⟨stage.after, none⟩ := by
  obtain ⟨actual, found, before, eventAt, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot (by omega)
  have permitted := (E.actions_correct _ _ _ _).mp actions slot (by omega)
  rw [atSlot] at permitted
  have permittedSetup : P.allowed config actual.before prior actual.event = true := by
    simpa only [E.allowed, ← before, ← eventAt] using permitted
  have event : actual.event = CampusTCPStartupMonitor.Setup.event config stage := by
    simp only [P.allowed, mode, P.nextDemand] at permittedSetup
    exact (Option.some.inj (of_decide_eq_true permittedSetup)).symm
  have following := (E.actions_correct _ _ _ _).mp actions (slot + 1) available
  rw [CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found, atSlot] at following
  have checked : (actual.result.supported && actual.result.passed && P.allowed config actual.before prior actual.event) = true := by
    by_cases accepted : (actual.result.supported && actual.result.passed && P.allowed config actual.before prior actual.event) = true
    · exact accepted
    · have invalid : P.observe config prior actual = ⟨.invalid, none⟩ := by
        simp only [P.observe, accepted, Bool.false_eq_true, ↓reduceIte]
      have outer : E.observe config (.startup prior) actual = .startup ⟨.invalid, none⟩ := by
        simp only [E.observe, invalid, reduceCtorEq, ↓reduceIte]
      rw [outer] at following
      change false = true at following
      cases following
  have flags := checked
  simp only [Bool.and_eq_true] at flags
  refine ⟨⟨actual, found, event, flags.1.1, flags.1.2, before, after⟩, ?_⟩
  simp only [P.observe, checked, mode, ↓reduceIte]

private theorem next_setup (taken : Taken config whole slot stage)
    (atSlot : E.monitorAt config (E.initial config) whole.steps slot = .startup prior)
    (observed : P.observe config prior taken.actual = ⟨stage.after, none⟩)
    (ordinary : stage.after ≠ .data) :
    E.monitorAt config (E.initial config) whole.steps (slot + 1) = .startup ⟨stage.after, none⟩ := by
  rw [CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps taken.selected, atSlot]
  simp only [E.observe, observed, ordinary, ↓reduceIte]

private theorem write_data (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (available : slot + 1 < whole.steps.length) (taken : Taken config whole slot .write)
    (atSlot : E.monitorAt config (E.initial config) whole.steps slot = .startup prior)
    (observed : P.observe config prior taken.actual = ⟨.data, none⟩) :
    ∃ handoff, E.monitorAt config (E.initial config) whole.steps (slot + 1) = .data handoff .initial := by
  have following := (E.actions_correct _ _ _ _).mp actions (slot + 1) available
  have update := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps taken.selected
  rw [atSlot] at update
  cases selected : T.snapshot taken.actual.result.state with
  | none =>
    have invalid : E.monitorAt config (E.initial config) whole.steps (slot + 1) = .invalid := by
      simpa only [E.observe, observed, selected, ↓reduceIte] using update
    simp only [invalid, E.allowed, Bool.false_eq_true] at following
  | some handoff =>
    exact ⟨handoff, by simpa only [E.observe, observed, selected, ↓reduceIte] using update⟩

structure Result (config : CampusTCPStartupTransferMonitor.Config) (whole : Report input events) (start : Nat) where
  clientRecovery : Taken config whole start .clientRecovery
  serverRecovery : Taken config whole (start + 1) .serverRecovery
  clientAck : Taken config whole (start + 2) .clientAck
  serverAck : Taken config whole (start + 3) .serverAck
  written : Taken config whole (start + 4) .write
  entry : CampusTCPStartupEntry.Entry config whole (start + 4)
  sameWrite : entry.actual = written.actual

theorem enter (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (available : start + 5 < whole.steps.length) (prior : P.Monitor)
    (atStart : E.monitorAt config (E.initial config) whole.steps start = .startup prior)
    (mode : prior.mode = .setup .clientRecovery) : Nonempty (Result config whole start) := by
  obtain ⟨clientRecovery, first⟩ := taken_at actions (by omega) prior atStart mode
  have atOne := next_setup clientRecovery atStart first (by decide)
  obtain ⟨serverRecovery, second⟩ := taken_at actions (by omega) _ atOne rfl
  have atTwo := next_setup serverRecovery atOne second (by decide)
  obtain ⟨clientAck, third⟩ := taken_at actions (by omega) _ atTwo rfl
  have atThree := next_setup clientAck atTwo third (by decide)
  obtain ⟨serverAck, fourth⟩ := taken_at actions (by omega) _ atThree rfl
  have atFour := next_setup serverAck atThree fourth (by decide)
  obtain ⟨written, fifth⟩ := taken_at actions (by omega) _ atFour rfl
  obtain ⟨handoff, entered⟩ := write_data actions (by omega) written atFour fifth
  let entry : CampusTCPStartupEntry.Entry config whole (start + 4) :=
    ⟨by omega, ⟨.setup .write, none⟩, atFour, handoff, .initial, entered⟩
  have same : entry.actual = written.actual := Option.some.inj (entry.selected.symm.trans written.selected)
  exact ⟨⟨clientRecovery, serverRecovery, clientAck, serverAck, written, entry, same⟩⟩

theorem Result.data_after (value : Result config whole start) :
    E.monitorAt config (E.initial config) whole.steps (start + 5) = .data value.entry.handoff value.entry.dataMonitor := by
  simpa only [Nat.add_assoc] using value.entry.after

end Netlib.Check.CampusTCPStartupSetupBound
