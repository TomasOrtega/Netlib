import Std

/-!
# Checked observed executions

Observations select operations and compare their computed results.
Failed comparisons never replace computed state.
-/

namespace Netlib.Check.Replay

universe u v w

structure System (State : Type u) (Observation : Type v) (Result : Type w) where
  step : State → Observation → Except String Result
  state : Result → State
  passed : Observation → Result → Bool
  Matches : Observation → Result → Prop
  correct : ∀ observation result, passed observation result = true ↔ Matches observation result

structure Finding (Observation : Type v) (Result : Type w) where
  observation : Observation
  result : Result
  passed : Bool

variable {State : Type u} {Observation : Type v} {Result : Type w}

def finding (system : System State Observation Result) (observation : Observation) (result : Result) :
    Finding Observation Result := ⟨observation, result, system.passed observation result⟩

theorem finding_correct (system : System State Observation Result) (observation : Observation) (result : Result) :
    (finding system observation result).passed = true ↔ system.Matches observation result := system.correct _ _

def Agreement (system : System State Observation Result) : State → List Observation → Prop
  | _, [] => True
  | before, observation :: observations =>
    ∃ result, system.step before observation = .ok result ∧ system.Matches observation result ∧
      Agreement system (system.state result) observations

inductive Trace (system : System State Observation Result) : State → List (Finding Observation Result) → State → Prop
  | nil (state : State) : Trace system state [] state
  | cons {before final : State} {head : Finding Observation Result} {tail : List (Finding Observation Result)}
      (computed : system.step before head.observation = .ok head.result)
      (rest : Trace system (system.state head.result) tail final) : Trace system before (head :: tail) final

theorem Trace.steps (trace : Trace system initial findings final) :
    ∀ finding ∈ findings, ∃ before, system.step before finding.observation = .ok finding.result := by
  induction trace with
  | nil => simp
  | @cons before final head tail computed rest ih =>
    intro finding member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨before, computed⟩
    · exact ih finding member

theorem Trace.invariant (trace : Trace system initial findings final) (property : State → Prop)
    (preserved : ∀ before observation result, property before → system.step before observation = .ok result →
      property (system.state result)) (valid : property initial) :
    property final ∧ ∀ finding ∈ findings, property (system.state finding.result) := by
  induction trace with
  | nil => exact ⟨valid, by simp⟩
  | @cons before final head tail computed rest ih =>
    have next := preserved before head.observation head.result valid computed
    obtain ⟨last, each⟩ := ih next
    exact ⟨last, fun finding member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact next
      · exact each finding member⟩

theorem Trace.matches (trace : Trace system initial findings final)
    (agreement : Agreement system initial (findings.map Finding.observation)) :
    ∀ finding ∈ findings, system.Matches finding.observation finding.result := by
  induction trace with
  | nil => simp
  | @cons before final head tail computed rest ih =>
    obtain ⟨actual, accepted, matched, next⟩ := agreement
    have equal : actual = head.result := Except.ok.inj (accepted.symm.trans computed)
    subst actual
    intro finding member
    rcases List.mem_cons.mp member with rfl | member
    · exact matched
    · exact ih next finding member

structure Report (system : System State Observation Result) (initial : State) (observations : List Observation) where
  final : State
  findings : List (Finding Observation Result)
  covered : findings.map Finding.observation = observations
  trace : Trace system initial findings final
  correct : findings.all Finding.passed = true ↔ Agreement system initial observations

def audit (system : System State Observation Result) (initial : State) :
    (observations : List Observation) → Except String (Report system initial observations)
  | [] => .ok ⟨initial, [], rfl, .nil initial, by simp [Agreement]⟩
  | observation :: observations => do
    match computed : system.step initial observation with
    | .error error => throw error
    | .ok result =>
      let tail ← audit system (system.state result) observations
      return ⟨tail.final, finding system observation result :: tail.findings,
        by simp only [List.map_cons, finding, tail.covered], .cons computed tail.trace, by
          simp only [List.all_cons, Bool.and_eq_true, finding_correct, tail.correct, Agreement]
          constructor
          · intro pair
            exact ⟨result, computed, pair.1, pair.2⟩
          · rintro ⟨actual, same, matched, rest⟩
            have equal : actual = result := Except.ok.inj (same.symm.trans computed)
            subst actual
            exact ⟨matched, rest⟩⟩

def Report.compliant (report : Report system initial observations) : Bool := report.findings.all Finding.passed

theorem Report.compliant_iff (report : Report system initial observations) :
    report.compliant = true ↔ Agreement system initial observations := report.correct

theorem Report.finding_matches (report : Report system initial observations) (compliant : report.compliant = true)
    (finding : Finding Observation Result) (member : finding ∈ report.findings) :
    system.Matches finding.observation finding.result := by
  have agreement := report.compliant_iff.mp compliant
  rw [← report.covered] at agreement
  exact report.trace.matches agreement finding member

end Netlib.Check.Replay
