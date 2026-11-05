import Netlib.Check.Replay
namespace Netlib.Check.Replay
universe u v w x
variable {State : Type u} {Observation : Type v} {Result : Type w} {Value : Type x}

theorem Trace.origin (trace : Trace system initial findings final) (holds : State → Value → Prop)
    (produced : State → Finding Observation Result → Value → Prop)
    (retained : ∀ before finding value,
      system.step before finding.observation = .ok finding.result →
      holds (system.state finding.result) value → holds before value ∨ produced before finding value)
    (value : Value) (present : holds final value) :
    holds initial value ∨ ∃ prior finding later before,
      findings = prior ++ finding :: later ∧ Trace system initial prior before ∧
      system.step before finding.observation = .ok finding.result ∧ produced before finding value := by
  induction trace with
  | nil => exact .inl present
  | @cons before final head tail computed rest ih =>
    rcases ih present with previous | found
    · rcases retained before head value computed previous with old | created
      · exact .inl old
      · exact .inr ⟨[], head, tail, before, rfl, .nil before, computed, created⟩
    · obtain ⟨prior, finding, later, state, covered, prefixTrace, accepted, created⟩ := found
      exact .inr ⟨head :: prior, finding, later, state, by simp [covered],
        .cons computed prefixTrace, accepted, created⟩
end Netlib.Check.Replay
