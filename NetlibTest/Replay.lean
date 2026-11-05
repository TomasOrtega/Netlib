import Netlib.Check.Replay

namespace NetlibTest.Replay

open Netlib.Check.Replay

private def counter : System Nat Nat Nat where
  step before _ := if before + 1 ≤ 10 then .ok (before + 1) else .error "Counter limit."
  state := id
  passed observed result := decide (observed = result)
  Matches := Eq
  correct _ _ := by simp

theorem bounded (report : Report counter initial observations) (valid : initial ≤ 10) :
    report.final ≤ 10 ∧ ∀ finding ∈ report.findings, finding.result ≤ 10 := by
  apply Trace.invariant report.trace (· ≤ 10) _ valid
  intro before observation result _ accepted
  dsimp [counter] at accepted ⊢
  split at accepted
  next bound => cases accepted; exact bound
  next => cases accepted

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let .ok report := audit counter 0 [99, 2, 3]
    | throw (IO.userError "The bounded counter replay must execute.")
  ensure (!report.compliant && report.final == 3 && report.findings.map (·.passed) == [false, true, true])
    "An incorrect observation must not replace computed state or poison later comparisons."
  let .ok accepted := audit counter 0 [1, 2, 3]
    | throw (IO.userError "The agreeing counter replay must execute.")
  ensure accepted.compliant "Every matching counter observation must agree."
  ensure (decide (accepted.final ≤ 10)) "Every certified final counter state must remain bounded."
  match audit counter 9 [10, 11] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "An execution error must prevent a report certificate.")

end NetlibTest.Replay
