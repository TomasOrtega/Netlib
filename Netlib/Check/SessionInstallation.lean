import Netlib.Check.SafeHandoff
import Netlib.Examples.SessionFirewallDeployment

/-!
# Installed policy at an actual authentication prefix

The native source is selected by the installed configuration identity.
Its compiled forward decision must equal the actual stored pipeline.
Current authentication, rather than the installation's earlier permission, determines the comparison.
-/

namespace Netlib.Check.SessionInstallation

open Packet Protocol

abbrev current := Check.SessionFirewall.stateAt

structure Checked (authentication : Check.EAP.Input) (requirements : List Compile.SessionFirewall.Intent)
    (after : Nat) (active : Protocol.SafeHandoff.Configuration) where
  source : Check.ConntrackLifecycle.Config
  identity : source.id = active.id
  rules : active.pipeline.forward = source.forward.compile
  fallback : active.pipeline.forwardDefault = source.forward.policy
  compiled : Compile.SessionFirewall.Certified authentication.context (current authentication after) requirements
  context : Check.StatefulRefinement.sameContext source.forward compiled.statefulSnapshot = true

def Checked.cells (checked : Checked authentication requirements after active) : Nat :=
  (Compile.ACL.partition (Compile.SessionFirewall.intents authentication.context
    (current authentication after) requirements)).cellCount +
    Check.StatefulRefinement.cellCount checked.source.forward checked.compiled.statefulSnapshot +
    Check.StatefulRefinement.cellCount checked.compiled.statefulSnapshot checked.source.forward

def Checked.passed (checked : Checked authentication requirements after active) : Bool :=
  Check.StatefulRefinement.check checked.source.forward checked.compiled.statefulSnapshot &&
    Check.StatefulRefinement.check checked.compiled.statefulSnapshot checked.source.forward

theorem Checked.forward_equivalent (checked : Checked authentication requirements after active)
    (passed : checked.passed = true) :
    Examples.SessionFirewallDeployment.ForwardEquivalent active.pipeline checked.compiled := by
  have pair : Check.StatefulRefinement.check checked.source.forward checked.compiled.statefulSnapshot = true ∧
      Check.StatefulRefinement.check checked.compiled.statefulSnapshot checked.source.forward = true := by
    simpa only [Checked.passed, Bool.and_eq_true] using passed
  have stronger := (Check.StatefulRefinement.check_correct _ _).mp pair.1
  have weaker := (Check.StatefulRefinement.check_correct _ _).mp pair.2
  intro state header
  rw [checked.rules, checked.fallback, checked.source.forward.compile_evaluate]
  have same : checked.source.forward.permits state header = checked.compiled.statefulSnapshot.permits state header :=
    Bool.eq_iff_iff.mpr ⟨stronger state header, weaker state header⟩
  cases native : checked.source.forward.evaluate state header <;>
    cases generated : checked.compiled.statefulSnapshot.evaluate state header <;>
      simp_all [Import.NftablesStateful.Snapshot.permits]

def check (authentication : Check.EAP.Input) (requirements : List Compile.SessionFirewall.Intent)
    (after : Nat) (active : Protocol.SafeHandoff.Configuration) (configs : List Check.ConntrackLifecycle.Config)
    (budget : Nat := 100000) : Except String (Checked authentication requirements after active) := do
  if after > authentication.observations.length then throw "The policy prefix exceeds the actual authentication history."
  let some source := configs.find? (·.id == active.id)
    | throw s!"No native source for installed configuration: {active.id}."
  if identity : source.id = active.id then
    if rules : active.pipeline.forward = source.forward.compile then
      if fallback : active.pipeline.forwardDefault = source.forward.policy then
        let compiled ← (Compile.SessionFirewall.compile authentication.context (current authentication after)
          requirements budget).mapError (·.describe)
        if context : Check.StatefulRefinement.sameContext source.forward compiled.statefulSnapshot = true then
          let checked : Checked authentication requirements after active :=
            ⟨source, identity, rules, fallback, compiled, context⟩
          if checked.cells > budget then throw "Current policy comparison exceeds the partition cell budget."
          return checked
        else throw "Installed policy requires the certified forward hook and priority."
      else throw "Installed forward fallback differs from its native source."
    else throw "Installed forward rules differ from their native source."
  else throw "Installed configuration identity differs from its native source."

end Netlib.Check.SessionInstallation
