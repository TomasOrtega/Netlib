import Netlib.Check.CampusRevocationFacts
import Netlib.Check.CampusRevocationTargets
import Netlib.Check.CampusRevocationTrace
import Netlib.Theory.BoundedServiceRank
import Netlib.Theory.BoundedServiceRestriction

/-!
# Persistent demands for actual policy installation and delivery

The update permits stale-policy processing before both targets are installed.
It retains each original policy verdict and rejects policy rollback.
-/

namespace Netlib.Check.CampusRevocationControl

open Packet Protocol
open StatefulFailover (Gateway)
open CampusRevocationModel
open CampusRevocationTargets

inductive Demand where
  | install (gateway : Gateway)
  | deliver
  deriving Repr, DecidableEq

def installed (targets : Targets input after) (state : State) (gateway : Gateway) : Bool :=
  sameConfiguration (state.campus.deployment.handoff.configurations gateway) (targets.get gateway)

def ready (targets : Targets input after) (state : State) : Bool :=
  installed targets state .primary && installed targets state .standby

def installRank (targets : Targets input after) (state : State) : Nat :=
  (if installed targets state .primary then 0 else 1) +
    (if installed targets state .standby then 0 else 1)

def pending (targets : Targets input after) (state : State) : Option Demand :=
  if !installed targets state .primary then some (.install .primary)
  else if !installed targets state .standby then some (.install .standby)
  else if state.queue.pending.isEmpty then none else some .deliver

def allowed (targets : Targets input after) (actual : Step input budget) : Bool :=
  match actual.effect.payload with
  | .campus _ result _ => match result.payload with
    | .authentication _ | .withdraw _ => false
    | .network evidence => match evidence.event with
      | .install gateway configuration => sameConfiguration configuration (targets.get gateway)
      | _ => true
  | .packet .. | .deliver _ | .idle => true

def serves (targets : Targets input after) (demand : Demand) : Option (Step input budget) → Bool
  | none => false
  | some actual => match demand, actual.effect.payload with
    | .install gateway, .campus _ result _ => match result.payload with
      | .network evidence => match evidence.event with
        | .install selected configuration => decide (selected = gateway) &&
            sameConfiguration configuration (targets.get gateway)
        | _ => false
      | _ => false
    | .deliver, .deliver capacity => decide (0 < capacity)
    | _, _ => false

def initialPassed (input : CampusRevocationModel.Input) (budget : Nat) : Bool :=
  match CampusDeployment.check input [] budget with
  | .error _ => false
  | .ok report => report.initial.passed

def actions (report : Report input budget events) (cut : Nat) (targets : Targets input after) : Bool :=
  initialPassed input budget && report.rawPassed &&
    (report.steps.take cut).all (fun actual => actual.effect.payload.policyPassed.getD true) &&
    (report.steps.drop cut).all (allowed targets)

def service (report : Report input budget events) (cut : Nat) (targets : Targets input after) (bound : Nat) : Bool :=
  Theory.BoundedServiceCheck.check report.steps.length
    (fun slot => if slot < cut then none else pending targets (stateAt input.initial report.steps slot))
    (fun slot => report.steps[slot]?) (serves targets) bound

theorem service_correct (report : Report input budget events) (cut : Nat) (targets : Targets input after) (bound : Nat) :
    service report cut targets bound = true ↔
      Theory.BoundedServiceCheck.Serviced report.steps.length
        (fun slot => if slot < cut then none else pending targets (stateAt input.initial report.steps slot))
        (fun slot => report.steps[slot]?) (serves targets) bound :=
  Theory.BoundedServiceCheck.check_correct _ _ _ _ _

def slots (backlog bound : Nat) : Nat := 2 * bound + (backlog + 2 * bound) * bound

theorem actions_allowed (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (actual : Step input budget)
    (member : actual ∈ report.steps.drop cut) : allowed targets actual = true := by
  have values : ((initialPassed input budget = true ∧ report.rawPassed = true) ∧
      (report.steps.take cut).all (fun actual => actual.effect.payload.policyPassed.getD true) = true) ∧
      (report.steps.drop cut).all (allowed targets) = true := by
    simpa only [actions, Bool.and_eq_true] using checked
  exact List.all_eq_true.mp values.2 actual member

theorem actions_rawPassed (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) : report.rawPassed = true := by
  have values : ((initialPassed input budget = true ∧ report.rawPassed = true) ∧
      (report.steps.take cut).all (fun actual => actual.effect.payload.policyPassed.getD true) = true) ∧
      (report.steps.drop cut).all (allowed targets) = true := by
    simpa only [actions, Bool.and_eq_true] using checked
  exact values.1.1.2

theorem installRank_le (targets : Targets input after) (state : State) : installRank targets state ≤ 2 := by
  simp only [installRank]
  split <;> split <;> omega

theorem installRank_zero (targets : Targets input after) (state : State) :
    installRank targets state = 0 ↔ ready targets state = true := by
  unfold installRank ready
  cases primary : installed targets state .primary <;> cases standby : installed targets state .standby <;> simp

end Netlib.Check.CampusRevocationControl
