import Netlib.Check.CampusRevocationControlFrames
import Netlib.Check.CampusRevocationDenial
import Netlib.Check.CampusRevocationTrigger
import Netlib.Theory.BoundedServiceRankAfter

/-!
# Bounded revocation on one recorded execution

The same service check first installs both native targets and then serves the FIFO.
The queue bound includes outputs from the actual stale-policy interval.
-/

namespace Netlib.Check.CampusRevocationControl

open Packet Protocol
open StatefulFailover (Gateway)
open CampusRevocationModel
open CampusRevocationTargets

theorem selected_allowed (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (slot : Nat) (afterCut : cut ≤ slot)
    (actual : Step input budget) (found : report.steps[slot]? = some actual) :
    allowed targets actual = true := by
  have index : cut + (slot - cut) = slot := by omega
  have selected : (report.steps.drop cut)[slot - cut]? = some actual := by
    simpa only [List.getElem?_drop, index] using found
  exact actions_allowed report cut targets checked actual (List.mem_of_getElem? selected)

theorem service_after (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (bound : Nat) (checked : service report cut targets bound = true) (within : cut ≤ report.steps.length) :
    Theory.BoundedServiceCheck.Serviced (report.steps.length - cut)
      (fun slot => pending targets (stateAt input.initial report.steps (cut + slot)))
      (fun slot => report.steps[cut + slot]?) (serves targets) bound := by
  have shifted := Theory.BoundedServiceRestriction.subinterval (offset := cut)
    (count := report.steps.length - cut) ((service_correct report cut targets bound).mp checked) (by omega)
  have same : (fun slot => if cut + slot < cut then none else
      pending targets (stateAt input.initial report.steps (cut + slot))) =
      (fun slot => pending targets (stateAt input.initial report.steps (cut + slot))) := by
    funext slot
    split
    · omega
    · rfl
  rw [same] at shifted
  exact shifted

theorem install_nonincrease_at (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (slot : Nat) (afterCut : cut ≤ slot)
    (within : slot < report.steps.length) :
    installRank targets (stateAt input.initial report.steps (slot + 1)) ≤
      installRank targets (stateAt input.initial report.steps slot) := by
  obtain ⟨actual, found, before, _, next⟩ := report.trace.at slot within
  have permitted := selected_allowed report cut targets checked slot afterCut actual found
  rw [← before, ← next]
  exact installRank_nonincrease targets actual.before actual.effect.state
    (allowed_installed targets actual permitted)

theorem install_persistent_at (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (slot : Nat) (afterCut : cut ≤ slot)
    (within : slot < report.steps.length)
    (positive : 0 < installRank targets (stateAt input.initial report.steps slot))
    (equal : installRank targets (stateAt input.initial report.steps (slot + 1)) =
      installRank targets (stateAt input.initial report.steps slot)) :
    pending targets (stateAt input.initial report.steps (slot + 1)) =
      pending targets (stateAt input.initial report.steps slot) := by
  obtain ⟨actual, found, before, _, next⟩ := report.trace.at slot within
  have permitted := selected_allowed report cut targets checked slot afterCut actual found
  rw [← before] at positive
  rw [← before, ← next] at equal ⊢
  exact pending_install_persistent targets actual.before actual.effect.state positive
    (allowed_installed targets actual permitted) equal

theorem install_strict_at (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (slot : Nat) (afterCut : cut ≤ slot)
    (within : slot < report.steps.length) (gateway : Gateway)
    (selected : pending targets (stateAt input.initial report.steps slot) = some (.install gateway))
    (served : serves targets (.install gateway) report.steps[slot]? = true) :
    installRank targets (stateAt input.initial report.steps (slot + 1)) <
      installRank targets (stateAt input.initial report.steps slot) := by
  obtain ⟨actual, found, before, _, next⟩ := report.trace.at slot within
  have permitted := selected_allowed report cut targets checked slot afterCut actual found
  rw [found] at served
  rw [← before] at selected
  rw [← before, ← next]
  exact installRank_strict targets actual.before actual.effect.state gateway
    (allowed_installed targets actual permitted) selected (serves_install targets actual gateway served)

theorem install_by (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (bound : Nat) (checked : actions report cut targets = true)
    (serviced : service report cut targets bound = true) (enough : cut + 2 * bound ≤ report.steps.length) :
    ready targets (stateAt input.initial report.steps (cut + 2 * bound)) = true := by
  let rank := fun slot => installRank targets (stateAt input.initial report.steps (cut + slot))
  have currentService := service_after report cut targets bound serviced (by omega)
  have nonincrease : ∀ slot, slot < report.steps.length - cut → rank (slot + 1) ≤ rank slot := by
    intro slot within
    exact install_nonincrease_at report cut targets checked (cut + slot) (by omega) (by omega)
  have demand : ∀ slot, slot ≤ report.steps.length - cut → 0 < rank slot →
      ∃ value, pending targets (stateAt input.initial report.steps (cut + slot)) = some value := by
    intro slot _ positive
    obtain ⟨gateway, selected, _⟩ := pending_install targets _ positive
    exact ⟨.install gateway, selected⟩
  have persistent : ∀ slot, slot < report.steps.length - cut → 0 < rank slot → ∀ value,
      rank (slot + 1) = rank slot →
      pending targets (stateAt input.initial report.steps (cut + slot)) = some value →
      pending targets (stateAt input.initial report.steps (cut + (slot + 1))) = some value := by
    intro slot within positive value equal selected
    have same := install_persistent_at report cut targets checked (cut + slot) (by omega) (by omega) positive equal
    exact same.trans selected
  have strict : ∀ slot, slot < report.steps.length - cut → 0 < rank slot → ∀ value,
      pending targets (stateAt input.initial report.steps (cut + slot)) = some value →
      serves targets value report.steps[cut + slot]? = true → rank (slot + 1) < rank slot := by
    intro slot within positive value selected served
    obtain ⟨gateway, chosen, _⟩ := pending_install targets _ positive
    have same : value = .install gateway := Option.some.inj (selected.symm.trans chosen)
    subst value
    exact install_strict_at report cut targets checked (cut + slot) (by omega) (by omega) gateway selected served
  have coarse : rank 0 * bound ≤ 2 * bound :=
    Nat.mul_le_mul_right bound (installRank_le targets _)
  have zero := Theory.BoundedServiceRank.zero_after currentService nonincrease demand persistent strict
    (2 * bound) coarse (by omega)
  exact (installRank_zero targets _).mp zero

end Netlib.Check.CampusRevocationControl
