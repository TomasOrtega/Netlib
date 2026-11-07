import Netlib.Check.CampusRevocationControl

namespace Netlib.Check.CampusRevocationControl

open Packet Protocol
open StatefulFailover (Gateway)
open CampusRevocationModel
open CampusRevocationTargets

theorem installed_correct (targets : Targets input after) (state : State) (gateway : Gateway) :
    installed targets state gateway = true ↔
      state.campus.deployment.handoff.configurations gateway = targets.get gateway :=
  sameConfiguration_correct _ _

theorem ready_correct (targets : Targets input after) (state : State) :
    ready targets state = true ↔ ∀ gateway, installed targets state gateway = true := by
  constructor
  · intro checked gateway
    have pair : installed targets state .primary = true ∧ installed targets state .standby = true := by
      simpa only [ready, Bool.and_eq_true] using checked
    cases gateway
    · exact pair.1
    · exact pair.2
  · intro each
    simp only [ready, each, Bool.and_self]

theorem installRank_nonincrease (targets : Targets input after) (before next : State)
    (retained : ∀ gateway, installed targets before gateway = true → installed targets next gateway = true) :
    installRank targets next ≤ installRank targets before := by
  have primary := retained .primary
  have standby := retained .standby
  cases first : installed targets before .primary <;>
    cases second : installed targets before .standby <;>
    cases third : installed targets next .primary <;>
    cases fourth : installed targets next .standby <;>
    simp_all [installRank]

theorem pending_install (targets : Targets input after) (state : State)
    (positive : 0 < installRank targets state) :
    ∃ gateway, pending targets state = some (.install gateway) ∧ installed targets state gateway = false := by
  cases primary : installed targets state .primary with
  | false => exact ⟨.primary, by simp [pending, primary], primary⟩
  | true =>
    have standby : installed targets state .standby = false := by
      cases selected : installed targets state .standby
      · rfl
      · simp [installRank, primary, selected] at positive
    exact ⟨.standby, by simp [pending, primary, standby], standby⟩

theorem pending_install_missing (targets : Targets input after) (state : State) (gateway : Gateway)
    (selected : pending targets state = some (.install gateway)) : installed targets state gateway = false := by
  unfold pending at selected
  split at selected
  · have same : gateway = .primary := by cases selected; rfl
    subst gateway
    simpa using (show !installed targets state .primary = true from ‹_›)
  · split at selected
    · have same : gateway = .standby := by cases selected; rfl
      subst gateway
      simpa using (show !installed targets state .standby = true from ‹_›)
    · split at selected <;> cases selected

theorem pending_install_persistent (targets : Targets input after) (before next : State)
    (positive : 0 < installRank targets before)
    (retained : ∀ gateway, installed targets before gateway = true → installed targets next gateway = true)
    (equal : installRank targets next = installRank targets before) :
    pending targets next = pending targets before := by
  have primary := retained .primary
  have standby := retained .standby
  cases first : installed targets before .primary <;>
    cases second : installed targets before .standby <;>
    cases third : installed targets next .primary <;>
    cases fourth : installed targets next .standby <;>
    simp_all [installRank, pending]

theorem installRank_strict (targets : Targets input after) (before next : State) (gateway : Gateway)
    (retained : ∀ selected, installed targets before selected = true → installed targets next selected = true)
    (selected : pending targets before = some (.install gateway))
    (completed : installed targets next gateway = true) :
    installRank targets next < installRank targets before := by
  have missing := pending_install_missing targets before gateway selected
  have primary := retained .primary
  have standby := retained .standby
  cases gateway <;>
    cases first : installed targets before .primary <;>
    cases second : installed targets before .standby <;>
    cases third : installed targets next .primary <;>
    cases fourth : installed targets next .standby <;>
    simp_all [installRank]

theorem pending_deliver (targets : Targets input after) (state : State) (installed : ready targets state = true)
    (nonempty : 0 < state.queue.pending.length) : pending targets state = some .deliver := by
  have each := (ready_correct targets state).mp installed
  have notEmpty : state.queue.pending.isEmpty = false := by
    cases empty : state.queue.pending with
    | nil => simp [empty] at nonempty
    | cons head tail => rfl
  simp [pending, each, notEmpty]

end Netlib.Check.CampusRevocationControl
