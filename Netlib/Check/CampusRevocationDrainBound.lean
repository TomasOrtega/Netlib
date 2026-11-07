import Netlib.Check.CampusRevocationBound
import Netlib.Check.CampusRevocationQueueBound

/-!
# Actual queue drain after both revocation targets install

The same service check clears the backlog from the stale-policy interval.
Later accepted steps retain both targets and emit no queued datagrams.
-/

namespace Netlib.Check.CampusRevocationControl

open Packet Protocol
open StatefulFailover (Gateway)
open CampusRevocationModel
open CampusRevocationTargets

theorem ready_at_after (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (start slot : Nat)
    (afterCut : cut ≤ start) (order : start ≤ slot) (within : slot ≤ report.steps.length)
    (initial : ready targets (stateAt input.initial report.steps start) = true) :
    ready targets (stateAt input.initial report.steps slot) = true := by
  have first : cut + (start - cut) = start := by omega
  have last : cut + (slot - cut) = slot := by omega
  have monotone := Theory.BoundedServiceRank.rank_mono
    (length := report.steps.length - cut)
    (rank := fun offset => installRank targets (stateAt input.initial report.steps (cut + offset)))
    (fun offset inside => install_nonincrease_at report cut targets checked (cut + offset) (by omega) (by omega))
    (first := start - cut) (last := slot - cut) (by omega) (by omega)
  rw [first, last] at monotone
  have zero := (installRank_zero targets _).mpr initial
  exact (installRank_zero targets _).mp (by omega)

private theorem queue_nonincrease_at (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (closed : revoked input after = true) (start slot : Nat)
    (afterCut : cut ≤ start) (order : start ≤ slot) (within : slot < report.steps.length)
    (initial : ready targets (stateAt input.initial report.steps start) = true) :
    (stateAt input.initial report.steps (slot + 1)).queue.pending.length ≤
      (stateAt input.initial report.steps slot).queue.pending.length := by
  have current := ready_at_after report cut targets checked start slot afterCut order (Nat.le_of_lt within) initial
  obtain ⟨actual, _, before, _, next⟩ := report.trace.at slot within
  rw [← before] at current
  rw [← before, ← next]
  apply actual.effect.payload.backlog_nonincrease targets closed
  intro gateway
  exact (installed_correct targets actual.before gateway).mp ((ready_correct targets actual.before).mp current gateway)

theorem serves_deliver_strict (targets : Targets input after) (actual : Step input budget)
    (served : serves targets .deliver (some actual) = true) (positive : 0 < actual.before.queue.pending.length) :
    actual.effect.state.queue.pending.length < actual.before.queue.pending.length := by
  change actual.effect.payload.state.queue.pending.length < _
  cases payload : actual.effect.payload with
  | deliver capacity =>
    have nonzero : 0 < capacity := by simpa only [serves, payload, decide_eq_true_eq] using served
    rw [Payload.deliver_backlog]
    omega
  | campus observation result computed => simp [serves, payload] at served
  | packet call outcome computed certificate => simp [serves, payload] at served
  | idle => simp [serves, payload] at served

theorem empty_at_after (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (closed : revoked input after = true) (start slot : Nat)
    (afterCut : cut ≤ start) (order : start ≤ slot) (within : slot ≤ report.steps.length)
    (initialReady : ready targets (stateAt input.initial report.steps start) = true)
    (initialEmpty : (stateAt input.initial report.steps start).queue.pending = []) :
    (stateAt input.initial report.steps slot).queue.pending = [] := by
  have selected : start + (slot - start) = slot := by omega
  have monotone := Theory.BoundedServiceRank.rank_mono
    (length := report.steps.length - start)
    (rank := fun offset => (stateAt input.initial report.steps (start + offset)).queue.pending.length)
    (fun offset inside => queue_nonincrease_at report cut targets checked closed start (start + offset)
      afterCut (by omega) (by omega) initialReady)
    (first := 0) (last := slot - start) (by omega) (by omega)
  simp only [Nat.add_zero, selected] at monotone
  have zero : (stateAt input.initial report.steps start).queue.pending.length = 0 := by rw [initialEmpty]; rfl
  exact List.length_eq_zero_iff.mp (by omega)

theorem served_nil_after (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (closed : revoked input after = true) (start slot : Nat)
    (afterCut : cut ≤ start) (order : start ≤ slot)
    (initialReady : ready targets (stateAt input.initial report.steps start) = true)
    (initialEmpty : (stateAt input.initial report.steps start).queue.pending = [])
    (actual : Step input budget) (found : report.steps[slot]? = some actual) : actual.effect.served = [] := by
  have within : slot ≤ report.steps.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp found).1
  have currentReady := ready_at_after report cut targets checked start slot afterCut order within initialReady
  have currentEmpty := empty_at_after report cut targets checked closed start slot afterCut order within initialReady initialEmpty
  have before := (report.trace.at_step found).1
  rw [← before] at currentReady currentEmpty
  change (Theory.Queue.step actual.before.queue actual.effect.payload.tick).served = []
  apply actual.effect.payload.queue_served_nil targets closed _ currentEmpty
  intro gateway
  exact (installed_correct targets actual.before gateway).mp ((ready_correct targets actual.before).mp currentReady gateway)

theorem drain_by (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (bound : Nat) (checked : actions report cut targets = true) (serviced : service report cut targets bound = true)
    (closed : revoked input after = true)
    (enough : cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound ≤ report.steps.length) :
    (stateAt input.initial report.steps
      (cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound)).queue.pending = [] := by
  let backlog := (stateAt input.initial report.steps cut).queue.pending.length
  let barrier := cut + 2 * bound
  let capacity := backlog + 2 * bound
  have room : barrier + capacity * bound ≤ report.steps.length := by
    simpa only [barrier, capacity, backlog, slots, Nat.add_assoc] using enough
  have afterCut : cut ≤ barrier := by dsimp only [barrier]; omega
  have barrierWithin : barrier ≤ report.steps.length := by omega
  have barrierReady := install_by report cut targets bound checked serviced (show cut + 2 * bound ≤ report.steps.length from barrierWithin)
  have growth := (report.trace.drop cut).backlog_at (2 * bound) (by
    simp only [List.length_drop]
    dsimp only [barrier] at barrierWithin
    omega)
  rw [stateAt_offset] at growth
  have queueBound : (stateAt input.initial report.steps barrier).queue.pending.length ≤ capacity := growth
  let rank := fun offset => (stateAt input.initial report.steps (barrier + offset)).queue.pending.length
  have currentService := service_after report cut targets bound serviced (by omega)
  have shifted := Theory.BoundedServiceRestriction.subinterval (offset := 2 * bound)
    (count := report.steps.length - barrier) currentService (by
      dsimp only [barrier] at barrierWithin ⊢
      omega)
  have atService : Theory.BoundedServiceCheck.Serviced (report.steps.length - barrier)
      (fun offset => pending targets (stateAt input.initial report.steps (barrier + offset)))
      (fun offset => report.steps[barrier + offset]?) (serves targets) bound := by
    simpa only [barrier, Nat.add_assoc] using shifted
  have nonincrease : ∀ offset, offset < report.steps.length - barrier → rank (offset + 1) ≤ rank offset := by
    intro offset inside
    exact queue_nonincrease_at report cut targets checked closed barrier (barrier + offset)
      afterCut (by omega) (by omega) barrierReady
  have demand : ∀ offset, offset ≤ report.steps.length - barrier → 0 < rank offset →
      ∃ value, pending targets (stateAt input.initial report.steps (barrier + offset)) = some value := by
    intro offset inside positive
    have current := ready_at_after report cut targets checked barrier (barrier + offset)
      afterCut (by omega) (by omega) barrierReady
    exact ⟨.deliver, pending_deliver targets _ current positive⟩
  have persistent : ∀ offset, offset < report.steps.length - barrier → 0 < rank offset → ∀ value,
      rank (offset + 1) = rank offset →
      pending targets (stateAt input.initial report.steps (barrier + offset)) = some value →
      pending targets (stateAt input.initial report.steps (barrier + (offset + 1))) = some value := by
    intro offset inside positive value equal selected
    have current := ready_at_after report cut targets checked barrier (barrier + offset)
      afterCut (by omega) (by omega) barrierReady
    have next := ready_at_after report cut targets checked barrier (barrier + (offset + 1))
      afterCut (by omega) (by omega) barrierReady
    have first := pending_deliver targets _ current positive
    have last := pending_deliver targets _ next (show 0 < rank (offset + 1) by omega)
    exact last.trans (first.symm.trans selected)
  have strict : ∀ offset, offset < report.steps.length - barrier → 0 < rank offset → ∀ value,
      pending targets (stateAt input.initial report.steps (barrier + offset)) = some value →
      serves targets value report.steps[barrier + offset]? = true → rank (offset + 1) < rank offset := by
    intro offset inside positive value selected served
    have current := ready_at_after report cut targets checked barrier (barrier + offset)
      afterCut (by omega) (by omega) barrierReady
    have chosen := pending_deliver targets _ current positive
    have same : value = .deliver := Option.some.inj (selected.symm.trans chosen)
    subst value
    obtain ⟨actual, found, before, _, next⟩ := report.trace.at (barrier + offset) (by omega)
    rw [found] at served
    dsimp only [rank] at positive
    rw [← before] at positive
    have reduced := serves_deliver_strict targets actual served positive
    simpa only [rank, before, next, Nat.add_assoc] using reduced
  have coarse : rank 0 * bound ≤ capacity * bound := by
    simpa only [rank, Nat.add_zero] using Nat.mul_le_mul_right bound queueBound
  have zero := Theory.BoundedServiceRank.zero_after atService nonincrease demand persistent strict
    (capacity * bound) coarse (by omega)
  apply List.length_eq_zero_iff.mp
  simpa only [rank, barrier, capacity, backlog, slots, Nat.add_assoc] using zero

theorem ready_by (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (bound : Nat) (checked : actions report cut targets = true) (serviced : service report cut targets bound = true)
    (enough : cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound ≤ report.steps.length) :
    ready targets (stateAt input.initial report.steps
      (cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound)) = true := by
  have barrierWithin : cut + 2 * bound ≤ report.steps.length := by
    simp only [slots] at enough
    omega
  have initial := install_by report cut targets bound checked serviced barrierWithin
  exact ready_at_after report cut targets checked (cut + 2 * bound)
    (cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound)
    (by omega) (by simp only [slots]; omega) enough initial

theorem empty_after (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (bound : Nat) (checked : actions report cut targets = true) (serviced : service report cut targets bound = true)
    (closed : revoked input after = true)
    (enough : cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound ≤ report.steps.length)
    (slot : Nat)
    (later : cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound ≤ slot)
    (within : slot ≤ report.steps.length) : (stateAt input.initial report.steps slot).queue.pending = [] :=
  empty_at_after report cut targets checked closed
    (cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound) slot (by omega) later within
    (ready_by report cut targets bound checked serviced enough) (drain_by report cut targets bound checked serviced closed enough)

theorem future_served_nil (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (bound : Nat) (checked : actions report cut targets = true) (serviced : service report cut targets bound = true)
    (closed : revoked input after = true)
    (enough : cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound ≤ report.steps.length)
    (slot : Nat)
    (later : cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound ≤ slot)
    (actual : Step input budget) (found : report.steps[slot]? = some actual) : actual.effect.served = [] :=
  served_nil_after report cut targets checked closed
    (cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound) slot (by omega) later
    (ready_by report cut targets bound checked serviced enough) (drain_by report cut targets bound checked serviced closed enough)
    actual found

end Netlib.Check.CampusRevocationControl
