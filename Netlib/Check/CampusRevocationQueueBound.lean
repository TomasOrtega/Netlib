import Netlib.Check.CampusRevocationFacts
import Netlib.Check.CampusRevocationTrace

namespace Netlib.Check.CampusRevocationModel

theorem Trace.backlog_bound (trace : Trace input budget initial steps final) :
    final.queue.pending.length ≤ initial.queue.pending.length + steps.length := by
  induction trace with
  | nil => simp
  | cons head rest ih =>
    have growth : head.effect.state.queue.pending.length ≤ head.before.queue.pending.length + 1 :=
      head.effect.payload.backlog_bound
    simp only [List.length_cons]
    omega

theorem Trace.backlog_at (trace : Trace input budget initial steps final) (count : Nat)
    (within : count ≤ steps.length) :
    (stateAt initial steps count).queue.pending.length ≤ initial.queue.pending.length + count := by
  have growth := (trace.take count within).backlog_bound
  simpa only [List.length_take, Nat.min_eq_left within] using growth

end Netlib.Check.CampusRevocationModel
