import Netlib.Protocol.TCP.RecoveryEnabled

/-!
# Retirement of the current recovery head

A positive ACK of the head count retains the literal remaining records.
RTT sampling uses the retired head, including its retry status.
-/

namespace Netlib.Protocol.TCP.Recovery

theorem retire_zero (entries : List Outstanding) : retire 0 entries = entries := by
  cases entries <;> rfl

theorem retired_zero (entries : List Outstanding) : retired 0 entries = [] := by
  cases entries <;> rfl

theorem retire_head (head : Outstanding) (tail : List Outstanding) (positive : 0 < head.count) :
    retire head.count (head :: tail) = tail := by
  simp only [retire, Nat.ne_of_gt positive, ite_false, Nat.le_refl, ite_true, Nat.sub_self, retire_zero]

theorem retired_head (head : Outstanding) (tail : List Outstanding) (positive : 0 < head.count) :
    retired head.count (head :: tail) = [head] := by
  simp only [retired, Nat.ne_of_gt positive, ite_false, Nat.le_refl, ite_true, Nat.sub_self, retired_zero]

theorem head_count_le_flight (state : State) (head : Outstanding) (tail : List Outstanding)
    (source : state.outstanding = head :: tail) : head.count ≤ flight state := by
  simp only [flight, source, List.map_cons, List.sum_cons]
  exact Nat.le_add_right _ _

theorem sample_head (state : State) (head : Outstanding) (tail : List Outstanding)
    (source : state.outstanding = head :: tail) (positive : 0 < head.count) :
    sample state head.count = if head.retried then none else some ⟨head.id, head.sentAt, state.now⟩ := by
  simp only [sample, source, retired_head head tail positive, List.any_cons, List.any_nil,
    Bool.or_false, List.head?_cons, Option.map_some]

theorem acknowledge_head_enabled (state : State) (head : Outstanding) (tail : List Outstanding)
    (source : state.outstanding = head :: tail) :
    acknowledge state head.count = .ok (acknowledgeState state head.count) :=
  acknowledge_of_bounded state head.count (head_count_le_flight state head tail source)

theorem acknowledgeState_head_fields (state : State) (head : Outstanding) (tail : List Outstanding)
    (source : state.outstanding = head :: tail) (positive : 0 < head.count) :
    let after := acknowledgeState state head.count
    after.outstanding = tail ∧ after.now = state.now ∧
      after.nextId = state.nextId ∧ after.frontier = state.frontier ∧
      after.smss = state.smss ∧ after.cwnd = state.cwnd ∧ after.ssthresh = state.ssthresh ∧
      after.deadline = (if tail.isEmpty then none else some (state.now + after.rto)) ∧
      after.lastTimedOut = (if tail.isEmpty then none else state.lastTimedOut) ∧
      after.timeoutCount = (if tail.isEmpty then 0 else state.timeoutCount) ∧
      after.duplicateAcks = 0 := by
  simp only [acknowledgeState, Nat.ne_of_gt positive, ite_false, source, retire_head head tail positive]
  trivial

theorem acknowledge_head_success (state : State) (head : Outstanding) (tail : List Outstanding)
    (source : state.outstanding = head :: tail) (positive : 0 < head.count)
    (valid : state.Valid) (clocked : state.Clocked) (counts : state.Positive) :
    ∃ after, acknowledge state head.count = .ok after ∧ after.Valid ∧ after.Clocked ∧ after.Positive ∧
      after.outstanding = tail ∧ flight after = (tail.map (·.count)).sum := by
  refine ⟨acknowledgeState state head.count, acknowledge_head_enabled state head tail source,
    acknowledgeState_valid state head.count valid, acknowledgeState_clocked state head.count clocked,
    acknowledgeState_positive state head.count counts, (acknowledgeState_head_fields state head tail source positive).1, ?_⟩
  rw [flight, (acknowledgeState_head_fields state head tail source positive).1]

theorem acknowledgeState_head_retried (state : State) (head : Outstanding) (tail : List Outstanding)
    (source : state.outstanding = head :: tail) (positive : 0 < head.count) (retried : head.retried = true) :
    (acknowledgeState state head.count).estimator = state.estimator ∧
      (acknowledgeState state head.count).lastSample = state.lastSample ∧
      (acknowledgeState state head.count).rto = state.rto := by
  simp only [acknowledgeState, Nat.ne_of_gt positive, ite_false, sample_head state head tail source positive,
    retried, ite_true, Option.map_none]
  trivial

theorem acknowledgeState_head_fresh (state : State) (head : Outstanding) (tail : List Outstanding)
    (source : state.outstanding = head :: tail) (positive : 0 < head.count) (fresh : head.retried = false) :
    let estimate := RTO.observe state.estimator (state.now - head.sentAt)
    (acknowledgeState state head.count).estimator = some estimate ∧
      (acknowledgeState state head.count).lastSample = some ⟨head.id, head.sentAt, state.now⟩ ∧
      (acknowledgeState state head.count).rto = RTO.interval estimate := by
  simp only [acknowledgeState, Nat.ne_of_gt positive, ite_false, sample_head state head tail source positive,
    fresh, Bool.false_eq_true, ite_false, Option.map_some, Sample.elapsed]
  trivial

theorem acknowledgeState_tail_metadata (state : State) (head tail : Outstanding) (rest : List Outstanding)
    (source : state.outstanding = head :: tail :: rest) (positive : 0 < head.count) :
    let after := acknowledgeState state head.count
    after.outstanding = tail :: rest ∧
      after.deadline = some (state.now + after.rto) ∧
      after.lastTimedOut = state.lastTimedOut ∧ after.timeoutCount = state.timeoutCount := by
  have fields := acknowledgeState_head_fields state head (tail :: rest) source positive
  exact ⟨fields.1, fields.2.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.2.2.1⟩

theorem acknowledgeState_tail_credit (state : State) (head tail : Outstanding) (rest : List Outstanding)
    (source : state.outstanding = head :: tail :: rest) (positive : 0 < head.count)
    (previous : state.lastTimedOut = some head.id) (distinct : head.id ≠ tail.id) :
    (acknowledgeState state head.count).lastTimedOut ≠ some tail.id := by
  rw [(acknowledgeState_tail_metadata state head tail rest source positive).2.2.1, previous]
  exact fun same => distinct (Option.some.inj same)

end Netlib.Protocol.TCP.Recovery
