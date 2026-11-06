import Netlib.Protocol.TCP.Recovery

/-!
# ACK receipt time and later processing time

A held packet retains its actual arrival time for an RTT sample.
Timer restart uses the current processing clock.
The endpoint supplies the stored receipt time from its actual receive operation.
-/

namespace Netlib.Protocol.TCP.Recovery

def touched (count : Nat) : List Outstanding → List Outstanding
  | [] => []
  | entry :: rest =>
    if count = 0 then []
    else entry :: if entry.count ≤ count then touched (count - entry.count) rest else []

def acknowledgeAtState (state sampled : State) (count : Nat) : State :=
  { sampled with
    now := state.now
    deadline := if count = 0 then state.deadline
      else if sampled.outstanding.isEmpty then none else some (state.now + sampled.rto) }

def acknowledgeAt (state : State) (count receivedAt : Nat) : Except Stop State :=
  if state.now < receivedAt then .error .ledger
  else if (touched count state.outstanding).any
      (fun entry => decide (receivedAt < entry.sentAt)) then .error .ledger
  else (acknowledge { state with now := receivedAt } count).map (fun sampled => acknowledgeAtState state sampled count)

theorem sample_time (state : State) (count : Nat) (measured : Sample)
    (selected : sample state count = some measured) : measured.acknowledgedAt = state.now := by
  unfold sample at selected
  dsimp only at selected
  split at selected
  · cases selected
  · cases head : (retired count state.outstanding).head? with
    | none => simp only [head, Option.map_none] at selected; cases selected
    | some entry =>
      simp only [head, Option.map_some, Option.some.injEq] at selected
      rw [← selected]

theorem acknowledgeAt_fields (state : State) (count receivedAt : Nat) (after : State)
    (selected : acknowledgeAt state count receivedAt = .ok after) :
    receivedAt ≤ state.now ∧ ∃ sampled,
      acknowledge { state with now := receivedAt } count = .ok sampled ∧
      after = acknowledgeAtState state sampled count := by
  unfold acknowledgeAt at selected
  split at selected
  · cases selected
  · rename_i past
    split at selected
    · cases selected
    · cases accepted : acknowledge { state with now := receivedAt } count with
      | error reason => simp [accepted, Except.map] at selected
      | ok sampled =>
        simp only [accepted, Except.map, Except.ok.injEq] at selected
        exact ⟨by omega, sampled, rfl, selected.symm⟩

theorem acknowledgeAt_now (state : State) (count receivedAt : Nat) (after : State)
    (selected : acknowledgeAt state count receivedAt = .ok after) : after.now = state.now := by
  obtain ⟨_, sampled, _, same⟩ := acknowledgeAt_fields state count receivedAt after selected
  rw [same]
  rfl

theorem acknowledgeAt_sent_before (state : State) (count receivedAt : Nat) (after : State)
    (selected : acknowledgeAt state count receivedAt = .ok after)
    (entry : Outstanding) (affected : entry ∈ touched count state.outstanding) : entry.sentAt ≤ receivedAt := by
  unfold acknowledgeAt at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · rename_i safe
      by_cases late : receivedAt < entry.sentAt
      · have someLate : (touched count state.outstanding).any
            (fun next => decide (receivedAt < next.sentAt)) = true :=
          List.any_eq_true.mpr ⟨entry, affected, by simp only [late, decide_true]⟩
        exact False.elim (safe someLate)
      · omega

theorem acknowledgeAt_flight (state : State) (count receivedAt : Nat) (after : State)
    (selected : acknowledgeAt state count receivedAt = .ok after) : flight after = flight state - count := by
  obtain ⟨_, sampled, accepted, same⟩ := acknowledgeAt_fields state count receivedAt after selected
  rw [same]
  exact acknowledge_flight { state with now := receivedAt } count sampled accepted

theorem acknowledgeAt_valid (state : State) (count receivedAt : Nat) (after : State)
    (valid : state.Valid) (selected : acknowledgeAt state count receivedAt = .ok after) : after.Valid := by
  obtain ⟨_, sampled, accepted, same⟩ := acknowledgeAt_fields state count receivedAt after selected
  have sampledValid := acknowledge_valid { state with now := receivedAt } count sampled valid accepted
  rw [same]
  exact sampledValid

theorem acknowledgeAt_deadline (state : State) (count receivedAt : Nat) (after : State)
    (selected : acknowledgeAt state count receivedAt = .ok after) (positive : count ≠ 0) :
    after.deadline = if after.outstanding.isEmpty then none else some (state.now + after.rto) := by
  obtain ⟨_, sampled, _, same⟩ := acknowledgeAt_fields state count receivedAt after selected
  simp only [same, acknowledgeAtState, positive, ite_false]

theorem acknowledgeAt_sample (state : State) (count receivedAt : Nat) (after : State)
    (selected : acknowledgeAt state count receivedAt = .ok after) (positive : count ≠ 0)
    (measured : Sample) (measurement : sample { state with now := receivedAt } count = some measured) :
    after.lastSample = some measured ∧ measured.acknowledgedAt = receivedAt := by
  obtain ⟨_, sampled, accepted, same⟩ := acknowledgeAt_fields state count receivedAt after selected
  have stored := (acknowledge_fields { state with now := receivedAt } count sampled accepted).2
  rw [same, stored]
  constructor
  · simp [acknowledgeAtState, acknowledgeState, positive, measurement]
  · exact sample_time { state with now := receivedAt } count measured measurement

end Netlib.Protocol.TCP.Recovery
