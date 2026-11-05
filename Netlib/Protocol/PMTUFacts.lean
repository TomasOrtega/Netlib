import Netlib.Protocol.PMTU

namespace Netlib.Protocol.PMTU

open Packet InternetChecksum

@[simp] theorem State.age_age (state : State) (now : Nat) :
    (state.age now).age now = state.age now := by
  cases found : state.exception with
  | none => simp [State.age, found]
  | some entry =>
    by_cases live : now < entry.expires <;> simp [State.age, found, Option.filter, live]

@[simp] theorem State.aged_current (state : State) (route : Route) (now : Nat) :
    ((state.age now).current route now) = state.current route now := by
  simp [State.current]

theorem State.expired (state : State) (entry : Entry) (found : state.exception = some entry)
    (expired : entry.expires ≤ now) : state.age now = ⟨none⟩ := by
  simp [State.age, found, Option.filter, expired]

theorem State.expired_current (state : State) (route : Route) (entry : Entry)
    (found : state.exception = some entry) (expired : entry.expires ≤ now) :
    (state.current route now) = route.mtu := by
  simp [State.current, state.expired entry found expired]

theorem State.current_lower (state : State) (route : Route) (now : Nat) :
    68 ≤ (state.current route now).val := (state.current route now).property.1

theorem State.valid_initial (route : Route) : (⟨none⟩ : State).Valid route := by
  intro entry found
  cases found

theorem reduced_below (old floor : MTU) (advertised : Word) (below : advertised.val < floor.val) :
    (reduced old floor advertised).val = min old.val floor.val := by
  simp [reduced, below]

theorem reduced_at_least_floor (old floor : MTU) (advertised : Word)
    (above : floor.val ≤ advertised.val) : (reduced old floor advertised).val = advertised.val := by
  simp [reduced, Nat.not_lt.mpr above]

theorem update_locked (policy : Policy) (route : Route) (before : State) (now : Nat) (advertised : Word)
    (locked : (route.locked || ((before.age now).exception.map (·.locked)).getD false) = true) :
    update policy route before now advertised = ⟨before.age now, .locked⟩ := by
  simp [update, locked]

theorem update_route_locked (policy : Policy) (route : Route) (before : State) (now : Nat) (advertised : Word)
    (locked : route.locked = true) :
    update policy route before now advertised = ⟨before.age now, .locked⟩ := by
  apply update_locked
  simp [locked]

theorem update_exception_locked (policy : Policy) (route : Route) (before : State) (now : Nat)
    (advertised : Word) (entry : Entry) (found : (before.age now).exception = some entry)
    (locked : entry.locked = true) :
    update policy route before now advertised = ⟨before.age now, .locked⟩ := by
  apply update_locked
  simp [found, locked]

theorem update_increase (policy : Policy) (route : Route) (before : State) (now : Nat) (advertised : Word)
    (unlocked : (route.locked || ((before.age now).exception.map (·.locked)).getD false) = false)
    (increase : (before.current route now).val < advertised.val) :
    update policy route before now advertised = ⟨before.age now, .increase⟩ := by
  simp [update, unlocked, increase]

theorem update_nonincrease (policy : Policy) (route : Route) (before : State) (now : Nat) (advertised : Word)
    (positive : 0 < policy.lifetime) :
    ((update policy route before now advertised).state.current route now).val ≤
      (before.current route now).val := by
  unfold update
  simp only [State.aged_current]
  split
  · simp
  · split
    · simp
    · rename_i notIncrease
      have reducedBound := reduced_le_old (before.current route now) policy.minimum advertised (by omega)
      split
      · simp
      · have live : now < now + policy.lifetime := by omega
        simpa only [State.current, State.age, Option.filter_some, live, decide_true,
          ↓reduceIte, Option.map_some, Option.getD_some] using reducedBound

theorem State.active_current (state : State) (route : Route) (now : Nat) (entry : Entry)
    (active : (state.age now).exception = some entry) : state.current route now = entry.mtu := by
  simp [State.current, active]

theorem update_entry_nonincrease (policy : Policy) (route : Route) (before : State) (now : Nat)
    (advertised : Word) (entry : Entry)
    (stored : (update policy route before now advertised).state.exception = some entry) :
    entry.mtu.val ≤ (before.current route now).val := by
  unfold update at stored
  simp only [State.aged_current] at stored
  split at stored
  · exact Nat.le_of_eq (congrArg Subtype.val (before.active_current route now entry stored)).symm
  · split at stored
    · exact Nat.le_of_eq (congrArg Subtype.val (before.active_current route now entry stored)).symm
    · rename_i notIncrease
      split at stored
      · exact Nat.le_of_eq (congrArg Subtype.val (before.active_current route now entry stored)).symm
      · cases Option.some.inj stored
        exact reduced_le_old _ _ _ (by omega)

theorem update_valid (policy : Policy) (route : Route) (before : State) (now : Nat)
    (advertised : Word) (valid : before.Valid route) :
    (update policy route before now advertised).state.Valid route := by
  intro entry stored
  exact Nat.le_trans (update_entry_nonincrease policy route before now advertised entry stored)
    (before.current_le_route route valid now)

theorem update_bounds (policy : Policy) (route : Route) (before : State) (now : Nat)
    (advertised : Word) (valid : before.Valid route) :
    68 ≤ ((update policy route before now advertised).state.current route now).val ∧
      ((update policy route before now advertised).state.current route now).val ≤ route.mtu.val :=
  ⟨State.current_lower _ _ _, State.current_le_route _ _ (update_valid _ _ _ _ _ valid) _⟩

theorem update_below_floor (policy : Policy) (route : Route) (before : State) (now : Nat)
    (advertised : Word)
    (unlocked : (route.locked || ((before.age now).exception.map (·.locked)).getD false) = false)
    (notIncrease : advertised.val ≤ (before.current route now).val)
    (below : advertised.val < policy.minimum.val) :
    (update policy route before now advertised).disposition = .updated ∧
      ∃ entry, (update policy route before now advertised).state.exception = some entry ∧
        entry.mtu.val = min (before.current route now).val policy.minimum.val ∧
        entry.locked = true ∧ entry.expires = now + policy.lifetime := by
  have noIncrease : ¬(before.current route now).val < advertised.val := by omega
  simp only [update, unlocked, Bool.false_eq_true, ↓reduceIte, State.aged_current, noIncrease,
    below, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
  cases found : (before.age now).exception <;>
    simp [reduced_below _ _ _ below]

theorem update_zero (policy : Policy) (route : Route) (before : State) (now : Nat)
    (unlocked : (route.locked || ((before.age now).exception.map (·.locked)).getD false) = false) :
    (update policy route before now 0).disposition = .updated ∧
      ∃ entry, (update policy route before now 0).state.exception = some entry ∧
        entry.mtu.val = min (before.current route now).val policy.minimum.val ∧
        entry.locked = true ∧ entry.expires = now + policy.lifetime := by
  apply update_below_floor _ _ _ _ _ unlocked
  · exact Nat.zero_le _
  · have minimum := policy.minimum.property.1
    change 0 < policy.minimum.val
    omega

theorem reduced_equal (old floor : MTU) (advertised : Word) (above : floor.val ≤ advertised.val)
    (same : advertised.val = old.val) : reduced old floor advertised = old := by
  apply Subtype.ext
  rw [reduced_at_least_floor _ _ _ above, same]

theorem update_equal_early (policy : Policy) (route : Route) (before : State) (now : Nat)
    (advertised : Word) (entry : Entry) (active : (before.age now).exception = some entry)
    (routeUnlocked : route.locked = false) (entryUnlocked : entry.locked = false)
    (same : advertised.val = entry.mtu.val) (above : policy.minimum.val ≤ advertised.val)
    (early : now < entry.expires - policy.lifetime / 2) :
    update policy route before now advertised = ⟨before.age now, .unchanged⟩ := by
  have current := before.active_current route now entry active
  have noIncrease : ¬(before.current route now).val < advertised.val := by rw [current, same]; omega
  have target : reduced (before.current route now) policy.minimum advertised = entry.mtu := by
    rw [current]
    exact reduced_equal _ _ _ above same
  simp [update, active, routeUnlocked, entryUnlocked, noIncrease, target, early, Nat.not_lt.mpr above]

theorem update_equal_refresh (policy : Policy) (route : Route) (before : State) (now : Nat)
    (advertised : Word) (entry : Entry) (active : (before.age now).exception = some entry)
    (routeUnlocked : route.locked = false) (entryUnlocked : entry.locked = false)
    (same : advertised.val = entry.mtu.val) (above : policy.minimum.val ≤ advertised.val)
    (later : entry.expires - policy.lifetime / 2 ≤ now) :
    update policy route before now advertised =
      ⟨⟨some ⟨entry.mtu, false, now + policy.lifetime⟩⟩, .updated⟩ := by
  have current := before.active_current route now entry active
  have noIncrease : ¬(before.current route now).val < advertised.val := by rw [current, same]; omega
  have target : reduced (before.current route now) policy.minimum advertised = entry.mtu := by
    rw [current]
    exact reduced_equal _ _ _ above same
  simp [update, active, routeUnlocked, entryUnlocked, noIncrease, target, Nat.not_lt.mpr above,
    Nat.not_lt.mpr later]

theorem update_strict_reduction (policy : Policy) (route : Route) (before : State) (now : Nat)
    (advertised : Word)
    (unlocked : (route.locked || ((before.age now).exception.map (·.locked)).getD false) = false)
    (above : policy.minimum.val ≤ advertised.val)
    (reducing : advertised.val < (before.current route now).val) :
    update policy route before now advertised =
      ⟨⟨some ⟨reduced (before.current route now) policy.minimum advertised, false,
        now + policy.lifetime⟩⟩, .updated⟩ := by
  have noIncrease : ¬(before.current route now).val < advertised.val := by omega
  have targetVal := reduced_at_least_floor (before.current route now) policy.minimum advertised above
  have refresh : ((before.age now).exception.map fun entry =>
      entry.mtu == reduced (before.current route now) policy.minimum advertised &&
        !decide (advertised.val < policy.minimum.val) &&
        decide (now < entry.expires - policy.lifetime / 2)).getD false = false := by
    cases active : (before.age now).exception with
    | none => simp
    | some entry =>
      have previousVal := congrArg Subtype.val (before.active_current route now entry active).symm
      have different : entry.mtu ≠ reduced (before.current route now) policy.minimum advertised := by
        intro same
        have values := congrArg Subtype.val same
        rw [targetVal] at values
        omega
      have differentBool := beq_eq_false_iff_ne.mpr different
      simp only [Option.map_some, Option.getD_some, differentBool, Bool.false_and]
  simp only [update, unlocked, Bool.false_eq_true, ↓reduceIte, State.aged_current, noIncrease]
  rw [refresh]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.not_lt.mpr above, decide_false]

/-- A cached path MTU can also be reduced by a matching quote from any reporter. -/
theorem feedback_forgery_cached (policy : Policy) (route : Route) (socket : Header) (before : State)
    (now : Nat) (advertised : Word) (reporter : Address)
    (unlocked : (route.locked || ((before.age now).exception.map (·.locked)).getD false) = false)
    (above : policy.minimum.val ≤ advertised.val)
    (reducing : advertised.val < (before.current route now).val) :
    ∃ result entry,
      feedback policy route socket before now ⟨.fragmentationNeeded advertised, socket, reporter⟩ = some result ∧
      result.disposition = .updated ∧ result.state.exception = some entry ∧
      entry.mtu.val = advertised.val ∧ entry.mtu.val < (before.current route now).val := by
  refine ⟨⟨⟨some ⟨reduced (before.current route now) policy.minimum advertised, false,
      now + policy.lifetime⟩⟩, .updated⟩,
    ⟨reduced (before.current route now) policy.minimum advertised, false, now + policy.lifetime⟩,
    ?_, rfl, rfl, ?_, ?_⟩
  · simp only [feedback, ↓reduceIte]
    rw [update_strict_reduction _ _ _ _ _ unlocked above reducing]
  · exact reduced_at_least_floor _ _ _ above
  · rw [reduced_at_least_floor _ _ _ above]
    exact reducing

theorem feedback_time_exceeded (policy : Policy) (route : Route) (socket : Header) (before : State)
    (now : Nat) (quote : Header) (reporter : Address) :
    feedback policy route socket before now ⟨.timeExceeded, quote, reporter⟩ = none := by
  by_cases matching : quote = socket <;> simp [feedback, matching]

theorem feedback_reassembly_timeout (policy : Policy) (route : Route) (socket : Header) (before : State)
    (now : Nat) (quote : Header) (reporter : Address) :
    feedback policy route socket before now ⟨.reassemblyTimeout, quote, reporter⟩ = none := by
  by_cases matching : quote = socket <;> simp [feedback, matching]

theorem feedback_accepted (policy : Policy) (route : Route) (socket : Header) (before : State)
    (now : Nat) (message : Feedback) (result : Result)
    (accepted : feedback policy route socket before now message = some result) :
    message.quoted = socket ∧ ∃ advertised, message.kind = .fragmentationNeeded advertised ∧
      result = update policy route before now advertised := by
  unfold feedback at accepted
  split at accepted
  · rename_i matching
    cases kind : message.kind with
    | timeExceeded | reassemblyTimeout => simp [kind] at accepted
    | fragmentationNeeded advertised =>
      simp only [kind, Option.some.injEq] at accepted
      exact ⟨matching, advertised, rfl, accepted.symm⟩
  · cases accepted

/-- A matching quote permits a reduction from any reporter address. -/
theorem feedback_forgery (policy : Policy) (route : Route) (socket : Header) (now : Nat)
    (advertised : Word) (reporter : Address) (routeUnlocked : route.locked = false)
    (above : policy.minimum.val ≤ advertised.val) (reducing : advertised.val < route.mtu.val) :
    ∃ result entry,
      feedback policy route socket ⟨none⟩ now ⟨.fragmentationNeeded advertised, socket, reporter⟩ = some result ∧
      result.disposition = .updated ∧ result.state.exception = some entry ∧
      entry.mtu.val = advertised.val ∧ entry.mtu.val < route.mtu.val := by
  have noIncrease : ¬route.mtu.val < advertised.val := by omega
  refine ⟨⟨⟨some ⟨reduced route.mtu policy.minimum advertised, false, now + policy.lifetime⟩⟩, .updated⟩,
    ⟨reduced route.mtu policy.minimum advertised, false, now + policy.lifetime⟩, ?_, rfl, rfl, ?_, ?_⟩
  · simp [feedback, update, State.age, State.current, routeUnlocked, noIncrease, Nat.not_lt.mpr above]
  · exact reduced_at_least_floor _ _ _ above
  · rw [reduced_at_least_floor _ _ _ above]
    exact reducing

def updateTrace (policy : Policy) (route : Route) (before : State) (events : List (Nat × Word)) : State :=
  events.foldl (fun state event => (update policy route state event.1 event.2).state) before

theorem updateTrace_valid (policy : Policy) (route : Route) (before : State)
    (events : List (Nat × Word)) (valid : before.Valid route) :
    (updateTrace policy route before events).Valid route := by
  induction events generalizing before with
  | nil => exact valid
  | cons event events ih =>
    exact ih _ (update_valid policy route before event.1 event.2 valid)

theorem updateTrace_prefix_bounds (policy : Policy) (route : Route) (before : State)
    (events : List (Nat × Word)) (valid : before.Valid route) (length now : Nat) :
    68 ≤ ((updateTrace policy route before (events.take length)).current route now).val ∧
      ((updateTrace policy route before (events.take length)).current route now).val ≤ route.mtu.val :=
  ⟨State.current_lower _ _ _, State.current_le_route _ _ (updateTrace_valid _ _ _ _ valid) _⟩

end Netlib.Protocol.PMTU
