import Netlib.Protocol.TCP.RTO

/-!
# A bounded timer profile for established TCP data

Unique bytes in flight are at most one effective MSS.
The timing records contain no stream bytes.
Endpoint histories supply their byte origin and actual output evidence.
The profile stops before fast recovery or excessive-retransmission handling.
-/

namespace Netlib.Protocol.TCP.Recovery

structure Outstanding where
  id : Nat
  start : Nat
  count : Nat
  sentAt : Nat
  lastAt : Nat
  retried : Bool := false
  deriving Repr, BEq, DecidableEq

structure Sample where
  id : Nat
  sentAt : Nat
  acknowledgedAt : Nat
  deriving Repr, BEq, DecidableEq

def Sample.elapsed (value : Sample) : Nat := value.acknowledgedAt - value.sentAt

structure State where
  now : Nat
  smss : Nat
  outstanding : List Outstanding
  nextId : Nat
  frontier : Nat
  estimator : Option RTO.Estimator
  lastSample : Option Sample
  rto : Nat
  deadline : Option Nat
  cwnd : Nat
  ssthresh : Nat
  lastTimedOut : Option Nat
  timeoutCount : Nat
  duplicateAcks : Nat
  deriving Repr, BEq, DecidableEq

def flight (state : State) : Nat := (state.outstanding.map (·.count)).sum

def State.Valid (state : State) : Prop :=
  0 < state.smss ∧ 1000 ≤ state.rto ∧ state.cwnd = state.smss ∧ flight state ≤ state.smss

instance (state : State) : Decidable state.Valid := by
  unfold State.Valid
  infer_instance

def initial (smss : Nat) : State :=
  ⟨0, smss, [], 0, 0, none, none, 1000, none, smss, 65535, none, 0, 0⟩

inductive Stop where
  | backwardClock | early | idle | ledger
  | fastRecovery | failureHandling | persist
  deriving Repr, BEq, DecidableEq

def Stop.unsupported : Stop → Bool
  | .fastRecovery | .failureHandling | .persist => true
  | _ => false

def advance (state : State) (now : Nat) : Except Stop State :=
  if now < state.now then .error .backwardClock
  else .ok { state with now := now }

def SendReady (state : State) (count : Nat) : Prop :=
  0 < count ∧ flight state + count ≤ state.smss ∧ flight state + count ≤ state.cwnd

instance (state : State) (count : Nat) : Decidable (SendReady state count) := by
  unfold SendReady
  infer_instance

def sent (state : State) (count : Nat) : State := {
  state with
  outstanding := state.outstanding ++ [⟨state.nextId, state.frontier, count, state.now, state.now, false⟩]
  nextId := state.nextId + 1
  frontier := state.frontier + count
  deadline := match state.deadline with | none => some (state.now + state.rto) | some time => some time }

def retire (count : Nat) : List Outstanding → List Outstanding
  | [] => []
  | entry :: rest =>
    if count = 0 then entry :: rest
    else if entry.count ≤ count then retire (count - entry.count) rest
    else { entry with start := entry.start + count, count := entry.count - count } :: rest

def retired (count : Nat) : List Outstanding → List Outstanding
  | [] => []
  | entry :: rest =>
    if count = 0 then []
    else if entry.count ≤ count then entry :: retired (count - entry.count) rest
    else []

def sample (state : State) (count : Nat) : Option Sample :=
  let entries := retired count state.outstanding
  if entries.any (·.retried) then none
  else entries.head?.map (fun entry => ⟨entry.id, entry.sentAt, state.now⟩)

def acknowledgeState (state : State) (count : Nat) : State :=
  if count = 0 then state
  else
    let remaining := retire count state.outstanding
    let measured := sample state count
    let estimate := measured.map (fun value => RTO.observe state.estimator value.elapsed)
    let rto := match estimate with | none => state.rto | some value => RTO.interval value
    { state with
      outstanding := remaining
      estimator := match estimate with | none => state.estimator | some value => some value
      lastSample := match measured with | none => state.lastSample | some value => some value
      rto := rto
      deadline := if remaining.isEmpty then none else some (state.now + rto)
      lastTimedOut := if remaining.isEmpty then none else state.lastTimedOut
      timeoutCount := if remaining.isEmpty then 0 else state.timeoutCount
      duplicateAcks := 0 }

def acknowledge (state : State) (count : Nat) : Except Stop State :=
  if count > flight state then .error .ledger
  else .ok (acknowledgeState state count)

def duplicate (state : State) : Except Stop State :=
  if state.duplicateAcks + 1 ≥ 3 then .error .fastRecovery
  else .ok { state with duplicateAcks := state.duplicateAcks + 1 }

def timeoutState (state : State) (entry : Outstanding) (rest : List Outstanding) : State :=
  let repeated := state.lastTimedOut = some entry.id
  { state with
    outstanding := { entry with lastAt := state.now, retried := true } :: rest
    rto := 2 * state.rto
    deadline := some (state.now + 2 * state.rto)
    cwnd := state.smss
    ssthresh := if repeated then state.ssthresh else max (flight state / 2) (2 * state.smss)
    lastTimedOut := some entry.id
    timeoutCount := if repeated then state.timeoutCount + 1 else 1
    duplicateAcks := 0 }

def timeout (state : State) : Except Stop (Nat × State) :=
  match state.outstanding, state.deadline with
  | [], _ | _, none => .error .idle
  | entry :: rest, some deadline =>
    if entry.count = 0 then .error .ledger
    else if state.now < deadline ∨ state.now < entry.lastAt + state.rto then .error .early
    else if state.lastTimedOut = some entry.id ∧ state.timeoutCount ≥ 2 then .error .failureHandling
    else .ok (entry.count, timeoutState state entry rest)

theorem initial_valid (smss : Nat) (positive : 0 < smss) : (initial smss).Valid := by
  simp [State.Valid, initial, flight, positive]

theorem sent_flight (state : State) (count : Nat) : flight (sent state count) = flight state + count := by
  simp [flight, sent]

theorem sent_smss (state : State) (count : Nat) : (sent state count).smss = state.smss := rfl

theorem sent_valid (state : State) (count : Nat) (valid : state.Valid) (ready : SendReady state count) :
    (sent state count).Valid := by
  exact ⟨valid.1, valid.2.1, valid.2.2.1, by rw [sent_flight]; exact ready.2.1⟩

theorem advance_fields (state : State) (now : Nat) (after : State) (accepted : advance state now = .ok after) :
    state.now ≤ now ∧ after = { state with now := now } := by
  unfold advance at accepted
  split at accepted
  · cases accepted
  · cases accepted
    exact ⟨by omega, rfl⟩

theorem advance_valid (state : State) (now : Nat) (after : State) (valid : state.Valid)
    (accepted : advance state now = .ok after) : after.Valid := by
  rw [(advance_fields state now after accepted).2]
  exact valid

theorem retire_count (count : Nat) (entries : List Outstanding) :
    ((retire count entries).map (·.count)).sum = (entries.map (·.count)).sum - count := by
  induction entries generalizing count with
  | nil => simp [retire]
  | cons entry rest ih =>
    unfold retire
    split
    · rename_i zero
      simp [zero]
    · split
      · rename_i bound
        rw [ih]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rename_i bound
        simp only [List.map_cons, List.sum_cons]
        omega

theorem acknowledgeState_flight (state : State) (count : Nat) :
    flight (acknowledgeState state count) = flight state - count := by
  unfold acknowledgeState
  split
  · rename_i zero
    simp [zero]
  · exact retire_count count state.outstanding

theorem acknowledgeState_smss (state : State) (count : Nat) :
    (acknowledgeState state count).smss = state.smss := by
  unfold acknowledgeState
  split <;> rfl

theorem acknowledgeState_cwnd (state : State) (count : Nat) :
    (acknowledgeState state count).cwnd = state.cwnd := by
  unfold acknowledgeState
  split <;> rfl

theorem acknowledgeState_valid (state : State) (count : Nat) (valid : state.Valid) :
    (acknowledgeState state count).Valid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [acknowledgeState_smss]
    exact valid.1
  · unfold acknowledgeState
    split
    · exact valid.2.1
    · cases measured : sample state count with
      | none => simpa only [measured, Option.map_none] using valid.2.1
      | some value => exact RTO.interval_floor _ 1
  · rw [acknowledgeState_cwnd, acknowledgeState_smss]
    exact valid.2.2.1
  · rw [acknowledgeState_flight, acknowledgeState_smss]
    have bounded := valid.2.2.2
    omega

theorem acknowledge_fields (state : State) (count : Nat) (after : State)
    (accepted : acknowledge state count = .ok after) :
    count ≤ flight state ∧ after = acknowledgeState state count := by
  unfold acknowledge at accepted
  split at accepted
  · cases accepted
  · cases accepted
    exact ⟨by omega, rfl⟩

theorem acknowledge_valid (state : State) (count : Nat) (after : State) (valid : state.Valid)
    (accepted : acknowledge state count = .ok after) : after.Valid := by
  rw [(acknowledge_fields state count after accepted).2]
  exact acknowledgeState_valid state count valid

theorem acknowledge_flight (state : State) (count : Nat) (after : State)
    (accepted : acknowledge state count = .ok after) : flight after = flight state - count := by
  rw [(acknowledge_fields state count after accepted).2]
  exact acknowledgeState_flight state count

theorem acknowledge_zero (state : State) : acknowledge state 0 = .ok state := by
  simp [acknowledge, acknowledgeState]

theorem duplicate_fields (state after : State) (accepted : duplicate state = .ok after) :
    after = { state with duplicateAcks := state.duplicateAcks + 1 } ∧ after.duplicateAcks < 3 := by
  unfold duplicate at accepted
  split at accepted
  · cases accepted
  · cases accepted
    exact ⟨rfl, by change state.duplicateAcks + 1 < 3; omega⟩

theorem duplicate_valid (state after : State) (valid : state.Valid)
    (accepted : duplicate state = .ok after) : after.Valid := by
  rw [(duplicate_fields state after accepted).1]
  exact valid

structure TimeoutFacts (state : State) (count : Nat) (after : State) where
  entry : Outstanding
  rest : List Outstanding
  deadline : Nat
  source : state.outstanding = entry :: rest
  timer : state.deadline = some deadline
  positive : 0 < entry.count
  due : deadline ≤ state.now
  since : entry.lastAt + state.rto ≤ state.now
  selected : count = entry.count
  changed : after = timeoutState state entry rest

def timeout_facts (state : State) (count : Nat) (after : State)
    (accepted : timeout state = .ok (count, after)) : TimeoutFacts state count after := by
  cases entries : state.outstanding with
  | nil => simp [timeout, entries] at accepted
  | cons entry rest =>
    cases timer : state.deadline with
    | none => simp [timeout, entries, timer] at accepted
    | some deadline =>
      simp only [timeout, entries, timer] at accepted
      split at accepted
      · cases accepted
      · rename_i nonzero
        split at accepted
        · cases accepted
        · rename_i elapsed
          split at accepted
          · cases accepted
          · cases accepted
            exact ⟨entry, rest, deadline, entries, timer, by omega, by omega, by omega, rfl, rfl⟩

theorem timeoutState_flight (state : State) (entry : Outstanding) (rest : List Outstanding)
    (source : state.outstanding = entry :: rest) : flight (timeoutState state entry rest) = flight state := by
  simp [flight, timeoutState, source]

theorem timeout_valid (state : State) (count : Nat) (after : State) (valid : state.Valid)
    (accepted : timeout state = .ok (count, after)) : after.Valid := by
  have facts := timeout_facts state count after accepted
  rw [facts.changed]
  refine ⟨valid.1, ?_, rfl, ?_⟩
  · change 1000 ≤ 2 * state.rto
    have floor := valid.2.1
    omega
  · rw [timeoutState_flight state facts.entry facts.rest facts.source]
    exact valid.2.2.2

theorem timeout_bounds (state : State) (count : Nat) (after : State)
    (accepted : timeout state = .ok (count, after)) : 0 < count ∧ count ≤ flight state := by
  have facts := timeout_facts state count after accepted
  rw [facts.selected]
  refine ⟨facts.positive, ?_⟩
  simp [flight, facts.source]

theorem timeout_flight (state : State) (count : Nat) (after : State)
    (accepted : timeout state = .ok (count, after)) : flight after = flight state := by
  have facts := timeout_facts state count after accepted
  rw [facts.changed]
  exact timeoutState_flight state facts.entry facts.rest facts.source

theorem timeout_smss (state : State) (count : Nat) (after : State)
    (accepted : timeout state = .ok (count, after)) : after.smss = state.smss := by
  exact (congrArg State.smss (timeout_facts state count after accepted).changed).trans rfl

theorem timeout_backoff (state : State) (count : Nat) (after : State)
    (accepted : timeout state = .ok (count, after)) :
    after.rto = 2 * state.rto ∧ after.deadline = some (state.now + 2 * state.rto) := by
  rw [(timeout_facts state count after accepted).changed]
  exact ⟨rfl, rfl⟩

theorem timeout_threshold (state : State) (count : Nat) (after : State)
    (accepted : timeout state = .ok (count, after)) :
    after.ssthresh = if state.lastTimedOut = some (timeout_facts state count after accepted).entry.id
      then state.ssthresh else max (flight state / 2) (2 * state.smss) := by
  exact (congrArg State.ssthresh (timeout_facts state count after accepted).changed).trans rfl

theorem sample_retried (state : State) (count : Nat) (entry : Outstanding)
    (member : entry ∈ retired count state.outstanding) (retried : entry.retried = true) :
    sample state count = none := by
  have ambiguous : (retired count state.outstanding).any (·.retried) = true :=
    List.any_eq_true.mpr ⟨entry, member, retried⟩
  simp [sample, ambiguous]

theorem sample_origin (state : State) (count : Nat) (value : Sample)
    (selected : sample state count = some value) :
    ∃ entry ∈ retired count state.outstanding,
      entry.retried = false ∧ value = ⟨entry.id, entry.sentAt, state.now⟩ := by
  unfold sample at selected
  dsimp only at selected
  split at selected
  · cases selected
  · rename_i unambiguous
    cases entries : retired count state.outstanding with
    | nil => simp [entries] at selected
    | cons entry rest =>
      simp only [entries, List.head?_cons, Option.map_some, Option.some.injEq] at selected
      refine ⟨entry, by simp, ?_, selected.symm⟩
      have clear : entry.retried ≠ true := by
        intro retried
        exact unambiguous (List.any_eq_true.mpr ⟨entry, by simp [entries], retried⟩)
      cases value : entry.retried <;> simp_all

theorem acknowledge_smss (state : State) (count : Nat) (after : State)
    (accepted : acknowledge state count = .ok after) : after.smss = state.smss := by
  rw [(acknowledge_fields state count after accepted).2]
  exact acknowledgeState_smss state count

theorem timeout_clock (state : State) (count : Nat) (after : State)
    (accepted : timeout state = .ok (count, after)) : after.now = state.now := by
  exact (congrArg State.now (timeout_facts state count after accepted).changed).trans rfl

theorem timeout_estimator (state : State) (count : Nat) (after : State)
    (accepted : timeout state = .ok (count, after)) :
    after.estimator = state.estimator ∧ after.lastSample = state.lastSample := by
  have changed := (timeout_facts state count after accepted).changed
  exact ⟨(congrArg State.estimator changed).trans rfl, (congrArg State.lastSample changed).trans rfl⟩

theorem timeout_unique (state : State) (count : Nat) (after : State)
    (accepted : timeout state = .ok (count, after)) :
    after.frontier = state.frontier ∧ after.nextId = state.nextId := by
  have changed := (timeout_facts state count after accepted).changed
  exact ⟨(congrArg State.frontier changed).trans rfl, (congrArg State.nextId changed).trans rfl⟩

end Netlib.Protocol.TCP.Recovery
