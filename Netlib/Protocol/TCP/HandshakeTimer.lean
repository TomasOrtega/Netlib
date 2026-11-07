import Netlib.Protocol.TCP.RTO

/-!
# Timers for one outstanding SYN position

SYN and SYN,ACK have timers; a bare ACK has none.
The packet history supplies the selected control and acknowledgment evidence.
Clock values and intervals use milliseconds.
-/

namespace Netlib.Protocol.TCP.HandshakeTimer

inductive Kind where
  | syn | synAck
  deriving Repr, BEq, DecidableEq

structure Flight where
  kind : Kind
  source : Nat
  firstAt : Nat
  lastAt : Nat
  initialRTO : Nat
  retries : Nat
  deadline : Nat
  deriving Repr, BEq, DecidableEq

inductive Status where
  | idle
  | pending (flight : Flight)
  | acknowledged (flight : Flight) (ackAt : Nat)
  deriving Repr, BEq, DecidableEq

structure State where
  now : Nat := 0
  rto : Nat := 1000
  estimator : Option RTO.Estimator := none
  status : Status := .idle
  shortSynTimeout : Bool := false
  deriving Repr, BEq, DecidableEq

def initial (rto : Nat := 1000) (now : Nat := 0) : State :=
  { now, rto }

def State.Valid (state : State) : Prop :=
  1000 ≤ state.rto ∧ match state.status with
  | .idle => True
  | .pending flight =>
    flight.firstAt ≤ flight.lastAt ∧ flight.lastAt ≤ state.now ∧
      flight.deadline = flight.lastAt + state.rto ∧
      state.rto = 2 ^ flight.retries * flight.initialRTO ∧ 1000 ≤ flight.initialRTO
  | .acknowledged flight ackAt =>
    flight.firstAt ≤ flight.lastAt ∧ flight.lastAt ≤ ackAt ∧ ackAt ≤ state.now

instance (state : State) : Decidable state.Valid := by
  unfold State.Valid
  cases state.status <;> infer_instance

inductive Stop where
  | backwardClock | alreadyStarted | idle | early | obsolete
  deriving Repr, BEq, DecidableEq

def advance (state : State) (now : Nat) : Except Stop State :=
  if now < state.now then .error .backwardClock
  else .ok { state with now }

def arm (state : State) (kind : Kind) (source : Nat) : Except Stop State :=
  match state.status with
  | .idle => .ok { state with
      status := .pending ⟨kind, source, state.now, state.now, state.rto, 0, state.now + state.rto⟩ }
  | _ => .error .alreadyStarted

def expire (state : State) (generation : Nat) : Except Stop State :=
  match state.status with
  | .pending flight =>
    if generation ≠ flight.retries then .error .obsolete
    else if state.now < flight.deadline then .error .early
    else .ok { state with
      rto := 2 * state.rto,
      status := .pending { flight with
        lastAt := state.now,
        retries := flight.retries + 1,
        deadline := state.now + 2 * state.rto },
      shortSynTimeout := state.shortSynTimeout || decide (state.rto < 3000) }
  | _ => .error .idle

def sampled (state : State) (flight : Flight) : Option RTO.Estimator :=
  if flight.retries = 0 then some (RTO.observe state.estimator (state.now - flight.firstAt))
  else none

def acknowledge (state : State) : Except Stop State :=
  match state.status with
  | .pending flight =>
    let measured := sampled state flight
    .ok { state with
      status := .acknowledged flight state.now,
      estimator := measured.or state.estimator,
      rto := (match measured with | none => state.rto | some value => RTO.interval value) }
  | _ => .error .idle

def dataRTO (state : State) : Nat :=
  if state.shortSynTimeout then max 3000 state.rto else state.rto

structure Data where
  now : Nat
  rto : Nat
  estimator : Option RTO.Estimator
  synRetransmitted : Bool
  deriving Repr, BEq, DecidableEq

def handoff (state : State) : Option Data :=
  match state.status with
  | .acknowledged flight _ =>
    some ⟨state.now, dataRTO state, state.estimator, decide (flight.retries ≠ 0)⟩
  | _ => none

variable {before after state : State} {flight : Flight} {kind : Kind} {source now rto generation : Nat} {data : Data}

theorem initial_valid (minimum : 1000 ≤ rto) : (initial rto now).Valid := ⟨minimum, trivial⟩

theorem advance_eq (computed : advance before now = .ok after) :
    before.now ≤ now ∧ after = { before with now } := by
  unfold advance at computed
  split at computed
  · cases computed
  · simp only [Except.ok.injEq] at computed
    exact ⟨by omega, computed.symm⟩

theorem advance_valid (valid : before.Valid) (computed : advance before now = .ok after) : after.Valid := by
  obtain ⟨monotone, rfl⟩ := advance_eq computed
  refine ⟨valid.1, ?_⟩
  have fields := valid.2
  cases status : before.status with
  | idle => trivial
  | pending flight =>
    simp only [status] at fields ⊢
    exact ⟨fields.1, Nat.le_trans fields.2.1 monotone, fields.2.2⟩
  | acknowledged flight ackAt =>
    simp only [status] at fields ⊢
    exact ⟨fields.1, fields.2.1, Nat.le_trans fields.2.2 monotone⟩

theorem arm_eq (computed : arm before kind source = .ok after) :
    before.status = .idle ∧ after = { before with
      status := .pending ⟨kind, source, before.now, before.now, before.rto, 0, before.now + before.rto⟩ } := by
  unfold arm at computed
  split at computed
  · exact ⟨by assumption, Except.ok.inj computed.symm⟩
  · cases computed

theorem arm_valid (valid : before.Valid) (computed : arm before kind source = .ok after) : after.Valid := by
  obtain ⟨_, rfl⟩ := arm_eq computed
  exact ⟨valid.1, Nat.le_refl _, Nat.le_refl _, rfl, by simp, valid.1⟩

theorem expire_eq (computed : expire before generation = .ok after) :
    ∃ flight, before.status = .pending flight ∧ generation = flight.retries ∧ flight.deadline ≤ before.now ∧
      after = { before with
        rto := 2 * before.rto,
        status := .pending { flight with
          lastAt := before.now,
          retries := flight.retries + 1,
          deadline := before.now + 2 * before.rto },
        shortSynTimeout := before.shortSynTimeout || decide (before.rto < 3000) } := by
  unfold expire at computed
  split at computed
  · rename_i flight status
    split at computed
    · cases computed
    · rename_i current
      split at computed
      · cases computed
      · exact ⟨flight, status, by omega, by omega, Except.ok.inj computed.symm⟩
  · cases computed

theorem expire_valid (valid : before.Valid) (computed : expire before generation = .ok after) : after.Valid := by
  obtain ⟨flight, status, _, _, rfl⟩ := expire_eq computed
  have fields := valid.2
  simp only [status] at fields
  refine ⟨by change 1000 ≤ 2 * before.rto; have floor := valid.1; omega, Nat.le_trans fields.1 fields.2.1, Nat.le_refl _, rfl, ?_, fields.2.2.2.2⟩
  rw [fields.2.2.2.1, Nat.pow_succ, Nat.mul_comm (2 ^ flight.retries) 2, Nat.mul_assoc]

theorem expire_fields (computed : expire before generation = .ok after) :
    after.now = before.now ∧ after.rto = 2 * before.rto ∧ after.estimator = before.estimator ∧
      (before.rto < 3000 → after.shortSynTimeout = true) := by
  obtain ⟨flight, _, _, _, rfl⟩ := expire_eq computed
  exact ⟨rfl, rfl, rfl, by intro small; simp only [small, decide_true, Bool.or_true]⟩

theorem sampled_retried (retried : flight.retries ≠ 0) : sampled state flight = none := by
  simp only [sampled, retried, ite_false]

theorem acknowledge_eq (computed : acknowledge before = .ok after) :
    ∃ flight, before.status = .pending flight ∧
      after = { before with
        status := .acknowledged flight before.now,
        estimator := (sampled before flight).or before.estimator,
        rto := (match sampled before flight with | none => before.rto | some value => RTO.interval value) } := by
  unfold acknowledge at computed
  split at computed
  · exact ⟨_, by assumption, Except.ok.inj computed.symm⟩
  · cases computed

theorem acknowledge_valid (valid : before.Valid) (computed : acknowledge before = .ok after) : after.Valid := by
  obtain ⟨flight, status, rfl⟩ := acknowledge_eq computed
  have fields := valid.2
  simp only [status] at fields
  refine ⟨?_, fields.1, fields.2.1, Nat.le_refl _⟩
  split
  · exact valid.1
  · exact RTO.interval_floor _ _

theorem acknowledge_karn (status : before.status = .pending flight) (retried : flight.retries ≠ 0)
    (computed : acknowledge before = .ok after) :
    after.estimator = before.estimator ∧ after.rto = before.rto := by
  simp only [acknowledge, status, sampled_retried retried, Option.or, Except.ok.injEq] at computed
  subst after
  exact ⟨rfl, rfl⟩

theorem acknowledge_stops (computed : acknowledge before = .ok after) : expire after generation = .error .idle := by
  obtain ⟨flight, _, rfl⟩ := acknowledge_eq computed
  rfl

theorem dataRTO_floor (valid : state.Valid) : 1000 ≤ dataRTO state := by
  unfold dataRTO
  split
  · exact Nat.le_trans valid.1 (Nat.le_max_right _ _)
  · exact valid.1

theorem dataRTO_short (short : state.shortSynTimeout = true) : 3000 ≤ dataRTO state := by
  simp only [dataRTO, short, ↓reduceIte]
  exact Nat.le_max_left _ _

theorem dataRTO_preserves : state.rto ≤ dataRTO state := by
  unfold dataRTO
  split
  · exact Nat.le_max_right _ _
  · exact Nat.le_refl _

theorem handoff_closed (computed : handoff state = some data) :
    ∃ flight ackAt, state.status = .acknowledged flight ackAt ∧
      data.now = state.now ∧ data.rto = dataRTO state ∧ data.estimator = state.estimator ∧
      data.synRetransmitted = decide (flight.retries ≠ 0) := by
  unfold handoff at computed
  split at computed
  · simp only [Option.some.injEq] at computed
    subst data
    exact ⟨_, _, by assumption, rfl, rfl, rfl, rfl⟩
  · cases computed


theorem expire_due (valid : before.Valid) (computed : expire before generation = .ok after) :
    ∃ flight, before.status = .pending flight ∧ generation = flight.retries ∧
      flight.lastAt + before.rto ≤ before.now := by
  obtain ⟨flight, status, current, due, _⟩ := expire_eq computed
  have fields := valid.2
  simp only [status] at fields
  exact ⟨flight, status, current, fields.2.2.1 ▸ due⟩

theorem expire_obsolete (status : state.status = .pending flight) (stale : generation ≠ flight.retries) :
    expire state generation = .error .obsolete := by
  simp only [expire, status]
  split
  · rfl
  · contradiction

theorem expire_restart (computed : expire before generation = .ok after) :
    ∃ flight, after.status = .pending flight ∧
      flight.retries = generation + 1 ∧ flight.lastAt = before.now ∧
      flight.deadline = before.now + 2 * before.rto := by
  obtain ⟨flight, _, current, _, rfl⟩ := expire_eq computed
  exact ⟨_, rfl, by rw [current], rfl, rfl⟩

theorem handoff_floor (valid : state.Valid) (computed : handoff state = some data) :
    1000 ≤ data.rto ∧ (state.shortSynTimeout = true → 3000 ≤ data.rto) ∧ state.rto ≤ data.rto := by
  obtain ⟨_, _, _, _, interval, _, _⟩ := handoff_closed computed
  rw [interval]
  exact ⟨dataRTO_floor valid, dataRTO_short, dataRTO_preserves⟩

end Netlib.Protocol.TCP.HandshakeTimer
