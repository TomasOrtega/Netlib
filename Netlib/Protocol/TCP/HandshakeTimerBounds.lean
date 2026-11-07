import Netlib.Protocol.TCP.HandshakeTimer
import Netlib.Protocol.TCP.RTOBound

/-!
# Startup timer intervals from actual elapsed time

Each due expiry accounts for its doubled interval in elapsed time.
The bound does not charge timer expirations to packet losses.
-/

namespace Netlib.Protocol.TCP.HandshakeTimer

def Flight.Elapsed (flight : Flight) : Prop :=
  2 ^ flight.retries * flight.initialRTO + flight.firstAt ≤ flight.initialRTO + flight.lastAt

def State.Elapsed (state : State) : Prop :=
  match state.status with
  | .idle => True
  | .pending flight | .acknowledged flight _ => flight.Elapsed

variable {before after state : State} {flight : Flight}

theorem initial_elapsed (rto now : Nat) : (initial rto now).Elapsed := trivial

theorem advance_elapsed (prior : before.Elapsed) (computed : advance before now = .ok after) : after.Elapsed := by
  obtain ⟨_, rfl⟩ := advance_eq computed
  exact prior

theorem arm_elapsed (computed : arm before kind source = .ok after) : after.Elapsed := by
  obtain ⟨_, rfl⟩ := arm_eq computed
  simp only [State.Elapsed, Flight.Elapsed, Nat.pow_zero, Nat.one_mul, Nat.le_refl]

theorem expire_elapsed (valid : before.Valid) (prior : before.Elapsed)
    (computed : expire before generation = .ok after) : after.Elapsed := by
  obtain ⟨flight, status, _, due, rfl⟩ := expire_eq computed
  have fields := valid.2
  simp only [status] at fields
  have elapsed : flight.Elapsed := by simpa only [State.Elapsed, status] using prior
  have interval := fields.2.2.2.1
  have deadline := fields.2.2.1
  unfold Flight.Elapsed at elapsed
  rw [← interval] at elapsed
  rw [deadline] at due
  change 2 ^ (flight.retries + 1) * flight.initialRTO + flight.firstAt ≤ flight.initialRTO + before.now
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ flight.retries) 2, Nat.mul_assoc, ← interval]
  omega

theorem acknowledge_elapsed (prior : before.Elapsed) (computed : acknowledge before = .ok after) : after.Elapsed := by
  obtain ⟨flight, status, rfl⟩ := acknowledge_eq computed
  simpa only [State.Elapsed, status] using prior

theorem pending_interval_elapsed (valid : state.Valid) (elapsed : state.Elapsed)
    (status : state.status = .pending flight) : state.rto ≤ flight.initialRTO + (state.now - flight.firstAt) := by
  have fields := valid.2
  simp only [status] at fields
  have bounded : flight.Elapsed := by simpa only [State.Elapsed, status] using elapsed
  unfold Flight.Elapsed at bounded
  rw [← fields.2.2.2.1] at bounded
  have first := fields.1
  have last := fields.2.1
  omega

theorem pending_interval_clock (valid : state.Valid) (elapsed : state.Elapsed)
    (status : state.status = .pending flight) : state.rto ≤ flight.initialRTO + state.now :=
  Nat.le_trans (pending_interval_elapsed valid elapsed status)
    (Nat.add_le_add_left (Nat.sub_le _ _) _)

theorem pending_deadline_remaining (valid : state.Valid) (status : state.status = .pending flight) :
    flight.deadline - state.now ≤ state.rto := by
  have fields := valid.2
  simp only [status] at fields
  rw [fields.2.2.1]
  have last := fields.2.1
  omega

theorem acknowledge_interval_clock (valid : before.Valid) (elapsed : before.Elapsed)
    (status : before.status = .pending flight) (computed : acknowledge before = .ok after) :
    after.rto ≤ max (flight.initialRTO + before.now) (RTO.sampleCap before.estimator before.now) := by
  have interval := pending_interval_clock valid elapsed status
  obtain ⟨selected, selectedStatus, rfl⟩ := acknowledge_eq computed
  rw [status] at selectedStatus
  cases selectedStatus
  change (match sampled before flight with | none => before.rto | some value => RTO.interval value) ≤ _
  by_cases fresh : flight.retries = 0
  · simp only [sampled, fresh, ite_true]
    exact Nat.le_trans (RTO.interval_observe_le_sampleCap _ _ _ (Nat.sub_le _ _)) (Nat.le_max_right _ _)
  · simp only [sampled, fresh, ite_false]
    exact Nat.le_trans interval (Nat.le_max_left _ _)

theorem dataRTO_bound (bounded : state.rto ≤ cap) : dataRTO state ≤ max 3000 cap := by
  unfold dataRTO
  split
  · exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans bounded (Nat.le_max_right _ _)⟩
  · exact Nat.le_trans bounded (Nat.le_max_right _ _)

def clockEnvelope (now : Nat) : Nat := max (1000 + now) (RTO.sampleCap none now)

def State.BoundedStartup (state : State) : Prop :=
  state.Elapsed ∧ match state.status with
  | .idle => state.rto = 1000 ∧ state.estimator = none
  | .pending flight => flight.initialRTO = 1000 ∧ state.estimator = none
  | .acknowledged flight ackAt =>
    flight.initialRTO = 1000 ∧ state.rto ≤ clockEnvelope ackAt ∧
      (state.estimator = none ∨ ∃ sample, sample ≤ ackAt ∧ state.estimator = some (RTO.observe none sample))

theorem initial_bounded_startup (now : Nat) : (initial 1000 now).BoundedStartup :=
  ⟨trivial, rfl, rfl⟩

theorem advance_bounded_startup (prior : before.BoundedStartup)
    (computed : advance before now = .ok after) : after.BoundedStartup := by
  obtain ⟨_, rfl⟩ := advance_eq computed
  exact prior

theorem arm_bounded_startup (prior : before.BoundedStartup)
    (computed : arm before kind source = .ok after) : after.BoundedStartup := by
  have elapsed := arm_elapsed computed
  obtain ⟨status, rfl⟩ := arm_eq computed
  refine ⟨elapsed, ?_⟩
  simpa only [status] using prior.2

theorem expire_bounded_startup (valid : before.Valid) (prior : before.BoundedStartup)
    (computed : expire before generation = .ok after) : after.BoundedStartup := by
  have elapsed := expire_elapsed valid prior.1 computed
  obtain ⟨flight, status, _, _, rfl⟩ := expire_eq computed
  refine ⟨elapsed, ?_⟩
  simpa only [status] using prior.2

theorem acknowledge_bounded_startup (valid : before.Valid) (prior : before.BoundedStartup)
    (computed : acknowledge before = .ok after) : after.BoundedStartup := by
  have elapsed := acknowledge_elapsed prior.1 computed
  obtain ⟨flight, status, afterEq⟩ := acknowledge_eq computed
  have fields : flight.initialRTO = 1000 ∧ before.estimator = none := by
    simpa only [status] using prior.2
  have interval := acknowledge_interval_clock valid prior.1 status computed
  rw [fields.1, fields.2] at interval
  rw [afterEq]
  refine ⟨by rw [← afterEq]; exact elapsed, fields.1, ?_, ?_⟩
  · simpa only [afterEq, clockEnvelope] using interval
  · by_cases fresh : flight.retries = 0
    · exact Or.inr ⟨before.now - flight.firstAt, Nat.sub_le _ _, by
        simp only [sampled, fresh, ite_true, fields.2, Option.or_none]⟩
    · exact Or.inl (by simp only [sampled, fresh, ite_false, fields.2, Option.or_none])

theorem clockEnvelope_mono (earlier : first ≤ last) : clockEnvelope first ≤ clockEnvelope last :=
  Nat.max_le.mpr ⟨Nat.le_trans (Nat.add_le_add_left earlier _) (Nat.le_max_left _ _),
    Nat.le_trans (RTO.sampleCap_mono none first last earlier) (Nat.le_max_right _ _)⟩

theorem State.BoundedStartup.interval (valid : state.Valid) (bounded : state.BoundedStartup) :
    state.rto ≤ clockEnvelope state.now := by
  cases status : state.status with
  | idle =>
    have fields := bounded.2
    simp only [status] at fields
    rw [fields.1]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_left _ _)
  | pending flight =>
    have fields := bounded.2
    simp only [status] at fields
    have interval := pending_interval_clock valid bounded.1 status
    rw [fields.1] at interval
    exact Nat.le_trans interval (Nat.le_max_left _ _)
  | acknowledged flight ackAt =>
    have fields := bounded.2
    have time := valid.2
    simp only [status] at fields time
    exact Nat.le_trans fields.2.1 (clockEnvelope_mono time.2.2)

theorem State.BoundedStartup.data_interval (valid : state.Valid) (bounded : state.BoundedStartup) :
    dataRTO state ≤ max 3000 (clockEnvelope state.now) :=
  dataRTO_bound (State.BoundedStartup.interval valid bounded)

theorem State.BoundedStartup.estimator (valid : state.Valid) (bounded : state.BoundedStartup) :
    state.estimator = none ∨ ∃ sample, sample ≤ state.now ∧ state.estimator = some (RTO.observe none sample) := by
  cases status : state.status with
  | idle | pending flight =>
    have fields := bounded.2
    simp only [status] at fields
    exact Or.inl fields.2
  | acknowledged flight ackAt =>
    have fields := bounded.2
    have time := valid.2
    simp only [status] at fields time
    rcases fields.2.2 with empty | ⟨sample, earlier, stored⟩
    · exact Or.inl empty
    · exact Or.inr ⟨sample, Nat.le_trans earlier time.2.2, stored⟩

end Netlib.Protocol.TCP.HandshakeTimer
