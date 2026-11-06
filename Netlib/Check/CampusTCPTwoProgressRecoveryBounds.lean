import Netlib.Check.CampusTCPTwoProgressPhaseAckReceive
import Netlib.Check.CampusTCPTwoProgressPhaseClock
import Netlib.Protocol.TCP.RTOBound

namespace Netlib.Check.CampusTCPTwoProgressRecoveryBounds

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressSetup (config)

namespace S
export CampusTCPTwoProgressSender (Stage Part Original Flight Retires)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane timerTarget)
end M
namespace T
export CampusTCPTwoProgressTimer (remaining slots target_some)
end T

def DeadlineWithin (state : Recovery.State) : Prop :=
  ∀ deadline, state.deadline = some deadline → deadline ≤ state.now + state.rto

theorem deadline_none (state : Recovery.State) (none : state.deadline = none) : DeadlineWithin state := by
  intro deadline present
  rw [none] at present
  cases present

theorem deadline_sent (state : Recovery.State) (count : Nat) (prior : DeadlineWithin state) :
    DeadlineWithin (Recovery.sent state count) := by
  intro deadline present
  cases timer : state.deadline with
  | none =>
    have same : state.now + state.rto = deadline := by simpa only [Recovery.sent, timer, Option.some.injEq] using present
    exact same ▸ Nat.le_refl _
  | some stored =>
    have same : stored = deadline := by simpa only [Recovery.sent, timer, Option.some.injEq] using present
    exact same ▸ prior stored timer

theorem deadline_acknowledge (state : Recovery.State) (count : Nat) (prior : DeadlineWithin state) :
    DeadlineWithin (Recovery.acknowledgeState state count) := by
  by_cases zero : count = 0
  · simpa only [Recovery.acknowledgeState, zero, ite_true] using prior
  · intro deadline present
    simp only [Recovery.acknowledgeState, zero, ite_false] at present ⊢
    split at present
    · cases present
    · exact (Option.some.inj present) ▸ Nat.le_refl _

theorem deadline_positive_ack (state : Recovery.State) (count : Nat) (positive : 0 < count) :
    DeadlineWithin (Recovery.acknowledgeState state count) := by
  intro deadline present
  simp only [Recovery.acknowledgeState, Nat.ne_of_gt positive, ite_false] at present ⊢
  split at present
  · cases present
  · exact (Option.some.inj present) ▸ Nat.le_refl _

theorem deadline_timeout (state : Recovery.State) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding) :
    DeadlineWithin (Recovery.timeoutState state head rest) := by
  intro deadline present
  exact (Option.some.inj present) ▸ Nat.le_refl _

theorem deadline_advance (state : Recovery.State) (millis : Nat) (prior : DeadlineWithin state)
    (monotone : state.now ≤ millis) : DeadlineWithin { state with now := millis } := by
  intro deadline present
  exact Nat.le_trans (prior deadline present) (Nat.add_le_add_right monotone state.rto)

theorem target_le (state : Recovery.State) (clocked : state.Clocked) (deadline : DeadlineWithin state)
    (target : Nat) (selected : M.timerTarget state = some target) : target ≤ state.now + state.rto := by
  obtain ⟨head, rest, due, ledger, timer, bound⟩ := T.target_some selected
  have past := (clocked head (by rw [ledger]; exact List.mem_cons_self)).2
  rw [bound]
  exact Nat.max_le.mpr ⟨deadline due timer, Nat.add_le_add_right past state.rto⟩

theorem remaining_le (state : Recovery.State) (clocked : state.Clocked) (deadline : DeadlineWithin state) :
    T.remaining state ≤ state.rto := by
  cases target : M.timerTarget state with
  | none => rw [CampusTCPTwoProgressTimer.remaining_none target]; exact Nat.zero_le _
  | some time =>
    have bound := target_le state clocked deadline time target
    rw [CampusTCPTwoProgressTimer.remaining_of_target target]
    omega

theorem slots_le (state : Recovery.State) (quantum : Nat) (clocked : state.Clocked) (deadline : DeadlineWithin state) :
    T.slots quantum state ≤ CampusTCPTwoProgressTimer.waitSlots quantum state.rto :=
  CampusTCPRecoveryRoundMonitor.waitSlots_mono (remaining_le state clocked deadline)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent next : S.Stage initial} {received : R.Stage} {lane : M.Lane} {actual : Step input}
variable {first : S.Original initial .lower} {second : S.Original initial .upper} {head : Recovery.Outstanding}

theorem initial_deadline (initial : TwoWriteInitial cut sender gateway lower upper) :
    DeadlineWithin initial.senderState.idle.recovery := deadline_none _ initial.senderState.idle.deadline

theorem send_recovery {count timeouts afterTimeouts : Nat}
    (before : S.Flight initial (endpoint current.endpoints sender) sent timeouts)
    (facts : CampusTCPTwoProgressSend.SendFacts current sender count actual)
    (after : S.Flight initial (endpoint facts.move.after.endpoints sender) next afterTimeouts) :
    after.recovery = Recovery.sent before.recovery count := by
  have runtime := after.runtime.symm.trans (congrArg (fun state : Endpoint.State => state.recovery) facts.sendState)
  change some after.recovery = (endpoint current.endpoints sender).recovery.map (fun recovery => Recovery.sent recovery count) at runtime
  rw [before.runtime, Option.map_some] at runtime
  exact Option.some.inj runtime

theorem first_deadline {core : Core initial native quantum allowance current monitor .written .empty}
    (value : CampusTCPTwoProgressPhaseSend.First core actual) (prior : DeadlineWithin core.live.senderFlight.recovery) :
    DeadlineWithin value.next.live.senderFlight.recovery := by
  rw [send_recovery core.live.senderFlight value.value.facts value.next.live.senderFlight]
  exact deadline_sent _ _ prior

theorem second_deadline {core : Core initial native quantum allowance current monitor (.lower first) .empty}
    (value : CampusTCPTwoProgressPhaseSend.Second core actual) (prior : DeadlineWithin core.live.senderFlight.recovery) :
    DeadlineWithin value.next.live.senderFlight.recovery := by
  rw [send_recovery core.live.senderFlight value.value.facts value.next.live.senderFlight]
  exact deadline_sent _ _ prior

variable {core : Core initial native quantum allowance current monitor sent received}

theorem advanced_recovery {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path) :
    value.nextCore.live.senderFlight.recovery = Endpoint.advancingAckRecovery (endpoint current.endpoints sender)
      path.emission.asInput core.live.senderFlight.recovery := by
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  have selected : endpoint value.value.delivery.move.after.endpoints sender = value.value.delivery.after := by
    change endpoint value.value.delivery.updated sender = value.value.delivery.after
    simpa only [other] using value.value.delivery.selected
  apply Option.some.inj
  exact value.nextCore.live.senderFlight.runtime.symm.trans (by rw [selected]; exact value.value.protocol.runtime)

theorem advanced_deadline {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path) : DeadlineWithin value.nextCore.live.senderFlight.recovery := by
  rw [advanced_recovery value]
  exact deadline_positive_ack _ _ value.value.protocol.count_positive

theorem zero_recovery {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Zero core path) :
    value.nextCore.live.senderFlight.recovery = Endpoint.zeroAckRecovery (endpoint current.endpoints sender)
      path.emission.asInput core.live.senderFlight.recovery := by
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  have selected : endpoint value.value.delivery.move.after.endpoints sender = value.value.delivery.after := by
    change endpoint value.value.delivery.updated sender = value.value.delivery.after
    simpa only [other] using value.value.delivery.selected
  apply Option.some.inj
  exact value.nextCore.live.senderFlight.runtime.symm.trans (by rw [selected]; exact value.value.protocol.runtime)

theorem zero_fields {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Zero core path) :
    value.nextCore.live.senderFlight.recovery.estimator = core.live.senderFlight.recovery.estimator ∧
      value.nextCore.live.senderFlight.recovery.rto = core.live.senderFlight.recovery.rto ∧
      value.nextCore.live.senderFlight.recovery.deadline = core.live.senderFlight.recovery.deadline := by
  rw [zero_recovery value]
  unfold Endpoint.zeroAckRecovery
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem zero_deadline {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Zero core path) (prior : DeadlineWithin core.live.senderFlight.recovery) :
    DeadlineWithin value.nextCore.live.senderFlight.recovery := by
  rw [zero_recovery value]
  unfold Endpoint.zeroAckRecovery
  split <;> exact prior

private theorem lower_shape {amount : Nat} {next : S.Stage initial}
    (retiring : S.Retires (.both first second head) amount next)
    (coordinate : next.retiredBytes = lower.length) : next = .tail first second second.entry ∧ amount = lower.length := by
  cases retiring with
  | lower => exact ⟨rfl, rfl⟩
  | both =>
    have positive := List.length_pos_iff.mpr initial.upperNonempty
    change lower.length + upper.length = lower.length at coordinate
    omega

theorem partial_shape {core : Core initial native quantum allowance current monitor (.both first second head) .lowerReleased}
    {path : CampusTCPTwoProgressPaths.AckLink initial current lower.length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path) :
    value.nextStage = .tail first second second.entry ∧ value.amount = lower.length :=
  lower_shape value.value.retiring value.coordinate

theorem partial_counted {core : Core initial native quantum allowance current monitor (.both first second head) .lowerReleased}
    {path : CampusTCPTwoProgressPaths.AckLink initial current lower.length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path) :
    Endpoint.inOrderCount (endpoint current.endpoints sender) path.emission.asInput = head.count := by
  have count := congrArg Recovery.Outstanding.count core.live.senderFlight.headFixed
  exact value.value.counted.trans ((partial_shape value).2.trans count.symm)

theorem partial_retried {core : Core initial native quantum allowance current monitor (.both first second head) .lowerReleased}
    {path : CampusTCPTwoProgressPaths.AckLink initial current lower.length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path) (retried : head.retried = true) :
    value.nextCore.live.senderFlight.recovery.estimator = core.live.senderFlight.recovery.estimator ∧
      value.nextCore.live.senderFlight.recovery.lastSample = core.live.senderFlight.recovery.lastSample ∧
      value.nextCore.live.senderFlight.recovery.rto = core.live.senderFlight.recovery.rto := by
  rw [advanced_recovery value]
  exact value.value.protocol.head_retried head [second.entry] core.live.senderFlight.ledger (partial_counted value) retried

theorem partial_fresh_cap {core : Core initial native quantum allowance current monitor (.both first second head) .lowerReleased}
    {path : CampusTCPTwoProgressPaths.AckLink initial current lower.length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path) (fresh : head.retried = false)
    (age : Nat) (elapsed : core.live.senderFlight.recovery.now - head.sentAt ≤ age) :
    value.nextCore.live.senderFlight.recovery.rto ≤ RTO.sampleCap core.live.senderFlight.recovery.estimator age := by
  rw [advanced_recovery value]
  have fields := value.value.protocol.head_fresh head [second.entry] core.live.senderFlight.ledger (partial_counted value) fresh
  rw [fields.2.2]
  exact RTO.interval_observe_le_sampleCap _ _ _ elapsed

theorem partial_deadline {core : Core initial native quantum allowance current monitor (.both first second head) .lowerReleased}
    {path : CampusTCPTwoProgressPaths.AckLink initial current lower.length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path) :
    value.nextCore.live.senderFlight.recovery.deadline = some
      (value.nextCore.live.senderFlight.recovery.now + value.nextCore.live.senderFlight.recovery.rto) := by
  rw [advanced_recovery value]
  have fields := value.value.protocol.tail_fields head second.entry [] core.live.senderFlight.ledger (partial_counted value)
  simpa only [Endpoint.advancingAckRecovery, Recovery.acknowledgeState_now] using fields.2.1

theorem retry_recovery {part : S.Part} {rest : List Recovery.Outstanding} {position : Nat}
    (value : CampusTCPTwoProgressPhaseRetry.Retried core part head rest position actual) :
    value.next.live.senderFlight.recovery = Recovery.timeoutState core.live.senderFlight.recovery head rest := by
  apply Option.some.inj
  exact value.next.live.senderFlight.runtime.symm.trans (by rw [value.value.endpointsEq]; exact value.value.facts.runtime)

theorem retry_fields {part : S.Part} {rest : List Recovery.Outstanding} {position : Nat}
    (value : CampusTCPTwoProgressPhaseRetry.Retried core part head rest position actual) :
    value.next.live.senderFlight.recovery.estimator = core.live.senderFlight.recovery.estimator ∧
      value.next.live.senderFlight.recovery.rto = 2 * core.live.senderFlight.recovery.rto ∧
      value.next.live.senderFlight.recovery.deadline = some
        (value.next.live.senderFlight.recovery.now + value.next.live.senderFlight.recovery.rto) := by
  rw [retry_recovery value]
  exact ⟨rfl, rfl, rfl⟩

theorem retry_deadline {part : S.Part} {rest : List Recovery.Outstanding} {position : Nat}
    (value : CampusTCPTwoProgressPhaseRetry.Retried core part head rest position actual) :
    DeadlineWithin value.next.live.senderFlight.recovery := by
  rw [retry_recovery value]
  exact deadline_timeout _ _ _

theorem clock_deadline {actor : Actor} {millis : Nat}
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor (.advanceClock actor millis))
    (prior : DeadlineWithin core.live.senderFlight.recovery) :
    DeadlineWithin (core.clock clocked allowed).live.senderFlight.recovery := by
  rw [CampusTCPTwoProgressPhaseState.clock_sender_recovery core clocked allowed]
  apply deadline_advance _ _ prior
  have monotone := (clocked.placement.frame.endpointFrame sender).monotone
  simpa only [Endpoint.State.now, core.live.senderFlight.runtime, Option.map_some, Option.getD_some] using monotone

theorem clock_fields {actor : Actor} {millis : Nat}
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor (.advanceClock actor millis)) :
    (core.clock clocked allowed).live.senderFlight.recovery.estimator = core.live.senderFlight.recovery.estimator ∧
      (core.clock clocked allowed).live.senderFlight.recovery.rto = core.live.senderFlight.recovery.rto ∧
      (core.clock clocked allowed).live.senderFlight.recovery.deadline = core.live.senderFlight.recovery.deadline := by
  rw [CampusTCPTwoProgressPhaseState.clock_sender_recovery core clocked allowed]
  exact ⟨rfl, rfl, rfl⟩

theorem same_endpoint_recovery {after : Cut input complete} {state : Endpoint.State} {timeouts afterTimeouts : Nat}
    (before : S.Flight initial state sent timeouts)
    (next : S.Flight initial (endpoint after.endpoints sender) next afterTimeouts)
    (same : endpoint after.endpoints sender = state) : next.recovery = before.recovery := by
  exact Option.some.inj (next.runtime.symm.trans (by rw [same]; exact before.runtime))

end Netlib.Check.CampusTCPTwoProgressRecoveryBounds
