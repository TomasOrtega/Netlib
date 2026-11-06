import Netlib.Check.CampusTCPTwoProgressSourceHistory
import Netlib.Check.CampusTCPTwoProgressLossHistory
import Netlib.Check.CampusTCPTwoProgressNetworkState
import Netlib.Check.CampusTCPTwoProgressPathsReady
import Netlib.Check.CampusTCPTwoProgressOriginalRank
import Netlib.Protocol.TCP.RecoveryDeadline
import Netlib.Protocol.TCP.RTOEnvelope

/-!
# Joint phase facts on one actual suffix

The phase retains writer sources and actual loss causes.
Receiver progress stays within the gateway's current admitted coverage.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseBase

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPathsReady (rangeAt)
open CampusTCPTwoProgressSetup (config)

namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace M
export CampusTCPTwoProgressMonitor (Monitor)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor}

def emitted (initial : TwoWriteInitial cut sender gateway lower upper) : S.Stage initial → List UInt8
  | .written => []
  | .lower _ => lower
  | _ => lower ++ upper

def Arrived : R.Stage → S.Part → Prop
  | .lowerReleased, .lower | .upperHeld, .upper | .allReleased, _ => True
  | _, _ => False

def OriginalTimes (initial : TwoWriteInitial cut sender gateway lower upper) : S.Stage initial → Prop
  | .written => True
  | .lower first => (endpoint cut.endpoints sender).now ≤ first.operation.before.now
  | .both first second _ | .tail first second _ | .retired first second =>
    (endpoint cut.endpoints sender).now ≤ first.operation.before.now ∧
      (endpoint cut.endpoints sender).now ≤ second.operation.before.now

theorem stage_prefix (stage : R.Stage) : stage.bytes lower upper <+: lower ++ upper := by
  cases stage
  · exact List.nil_prefix
  · exact List.nil_prefix
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

structure Core (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (current : Cut input complete) (monitor : M.Monitor) (sent : S.Stage initial) (received : R.Stage) where
  live : CampusTCPTwoProgressState.Live initial current sent monitor.retries received
  senderWindow : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent
  originals : CampusTCPTwoProgressSourceHistory.Originals initial current sent
  originalTimes : OriginalTimes initial sent
  writer : CampusTCPTwoProgressWriteHistory.History initial current (emitted initial sent)
  losses : CampusTCPTwoProgressLossHistory.History initial (config initial native quantum allowance) current monitor
  lossBound : monitor.drops.length ≤ allowance
  retired : sent.retiredBytes ≤ (received.bytes lower upper).length
  gatewayAck : (live.gatewayState.gateway.session.lane sender.direction).acknowledged ≤
    initial.geometry.«prefix» + (received.bytes lower upper).length
  covered : ∀ part, Arrived received part → (rangeAt live.gatewayState part).isSome = true
  duplicates : live.senderFlight.recovery.duplicateAcks ≤ 1
  emptyDuplicate : received = .empty → live.senderFlight.recovery.duplicateAcks = 0
  deadline : RecoveryDeadline.Bound live.senderFlight.recovery
  estimatorBeforeRetire : sent.retiredBytes = 0 → live.senderFlight.recovery.estimator = initial.senderState.idle.recovery.estimator
  rtoBeforeRetire : sent.retiredBytes = 0 → live.senderFlight.recovery.rto = 2 ^ monitor.retries * initial.senderState.idle.recovery.rto
  rtoPending : sent.ledger ≠ [] → RTOEnvelope.Bound initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator
    (endpoint cut.endpoints sender).now monitor.retries live.senderFlight.recovery

def Core.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat) :
    Core initial native quantum allowance cut .initial .written .empty where
  live := CampusTCPTwoProgressState.Live.ofInitial initial
  senderWindow := CampusTCPTwoProgressSenderWindow.initial_reserved initial
  originals := CampusTCPTwoProgressSourceHistory.Originals.ofInitial initial
  originalTimes := trivial
  writer := CampusTCPTwoProgressWriteHistory.History.ofInitial initial
  losses := CampusTCPTwoProgressLossHistory.History.empty initial (config initial native quantum allowance)
  lossBound := Nat.zero_le _
  retired := Nat.le_refl _
  gatewayAck := by
    change (initial.gatewayState.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + 0
    rw [initial.geometry.acknowledged]
    exact Nat.le_refl _
  covered := by intro part impossible; cases part <;> cases impossible
  duplicates := by
    change initial.senderState.idle.recovery.duplicateAcks ≤ 1
    rw [initial.senderState.idle.duplicate]
    decide
  emptyDuplicate := fun _ => initial.senderState.idle.duplicate
  deadline := RecoveryDeadline.of_none _ initial.senderState.idle.deadline
  estimatorBeforeRetire := fun _ => rfl
  rtoBeforeRetire := by
    intro _
    change initial.senderState.idle.recovery.rto = 2 ^ 0 * initial.senderState.idle.recovery.rto
    rw [Nat.pow_zero, Nat.one_mul]
  rtoPending := by intro impossible; exact False.elim (impossible rfl)

theorem covered_observed (stage : R.Stage) (view : CampusTCPTwoProgressGatewayState.View initial current)
    (covered : ∀ part, Arrived stage part → (rangeAt view part).isSome = true) :
    initial.geometry.«prefix» + (stage.bytes lower upper).length ≤
      (view.gateway.session.lane sender.direction).observed := by
  have observed := view.observed
  cases stage with
  | empty | upperHeld =>
    simp only [CampusTCPTwoProgressReceiver.Stage.bytes, List.length_nil, Nat.add_zero]
    rw [observed]
    split <;> omega
  | lowerReleased =>
    have first := covered .lower trivial
    change view.ranges.lowerRun.isSome = true at first
    rw [observed, first]
    simp only [CampusTCPTwoProgressReceiver.Stage.bytes, ite_true]
    omega
  | allReleased =>
    have first := covered .lower trivial
    have second := covered .upper trivial
    change view.ranges.lowerRun.isSome = true at first
    change view.ranges.upperRun.isSome = true at second
    rw [observed, first, second]
    simp only [CampusTCPTwoProgressReceiver.Stage.bytes, List.length_append, ite_true]
    omega

variable {sent : S.Stage initial} {received : R.Stage}

theorem Core.gateway_observed (core : Core initial native quantum allowance current monitor sent received) :
    initial.geometry.«prefix» + (received.bytes lower upper).length ≤
      (core.live.gatewayState.gateway.session.lane sender.direction).observed :=
  covered_observed received core.live.gatewayState core.covered

theorem Core.retry_count (core : Core initial native quantum allowance current monitor sent received) : monitor.retries ≤ monitor.drops.length :=
  core.losses.count

theorem Core.retry_bound (core : Core initial native quantum allowance current monitor sent received) : monitor.retries ≤ allowance :=
  Nat.le_trans core.retry_count core.lossBound

theorem Core.timeout_credit (core : Core initial native quantum allowance current monitor sent received)
    (role : S.Part) (position : Nat) (cause : core.losses.book.cause role = some position) : monitor.retries < allowance :=
  Nat.lt_of_lt_of_le (core.losses.credit cause) core.lossBound

variable {actor : Actor} {millis : Nat} {actual : Step input}

theorem Core.clock_now_monotone (core : Core initial native quantum allowance current monitor sent received)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.advanceClock actor millis)) :
    core.live.senderFlight.recovery.now ≤ (endpoint clocked.move.after.endpoints sender).now := by
  by_cases selected : sender = actor
  · subst actor
    obtain ⟨recovery, runtime, monotone, _, _⟩ := CampusTCPGapProgressClock.clock_allowed_fields
      (config initial native quantum allowance).toConfig current sender millis
      (CampusTCPTwoProgressClock.allowed_guard _ _ _ _ _ allowed)
    have same := Option.some.inj (core.live.senderFlight.runtime.symm.trans runtime)
    subst recovery
    rw [clocked.selected]
    simpa only [Endpoint.clockState, Endpoint.State.now, core.live.senderFlight.runtime,
      Option.map_some, Option.getD_some] using monotone
  · have peer : sender = actor.other := by cases sender <;> cases actor <;> simp_all [Actor.other]
    have unchanged : endpoint clocked.move.after.endpoints sender = endpoint current.endpoints sender :=
      (congrArg (endpoint clocked.move.after.endpoints) peer).trans
        (clocked.peer.trans (congrArg (endpoint current.endpoints) peer.symm))
    rw [unchanged]
    simp only [Endpoint.State.now, core.live.senderFlight.runtime, Option.map_some, Option.getD_some]
    exact Nat.le_refl _

def Core.clock (core : Core initial native quantum allowance current monitor sent received)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.advanceClock actor millis)) :
    Core initial native quantum allowance clocked.move.after monitor sent received := by
  let joint := CampusTCPTwoProgressNetworkState.clock_live core.live clocked allowed
  have folded : (clocked.move.after.report.steps.drop current.report.steps.length).foldl
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance)) monitor = monitor := by
    rw [clocked.move.history, List.drop_append_length]
    simpa only [List.foldl_cons, List.foldl_nil] using clocked.observed
  exact {
    live := joint
    senderWindow := CampusTCPTwoProgressSenderWindow.clock core.senderWindow (clocked.placement.frame.endpointFrame sender)
    originals := core.originals.clock clocked.placement
    originalTimes := core.originalTimes
    writer := core.writer.clock clocked.placement
    losses := core.losses.clock clocked.placement folded
    lossBound := core.lossBound, retired := core.retired, gatewayAck := core.gatewayAck
    covered := core.covered, duplicates := core.duplicates, emptyDuplicate := core.emptyDuplicate
    deadline := RecoveryDeadline.advance _ _ core.deadline (core.clock_now_monotone clocked allowed)
    estimatorBeforeRetire := core.estimatorBeforeRetire
    rtoBeforeRetire := core.rtoBeforeRetire
    rtoPending := fun nonempty => RTOEnvelope.advance _ (core.rtoPending nonempty) (core.clock_now_monotone clocked allowed) }

end Netlib.Check.CampusTCPTwoProgressPhaseBase
