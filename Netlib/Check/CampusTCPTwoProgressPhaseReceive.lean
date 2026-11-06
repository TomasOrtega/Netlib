import Netlib.Check.CampusTCPTwoProgressPhaseBase
import Netlib.Check.CampusTCPTwoProgressReceiveState
import Netlib.Check.CampusTCPTwoProgressPathsFrames

namespace Netlib.Check.CampusTCPTwoProgressPhaseReceive

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core Arrived)
open CampusTCPTwoProgressPathsReady (rangeAt)
open CampusTCPTwoProgressPaths (DataLink)
open CampusTCPTwoProgressSetup (config)

namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace M
export CampusTCPTwoProgressMonitor (Monitor observe)
end M
namespace F
export CampusTCPTwoProgressMonitorFacts (counters ordinary_counters)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper chunk : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {beforeStage afterStage : R.Stage}
variable {part : S.Part} {lane : CampusTCPTwoProgressMonitor.Lane}

inductive Arrival : R.Stage → S.Part → R.Stage → Prop where
  | lower : Arrival .empty .lower .lowerReleased
  | hold : Arrival .empty .upper .upperHeld
  | upper : Arrival .lowerReleased .upper .allReleased
  | gap : Arrival .upperHeld .lower .allReleased
  | old (stage : R.Stage) (part : S.Part) : Arrival stage part stage

private theorem Arrival.covered {present : S.Part → Prop} (arrival : Arrival beforeStage part afterStage)
    (old : ∀ role, Arrived beforeStage role → present role)
    (known : present part) : ∀ role, Arrived afterStage role → present role := by
  cases arrival with
  | lower => intro role arrived; cases role; exact known; cases arrived
  | hold => intro role arrived; cases role; cases arrived; exact known
  | upper => intro role _; cases role; exact old .lower trivial; exact known
  | gap => intro role _; cases role; exact known; exact old .upper trivial
  | old => exact old

private theorem Arrival.empty (arrival : Arrival beforeStage part afterStage) (empty : afterStage = .empty) : beforeStage = .empty := by
  cases arrival <;> cases empty
  rfl

private theorem delivery_counters (actual : Step input) (monitor : M.Monitor)
    (event : actual.event = .deliver index bytes true) :
    (M.observe cfg monitor actual).retries = monitor.retries ∧ (M.observe cfg monitor actual).drops = monitor.drops := by
  have ordinary := F.ordinary_counters cfg monitor actual
  have frame : F.counters (M.observe cfg monitor actual) = F.counters monitor := by
    unfold M.observe
    split
    · rw [event]
      exact ordinary
    · rfl
  exact ⟨congrArg Prod.fst frame, congrArg Prod.snd frame⟩

structure Delivered (core : Core initial native quantum allowance current monitor sent beforeStage)
    (path : DataLink initial current part lane) (afterStage : R.Stage) (chunk : List UInt8) where
  value : CampusTCPTwoProgressReceive.Received initial current beforeStage afterStage chunk
    path.index path.served path.emission path.emitted
  next : Core initial native quantum allowance value.move.after
    (M.observe (config initial native quantum allowance) monitor value.delivery.step) sent afterStage
  book : next.losses.book = core.losses.book

private def finish (core : Core initial native quantum allowance current monitor sent beforeStage)
    (path : DataLink initial current part lane)
    (known : (rangeAt core.live.gatewayState part).isSome = true) (arrival : Arrival beforeStage part afterStage)
    (value : CampusTCPTwoProgressReceive.Received initial current beforeStage afterStage chunk
      path.index path.served path.emission path.emitted) : Delivered core path afterStage chunk := by
  let cfg := config initial native quantum allowance
  let updated := M.observe cfg monitor value.delivery.step
  obtain ⟨retries, drops⟩ := delivery_counters value.delivery.step monitor value.delivery.event
  let prior := value.joint core.live
  let joint : CampusTCPTwoProgressState.Live initial value.move.after sent updated.retries afterStage := {
    anchor := prior.anchor
    senderFlight := by rw [retries]; exact prior.senderFlight
    receiverFacts := prior.receiverFacts
    gatewayState := prior.gatewayState
    gatewayWindow := prior.gatewayWindow
    history := prior.history }
  have sameRuntime : joint.senderFlight.recovery = core.live.senderFlight.recovery := by
    have runtime := joint.senderFlight.runtime
    have slots := congrArg Endpoint.State.recovery value.peer
    exact Option.some.inj (runtime.symm.trans (slots.trans core.live.senderFlight.runtime))
  have length := congrArg List.length value.stream
  simp only [List.length_append] at length
  have monotone : (beforeStage.bytes lower upper).length ≤ (afterStage.bytes lower upper).length :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq length)
  have ranges (role : S.Part) : rangeAt joint.gatewayState role = rangeAt core.live.gatewayState role := by
    cases role <;> rfl
  refine ⟨value, {
    live := joint
    senderWindow := value.sender_reserved core.senderWindow
    originals := core.originals.retain_steps value.move.retained
    originalTimes := core.originalTimes
    writer := core.writer.same value.peerSteps
    losses := core.losses.append value.move
      (by simp only [CampusTCPTwoProgressLossHistory.isDrop, value.delivery.event])
      (by simp only [CampusTCPTwoProgressLossHistory.isTimeout, value.delivery.event]) drops retries
    lossBound := by rw [drops]; exact core.lossBound
    retired := Nat.le_trans core.retired monotone
    gatewayAck := Nat.le_trans core.gatewayAck (Nat.add_le_add_left monotone _)
    peerSettled := core.peerSettled, peerWindow := core.peerWindow
    covered := ?_
    duplicates := by rw [sameRuntime]; exact core.duplicates
    deadline := by rw [sameRuntime]; exact core.deadline
    estimatorBeforeRetire := by rw [sameRuntime]; exact core.estimatorBeforeRetire
    rtoBeforeRetire := by rw [sameRuntime, retries]; exact core.rtoBeforeRetire
    rtoPending := by rw [sameRuntime, retries]; exact core.rtoPending
    emptyDuplicate := ?_ }, rfl⟩
  · intro role arrived
    rw [ranges]
    exact arrival.covered core.covered known role arrived
  · intro empty
    rw [sameRuntime]
    exact core.emptyDuplicate (arrival.empty empty)

theorem Delivered.step_eq {core : Core initial native quantum allowance current monitor sent beforeStage}
    {path : DataLink initial current part lane} (delivered : Delivered core path afterStage chunk)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .deliver path.index path.emission.bytes true) : delivered.value.delivery.step = actual :=
  delivered.value.step_eq actual before event

theorem Delivered.data_lane {core : Core initial native quantum allowance current monitor sent beforeStage}
    {path : DataLink initial current part lane} (delivered : Delivered core path afterStage chunk) :
    CampusTCPTwoProgressMonitor.dataLane (config initial native quantum allowance) lane delivered.value.delivery.step =
      ⟨.done, { lane.refs with
        dataReceipt := some current.report.final.receipts.length
        dataReceiveStamp := some delivered.value.delivery.localStep.stamp }⟩ := by
  have receiver : delivered.value.delivery.receipt.actor = sender.other := by
    calc
      delivered.value.delivery.receipt.actor = delivered.value.delivery.receipt.served.ticket.value.produced.actor.other :=
        delivered.value.delivery.receipt.receiver
      _ = sender.other := by rw [delivered.value.delivery.receiptService, path.actor]
  have recorded : delivered.value.delivery.step.result.application = some (sender.other, delivered.value.delivery.localStep) := by
    simpa only [path.actor] using delivered.value.delivery.recorded
  simp only [CampusTCPTwoProgressMonitor.dataLane, path.phase, CampusTCPGapProgressMonitor.observeReceipt,
    delivered.value.delivery.receiptAt, recorded, receiver, delivered.value.delivery.beforeEq,
    CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap]
  cases sender <;> rfl

theorem lower_at (core : Core initial native quantum allowance current monitor sent .empty)
    (path : DataLink initial current .lower lane)
    (known : (rangeAt core.live.gatewayState .lower).isSome = true) :
    Nonempty (Delivered core path .lowerReleased lower) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.lower_at core.live.receiverFacts path.receive_link
  exact ⟨finish core path known .lower value⟩

theorem hold_at (core : Core initial native quantum allowance current monitor sent .empty)
    (path : DataLink initial current .upper lane)
    (known : (rangeAt core.live.gatewayState .upper).isSome = true) :
    Nonempty (Delivered core path .upperHeld []) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.hold_at core.live.receiverFacts path.receive_link
  exact ⟨finish core path known .hold value⟩

theorem upper_at (core : Core initial native quantum allowance current monitor sent .lowerReleased)
    (path : DataLink initial current .upper lane)
    (known : (rangeAt core.live.gatewayState .upper).isSome = true) :
    Nonempty (Delivered core path .allReleased upper) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.upper_at core.live.receiverFacts path.receive_link
  exact ⟨finish core path known .upper value⟩

theorem gap_at (core : Core initial native quantum allowance current monitor sent .upperHeld)
    (path : DataLink initial current .lower lane)
    (known : (rangeAt core.live.gatewayState .lower).isSome = true) :
    Nonempty (Delivered core path .allReleased (lower ++ upper)) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.gap_at core.live.receiverFacts path.receive_link
  exact ⟨finish core path known .gap value⟩

private theorem part_nonempty (initial : TwoWriteInitial cut sender gateway lower upper) (part : S.Part) :
    part.bytes lower upper ≠ [] := by cases part; exact initial.lowerNonempty; exact initial.upperNonempty

theorem old_at (core : Core initial native quantum allowance current monitor sent beforeStage)
    (path : DataLink initial current part lane)
    (known : (rangeAt core.live.gatewayState part).isSome = true)
    (old : part.offset lower + (part.bytes lower upper).length ≤ (beforeStage.bytes lower upper).length) :
    Nonempty (Delivered core path beforeStage []) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.old_at core.live.receiverFacts path.receive_link (part_nonempty initial part) old
  exact ⟨finish core path known (.old _ _) value⟩

theorem old_lower_at (core : Core initial native quantum allowance current monitor sent .lowerReleased)
    (path : DataLink initial current .lower lane)
    (known : (rangeAt core.live.gatewayState .lower).isSome = true) :
    Nonempty (Delivered core path .lowerReleased []) :=
  old_at core path known (by
    simp only [CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes,
      CampusTCPTwoProgressReceiver.Stage.bytes, Nat.zero_add]
    exact Nat.le_refl _)

theorem old_lower_all_at (core : Core initial native quantum allowance current monitor sent .allReleased)
    (path : DataLink initial current .lower lane)
    (known : (rangeAt core.live.gatewayState .lower).isSome = true) :
    Nonempty (Delivered core path .allReleased []) := by
  apply old_at core path known
  change 0 + lower.length ≤ (lower ++ upper).length
  simp only [Nat.zero_add, List.length_append]
  exact Nat.le_add_right _ _

theorem old_upper_at (core : Core initial native quantum allowance current monitor sent .allReleased)
    (path : DataLink initial current .upper lane)
    (known : (rangeAt core.live.gatewayState .upper).isSome = true) :
    Nonempty (Delivered core path .allReleased []) :=
  old_at core path known (by
    simp only [CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes,
      CampusTCPTwoProgressReceiver.Stage.bytes, List.length_append]
    exact Nat.le_refl _)

end Netlib.Check.CampusTCPTwoProgressPhaseReceive
