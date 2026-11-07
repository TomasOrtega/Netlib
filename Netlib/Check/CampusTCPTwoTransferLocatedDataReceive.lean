import Netlib.Check.CampusTCPTwoTransferReceiveObserve

/-!
# Located Core after the actual data receipt

The current path enables delivery. The same receipt extends the receiver
stream and loss suffix without changing sender recovery or gateway ranges.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedDataReceive

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferPaths (DataLink)
open CampusTCPTwoTransferAdmission (rangeAt)
open CampusTCPTwoProgressPhaseBase (Arrived)

namespace W
export CampusTCPTwoTransferMonitor (Config Monitor Allowed observe)
end W
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane DropTarget laneDemand servesOption)
end M
namespace O
export CampusTCPTwoTransferReceiveObserve (afterReceipt)
end O
namespace D
export CampusTCPTwoTransferLocatedReceive (Delivered lower_at hold_at upper_at gap_at old_at)
end D
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace Q
export CampusTCPTwoTransferQueue (Closed TicketAt)
end Q
namespace P
export CampusTCPTwoProgressPhaseObserveReceive (dataLaneAt receiptUpdate)
end P

export CampusTCPTwoProgressPhaseReceive (Arrival)

inductive Dispatch (config : W.Config) (state : State input) (monitor : W.Monitor) : M.Lane → M.DropTarget → Prop where
  | lower (forward : monitor.exchange.mode = .forward) (mode : monitor.exchange.forward.mode = .originals)
      (first : monitor.exchange.forward.lower.phase ≠ .needSend) (second : monitor.exchange.forward.upper.phase ≠ .needSend)
      (ack : monitor.exchange.forward.ack = none) : Dispatch config state monitor monitor.exchange.forward.lower .lower
  | upper (forward : monitor.exchange.mode = .forward) (mode : monitor.exchange.forward.mode = .originals)
      (first : monitor.exchange.forward.lower.phase ≠ .needSend) (second : monitor.exchange.forward.upper.phase ≠ .needSend)
      (ack : monitor.exchange.forward.ack = none)
      (lower : ∀ index bytes, CampusTCPGapProgressMonitor.nextAction (config.at state).forward.toConfig state monitor.exchange.forward.upper.toGap =
        some (.deliver index bytes true) → M.servesOption (M.laneDemand (config.at state).forward state monitor.exchange.forward
          monitor.exchange.forward.lower) (.deliver index bytes true) = false) :
      Dispatch config state monitor monitor.exchange.forward.upper .upper
  | retry (forward : monitor.exchange.mode = .forward) (mode : monitor.exchange.forward.mode = .recovery)
      (ack : monitor.exchange.forward.ack = none) (waiting : monitor.exchange.forward.waiting = false) :
      Dispatch config state monitor monitor.exchange.forward.retry .retry

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper chunk : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {beforeStage afterStage : R.Stage}
variable {part : S.Part} {lane : M.Lane} {target : M.DropTarget}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent beforeStage}
variable {path : DataLink initial current part lane}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem Dispatch.not_ack (selected : Dispatch cfg current.report.final monitor lane target) : target ≠ .ack := by cases selected <;> decide

theorem Dispatch.selected_lane (selected : Dispatch cfg current.report.final monitor lane target) : P.dataLaneAt monitor.exchange.forward target = lane := by
  cases selected <;> rfl

theorem Dispatch.observed (selected : Dispatch cfg current.report.final monitor lane target)
    (value : D.Delivered core.live path afterStage chunk)
    (allowed : W.Allowed cfg current.report.final monitor value.value.delivery.step.event) :
    W.observe cfg monitor value.value.delivery.step = O.afterReceipt monitor target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  cases selected with
  | lower forward mode first second ack => exact CampusTCPTwoTransferReceiveObserve.lower_observe value forward mode first second ack allowed
  | upper forward mode first second ack lower =>
    exact CampusTCPTwoTransferReceiveObserve.upper_observe value forward mode first second ack
      (by rw [value.value.delivery.event]; exact lower _ _ (path.action _)) allowed
  | retry forward mode ack waiting => exact CampusTCPTwoTransferReceiveObserve.retry_observe value forward mode ack waiting allowed

private theorem arrival_covered {present : S.Part → Prop} (arrival : Arrival beforeStage part afterStage)
    (old : ∀ role, Arrived beforeStage role → present role) (known : present part) : ∀ role, Arrived afterStage role → present role := by
  cases arrival with
  | lower => intro role arrived; cases role; exact known; cases arrived
  | hold => intro role arrived; cases role; cases arrived; exact known
  | upper => intro role _; cases role; exact old .lower trivial; exact known
  | gap => intro role _; cases role; exact known; exact old .upper trivial
  | old => exact old

private theorem arrival_empty (arrival : Arrival beforeStage part afterStage) (empty : afterStage = .empty) : beforeStage = .empty := by
  cases arrival <;> cases empty
  rfl

structure Received (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent beforeStage)
    (path : DataLink initial current part lane) (target : M.DropTarget) (afterStage : R.Stage) (chunk : List UInt8) where
  value : D.Delivered core.live path afterStage chunk
  arrival : Arrival beforeStage part afterStage
  next : Core initial checks routing quantum allowance reverseLower reverseUpper value.value.move.after
    (W.observe cfg monitor value.value.delivery.step) location sent afterStage
  gateway : next.live.gatewayState = core.live.gatewayState.reframe (value.value.gateway location)
  observed : W.observe cfg monitor value.value.delivery.step =
    O.afterReceipt monitor target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk
  book : next.losses.book = core.losses.book

private theorem receipt_queue (selected : Dispatch cfg current.report.final monitor lane target)
    (value : D.Delivered core.live path afterStage chunk)
    (observed : W.observe cfg monitor value.value.delivery.step = O.afterReceipt monitor target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk) :
    Q.Closed value.value.move.after.report.final (W.observe cfg monitor value.value.delivery.step).exchange.forward := by
  have work : value.value.move.after.report.final.work = current.report.final.work := by
    rw [value.value.move.final, CampusTCPTwoProgressPathRetain.Step.work_quiet value.value.delivery.step
      (by rw [value.value.delivery.event]; trivial), value.value.delivery.beforeEq]
  have closed := core.primaryQueue.work_same work
  rw [observed]
  cases selected with
  | lower =>
    intro item member primary
    rcases closed item member primary with first | second
    · rw [Q.TicketAt, path.phase] at first; cases first.1
    · exact Or.inr second
  | upper =>
    intro item member primary
    rcases closed item member primary with first | second
    · exact Or.inl first
    · rw [Q.TicketAt, path.phase] at second; cases second.1
  | retry => exact closed

private def finish (selected : Dispatch cfg current.report.final monitor lane target)
    (known : (rangeAt core.live.gatewayState part).isSome = true) (arrival : Arrival beforeStage part afterStage)
    (value : D.Delivered core.live path afterStage chunk)
    (allowed : W.Allowed cfg current.report.final monitor value.value.delivery.step.event) : Received core path target afterStage chunk := by
  have observed := selected.observed value allowed
  have counter : (W.observe cfg monitor value.value.delivery.step).exchange.forward.retries = monitor.exchange.forward.retries := by
    rw [observed]; cases target <;> rfl
  let live : LiveAt initial value.value.move.after location sent (W.observe cfg monitor value.value.delivery.step).exchange.forward.retries afterStage := {
    anchor := value.next.anchor
    senderFlight := by rw [counter]; exact value.next.senderFlight
    receiverFacts := value.next.receiverFacts
    gatewayState := core.live.gatewayState.reframe (value.value.gateway location)
    gatewayWindow := core.live.gatewayWindow
    history := value.next.history }
  have recovery : live.senderFlight.recovery = core.live.senderFlight.recovery := by
    have same := congrArg Endpoint.State.recovery value.value.peer
    exact Option.some.inj (live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))
  have length := congrArg List.length value.value.stream
  simp only [List.length_append] at length
  have monotone : (beforeStage.bytes lower upper).length ≤ (afterStage.bytes lower upper).length := by omega
  let next : Core initial checks routing quantum allowance reverseLower reverseUpper value.value.move.after
      (W.observe cfg monitor value.value.delivery.step) location sent afterStage := {
    live
    senderWindow := value.value.sender_reserved core.senderWindow
    originals := core.originals.retain_steps value.value.move.retained
    originalTimes := core.originalTimes
    writer := core.writer.same value.value.peerSteps
    losses := core.losses.append value.value.move
      (by rw [CampusTCPTwoProgressLossHistory.isDrop, value.value.delivery.event])
      (by rw [CampusTCPTwoExchangeLoss.isTimeoutOutput, value.value.delivery.event])
      (by rw [observed]; cases target <;> rfl) counter (by rw [observed]; rfl) (by rw [observed]; rfl)
    lossBound := by rw [observed]; cases target <;> exact core.lossBound
    primaryQueue := receipt_queue selected value observed
    retired := Nat.le_trans core.retired monotone
    gatewayAck := Nat.le_trans core.gatewayAck (Nat.add_le_add_left monotone _)
    peerSettled := core.peerSettled
    peerWindow := core.peerWindow
    covered := fun role arrived => arrival_covered arrival core.covered known role arrived
    duplicates := by rw [recovery]; exact core.duplicates
    emptyDuplicate := fun empty => by rw [recovery]; exact core.emptyDuplicate (arrival_empty arrival empty)
    deadline := by rw [recovery]; exact core.deadline
    estimatorBeforeRetire := by rw [recovery]; exact core.estimatorBeforeRetire
    rtoBeforeRetire := by rw [recovery, counter]; exact core.rtoBeforeRetire
    rtoPending := by rw [recovery, counter]; exact core.rtoPending }
  exact ⟨value, arrival, next, rfl, observed, rfl⟩

theorem lower_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent .empty)
    (path : DataLink initial current .lower lane) (selected : Dispatch cfg current.report.final monitor lane target)
    (known : (rangeAt core.live.gatewayState .lower).isSome = true)
    (allowed : W.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Nonempty (Received core path target .lowerReleased lower) := by
  obtain ⟨value⟩ := D.lower_at core.live path
  exact ⟨finish selected known .lower value (by rw [value.value.delivery.event]; exact allowed)⟩

theorem hold_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent .empty)
    (path : DataLink initial current .upper lane) (selected : Dispatch cfg current.report.final monitor lane target)
    (known : (rangeAt core.live.gatewayState .upper).isSome = true)
    (allowed : W.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Nonempty (Received core path target .upperHeld []) := by
  obtain ⟨value⟩ := D.hold_at core.live path
  exact ⟨finish selected known .hold value (by rw [value.value.delivery.event]; exact allowed)⟩

theorem upper_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent .lowerReleased)
    (path : DataLink initial current .upper lane) (selected : Dispatch cfg current.report.final monitor lane target)
    (known : (rangeAt core.live.gatewayState .upper).isSome = true)
    (allowed : W.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Nonempty (Received core path target .allReleased upper) := by
  obtain ⟨value⟩ := D.upper_at core.live path
  exact ⟨finish selected known .upper value (by rw [value.value.delivery.event]; exact allowed)⟩

theorem gap_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent .upperHeld)
    (path : DataLink initial current .lower lane) (selected : Dispatch cfg current.report.final monitor lane target)
    (known : (rangeAt core.live.gatewayState .lower).isSome = true)
    (allowed : W.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Nonempty (Received core path target .allReleased (lower ++ upper)) := by
  obtain ⟨value⟩ := D.gap_at core.live path
  exact ⟨finish selected known .gap value (by rw [value.value.delivery.event]; exact allowed)⟩

theorem old_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent beforeStage)
    (path : DataLink initial current part lane) (selected : Dispatch cfg current.report.final monitor lane target)
    (known : (rangeAt core.live.gatewayState part).isSome = true)
    (old : part.offset lower + (part.bytes lower upper).length ≤ (beforeStage.bytes lower upper).length)
    (allowed : W.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Nonempty (Received core path target beforeStage []) := by
  obtain ⟨value⟩ := D.old_at core.live path old
  exact ⟨finish selected known (.old _ _) value (by rw [value.value.delivery.event]; exact allowed)⟩

theorem Received.sender_recovery (value : Received core path target afterStage chunk) :
    value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
  have same := congrArg Endpoint.State.recovery value.value.value.peer
  exact Option.some.inj (value.next.live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))

theorem Received.pending (value : Received core path target afterStage chunk) : value.next.live.receiverFacts.reaction.work.pending ≠ [] := by
  have same := Option.some.inj (value.next.live.receiverFacts.ackRuntime.symm.trans value.value.value.receiver.ackRuntime)
  rw [same]
  exact value.value.value.pending

theorem Received.step_eq (value : Received core path target afterStage chunk) (actual : Step input)
    (before : actual.before = current.report.final) (event : actual.event = .deliver path.index path.emission.bytes true) :
    value.value.value.delivery.step = actual := value.value.step_eq actual before event

end Netlib.Check.CampusTCPTwoTransferLocatedDataReceive
