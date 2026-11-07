import Netlib.Check.CampusTCPTwoTransferServiceWorkFrames

/-!
# Forward phase progress through ordinary service

The actual selected ticket supplies its new link.
Unselected paths and the same loss book retain current head debt.
-/

namespace Netlib.Check.CampusTCPTwoTransferServiceProgress

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferWork (Work DataWork OriginalLane RetryLane AckWork AckState)
open CampusTCPTwoTransferPhaseState (Active Debt)
open CampusTCPTwoTransferPaths (DataTicket AckTicket)
open CampusTCPTwoTransferLocatedService (DataServiced AckServiced DataTarget)

namespace W
export CampusTCPTwoTransferMonitor (Monitor observe Allowed)
end W
namespace M
export CampusTCPTwoProgressMonitor (Lane)
end M
namespace S
export CampusTCPTwoProgressSender (Part Stage)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace N
export CampusTCPTwoTransferNetwork (Service)
end N
namespace F
export CampusTCPTwoProgressPhaseNetworkState (Frame)
end F
namespace H
export CampusTCPTwoTransferServiceWorkFrames (data_other original_other data_ack original_ack phase_service)
end H

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {part role : S.Part} {lane : M.Lane} {target : DataTarget} {actual : Step input}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private def assemble
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
    (active : Active core) (value : N.Service current item hit session actual served emission emitted)
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after (W.observe cfg monitor actual) location sent received)
    (book : next.losses.book = core.losses.book)
    (exchange : (W.observe cfg monitor actual).exchange.mode = monitor.exchange.mode)
    (frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward)
    (lowerLane : OriginalLane initial checks value.move.after next.live.gatewayState received .lower
      (W.observe cfg monitor actual).exchange.forward.lower)
    (upperLane : OriginalLane initial checks value.move.after next.live.gatewayState received .upper
      (W.observe cfg monitor actual).exchange.forward.upper)
    (retry : RetryLane initial checks value.move.after next.live.gatewayState sent (W.observe cfg monitor actual).exchange.forward.retry)
    (ack : AckState checks next.live (W.observe cfg monitor actual).exchange.forward.ack)
    (ackGateway : ∀ lane, (W.observe cfg monitor actual).exchange.forward.ack = some lane → lane.phase = .ackLink →
      (next.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
        initial.geometry.«prefix» + (received.bytes lower upper).length) : Active next := by
  let raw := (W.observe cfg monitor actual).exchange.forward
  change AckState checks next.live raw.ack at ack
  have someBefore : raw.ack.isSome = true → monitor.exchange.forward.ack.isSome = true := by
    intro pending
    cases old : monitor.exchange.forward.ack with
    | none => rw [frame.ackNone.mpr old] at pending; cases pending
    | some lane => rfl
  have runtime : next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
    have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
    exact Option.some.inj (next.live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))
  refine {
    exchange := exchange.trans active.exchange
    mode := by rw [frame.mode]; exact active.mode
    preparing := active.preparing, nonempty := active.nonempty
    lowerLane, upperLane, retry, ack, ackGateway
    originals := ?_, recovery := ?_, serial := ?_, ackNonempty := ?_, waiting := ?_, runnable := ?_
    recoveryHead := fun mode waiting => active.recoveryHead (frame.mode ▸ mode) (frame.waiting ▸ waiting)
    originalOpen := ?_, debt := ?_, upperMissing := ?_, zeroAck := ?_
    sources := (CampusTCPTwoTransferSources.Frame.service value).receipts active.sources }
  · intro mode
    obtain ⟨done, waiting, retries⟩ := active.originals (frame.mode ▸ mode)
    exact ⟨frame.retryDone.mpr done, frame.waiting.trans waiting, frame.retries.trans retries⟩
  · intro mode
    obtain ⟨first, second⟩ := active.recovery (frame.mode ▸ mode)
    exact ⟨frame.lowerDone.mpr first, frame.upperDone.mpr second⟩
  · intro pending
    exact frame.retryDone.mpr (active.serial (someBefore pending))
  · intro pending
    exact active.ackNonempty (someBefore pending)
  · intro waiting
    obtain ⟨ack, done⟩ := active.waiting (frame.waiting ▸ waiting)
    exact ⟨frame.ackNone.mpr ack, frame.retryDone.mpr done⟩
  · intro mode waiting ack done
    exact active.runnable (frame.mode ▸ mode) (frame.waiting ▸ waiting) (frame.ackNone.mp ack) (frame.retryDone.mp done)
  · intro mode ack both
    exact active.originalOpen (frame.mode ▸ mode) (frame.ackNone.mp ack)
      ⟨frame.lowerDone.mp both.1, frame.upperDone.mp both.2⟩
  · intro role head rest selected
    obtain ⟨debt⟩ := active.debt role head rest selected
    cases debt with
    | cause position chosen => exact ⟨.cause position (by rw [book]; exact chosen)⟩
    | lower same work => exact ⟨.lower same (lowerLane.work (fun done => work.not_done (frame.lowerDone.mp done)))⟩
    | upper same work => exact ⟨.upper same (upperLane.work (fun done => work.not_done (frame.upperDone.mp done)))⟩
    | retry work => exact ⟨.retry (retry.work (fun done => work.not_done (frame.retryDone.mp done)) selected)⟩
    | ack lane pending _ covered =>
      have notNone : raw.ack ≠ none := by intro absent; rw [frame.ackNone.mp absent] at pending; cases pending
      cases found : raw.ack with
      | none => exact False.elim (notNone found)
      | some lane =>
        exact ⟨.ack lane found (by simpa only [AckState, found] using ack) covered⟩
  · intro retired missing done
    obtain ⟨position, chosen⟩ := active.upperMissing retired missing (frame.upperDone.mp done)
    exact ⟨position, by rw [book]; exact chosen⟩
  · intro lane pending retired
    have old : monitor.exchange.forward.ack.isSome = true := someBefore (by rw [pending]; rfl)
    cases found : monitor.exchange.forward.ack with
    | none => rw [found] at old; cases old
    | some lane => rw [runtime]; exact active.zeroAck lane found retired


def active_lower (active : Active core) {path : DataTicket initial checks current .lower monitor.exchange.forward.lower}
    (value : DataServiced core path .lower actual) (mode : monitor.exchange.forward.mode = .originals)
    (ackNone : monitor.exchange.forward.ack = none) : Active value.next := by
  have missing : ¬CampusTCPTwoProgressPhaseBase.Arrived received .lower := by
    cases active.lowerLane with
    | active _ missing => exact missing
    | done phase => rw [path.phase] at phase; cases phase
  have nextLower := congrArg (fun whole : W.Monitor => whole.exchange.forward.lower) value.observed
  have nextUpper := congrArg (fun whole : W.Monitor => whole.exchange.forward.upper) value.observed
  have nextRetry := congrArg (fun whole : W.Monitor => whole.exchange.forward.retry) value.observed
  have nextAck := congrArg (fun whole : W.Monitor => whole.exchange.forward.ack) value.observed
  have frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward := by
    rw [value.observed]
    exact CampusTCPTwoProgressPhaseNetworkState.Frame.data_lower _ _ (by rw [path.phase]; decide) (by change CampusTCPRoundMonitor.Phase.dataLink ≠ .done; decide)
  apply assemble active value.value.value value.next value.book (by rw [value.observed]; rfl) frame
  · rw [nextLower]
    exact .active value.work missing
  · rw [nextUpper]
    exact H.original_other value active.upperLane (by decide)
  · rw [nextRetry]
    exact .done (active.originals mode).1
  · rw [nextAck]
    change AckState checks value.next.live monitor.exchange.forward.ack
    rw [ackNone]
    exact PUnit.unit
  · intro lane pending _
    rw [value.ack, ackNone] at pending
    cases pending


def active_upper (active : Active core) {path : DataTicket initial checks current .upper monitor.exchange.forward.upper}
    (value : DataServiced core path .upper actual) (mode : monitor.exchange.forward.mode = .originals)
    (ackNone : monitor.exchange.forward.ack = none) : Active value.next := by
  have missing : ¬CampusTCPTwoProgressPhaseBase.Arrived received .upper := by
    cases active.upperLane with
    | active _ missing => exact missing
    | done phase => rw [path.phase] at phase; cases phase
  have nextLower := congrArg (fun whole : W.Monitor => whole.exchange.forward.lower) value.observed
  have nextUpper := congrArg (fun whole : W.Monitor => whole.exchange.forward.upper) value.observed
  have nextRetry := congrArg (fun whole : W.Monitor => whole.exchange.forward.retry) value.observed
  have nextAck := congrArg (fun whole : W.Monitor => whole.exchange.forward.ack) value.observed
  have frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward := by
    rw [value.observed]
    exact CampusTCPTwoProgressPhaseNetworkState.Frame.data_upper _ _ (by rw [path.phase]; decide) (by change CampusTCPRoundMonitor.Phase.dataLink ≠ .done; decide)
  apply assemble active value.value.value value.next value.book (by rw [value.observed]; rfl) frame
  · rw [nextLower]
    exact H.original_other value active.lowerLane (by decide)
  · rw [nextUpper]
    exact .active value.work missing
  · rw [nextRetry]
    exact .done (active.originals mode).1
  · rw [nextAck]
    change AckState checks value.next.live monitor.exchange.forward.ack
    rw [ackNone]
    exact PUnit.unit
  · intro lane pending _
    rw [value.ack, ackNone] at pending
    cases pending


def active_retry (active : Active core) {path : DataTicket initial checks current part monitor.exchange.forward.retry}
    (value : DataServiced core path .retry actual) (mode : monitor.exchange.forward.mode = .recovery)
    (ackNone : monitor.exchange.forward.ack = none)
    (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) : Active value.next := by
  have nextLower := congrArg (fun whole : W.Monitor => whole.exchange.forward.lower) value.observed
  have nextUpper := congrArg (fun whole : W.Monitor => whole.exchange.forward.upper) value.observed
  have nextRetry := congrArg (fun whole : W.Monitor => whole.exchange.forward.retry) value.observed
  have nextAck := congrArg (fun whole : W.Monitor => whole.exchange.forward.ack) value.observed
  have frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward := by
    rw [value.observed]
    exact CampusTCPTwoProgressPhaseNetworkState.Frame.retry _ _ (by rw [path.phase]; decide) (by change CampusTCPRoundMonitor.Phase.dataLink ≠ .done; decide)
  apply assemble active value.value.value value.next value.book (by rw [value.observed]; rfl) frame
  · rw [nextLower]
    exact .done (active.recovery mode).1
  · rw [nextUpper]
    exact .done (active.recovery mode).2
  · rw [nextRetry]
    exact .active part head rest selected value.work
  · rw [nextAck]
    change AckState checks value.next.live monitor.exchange.forward.ack
    rw [ackNone]
    exact PUnit.unit
  · intro lane pending _
    rw [value.ack, ackNone] at pending
    cases pending


def active_ack (active : Active core)
    {path : AckTicket initial checks current (received.bytes lower upper).length lane}
    (value : AckServiced core path actual) (pending : monitor.exchange.forward.ack = some lane) : Active value.next := by
  have nextLower := congrArg (fun whole : W.Monitor => whole.exchange.forward.lower) value.observed
  have nextUpper := congrArg (fun whole : W.Monitor => whole.exchange.forward.upper) value.observed
  have nextRetry := congrArg (fun whole : W.Monitor => whole.exchange.forward.retry) value.observed
  have nextAck := congrArg (fun whole : W.Monitor => whole.exchange.forward.ack) value.observed
  have frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward := by
    rw [value.observed]
    exact CampusTCPTwoProgressPhaseNetworkState.Frame.ack _ _ _ pending
  apply assemble active value.value.value value.next value.book (by rw [value.observed]; rfl) frame
  · rw [nextLower]
    exact H.original_ack value active.lowerLane
  · rw [nextUpper]
    exact H.original_ack value active.upperLane
  · rw [nextRetry]
    exact .done (active.serial (by rw [pending]; rfl))
  · rw [nextAck]
    exact .link value.paths.link
  · intro _ _ _
    exact value.acknowledged


theorem DataServiced.phase {path : DataTicket initial checks current part lane}
    (value : DataServiced core path target actual)
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished) (selected : path.assignedGateway = location) :
    CampusTCPTwoTransferControlState.Phase value.value.value.move.after.report.final (W.observe cfg monitor actual).mode location := by
  rw [value.observed]
  exact H.phase_service phase ordinary value.value.value (path.ticket_gateway.trans selected)


theorem AckServiced.phase {path : AckTicket initial checks current (received.bytes lower upper).length lane}
    (value : AckServiced core path actual)
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished) (selected : path.assignedGateway = location) :
    CampusTCPTwoTransferControlState.Phase value.value.value.move.after.report.final (W.observe cfg monitor actual).mode location := by
  rw [value.observed]
  exact H.phase_service phase ordinary value.value.value (path.ticket_gateway.trans selected)

end Netlib.Check.CampusTCPTwoTransferServiceProgress
