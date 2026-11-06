import Netlib.Check.CampusTCPTwoProgressPhaseState
import Netlib.Check.CampusTCPTwoProgressPhaseObserve
import Netlib.Check.CampusTCPTwoProgressPathRetain
import Netlib.Check.CampusTCPTwoProgressPathsDistinct

namespace Netlib.Check.CampusTCPTwoProgressPhaseNetworkState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressPhaseState CampusTCPTwoProgressPaths
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressPathsReady (rangeAt)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane observe)
end M
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace N
export CampusTCPTwoProgressPhaseNetwork (Advance DataAssigned DataServed AckAssigned AckServed)
end N
namespace D
export CampusTCPTwoProgressPhaseDebt (Work Debt)
end D

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor updated : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {part : S.Part} {lane : M.Lane} {actual : Step input}
variable {core : Core initial native quantum allowance current monitor sent received}

theorem DataWork.not_needSend {view : CampusTCPTwoProgressGatewayState.View initial current}
    (work : DataWork initial native current view part lane) : lane.phase ≠ .needSend := by
  cases work with
  | ingress path _ => rw [path.phase]; decide
  | ticket path _ => rw [path.phase]; decide
  | link path _ _ => rw [path.phase]; decide

theorem OriginalLane.not_needSend {view : CampusTCPTwoProgressGatewayState.View initial current}
    (value : OriginalLane initial native current view received part lane) : lane.phase ≠ .needSend := by
  cases value with
  | active work _ => exact DataWork.not_needSend work
  | done phase => rw [phase]; decide

def OriginalLane.work {view : CampusTCPTwoProgressGatewayState.View initial current}
    (value : OriginalLane initial native current view received part lane) (live : lane.phase ≠ .done) :
    D.Work initial native current part lane := by
  cases value with
  | active work _ => exact work.work
  | done phase => exact False.elim (live phase)

omit core in
def RetryLane.work {view : CampusTCPTwoProgressGatewayState.View initial current}
    (value : RetryLane initial native current view sent lane) (live : lane.phase ≠ .done)
    {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) : D.Work initial native current part lane := by
  clear core
  cases value with
  | active role head rest chosen work =>
    have same : role = part := by cases chosen <;> cases selected <;> rfl
    subst role
    exact work.work
  | done phase => exact False.elim (live phase)

structure Frame (before after : M.Monitor) : Prop where
  mode : after.mode = before.mode
  waiting : after.waiting = before.waiting
  retries : after.retries = before.retries
  lowerDone : after.lower.phase = .done ↔ before.lower.phase = .done
  upperDone : after.upper.phase = .done ↔ before.upper.phase = .done
  retryDone : after.retry.phase = .done ↔ before.retry.phase = .done
  ackNone : after.ack = none ↔ before.ack = none

theorem Frame.data_lower (before : M.Monitor) (next : M.Lane)
    (old : before.lower.phase ≠ .done) (fresh : next.phase ≠ .done) :
    Frame before { before with lower := next, lastOriginal := some .lower } := by
  exact ⟨rfl, rfl, rfl, by simp only [fresh, old], Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem Frame.data_upper (before : M.Monitor) (next : M.Lane)
    (old : before.upper.phase ≠ .done) (fresh : next.phase ≠ .done) :
    Frame before { before with upper := next, lastOriginal := some .upper } := by
  exact ⟨rfl, rfl, rfl, Iff.rfl, by simp only [fresh, old], Iff.rfl, Iff.rfl⟩

theorem Frame.retry (before : M.Monitor) (next : M.Lane)
    (old : before.retry.phase ≠ .done) (fresh : next.phase ≠ .done) :
    Frame before { before with retry := next } := by
  exact ⟨rfl, rfl, rfl, Iff.rfl, Iff.rfl, by simp only [fresh, old], Iff.rfl⟩

theorem Frame.ack (before : M.Monitor) (next : M.Lane) (lane : M.Lane) (pending : before.ack = some lane) :
    Frame before { before with ack := some next } := by
  refine ⟨rfl, rfl, rfl, Iff.rfl, Iff.rfl, Iff.rfl, ?_⟩
  simp only [pending, reduceCtorEq]

def assemble (active : Active core) (move : Move current actual) (advance : N.Advance core actual move)
    (endpoints : move.after.endpoints = current.endpoints)
    (quiet : CampusTCPTwoProgressReceiptFrames.NonDelivery actual.event)
    (frame : Frame monitor (M.observe (config initial native quantum allowance) monitor actual))
    (lowerLane : OriginalLane initial native move.after advance.nextCore.live.gatewayState received .lower
      (M.observe (config initial native quantum allowance) monitor actual).lower)
    (upperLane : OriginalLane initial native move.after advance.nextCore.live.gatewayState received .upper
      (M.observe (config initial native quantum allowance) monitor actual).upper)
    (retry : RetryLane initial native move.after advance.nextCore.live.gatewayState sent
      (M.observe (config initial native quantum allowance) monitor actual).retry)
    (ack : AckState advance.nextCore)
    (ackGateway : ∀ lane, (M.observe (config initial native quantum allowance) monitor actual).ack = some lane →
      lane.phase = .ackLink →
      (advance.nextCore.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
        initial.geometry.«prefix» + (received.bytes lower upper).length) : Active advance.nextCore := by
  let next := M.observe (config initial native quantum allowance) monitor actual
  have someBefore : next.ack.isSome = true → monitor.ack.isSome = true := by
    intro pending
    cases old : monitor.ack with
    | none => rw [frame.ackNone.mpr old] at pending; cases pending
    | some value => rfl
  have runtime : advance.nextCore.live.senderFlight.recovery = core.live.senderFlight.recovery := by
    have slots := congrArg (fun value => (endpoint value sender).recovery) endpoints
    exact Option.some.inj (advance.nextCore.live.senderFlight.runtime.symm.trans (slots.trans core.live.senderFlight.runtime))
  refine {
    mode := by rw [frame.mode]; exact active.mode
    preparing := active.preparing, nonempty := active.nonempty
    lowerLane, upperLane, retry, ack, ackGateway
    originals := ?_, recovery := ?_, serial := ?_, ackNonempty := ?_, waiting := ?_, runnable := ?_
    recoveryHead := fun mode waiting => active.recoveryHead (frame.mode ▸ mode) (frame.waiting ▸ waiting)
    originalOpen := ?_, debt := ?_, upperMissing := ?_, zeroAck := ?_
    sources := active.sources.non_delivery move quiet }
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
    | cause position chosen => exact ⟨.cause position (by rw [advance.book]; exact chosen)⟩
    | lower same work => exact ⟨.lower same (OriginalLane.work lowerLane (fun done => work.not_done (frame.lowerDone.mp done)))⟩
    | upper same work => exact ⟨.upper same (OriginalLane.work upperLane (fun done => work.not_done (frame.upperDone.mp done)))⟩
    | retry work => exact ⟨.retry (RetryLane.work retry (fun done => work.not_done (frame.retryDone.mp done)) selected)⟩
    | ack lane pending covered =>
      have notNone : next.ack ≠ none := by intro absent; rw [frame.ackNone.mp absent] at pending; cases pending
      cases found : next.ack with
      | none => exact False.elim (notNone found)
      | some lane => exact ⟨.ack lane found covered⟩
  · intro retired missing done
    obtain ⟨position, chosen⟩ := active.upperMissing retired missing (frame.upperDone.mp done)
    exact ⟨position, by rw [advance.book]; exact chosen⟩
  · intro lane pending retired
    have old : monitor.ack.isSome = true := someBefore (by rw [pending]; rfl)
    cases found : monitor.ack with
    | none => rw [found] at old; cases old
    | some lane => rw [runtime]; exact active.zeroAck lane found retired

def DataWork.after_assignment {view : CampusTCPTwoProgressGatewayState.View initial current}
    (work : DataWork initial native current view part lane)
    {index : Nat} {ingress : I.InterfaceRef} {produced : Produced input.active input.passive}
    (value : CampusTCPTwoProgressNetwork.AssignmentMove initial current index ingress produced actual)
    (next : CampusTCPTwoProgressGatewayState.View initial value.move.after)
    (ingressOther : ∀ path : DataIngress initial current part lane,
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID)
    (linkOther : ∀ path : DataLink initial current part lane,
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    DataWork initial native value.move.after next part lane := by
  cases work with
  | ingress path source => exact .ingress (path.after_move value.move (ingressOther path)) (source.retain_steps value.move.retained)
  | ticket path source => exact .ticket (path.after_assignment value) (source.retain_steps value.move.retained)
  | link path source covered =>
    refine .link (path.after_move value.move (linkOther path)) (source.retain_steps value.move.retained) ?_
    have ranges := view.ranges_same next (value.serviceFrame gateway)
    cases part with
    | lower => change next.ranges.lowerRun.isSome = true; rw [ranges.1]; exact covered
    | upper => change next.ranges.upperRun.isSome = true; rw [ranges.2]; exact covered

def DataWork.after_service {view : CampusTCPTwoProgressGatewayState.View initial current}
    (work : DataWork initial native current view part lane)
    {item : Work.Item (Ticket input.active input.passive)} {hit : FlowNAT.Hit} {session : Admission.Session}
    {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
    {emitted : served.evidence.output = some emission}
    (value : CampusTCPTwoProgressNetwork.ServiceMove initial current item hit session actual served emission emitted)
    (next : CampusTCPTwoProgressGatewayState.View initial value.move.after)
    (preserved : (rangeAt view part).isSome = true → (rangeAt next part).isSome = true)
    (other : ∀ path : DataTicket initial native current part lane, path.ticket.id ≠ item.id) :
    DataWork initial native value.move.after next part lane := by
  have quiet : CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event = none := by
    rw [value.facts.event]; rfl
  cases work with
  | ingress path source => exact .ingress (path.after_move value.move (by rw [quiet]; simp)) (source.retain_steps value.move.retained)
  | ticket path source => exact .ticket (path.after_service value (other path)) (source.retain_steps value.move.retained)
  | link path source covered =>
    exact .link (path.after_move value.move (by rw [quiet]; simp)) (source.retain_steps value.move.retained) (preserved covered)

end Netlib.Check.CampusTCPTwoProgressPhaseNetworkState
