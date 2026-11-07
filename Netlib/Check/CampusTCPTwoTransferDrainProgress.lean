import Netlib.Check.CampusTCPTwoTransferLocatedDrain
import Netlib.Check.CampusTCPTwoTransferPhaseState
import Netlib.Check.CampusTCPTwoTransferControlState
import Netlib.Check.CampusTCPTwoTransferScope

/-!
# Forward phase progress through the actual primary drain

The selected ticket becomes its actual serviced link.
The other original is resolved, and pending ACK work keeps its identity.
-/

namespace Netlib.Check.CampusTCPTwoTransferDrainProgress

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferWork (Work DataWork OriginalLane RetryLane AckWork AckState)
open CampusTCPTwoTransferPhaseState (Active Debt)
open CampusTCPTwoTransferPaths (DataTicket)
open CampusTCPTwoTransferLocatedDrain (Drained forwardAfter)

namespace W
export CampusTCPTwoTransferMonitor (Monitor observe drainTicket)
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

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {part role : S.Part} {lane : M.Lane} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem ack_ticket_different (data : DataTicket initial checks current part lane)
    (ack : CampusTCPTwoTransferPaths.AckTicket initial checks current count other) : ack.ticket.id ≠ data.ticket.id := by
  intro sameID
  obtain ⟨completed, _, selected⟩ := data.completes
  have same := selected.symm.trans
    (completed.item_eq (CampusTCPOrigins.Report.work_valid current.report) ack.ticket ack.pending sameID)
  have dataActor : data.ticket.value.produced.actor = sender := by
    rw [data.toTicketPath.produced]
    exact data.output.actor
  have ackActor : ack.ticket.value.produced.actor = sender.other := by
    rw [ack.toTicketPath.produced]
    exact ack.output.actor
  have impossible := dataActor.symm.trans ((congrArg (fun item => item.value.produced.actor) same).trans ackActor)
  cases sender <;> cases impossible

private def ack_after
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    {path : DataTicket initial checks current part lane} (drained : Drained core path actual)
    (work : AckWork checks core.live ackLane) : AckWork checks drained.next.live ackLane := by
  cases work with
  | pending phase queue =>
    exact .pending phase (by rw [drained.receiver_reaction]; exact queue)
  | ingress path =>
    exact .ingress (path.after_move drained.value.value.move (by
      simp only [drained.value.value.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket, ne_eq,
        reduceCtorEq, not_false_eq_true]))
  | ticket path selected =>
    exact .ticket (path.after_service drained.value.value (ack_ticket_different _ path)) selected
  | link path =>
    exact .link (path.after_move drained.value.value.move (by
      simp only [drained.value.value.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket, ne_eq,
        reduceCtorEq, not_false_eq_true]))

private def ack_state_after
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    {path : DataTicket initial checks current part lane} (drained : Drained core path actual)
    (work : AckState checks core.live monitor.exchange.forward.ack) :
    AckState checks drained.next.live (W.observe cfg monitor actual).exchange.forward.ack := by
  rw [drained.ack]
  cases selected : monitor.exchange.forward.ack with
  | none => exact PUnit.unit
  | some ackLane =>
    exact ack_after drained (by simpa only [AckState, selected] using work)

private def debt_lower
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    {path : DataTicket initial checks current .lower monitor.exchange.forward.lower} (drained : Drained core path actual)
    (upperDone : monitor.exchange.forward.upper.phase = .done)
    (retryDone : monitor.exchange.forward.retry.phase = .done) (debt : Debt core role) : Debt drained.next role := by
  cases debt with
  | cause position chosen => exact .cause position (by rw [drained.book]; exact chosen)
  | lower same work =>
    subst role
    exact .lower rfl (by rw [drained.observed]; exact drained.work.work)
  | upper _ work => exact False.elim (work.not_done upperDone)
  | retry work => exact False.elim (work.not_done retryDone)
  | ack ackLane pending work covered =>
    exact .ack ackLane (by rw [drained.ack]; exact pending) (ack_after drained work) covered

private def debt_upper
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    {path : DataTicket initial checks current .upper monitor.exchange.forward.upper} (drained : Drained core path actual)
    (lowerDone : monitor.exchange.forward.lower.phase = .done)
    (retryDone : monitor.exchange.forward.retry.phase = .done) (debt : Debt core role) : Debt drained.next role := by
  cases debt with
  | cause position chosen => exact .cause position (by rw [drained.book]; exact chosen)
  | lower _ work => exact False.elim (work.not_done lowerDone)
  | upper same work =>
    subst role
    exact .upper rfl (by rw [drained.observed]; exact drained.work.work)
  | retry work => exact False.elim (work.not_done retryDone)
  | ack ackLane pending work covered =>
    exact .ack ackLane (by rw [drained.ack]; exact pending) (ack_after drained work) covered

def active_lower
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (active : Active core) {path : DataTicket initial checks current .lower monitor.exchange.forward.lower}
    (drained : Drained core path actual) (selected : path.assignedGateway = .primary)
    (mode : monitor.exchange.forward.mode = .originals) (upperDone : monitor.exchange.forward.upper.phase = .done) : Active drained.next := by
  have original := active.originals mode
  have nextLower : (W.observe cfg monitor actual).exchange.forward.lower =
      CampusTCPTwoTransferDrainObserve.linkLane monitor.exchange.forward.lower
        current.report.final.services.length drained.paths.linked.packetID := by rw [drained.observed]; rfl
  have nextUpper : (W.observe cfg monitor actual).exchange.forward.upper = monitor.exchange.forward.upper := by
    rw [drained.observed]; rfl
  have nextRetry : (W.observe cfg monitor actual).exchange.forward.retry = monitor.exchange.forward.retry := by
    rw [drained.observed]; rfl
  have nextMode : (W.observe cfg monitor actual).exchange.forward.mode = monitor.exchange.forward.mode := by
    rw [drained.observed]; rfl
  have missing : ¬CampusTCPTwoProgressPhaseBase.Arrived received .lower := by
    cases active.lowerLane with
    | active _ missing => exact missing
    | done phase => rw [path.phase] at phase; cases phase
  have acknowledged := CampusTCPTwoTransferServiceFrames.data_acknowledged core.live.gatewayState
    drained.value.value (path.ticket_gateway.trans selected) drained.value.next
  refine {
    exchange := by rw [drained.observed]; exact active.exchange
    mode := by rw [drained.observed]; exact Or.inl mode
    preparing := active.preparing
    nonempty := active.nonempty
    lowerLane := by rw [nextLower]; exact .active drained.work missing
    upperLane := by rw [nextUpper]; exact .done upperDone
    retry := by rw [nextRetry]; exact .done original.1
    ack := ack_state_after drained active.ack
    originals := by rw [drained.observed]; intro _; exact original
    recovery := by rw [nextMode, mode]; intro impossible; cases impossible
    recoveryHead := by rw [nextMode, mode]; intro impossible; cases impossible
    serial := by rw [drained.observed]; exact active.serial
    ackNonempty := by rw [drained.observed]; exact active.ackNonempty
    ackGateway := ?_
    waiting := by rw [drained.observed]; exact active.waiting
    runnable := by rw [nextMode, mode]; intro impossible; cases impossible
    originalOpen := by rw [drained.observed]; intro _ _ impossible; cases impossible.1
    debt := fun role head rest selected => ?_
    upperMissing := by rw [nextUpper, drained.book]; exact active.upperMissing
    zeroAck := by rw [drained.ack, drained.sender_recovery]; exact active.zeroAck
    sources := (CampusTCPTwoTransferSources.Frame.service drained.value.value).receipts active.sources }
  · intro ackLane pending phase
    rw [drained.gateway, acknowledged]
    exact active.ackGateway ackLane (drained.ack ▸ pending) phase
  · obtain ⟨debt⟩ := active.debt role head rest selected
    exact ⟨debt_lower drained upperDone original.1 debt⟩

def active_upper
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (active : Active core) {path : DataTicket initial checks current .upper monitor.exchange.forward.upper}
    (drained : Drained core path actual) (selected : path.assignedGateway = .primary)
    (mode : monitor.exchange.forward.mode = .originals) (lowerDone : monitor.exchange.forward.lower.phase = .done) : Active drained.next := by
  have original := active.originals mode
  have nextSelected : (W.observe cfg monitor actual).exchange.forward.upper =
      CampusTCPTwoTransferDrainObserve.linkLane monitor.exchange.forward.upper
        current.report.final.services.length drained.paths.linked.packetID := by rw [drained.observed]; rfl
  have nextOther : (W.observe cfg monitor actual).exchange.forward.lower = monitor.exchange.forward.lower := by
    rw [drained.observed]; rfl
  have nextRetry : (W.observe cfg monitor actual).exchange.forward.retry = monitor.exchange.forward.retry := by
    rw [drained.observed]; rfl
  have nextMode : (W.observe cfg monitor actual).exchange.forward.mode = monitor.exchange.forward.mode := by
    rw [drained.observed]; rfl
  have missing : ¬CampusTCPTwoProgressPhaseBase.Arrived received .upper := by
    cases active.upperLane with
    | active _ missing => exact missing
    | done phase => rw [path.phase] at phase; cases phase
  have acknowledged := CampusTCPTwoTransferServiceFrames.data_acknowledged core.live.gatewayState
    drained.value.value (path.ticket_gateway.trans selected) drained.value.next
  refine {
    exchange := by rw [drained.observed]; exact active.exchange
    mode := by rw [drained.observed]; exact Or.inl mode
    preparing := active.preparing
    nonempty := active.nonempty
    upperLane := by rw [nextSelected]; exact .active drained.work missing
    lowerLane := by rw [nextOther]; exact .done lowerDone
    retry := by rw [nextRetry]; exact .done original.1
    ack := ack_state_after drained active.ack
    originals := by rw [drained.observed]; intro _; exact original
    recovery := by rw [nextMode, mode]; intro impossible; cases impossible
    recoveryHead := by rw [nextMode, mode]; intro impossible; cases impossible
    serial := by rw [drained.observed]; exact active.serial
    ackNonempty := by rw [drained.observed]; exact active.ackNonempty
    ackGateway := ?_
    waiting := by rw [drained.observed]; exact active.waiting
    runnable := by rw [nextMode, mode]; intro impossible; cases impossible
    originalOpen := by rw [drained.observed]; intro _ _ impossible; cases impossible.2
    debt := fun role head rest selected => ?_
    upperMissing := by
      intro _ _ done
      rw [nextSelected] at done
      cases done
    zeroAck := by rw [drained.ack, drained.sender_recovery]; exact active.zeroAck
    sources := (CampusTCPTwoTransferSources.Frame.service drained.value.value).receipts active.sources }
  · intro ackLane pending phase
    rw [drained.gateway, acknowledged]
    exact active.ackGateway ackLane (drained.ack ▸ pending) phase
  · obtain ⟨debt⟩ := active.debt role head rest selected
    exact ⟨debt_upper drained lowerDone original.1 debt⟩

def laneAt (monitor : CampusTCPTwoProgressMonitor.Monitor) : S.Part → M.Lane
  | .lower => monitor.lower
  | .upper => monitor.upper

structure Advanced
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received)
    (ticket : Nat) (actual : Step input) where
  part : S.Part
  path : DataTicket initial checks current part (laneAt monitor.exchange.forward part)
  ticketEq : path.ticket.id = ticket
  selected : path.assignedGateway = .primary
  value : Drained core path actual
  active : Active value.next
  phase : CampusTCPTwoTransferControlState.Phase value.value.value.move.after.report.final
    (W.observe cfg monitor actual).mode .primary

private theorem capture_source
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode .primary)
    (drain : W.drainTicket current.report.final monitor = some ticket) :
    CampusTCPTwoTransferControlState.Source current.report.final true := by
  rw [CampusTCPTwoTransferDrainObserve.drain_mode drain] at phase
  cases phase with
  | capture source => exact source

private theorem phase_after
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    {path : DataTicket initial checks current part lane}
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode .primary)
    (drain : W.drainTicket current.report.final monitor = some path.ticket.id)
    (selected : path.assignedGateway = .primary) (value : Drained core path actual) :
    CampusTCPTwoTransferControlState.Phase value.value.value.move.after.report.final
      (W.observe cfg monitor actual).mode .primary := by
  have nextMode : (W.observe cfg monitor actual).mode = monitor.mode := by rw [value.observed]; rfl
  rw [nextMode, CampusTCPTwoTransferDrainObserve.drain_mode drain]
  exact .capture ((capture_source phase drain).primary_service value.value.value
    (path.ticket_gateway.trans selected))

theorem drain_at
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (active : Active core)
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode .primary)
    (mode : monitor.exchange.forward.mode = .originals)
    (resolved : monitor.exchange.forward.lower.phase = .done ∨ monitor.exchange.forward.upper.phase = .done)
    (drain : W.drainTicket current.report.final monitor = some ticket) :
    ∃ actual, Nonempty (Advanced core ticket actual) := by
  have source := capture_source phase drain
  have ready : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final .primary :=
    ⟨fun _ => ⟨source.unsealed, source.unfenced⟩, by intro impossible; cases impossible⟩
  have healthy : monitor.exchange.forward.mode ≠ .invalid := by rw [mode]; decide
  rcases core.primaryQueue.drain_selected drain with lowerTicket | upperTicket
  · have upperDone : monitor.exchange.forward.upper.phase = .done :=
      resolved.resolve_left (by rw [lowerTicket.1]; decide)
    cases active.lowerLane with
    | done done => rw [lowerTicket.1] at done; cases done
    | active work _ =>
      cases work with
      | ingress path _ => have bad := path.phase; rw [lowerTicket.1] at bad; cases bad
      | link path _ _ => have bad := path.phase; rw [lowerTicket.1] at bad; cases bad
      | ticket path selected writer =>
        have ticketEq : path.ticket.id = ticket := Option.some.inj (path.ticketRef.symm.trans lowerTicket.2)
        have selectedDrain : W.drainTicket current.report.final monitor = some path.ticket.id := by rw [ticketEq]; exact drain
        obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoTransferLocatedDrain.drain_lower_at core path selected writer selectedDrain ready healthy
        exact ⟨actual, ⟨⟨.lower, path, ticketEq, selected, value,
          active_lower active value selected mode upperDone, phase_after phase selectedDrain selected value⟩⟩⟩
  · have lowerDone : monitor.exchange.forward.lower.phase = .done :=
      resolved.resolve_right (by rw [upperTicket.1]; decide)
    cases active.upperLane with
    | done done => rw [upperTicket.1] at done; cases done
    | active work _ =>
      cases work with
      | ingress path _ => have bad := path.phase; rw [upperTicket.1] at bad; cases bad
      | link path _ _ => have bad := path.phase; rw [upperTicket.1] at bad; cases bad
      | ticket path selected writer =>
        have ticketEq : path.ticket.id = ticket := Option.some.inj (path.ticketRef.symm.trans upperTicket.2)
        have selectedDrain : W.drainTicket current.report.final monitor = some path.ticket.id := by rw [ticketEq]; exact drain
        have other : ¬(monitor.exchange.forward.lower.phase = .dataTicket ∧
            monitor.exchange.forward.lower.refs.dataTicket = some path.ticket.id) := by
          rw [lowerDone]
          simp
        obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoTransferLocatedDrain.drain_upper_at core path selected writer selectedDrain ready other healthy
        exact ⟨actual, ⟨⟨.upper, path, ticketEq, selected, value,
          active_upper active value selected mode lowerDone, phase_after phase selectedDrain selected value⟩⟩⟩

theorem drain_step
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (active : Active core)
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode .primary)
    (mode : monitor.exchange.forward.mode = .originals)
    (resolved : monitor.exchange.forward.lower.phase = .done ∨ monitor.exchange.forward.upper.phase = .done)
    (drain : W.drainTicket current.report.final monitor = some ticket)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .serve ticket none) :
    Nonempty (Advanced core ticket actual) := by
  obtain ⟨chosen, ⟨value⟩⟩ := drain_at active phase mode resolved drain
  have same : chosen = actual := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
    (value.value.value.value.move.beforeEq.trans before.symm)
    (by rw [value.value.value.value.facts.event, value.ticketEq, event])
  exact same ▸ ⟨value⟩

theorem scope_drain_at
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (active : Active core)
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode .primary)
    (scope : CampusTCPTwoTransferScope.TransferScope monitor)
    (drain : W.drainTicket current.report.final monitor = some ticket) :
    ∃ actual, Nonempty (Advanced core ticket actual) :=
  drain_at active phase scope.mode scope.resolved drain

theorem Advanced.scope
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (value : Advanced core ticket actual) (scope : CampusTCPTwoTransferScope.TransferScope monitor) :
    CampusTCPTwoTransferScope.TransferScope (W.observe cfg monitor actual) := by
  rcases value with ⟨part, path, ticketEq, selected, drained, active, phase⟩
  cases part with
  | lower => exact scope.lower_drain drained
  | upper => exact scope.upper_drain drained

theorem Advanced.primary_empty
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (value : Advanced core ticket actual) (scope : CampusTCPTwoTransferScope.TransferScope monitor)
    (drain : W.drainTicket current.report.final monitor = some ticket) :
    value.value.value.value.move.after.report.final.outstanding .primary = 0 := by
  have one := scope.selected_primary_count core drain
  let service := value.value.value.value
  have primary := (congrArg (fun item => item.value.gateway) service.facts.ticket).trans
    (value.path.ticket_gateway.trans value.selected)
  have counted := CampusTCPPrimaryDrain.serve_primary_count actual value.path.ticket.id
    service.facts.event _ service.facts.recorded primary
  rw [service.move.beforeEq, ← service.move.final] at counted
  change value.value.value.value.move.after.report.final.outstanding .primary + 1 =
    current.report.final.outstanding .primary at counted
  rw [one] at counted
  exact Nat.add_right_cancel (counted.trans (Nat.zero_add 1).symm)

theorem Advanced.allowed
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (value : Advanced core ticket actual) (drain : W.drainTicket current.report.final monitor = some ticket) :
    CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor actual.event := by
  apply CampusTCPTwoTransferDrainObserve.drain_allowed value.value.value.value
  rw [value.ticketEq]
  exact drain

end Netlib.Check.CampusTCPTwoTransferDrainProgress
