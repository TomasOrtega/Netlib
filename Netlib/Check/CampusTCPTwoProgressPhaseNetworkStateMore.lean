import Netlib.Check.CampusTCPTwoProgressPhaseNetworkState

namespace Netlib.Check.CampusTCPTwoProgressPhaseNetworkState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressPhaseState CampusTCPTwoProgressPaths
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressPathsReady (rangeAt)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {part : S.Part} {lane otherLane : M.Lane} {actual : Step input}
variable {core : Core initial native quantum allowance current monitor sent received}

private theorem retry_mode (active : Active core) (live : monitor.retry.phase ≠ .done) : monitor.mode = .recovery := by
  rcases active.mode with mode | mode
  · exact False.elim (live (active.originals mode).1)
  · exact mode

private theorem retry_ack (active : Active core) (live : monitor.retry.phase ≠ .done) : monitor.ack = none := by
  cases found : monitor.ack with
  | none => rfl
  | some lane => exact False.elim (live (active.serial (by rw [found]; rfl)))

private theorem retry_waiting (active : Active core) (live : monitor.retry.phase ≠ .done) : monitor.waiting = false := by
  cases waiting : monitor.waiting with
  | false => rfl
  | true => exact False.elim (live (active.waiting waiting).2)

def retry_assigned (active : Active core) (path : DataIngress initial current part monitor.retry)
    (source : SelectedOutput initial current path.output.produced) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (_current : active.retry = .active part head rest selected (.ingress path source))
    (value : N.DataAssigned core path actual) : Active value.advance.nextCore := by
  have old : monitor.retry.phase ≠ .done := by rw [path.phase]; decide
  have fresh : value.value.nextLane.phase ≠ .done := by rw [value.value.ticket.phase]; decide
  have mode := retry_mode active old
  have ackNone := retry_ack active old
  have observed := CampusTCPTwoProgressPhaseObserve.data_assigned_retry value mode ackNone (retry_waiting active old)
  have frame : Frame monitor (M.observe (config initial native quantum allowance) monitor actual) := by
    rw [observed]; exact Frame.retry monitor value.value.nextLane old fresh
  apply assemble active value.value.value.move value.advance value.value.value.endpoints
    (by rw [value.value.event]; trivial) frame
  · exact .done (frame.lowerDone.mpr (active.recovery mode).1)
  · exact .done (frame.upperDone.mpr (active.recovery mode).2)
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).retry = value.value.nextLane := by rw [observed]
    rw [lane]
    exact .active part head rest selected (.ticket value.value.ticket (CampusTCPTwoProgressPhaseSources.assigned_source source value.value))
  · unfold AckState
    rw [frame.ackNone.mpr ackNone]
    exact PUnit.unit

def retry_served (active : Active core) (path : DataTicket initial native current part monitor.retry)
    (source : SelectedOutput initial current path.output.produced) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (_current : active.retry = .active part head rest selected (.ticket path source))
    (value : N.DataServed core path actual) : Active value.advance.nextCore := by
  have old : monitor.retry.phase ≠ .done := by rw [path.phase]; decide
  have fresh : value.value.nextLane.phase ≠ .done := by rw [value.value.link.phase]; decide
  have mode := retry_mode active old
  have ackNone := retry_ack active old
  have observed := CampusTCPTwoProgressPhaseObserve.data_served_retry value mode ackNone (retry_waiting active old)
  have frame : Frame monitor (M.observe (config initial native quantum allowance) monitor actual) := by
    rw [observed]; exact Frame.retry monitor value.value.nextLane old fresh
  apply assemble active value.value.value.move value.advance value.value.value.endpoints
    (by rw [value.value.value.facts.event]; trivial) frame
  · exact .done (frame.lowerDone.mpr (active.recovery mode).1)
  · exact .done (frame.upperDone.mpr (active.recovery mode).2)
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).retry = value.value.nextLane := by rw [observed]
    rw [lane]
    exact .active part head rest selected (.link value.value.link (CampusTCPTwoProgressPhaseSources.served_source source value.value) value.covered)
  · unfold AckState
    rw [frame.ackNone.mpr ackNone]
    exact PUnit.unit

private theorem actor_ne (first second : Produced input.active input.passive)
    (data : first.actor = sender) (ack : second.actor = sender.other) : first ≠ second := by
  intro same
  have actors := data.symm.trans ((congrArg Produced.actor same).trans ack)
  cases sender <;> cases actors

private theorem pending_same (first second : Theory.PacketCustody.Item (Transit input))
    (firstMember : first ∈ current.report.final.custody.pending)
    (secondMember : second ∈ current.report.final.custody.pending) (same : first.id = second.id) : first = second := by
  obtain ⟨resolved, _⟩ := Theory.PacketCustody.resolve_completes current.report.final.custody first firstMember .dropped
  have valid := CampusTCPCustodyFacts.Report.valid current.report
  exact (resolved.item_eq valid first firstMember rfl).symm.trans (resolved.item_eq valid second secondMember same.symm)

private theorem ack_ingress_other (first : AckIngress initial current count lane)
    (second : DataIngress initial current part otherLane) : first.packetID ≠ second.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := first.toIngress.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := second.toIngress.custody_item
  have items := pending_same left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  exact actor_ne second.output.produced first.output.produced second.output.actor first.output.actor
    (congrArg CampusTCPTwoProgressLossHistory.transitSource payload).symm

private theorem ack_ingress_link_other (first : AckIngress initial current count lane)
    (second : DataLink initial current part otherLane) : first.packetID ≠ second.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := first.toIngress.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := second.toLink.custody_item
  have items := pending_same left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  cases payload

private theorem ack_ticket_other (first : AckTicket initial native current count lane)
    (second : DataTicket initial native current part otherLane) : first.ticket.id ≠ second.ticket.id := by
  intro same
  have valid := CampusTCPOrigins.Report.work_valid current.report
  obtain ⟨completed, _, identity⟩ := Theory.Outstanding.complete_item current.report.final.work first.ticket valid first.pending
  have selected := completed.item_eq valid second.ticket second.pending same.symm
  have tickets : first.ticket = second.ticket := identity.symm.trans selected
  apply actor_ne second.output.produced first.output.produced second.output.actor first.output.actor
  exact second.produced.symm.trans ((congrArg (fun item => item.value.produced) tickets.symm).trans first.produced)

private def retain_ack_assigned {path : AckIngress initial current (received.bytes lower upper).length lane}
    (value : N.AckAssigned core path actual)
    (before : OriginalLane initial native current core.live.gatewayState received part otherLane) :
    OriginalLane initial native value.value.value.move.after value.advance.nextCore.live.gatewayState received part otherLane := by
  cases before with
  | done phase => exact .done phase
  | active work missing =>
    refine .active (DataWork.after_assignment work value.value.value value.advance.nextCore.live.gatewayState ?_ ?_) missing
    · intro second
      rw [value.value.event, CampusTCPTwoProgressPathRetain.consumedPacket, path.custody]
      intro same
      exact ack_ingress_other path second (Option.some.inj same)
    · intro second
      rw [value.value.event, CampusTCPTwoProgressPathRetain.consumedPacket, path.custody]
      intro same
      exact ack_ingress_link_other path second (Option.some.inj same)

private def retain_ack_served {path : AckTicket initial native current (received.bytes lower upper).length lane}
    (value : N.AckServed core path actual)
    (before : OriginalLane initial native current core.live.gatewayState received part otherLane) :
    OriginalLane initial native value.value.value.move.after value.advance.nextCore.live.gatewayState received part otherLane := by
  cases before with
  | done phase => exact .done phase
  | active work missing =>
    refine .active (DataWork.after_service work value.value.value value.advance.nextCore.live.gatewayState ?_ ?_) missing
    · intro covered
      rw [value.gateway]
      cases part with
      | lower => change value.value.next.gatewayState.ranges.lowerRun.isSome = true; rw [value.value.lowerRun]; exact covered
      | upper => change value.value.next.gatewayState.ranges.upperRun.isSome = true; rw [value.value.upperRun]; exact covered
    · intro second
      exact (ack_ticket_other path second).symm

def ack_assigned (active : Active core) (path : AckIngress initial current (received.bytes lower upper).length lane)
    (pending : monitor.ack = some lane) (value : N.AckAssigned core path actual) : Active value.advance.nextCore := by
  have observed := CampusTCPTwoProgressPhaseObserve.ack_assigned value active.mode
    (OriginalLane.not_needSend active.lowerLane) (OriginalLane.not_needSend active.upperLane) pending
  have frame : Frame monitor (M.observe (config initial native quantum allowance) monitor actual) := by
    rw [observed]; exact Frame.ack monitor value.value.nextLane lane pending
  apply assemble active value.value.value.move value.advance value.value.value.endpoints
    (by rw [value.value.event]; trivial) frame
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).lower = monitor.lower := by rw [observed]
    rw [lane]
    exact retain_ack_assigned value active.lowerLane
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).upper = monitor.upper := by rw [observed]
    rw [lane]
    exact retain_ack_assigned value active.upperLane
  · exact .done (frame.retryDone.mpr (active.serial (by rw [pending]; rfl)))
  · have ack : (M.observe (config initial native quantum allowance) monitor actual).ack = some value.value.nextLane := by rw [observed]
    unfold AckState
    rw [ack]
    exact .ticket value.value.ticket

def ack_served (active : Active core) (path : AckTicket initial native current (received.bytes lower upper).length lane)
    (pending : monitor.ack = some lane) (value : N.AckServed core path actual) : Active value.advance.nextCore := by
  have observed := CampusTCPTwoProgressPhaseObserve.ack_served value active.mode
    (OriginalLane.not_needSend active.lowerLane) (OriginalLane.not_needSend active.upperLane) pending
  have frame : Frame monitor (M.observe (config initial native quantum allowance) monitor actual) := by
    rw [observed]; exact Frame.ack monitor value.value.nextLane lane pending
  apply assemble active value.value.value.move value.advance value.value.value.endpoints
    (by rw [value.value.value.facts.event]; trivial) frame
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).lower = monitor.lower := by rw [observed]
    rw [lane]
    exact retain_ack_served value active.lowerLane
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).upper = monitor.upper := by rw [observed]
    rw [lane]
    exact retain_ack_served value active.upperLane
  · exact .done (frame.retryDone.mpr (active.serial (by rw [pending]; rfl)))
  · have ack : (M.observe (config initial native quantum allowance) monitor actual).ack = some value.value.nextLane := by rw [observed]
    unfold AckState
    rw [ack]
    exact .link value.value.link

end Netlib.Check.CampusTCPTwoProgressPhaseNetworkState
