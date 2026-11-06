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
variable {part other : S.Part} {lane otherLane : M.Lane} {actual : Step input}
variable {core : Core initial native quantum allowance current monitor sent received}

private theorem ingress_other (first : DataIngress initial current part lane)
    (second : DataIngress initial current other otherLane) (different : part ≠ other) : first.packetID ≠ second.packetID := by
  cases part <;> cases other
  · exact False.elim (different rfl)
  · exact CampusTCPTwoProgressPathsDistinct.ingress_packet_ne first second
  · exact (CampusTCPTwoProgressPathsDistinct.ingress_packet_ne second first).symm
  · exact False.elim (different rfl)

private theorem ingress_link_other (first : DataIngress initial current part lane)
    (second : DataLink initial current other otherLane) (different : part ≠ other) : first.packetID ≠ second.packetID := by
  cases part <;> cases other
  · exact False.elim (different rfl)
  · exact CampusTCPTwoProgressPathsDistinct.ingress_link_packet_ne first second
  · exact (CampusTCPTwoProgressPathsDistinct.link_ingress_packet_ne second first).symm
  · exact False.elim (different rfl)

private theorem ticket_other (first : DataTicket initial native current part lane)
    (second : DataTicket initial native current other otherLane) (different : part ≠ other) : first.ticket.id ≠ second.ticket.id := by
  cases part <;> cases other
  · exact False.elim (different rfl)
  · exact CampusTCPTwoProgressPathsDistinct.ticket_id_ne first second
  · exact (CampusTCPTwoProgressPathsDistinct.ticket_id_ne second first).symm
  · exact False.elim (different rfl)

private def retain_assigned {path : DataIngress initial current part lane} (value : N.DataAssigned core path actual)
    (different : part ≠ other)
    (before : OriginalLane initial native current core.live.gatewayState received other otherLane) :
    OriginalLane initial native value.value.value.move.after value.advance.nextCore.live.gatewayState received other otherLane := by
  cases before with
  | done phase => exact .done phase
  | active work missing =>
    refine .active (DataWork.after_assignment work value.value.value value.advance.nextCore.live.gatewayState ?_ ?_) missing
    · intro second
      rw [value.value.event, CampusTCPTwoProgressPathRetain.consumedPacket, path.custody]
      intro same
      exact ingress_other path second different (Option.some.inj same)
    · intro second
      rw [value.value.event, CampusTCPTwoProgressPathRetain.consumedPacket, path.custody]
      intro same
      exact ingress_link_other path second different (Option.some.inj same)

private def retain_served {path : DataTicket initial native current part lane} (value : N.DataServed core path actual)
    (different : part ≠ other)
    (before : OriginalLane initial native current core.live.gatewayState received other otherLane) :
    OriginalLane initial native value.value.value.move.after value.advance.nextCore.live.gatewayState received other otherLane := by
  cases before with
  | done phase => exact .done phase
  | active work missing =>
    refine .active (DataWork.after_service work value.value.value value.advance.nextCore.live.gatewayState ?_ ?_) missing
    · intro covered
      rw [value.gateway]
      exact value.value.preserved other covered
    · intro second
      exact (ticket_other path second different).symm

private theorem lower_mode (active : Active core) (live : monitor.lower.phase ≠ .done) : monitor.mode = .originals := by
  rcases active.mode with mode | mode
  · exact mode
  · exact False.elim (live (active.recovery mode).1)

private theorem upper_mode (active : Active core) (live : monitor.upper.phase ≠ .done) : monitor.mode = .originals := by
  rcases active.mode with mode | mode
  · exact mode
  · exact False.elim (live (active.recovery mode).2)

def lower_assigned (active : Active core) (path : DataIngress initial current .lower monitor.lower)
    (source : SelectedOutput initial current path.output.produced) (missing : ¬Arrived received .lower)
    (_selected : active.lowerLane = .active (.ingress path source) missing)
    (value : N.DataAssigned core path actual) (ackNone : monitor.ack = none) : Active value.advance.nextCore := by
  have old : monitor.lower.phase ≠ .done := by rw [path.phase]; decide
  have fresh : value.value.nextLane.phase ≠ .done := by rw [value.value.ticket.phase]; decide
  have mode := lower_mode active old
  have observed := CampusTCPTwoProgressPhaseObserve.data_assigned_lower value mode
    (OriginalLane.not_needSend active.lowerLane) (OriginalLane.not_needSend active.upperLane) ackNone
  have frame : Frame monitor (M.observe (config initial native quantum allowance) monitor actual) := by
    rw [observed]; exact Frame.data_lower monitor value.value.nextLane old fresh
  apply assemble active value.value.value.move value.advance value.value.value.endpoints
    (by rw [value.value.event]; trivial) frame
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).lower = value.value.nextLane := by rw [observed]
    rw [lane]
    exact .active (.ticket value.value.ticket (CampusTCPTwoProgressPhaseSources.assigned_source source value.value)) missing
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).upper = monitor.upper := by rw [observed]
    rw [lane]
    exact retain_assigned value (by decide) active.upperLane
  · exact .done (frame.retryDone.mpr (active.originals mode).1)
  · unfold AckState
    rw [frame.ackNone.mpr ackNone]
    exact PUnit.unit

def lower_served (active : Active core) (path : DataTicket initial native current .lower monitor.lower)
    (source : SelectedOutput initial current path.output.produced) (missing : ¬Arrived received .lower)
    (_selected : active.lowerLane = .active (.ticket path source) missing)
    (value : N.DataServed core path actual) (ackNone : monitor.ack = none) : Active value.advance.nextCore := by
  have old : monitor.lower.phase ≠ .done := by rw [path.phase]; decide
  have fresh : value.value.nextLane.phase ≠ .done := by rw [value.value.link.phase]; decide
  have mode := lower_mode active old
  have observed := CampusTCPTwoProgressPhaseObserve.data_served_lower value mode
    (OriginalLane.not_needSend active.lowerLane) (OriginalLane.not_needSend active.upperLane) ackNone
  have frame : Frame monitor (M.observe (config initial native quantum allowance) monitor actual) := by
    rw [observed]; exact Frame.data_lower monitor value.value.nextLane old fresh
  apply assemble active value.value.value.move value.advance value.value.value.endpoints
    (by rw [value.value.value.facts.event]; trivial) frame
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).lower = value.value.nextLane := by rw [observed]
    rw [lane]
    exact .active (.link value.value.link (CampusTCPTwoProgressPhaseSources.served_source source value.value) value.covered) missing
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).upper = monitor.upper := by rw [observed]
    rw [lane]
    exact retain_served value (by decide) active.upperLane
  · exact .done (frame.retryDone.mpr (active.originals mode).1)
  · unfold AckState
    rw [frame.ackNone.mpr ackNone]
    exact PUnit.unit

def upper_assigned (active : Active core) (path : DataIngress initial current .upper monitor.upper)
    (source : SelectedOutput initial current path.output.produced) (missing : ¬Arrived received .upper)
    (_selected : active.upperLane = .active (.ingress path source) missing)
    (value : N.DataAssigned core path actual) (ackNone : monitor.ack = none)
    (lowerServes : CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) actual.before monitor monitor.lower) actual.event = false) :
    Active value.advance.nextCore := by
  have old : monitor.upper.phase ≠ .done := by rw [path.phase]; decide
  have fresh : value.value.nextLane.phase ≠ .done := by rw [value.value.ticket.phase]; decide
  have mode := upper_mode active old
  have observed := CampusTCPTwoProgressPhaseObserve.data_assigned_upper value mode
    (OriginalLane.not_needSend active.lowerLane) (OriginalLane.not_needSend active.upperLane) ackNone lowerServes
  have frame : Frame monitor (M.observe (config initial native quantum allowance) monitor actual) := by
    rw [observed]; exact Frame.data_upper monitor value.value.nextLane old fresh
  apply assemble active value.value.value.move value.advance value.value.value.endpoints
    (by rw [value.value.event]; trivial) frame
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).lower = monitor.lower := by rw [observed]
    rw [lane]
    exact retain_assigned value (by decide) active.lowerLane
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).upper = value.value.nextLane := by rw [observed]
    rw [lane]
    exact .active (.ticket value.value.ticket (CampusTCPTwoProgressPhaseSources.assigned_source source value.value)) missing
  · exact .done (frame.retryDone.mpr (active.originals mode).1)
  · unfold AckState
    rw [frame.ackNone.mpr ackNone]
    exact PUnit.unit

def upper_served (active : Active core) (path : DataTicket initial native current .upper monitor.upper)
    (source : SelectedOutput initial current path.output.produced) (missing : ¬Arrived received .upper)
    (_selected : active.upperLane = .active (.ticket path source) missing)
    (value : N.DataServed core path actual) (ackNone : monitor.ack = none)
    (lowerServes : CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) actual.before monitor monitor.lower) actual.event = false) :
    Active value.advance.nextCore := by
  have old : monitor.upper.phase ≠ .done := by rw [path.phase]; decide
  have fresh : value.value.nextLane.phase ≠ .done := by rw [value.value.link.phase]; decide
  have mode := upper_mode active old
  have observed := CampusTCPTwoProgressPhaseObserve.data_served_upper value mode
    (OriginalLane.not_needSend active.lowerLane) (OriginalLane.not_needSend active.upperLane) ackNone lowerServes
  have frame : Frame monitor (M.observe (config initial native quantum allowance) monitor actual) := by
    rw [observed]; exact Frame.data_upper monitor value.value.nextLane old fresh
  apply assemble active value.value.value.move value.advance value.value.value.endpoints
    (by rw [value.value.value.facts.event]; trivial) frame
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).lower = monitor.lower := by rw [observed]
    rw [lane]
    exact retain_served value (by decide) active.lowerLane
  · have lane : (M.observe (config initial native quantum allowance) monitor actual).upper = value.value.nextLane := by rw [observed]
    rw [lane]
    exact .active (.link value.value.link (CampusTCPTwoProgressPhaseSources.served_source source value.value) value.covered) missing
  · exact .done (frame.retryDone.mpr (active.originals mode).1)
  · unfold AckState
    rw [frame.ackNone.mpr ackNone]
    exact PUnit.unit

end Netlib.Check.CampusTCPTwoProgressPhaseNetworkState
