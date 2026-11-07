import Netlib.Check.CampusTCPTwoTransferAssignFrames
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase

/-!
# Forward progress through the actual ordinary assignment

The selected ingress becomes its literal assigned ticket. Unselected paths and
all actual loss causes remain in the same current task.
-/

namespace Netlib.Check.CampusTCPTwoTransferAssignProgress

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferControlState (Phase)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferWork (Work DataWork OriginalLane RetryLane AckWork AckState)
open CampusTCPTwoTransferPaths (DataIngress DataTicket AckIngress dataTicketLane ackTicketLane)
open CampusTCPTwoTransferLocatedAssign (DataAssigned RetryAssigned AckAssigned afterAssign dataAfter)
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoProgressPhaseBase (Arrived)

namespace W
export CampusTCPTwoTransferMonitor (Monitor observe)
end W
namespace M
export CampusTCPTwoProgressMonitor (Lane)
end M
namespace A
export CampusTCPTwoTransferAssignFrames (original_after assemble)
end A
namespace F
export CampusTCPTwoProgressPhaseNetworkState (Frame)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {part : CampusTCPTwoProgressSender.Part}
variable {lane : M.Lane} {actual : Step input}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private def ingress_source {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    (work : DataWork initial checks current view part lane) (path : DataIngress initial current part lane) :
    SelectedOutput initial current path.output.produced := by
  cases work with
  | ingress stored source =>
    have index : stored.output.index = path.output.index := Option.some.inj (stored.outputRef.symm.trans path.outputRef)
    have produced : stored.output.produced = path.output.produced := by
      have present := stored.output.stored
      rw [index] at present
      exact Option.some.inj (present.symm.trans path.output.stored)
    exact source.reindex produced
  | ticket stored _ _ => have impossible := stored.phase.symm.trans path.phase; cases impossible
  | link stored _ _ => have impossible := stored.phase.symm.trans path.phase; cases impossible

private theorem ingress_missing {view : CampusTCPTwoProgressGatewayAt.ViewAt initial current location}
    (work : OriginalLane initial checks current view received part lane) (path : DataIngress initial current part lane) :
    ¬Arrived received part := by
  cases work with
  | active _ missing => exact missing
  | done phase => rw [path.phase] at phase; cases phase

def active_lower (active : Active core)
    {path : DataIngress initial current .lower monitor.exchange.forward.lower} (value : DataAssigned core path actual)
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none) : Active value.next := by
  let source := ingress_source (active.lowerLane.dataWork (by rw [path.phase]; decide)) path
  have frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward := by
    rw [value.observed]
    exact CampusTCPTwoProgressPhaseNetworkState.Frame.data_lower _ _ (by rw [path.phase]; decide) (by change CampusTCPRoundMonitor.Phase.dataTicket ≠ .done; decide)
  have nextLower : (W.observe cfg monitor actual).exchange.forward.lower = dataTicketLane monitor.exchange.forward.lower value.value.ticket.id := by rw [value.observed]; rfl
  have nextUpper : (W.observe cfg monitor actual).exchange.forward.upper = monitor.exchange.forward.upper := by rw [value.observed]; rfl
  have nextRetry : (W.observe cfg monitor actual).exchange.forward.retry = monitor.exchange.forward.retry := by rw [value.observed]; rfl
  have nextAck : (W.observe cfg monitor actual).exchange.forward.ack = none := by rw [value.observed]; exact ack
  apply A.assemble active value.value value.next value.book (by rw [value.observed]; rfl) frame
  · rw [nextLower]
    refine .active (.ticket value.ticket value.assigned ?_) (ingress_missing active.lowerLane path)
    rw [value.literal]
    exact DataTicket.assignment_source path checks value.value source
  · rw [nextUpper, value.gateway]
    exact A.original_after path.toIngress value.value active.upperLane (fun other =>
      CampusTCPTwoProgressPathsDistinct.produced_ne path.output.fields other.output.fields)
  · rw [nextRetry]
    exact .done (active.originals mode).1
  · rw [nextAck]
    exact PUnit.unit
  · intro lane pending _
    have absent : (W.observe cfg monitor actual).exchange.forward.ack = none := by rw [value.observed]; exact ack
    rw [absent] at pending
    cases pending

def active_upper (active : Active core)
    {path : DataIngress initial current .upper monitor.exchange.forward.upper} (value : DataAssigned core path actual)
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none) : Active value.next := by
  let source := ingress_source (active.upperLane.dataWork (by rw [path.phase]; decide)) path
  have frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward := by
    rw [value.observed]
    exact CampusTCPTwoProgressPhaseNetworkState.Frame.data_upper _ _ (by rw [path.phase]; decide) (by change CampusTCPRoundMonitor.Phase.dataTicket ≠ .done; decide)
  have nextLower : (W.observe cfg monitor actual).exchange.forward.lower = monitor.exchange.forward.lower := by rw [value.observed]; rfl
  have nextUpper : (W.observe cfg monitor actual).exchange.forward.upper = dataTicketLane monitor.exchange.forward.upper value.value.ticket.id := by rw [value.observed]; rfl
  have nextRetry : (W.observe cfg monitor actual).exchange.forward.retry = monitor.exchange.forward.retry := by rw [value.observed]; rfl
  have nextAck : (W.observe cfg monitor actual).exchange.forward.ack = none := by rw [value.observed]; exact ack
  apply A.assemble active value.value value.next value.book (by rw [value.observed]; rfl) frame
  · rw [nextLower, value.gateway]
    exact A.original_after path.toIngress value.value active.lowerLane (fun other =>
      Ne.symm (CampusTCPTwoProgressPathsDistinct.produced_ne other.output.fields path.output.fields))
  · rw [nextUpper]
    refine .active (.ticket value.ticket value.assigned ?_) (ingress_missing active.upperLane path)
    rw [value.literal]
    exact DataTicket.assignment_source path checks value.value source
  · rw [nextRetry]
    exact .done (active.originals mode).1
  · rw [nextAck]
    exact PUnit.unit
  · intro lane pending _
    have absent : (W.observe cfg monitor actual).exchange.forward.ack = none := by rw [value.observed]; exact ack
    rw [absent] at pending
    cases pending

theorem DataAssigned.phase (value : DataAssigned core path actual) (phase : Phase current.report.final monitor.mode location)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor actual.event) :
    Phase value.value.move.after.report.final (W.observe cfg monitor actual).mode location := by
  have ordinary := (CampusTCPTwoTransferLocatedAssign.allowed_assign cfg current.report.final monitor
    (by rw [← value.value.facts.event]; exact allowed)).2.1
  rw [value.observed]
  exact phase.nonservice ordinary value.value.move (by rw [value.value.facts.event]; trivial)

def active_retry (active : Active core)
    {path : DataIngress initial current part monitor.exchange.forward.retry} (value : RetryAssigned core path actual)
    (mode : monitor.exchange.forward.mode = .recovery) (ack : monitor.exchange.forward.ack = none)
    (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) : Active value.next := by
  let work : DataWork initial checks current core.live.gatewayState part monitor.exchange.forward.retry := by
    cases active.retry with
    | active role otherHead otherRest chosen work =>
      have same : role = part := by cases chosen <;> cases selected <;> rfl
      subst role
      exact work
    | done phase => rw [path.phase] at phase; cases phase
  let source := ingress_source work path
  have frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward := by
    rw [value.observed]
    exact CampusTCPTwoProgressPhaseNetworkState.Frame.retry _ _ (by rw [path.phase]; decide)
      (by change CampusTCPRoundMonitor.Phase.dataTicket ≠ .done; decide)
  have nextLower : (W.observe cfg monitor actual).exchange.forward.lower = monitor.exchange.forward.lower := by rw [value.observed]; rfl
  have nextUpper : (W.observe cfg monitor actual).exchange.forward.upper = monitor.exchange.forward.upper := by rw [value.observed]; rfl
  have nextRetry : (W.observe cfg monitor actual).exchange.forward.retry = dataTicketLane monitor.exchange.forward.retry value.value.ticket.id := by
    rw [value.observed]; rfl
  have nextAck : (W.observe cfg monitor actual).exchange.forward.ack = none := by rw [value.observed]; exact ack
  apply A.assemble active value.value value.next value.book (by rw [value.observed]; rfl) frame
  · rw [nextLower]
    exact .done (active.recovery mode).1
  · rw [nextUpper]
    exact .done (active.recovery mode).2
  · rw [nextRetry]
    refine .active part head rest selected (.ticket value.ticket value.assigned ?_)
    rw [value.literal]
    exact DataTicket.assignment_source path checks value.value source
  · rw [nextAck]
    exact PUnit.unit
  · intro lane pending _
    rw [nextAck] at pending
    cases pending

def active_ack (active : Active core)
    {path : AckIngress initial current (received.bytes lower upper).length lane} (value : AckAssigned core path actual)
    (pending : monitor.exchange.forward.ack = some lane) : Active value.next := by
  have frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward := by
    rw [value.observed]
    exact CampusTCPTwoProgressPhaseNetworkState.Frame.ack _ _ lane pending
  have nextLower : (W.observe cfg monitor actual).exchange.forward.lower = monitor.exchange.forward.lower := by rw [value.observed]; rfl
  have nextUpper : (W.observe cfg monitor actual).exchange.forward.upper = monitor.exchange.forward.upper := by rw [value.observed]; rfl
  have nextRetry : (W.observe cfg monitor actual).exchange.forward.retry = monitor.exchange.forward.retry := by rw [value.observed]; rfl
  have nextAck : (W.observe cfg monitor actual).exchange.forward.ack = some (ackTicketLane lane value.value.ticket.id) := by
    rw [value.observed]; rfl
  have different : ∀ part otherLane (other : DataIngress initial current part otherLane),
      path.output.produced ≠ other.output.produced := by
    intro part otherLane other same
    have actors := congrArg (fun produced => produced.actor) same
    rw [path.output.actor, other.output.actor] at actors
    cases sender <;> cases actors
  apply A.assemble active value.value value.next value.book (by rw [value.observed]; rfl) frame
  · rw [nextLower, value.gateway]
    exact A.original_after path.toIngress value.value active.lowerLane (different .lower _)
  · rw [nextUpper, value.gateway]
    exact A.original_after path.toIngress value.value active.upperLane (different .upper _)
  · rw [nextRetry]
    exact .done (active.serial (by rw [pending]; rfl))
  · rw [nextAck]
    exact .ticket value.ticket value.assigned
  · intro lane present phase
    have same := Option.some.inj (nextAck.symm.trans present)
    rw [← same] at phase
    cases phase

theorem RetryAssigned.phase (value : RetryAssigned core path actual) (phase : Phase current.report.final monitor.mode location)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor actual.event) :
    Phase value.value.move.after.report.final (W.observe cfg monitor actual).mode location := by
  have ordinary := (CampusTCPTwoTransferLocatedAssign.allowed_assign cfg current.report.final monitor
    (by rw [← value.value.facts.event]; exact allowed)).2.1
  rw [value.observed]
  exact phase.nonservice ordinary value.value.move (by rw [value.value.facts.event]; trivial)

theorem AckAssigned.phase (value : AckAssigned core path actual) (phase : Phase current.report.final monitor.mode location)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor actual.event) :
    Phase value.value.move.after.report.final (W.observe cfg monitor actual).mode location := by
  have ordinary := (CampusTCPTwoTransferLocatedAssign.allowed_assign cfg current.report.final monitor
    (by rw [← value.value.facts.event]; exact allowed)).2.1
  rw [value.observed]
  exact phase.nonservice ordinary value.value.move (by rw [value.value.facts.event]; trivial)

end Netlib.Check.CampusTCPTwoTransferAssignProgress
