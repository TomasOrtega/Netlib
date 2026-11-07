import Netlib.Check.CampusTCPTwoProgressPathRetain
import Netlib.Check.CampusTCPTwoProgressReadWriter
import Netlib.Check.CampusTCPTwoTransferNative
import Netlib.Check.CampusTCPTwoTransferNetwork
import Netlib.Check.CampusTCPTransferEnabled

/-!
# Packet tickets retain their actual assigned gateway

Route changes do not retag stored tickets.
Clock and control frames retain the same output and selected writer evidence.
-/

namespace Netlib.Check.CampusTCPTwoTransferPaths

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks)

namespace P
export CampusTCPTwoProgressPaths
  (Output Ingress TicketPath Link DataOutput AckOutput DataIngress DataLink AckIngress AckLink)
end P
namespace M
export CampusTCPTwoProgressMonitor (Config Lane)
end M
namespace N
export CampusTCPTwoTransferNetwork (Assignment Service)
end N
namespace H
export CampusTCPTwoProgressPathRetain (QuietWork)
end H
namespace W
export CampusTCPTwoProgressReadWriter (SelectedOutput)
end W

export CampusTCPTwoProgressPaths
  (Output Ingress Link DataOutput AckOutput DataIngress DataLink AckIngress AckLink)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry}
variable {part : CampusTCPTwoProgressSender.Part} {lane otherLane : M.Lane} {count : Nat}
variable {actual : Step input}

structure DataTicket (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (current : Cut input complete)
    (part : CampusTCPTwoProgressSender.Part) (lane : M.Lane) where
  assignedGateway : Gateway
  toTicketPath : P.TicketPath current sender
    (CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper))
    assignedGateway (checks.ingress assignedGateway sender)
  phase : lane.phase = .dataTicket
  outputRef : lane.refs.dataOutput = some toTicketPath.output.index
  ticketRef : lane.refs.dataTicket = some toTicketPath.ticket.id

structure AckTicket (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (current : Cut input complete)
    (count : Nat) (lane : M.Lane) where
  assignedGateway : Gateway
  toTicketPath : P.TicketPath current sender.other (CampusTCPTwoProgressWire.AckFields initial count)
    assignedGateway (checks.ingress assignedGateway sender.other)
  phase : lane.phase = .ackTicket
  outputRef : lane.refs.ackOutput = some toTicketPath.output.index
  ticketRef : lane.refs.ackTicket = some toTicketPath.ticket.id

abbrev DataTicket.output (path : DataTicket initial checks current part lane) := path.toTicketPath.output
abbrev DataTicket.ticket (path : DataTicket initial checks current part lane) := path.toTicketPath.ticket
abbrev AckTicket.output (path : AckTicket initial checks current count lane) := path.toTicketPath.output
abbrev AckTicket.ticket (path : AckTicket initial checks current count lane) := path.toTicketPath.ticket

def dataTicketLane (lane : M.Lane) (ticket : Nat) : M.Lane :=
  ⟨.dataTicket, { lane.refs with dataTicket := some ticket }⟩

def ackTicketLane (lane : M.Lane) (ticket : Nat) : M.Lane :=
  ⟨.ackTicket, { lane.refs with ackTicket := some ticket }⟩

def dataIngress_control (path : P.DataIngress initial current part lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    P.DataIngress initial value.move.after part lane :=
  path.reframe (by rw [value.frame.outputs]; exact path.output.stored)
    (by rw [value.frame.custody]; exact path.custody)

def ackIngress_control (path : P.AckIngress initial current count lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    P.AckIngress initial value.move.after count lane :=
  path.reframe (by rw [value.frame.outputs]; exact path.output.stored)
    (by rw [value.frame.custody]; exact path.custody)

def dataLink_control (path : P.DataLink initial current part lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    P.DataLink initial value.move.after part lane :=
  path.reframe (by rw [value.frame.services]; exact path.stored)
    (by rw [value.frame.custody]; exact path.custody)

def ackLink_control (path : P.AckLink initial current count lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    P.AckLink initial value.move.after count lane :=
  path.reframe (by rw [value.frame.services]; exact path.stored)
    (by rw [value.frame.custody]; exact path.custody)

def dataIngress_control_source (path : P.DataIngress initial current part lane)
    (value : CampusTCPTransferEnabled.Control current event actual)
    (source : W.SelectedOutput initial current path.output.produced) :
    W.SelectedOutput initial value.move.after (dataIngress_control path value).output.produced :=
  source.retain_steps value.move.retained

def dataLink_control_source (path : P.DataLink initial current part lane)
    (value : CampusTCPTransferEnabled.Control current event actual)
    (source : W.SelectedOutput initial current path.served.ticket.value.produced) :
    W.SelectedOutput initial value.move.after (dataLink_control path value).served.ticket.value.produced :=
  source.retain_steps value.move.retained

theorem DataTicket.pending (path : DataTicket initial checks current part lane) : path.ticket ∈ current.report.final.work.pending :=
  path.toTicketPath.pending

theorem DataTicket.ticket_gateway (path : DataTicket initial checks current part lane) : path.ticket.value.gateway = path.assignedGateway :=
  path.toTicketPath.gateway

theorem DataTicket.ingress (path : DataTicket initial checks current part lane) :
    path.ticket.value.ingress = checks.ingress path.assignedGateway sender := path.toTicketPath.ingress

theorem DataTicket.action (path : DataTicket initial checks current part lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.serve path.ticket.id) := by
  simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.ticketRef]
  exact path.toTicketPath.action

theorem DataTicket.completes (path : DataTicket initial checks current part lane) :
    ∃ completed, Work.complete current.report.final.work path.ticket.id = .ok completed ∧ completed.item = path.ticket :=
  path.toTicketPath.completes

theorem DataTicket.packet_at (path : DataTicket initial checks current part lane) : CampusTCPGapProgressMonitor.packetAt lane.toGap = none := by
  simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase]

theorem DataTicket.exposed_packet (path : DataTicket initial checks current part lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = none := by
  simp only [CampusTCPTwoProgressMonitor.exposedPacket, path.action config, bind, Option.bind]
  exact path.packet_at

def DataTicket.ofOld (path : CampusTCPTwoProgressPaths.DataTicket initial native current part lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (ingress : checks.ingress gateway sender = native.ingress sender) :
    DataTicket initial checks current part lane where
  assignedGateway := gateway
  toTicketPath := ⟨path.output, path.ticket, path.pending, path.outputIndex, path.produced,
    path.gateway, path.ingress.trans ingress.symm⟩
  phase := path.phase
  outputRef := path.outputRef
  ticketRef := path.ticketRef

def DataTicket.reframe (path : DataTicket initial checks current part lane)
    (stored : next.report.final.outputs[path.output.index]? = some path.output.produced)
    (pending : path.ticket ∈ next.report.final.work.pending) : DataTicket initial checks next part lane where
  assignedGateway := path.assignedGateway
  toTicketPath := path.toTicketPath.reframe stored pending
  phase := path.phase
  outputRef := path.outputRef
  ticketRef := path.ticketRef

def DataTicket.retain (path : DataTicket initial checks current part lane)
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (pending : path.ticket ∈ next.report.final.work.pending) : DataTicket initial checks next part lane where
  assignedGateway := path.assignedGateway
  toTicketPath := path.toTicketPath.retain outputs pending
  phase := path.phase
  outputRef := path.outputRef
  ticketRef := path.ticketRef

def DataTicket.clock (path : DataTicket initial checks current part lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : DataTicket initial checks next part lane where
  assignedGateway := path.assignedGateway
  toTicketPath := path.toTicketPath.clock placement
  phase := path.phase
  outputRef := path.outputRef
  ticketRef := path.ticketRef

def DataTicket.reindex (path : DataTicket initial checks current part lane) (same : otherLane = lane) :
    DataTicket initial checks current part otherLane where
  assignedGateway := path.assignedGateway
  toTicketPath := path.toTicketPath
  phase := by rw [same]; exact path.phase
  outputRef := by rw [same]; exact path.outputRef
  ticketRef := by rw [same]; exact path.ticketRef

def DataTicket.after_quiet (path : DataTicket initial checks current part lane) (move : Move current actual)
    (quiet : H.QuietWork actual.event) : DataTicket initial checks move.after part lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs move) (by
    rw [move.final, CampusTCPTwoProgressPathRetain.Step.work_quiet actual quiet, move.beforeEq]
    exact path.pending)

def DataTicket.control (path : DataTicket initial checks current part lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    DataTicket initial checks value.move.after part lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs value.move) (by
    rw [value.frame.work]
    exact path.pending)

def DataTicket.after_assignment (path : DataTicket initial checks current part lane)
    (assigned : N.Assignment current outputIndex selectedIngress produced actual) :
    DataTicket initial checks assigned.move.after part lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs assigned.move) (by
    rw [assigned.move.final, assigned.facts.work]
    exact CampusTCPTwoProgressPathRetain.enqueue_other _ _ path.ticket path.pending)

def DataTicket.after_service (path : DataTicket initial checks current part lane)
    (service : N.Service current item hit session actual served emission emitted)
    (different : path.ticket.id ≠ item.id) : DataTicket initial checks service.move.after part lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs service.move) (by
    obtain ⟨completed, _, _, work⟩ := service.facts.completed
    rw [service.move.final, work]
    exact CampusTCPTwoProgressPathRetain.completed_other completed path.ticket
      (by rw [service.move.beforeEq]; exact path.pending) different)

@[simp] theorem DataTicket.clock_ticket (path : DataTicket initial checks current part lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    (path.clock placement).ticket = path.ticket := rfl

@[simp] theorem DataTicket.clock_assignedGateway (path : DataTicket initial checks current part lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    (path.clock placement).assignedGateway = path.assignedGateway := rfl

@[simp] theorem DataTicket.control_ticket (path : DataTicket initial checks current part lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    (path.control value).ticket = path.ticket := rfl

@[simp] theorem DataTicket.control_assignedGateway (path : DataTicket initial checks current part lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    (path.control value).assignedGateway = path.assignedGateway := rfl

def DataTicket.clock_source (path : DataTicket initial checks current part lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (source : W.SelectedOutput initial current path.output.produced) :
    W.SelectedOutput initial next (path.clock placement).output.produced := source.clock placement

def DataTicket.control_source (path : DataTicket initial checks current part lane)
    (value : CampusTCPTransferEnabled.Control current event actual)
    (source : W.SelectedOutput initial current path.output.produced) :
    W.SelectedOutput initial value.move.after (path.control value).output.produced := source.retain_steps value.move.retained

def DataTicket.ofAssignment (path : P.DataIngress initial current part lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual) :
    DataTicket initial checks value.move.after part (dataTicketLane lane value.ticket.id) where
  assignedGateway := current.report.final.owner sender
  toTicketPath := {
    output := path.output.after_move value.move
    ticket := value.ticket
    pending := value.pending
    outputIndex := rfl
    produced := rfl
    gateway := by change current.report.final.owner path.output.produced.actor = _; rw [path.output.actor]
    ingress := rfl }
  phase := rfl
  outputRef := path.outputRef
  ticketRef := rfl

theorem DataTicket.assignment_observed (path : P.DataIngress initial current part lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual) :
    CampusTCPTwoProgressMonitor.Lane.ofGap
      (CampusTCPGapProgressMonitor.observeAssignment lane.toGap actual true .dataTicket) =
        dataTicketLane lane value.ticket.id := by
  simp only [CampusTCPGapProgressMonitor.observeAssignment,
    CampusTCPRoundMonitorFacts.AssignmentFacts.find_new value.facts,
    CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap]
  rfl

@[simp] theorem DataTicket.ofAssignment_ticket (path : P.DataIngress initial current part lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual) :
    (ofAssignment path checks value).ticket = value.ticket := rfl

@[simp] theorem DataTicket.ofAssignment_gateway (path : P.DataIngress initial current part lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual) :
    (ofAssignment path checks value).assignedGateway = current.report.final.owner sender := rfl

@[simp] theorem DataTicket.ofAssignment_ticketID (path : P.DataIngress initial current part lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual) :
    (ofAssignment path checks value).ticket.id = current.report.final.work.nextID := rfl

@[simp] theorem DataTicket.ofAssignment_produced (path : P.DataIngress initial current part lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual) :
    (ofAssignment path checks value).output.produced = path.output.produced := rfl

def DataTicket.assignment_source (path : P.DataIngress initial current part lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual)
    (source : W.SelectedOutput initial current path.output.produced) :
    W.SelectedOutput initial value.move.after (ofAssignment path checks value).output.produced :=
  source.retain_steps value.move.retained

theorem AckTicket.pending (path : AckTicket initial checks current count lane) : path.ticket ∈ current.report.final.work.pending :=
  path.toTicketPath.pending

theorem AckTicket.ticket_gateway (path : AckTicket initial checks current count lane) : path.ticket.value.gateway = path.assignedGateway :=
  path.toTicketPath.gateway

theorem AckTicket.ingress (path : AckTicket initial checks current count lane) :
    path.ticket.value.ingress = checks.ingress path.assignedGateway sender.other := path.toTicketPath.ingress

theorem AckTicket.action (path : AckTicket initial checks current count lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.serve path.ticket.id) := by
  simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.ticketRef]
  exact path.toTicketPath.action

theorem AckTicket.completes (path : AckTicket initial checks current count lane) :
    ∃ completed, Work.complete current.report.final.work path.ticket.id = .ok completed ∧ completed.item = path.ticket :=
  path.toTicketPath.completes

theorem AckTicket.packet_at (path : AckTicket initial checks current count lane) : CampusTCPGapProgressMonitor.packetAt lane.toGap = none := by
  simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase]

theorem AckTicket.exposed_packet (path : AckTicket initial checks current count lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = none := by
  simp only [CampusTCPTwoProgressMonitor.exposedPacket, path.action config, bind, Option.bind]
  exact path.packet_at

def AckTicket.ofOld (path : CampusTCPTwoProgressPaths.AckTicket initial native current count lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (ingress : checks.ingress gateway sender.other = native.ingress sender.other) :
    AckTicket initial checks current count lane where
  assignedGateway := gateway
  toTicketPath := ⟨path.output, path.ticket, path.pending, path.outputIndex, path.produced,
    path.gateway, path.ingress.trans ingress.symm⟩
  phase := path.phase
  outputRef := path.outputRef
  ticketRef := path.ticketRef

def AckTicket.reframe (path : AckTicket initial checks current count lane)
    (stored : next.report.final.outputs[path.output.index]? = some path.output.produced)
    (pending : path.ticket ∈ next.report.final.work.pending) : AckTicket initial checks next count lane where
  assignedGateway := path.assignedGateway
  toTicketPath := path.toTicketPath.reframe stored pending
  phase := path.phase
  outputRef := path.outputRef
  ticketRef := path.ticketRef

def AckTicket.retain (path : AckTicket initial checks current count lane)
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (pending : path.ticket ∈ next.report.final.work.pending) : AckTicket initial checks next count lane where
  assignedGateway := path.assignedGateway
  toTicketPath := path.toTicketPath.retain outputs pending
  phase := path.phase
  outputRef := path.outputRef
  ticketRef := path.ticketRef

def AckTicket.clock (path : AckTicket initial checks current count lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : AckTicket initial checks next count lane where
  assignedGateway := path.assignedGateway
  toTicketPath := path.toTicketPath.clock placement
  phase := path.phase
  outputRef := path.outputRef
  ticketRef := path.ticketRef

def AckTicket.reindex (path : AckTicket initial checks current count lane) (same : otherLane = lane) :
    AckTicket initial checks current count otherLane where
  assignedGateway := path.assignedGateway
  toTicketPath := path.toTicketPath
  phase := by rw [same]; exact path.phase
  outputRef := by rw [same]; exact path.outputRef
  ticketRef := by rw [same]; exact path.ticketRef

def AckTicket.after_quiet (path : AckTicket initial checks current count lane) (move : Move current actual)
    (quiet : H.QuietWork actual.event) : AckTicket initial checks move.after count lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs move) (by
    rw [move.final, CampusTCPTwoProgressPathRetain.Step.work_quiet actual quiet, move.beforeEq]
    exact path.pending)

def AckTicket.control (path : AckTicket initial checks current count lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    AckTicket initial checks value.move.after count lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs value.move) (by
    rw [value.frame.work]
    exact path.pending)

def AckTicket.after_assignment (path : AckTicket initial checks current count lane)
    (assigned : N.Assignment current outputIndex selectedIngress produced actual) :
    AckTicket initial checks assigned.move.after count lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs assigned.move) (by
    rw [assigned.move.final, assigned.facts.work]
    exact CampusTCPTwoProgressPathRetain.enqueue_other _ _ path.ticket path.pending)

def AckTicket.after_service (path : AckTicket initial checks current count lane)
    (service : N.Service current item hit session actual served emission emitted)
    (different : path.ticket.id ≠ item.id) : AckTicket initial checks service.move.after count lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs service.move) (by
    obtain ⟨completed, _, _, work⟩ := service.facts.completed
    rw [service.move.final, work]
    exact CampusTCPTwoProgressPathRetain.completed_other completed path.ticket
      (by rw [service.move.beforeEq]; exact path.pending) different)

@[simp] theorem AckTicket.clock_ticket (path : AckTicket initial checks current count lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    (path.clock placement).ticket = path.ticket := rfl

@[simp] theorem AckTicket.clock_assignedGateway (path : AckTicket initial checks current count lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    (path.clock placement).assignedGateway = path.assignedGateway := rfl

@[simp] theorem AckTicket.control_ticket (path : AckTicket initial checks current count lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    (path.control value).ticket = path.ticket := rfl

@[simp] theorem AckTicket.control_assignedGateway (path : AckTicket initial checks current count lane)
    (value : CampusTCPTransferEnabled.Control current event actual) :
    (path.control value).assignedGateway = path.assignedGateway := rfl

def AckTicket.ofAssignment (path : P.AckIngress initial current count lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender.other) sender.other) path.output.produced actual) :
    AckTicket initial checks value.move.after count (ackTicketLane lane value.ticket.id) where
  assignedGateway := current.report.final.owner sender.other
  toTicketPath := {
    output := path.output.after_move value.move
    ticket := value.ticket
    pending := value.pending
    outputIndex := rfl
    produced := rfl
    gateway := by change current.report.final.owner path.output.produced.actor = _; rw [path.output.actor]
    ingress := rfl }
  phase := rfl
  outputRef := path.outputRef
  ticketRef := rfl

theorem AckTicket.assignment_observed (path : P.AckIngress initial current count lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender.other) sender.other) path.output.produced actual) :
    CampusTCPTwoProgressMonitor.Lane.ofGap
      (CampusTCPGapProgressMonitor.observeAssignment lane.toGap actual false .ackTicket) =
        ackTicketLane lane value.ticket.id := by
  simp only [CampusTCPGapProgressMonitor.observeAssignment,
    CampusTCPRoundMonitorFacts.AssignmentFacts.find_new value.facts,
    CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap]
  rfl

@[simp] theorem AckTicket.ofAssignment_ticket (path : P.AckIngress initial current count lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender.other) sender.other) path.output.produced actual) :
    (ofAssignment path checks value).ticket = value.ticket := rfl

@[simp] theorem AckTicket.ofAssignment_gateway (path : P.AckIngress initial current count lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender.other) sender.other) path.output.produced actual) :
    (ofAssignment path checks value).assignedGateway = current.report.final.owner sender.other := rfl

@[simp] theorem AckTicket.ofAssignment_ticketID (path : P.AckIngress initial current count lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender.other) sender.other) path.output.produced actual) :
    (ofAssignment path checks value).ticket.id = current.report.final.work.nextID := rfl

@[simp] theorem AckTicket.ofAssignment_produced (path : P.AckIngress initial current count lane)
    (checks : Checks cut initial.gatewayState.session.entry)
    (value : N.Assignment current path.output.index
      (checks.ingress (current.report.final.owner sender.other) sender.other) path.output.produced actual) :
    (ofAssignment path checks value).output.produced = path.output.produced := rfl

end Netlib.Check.CampusTCPTwoTransferPaths
