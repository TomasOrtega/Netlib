import Netlib.Check.CampusTCPTwoProgressPathsFrames
import Netlib.Check.CampusTCPTwoProgressNetworkState
import Netlib.Check.CampusTCPTwoProgressSenderWindow

namespace Netlib.Check.CampusTCPTwoProgressPathsAssign

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressState (Live)
open CampusTCPTwoProgressNetwork (AssignmentMove)
open CampusTCPTwoProgressPaths (Output Ingress DataIngress DataTicket AckIngress AckTicket)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender actor : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {timeouts : Nat} {received : CampusTCPTwoProgressReceiver.Stage}
variable {fields : Produced input.active input.passive → Prop} {actual : Step input}
variable {part : CampusTCPTwoProgressSender.Part} {count : Nat} {lane : CampusTCPTwoProgressMonitor.Lane}

structure Assigned (live : Live initial current sent timeouts received) (path : Ingress current actor fields)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (actual : Step input) where
  value : AssignmentMove initial current path.output.index (native.ingress path.output.produced.actor) path.output.produced actual
  output : Output value.move.after actor fields
  outputIndex : output.index = path.output.index
  produced : output.produced = path.output.produced
  next : Live initial value.move.after sent timeouts received
  reserve : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint value.move.after.endpoints sender) sent
  consumed : ∃ resolved : Theory.PacketCustody.Resolved current.report.final.custody path.packetID .assigned,
    Theory.PacketCustody.resolve current.report.final.custody path.packetID .assigned = .ok resolved ∧
      resolved.item.value.payload = .ingress path.output.index path.output.produced ∧
      actual.result.state.custody = resolved.state ∧
      ∀ item ∈ actual.result.state.custody.pending, item.id ≠ path.packetID

theorem assign_at (live : Live initial current sent timeouts received)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (path : Ingress current actor fields) :
    ∃ actual, Nonempty (Assigned live path native actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressNetwork.assign_at initial native current live.anchor
    path.output.index path.output.produced path.output.stored path.pending
  have stored : value.move.after.report.final.outputs[path.output.index]? = some path.output.produced := by
    rw [value.move.final, value.facts.frame]
    exact path.output.stored
  obtain ⟨id, resolved, selected, resolution, payload, custody, absent⟩ := value.facts.consumed
  have same : id = path.packetID := Option.some.inj (selected.symm.trans path.custody)
  subst id
  exact ⟨actual, ⟨{
    value
    output := path.output.reframe stored
    outputIndex := rfl
    produced := rfl
    next := CampusTCPTwoProgressNetworkState.assignment_live live value
    reserve := by rw [value.endpoints]; exact space
    consumed := ⟨resolved, resolution, payload, custody, absent⟩ }⟩⟩

structure DataAssigned (live : Live initial current sent timeouts received)
    (path : DataIngress initial current part lane) (native : NativeEnv cut gateway initial.gatewayState.session.entry)
    (actual : Step input) extends Assigned live path.toIngress native actual where
  event : actual.event = .assign path.output.index (native.ingress sender)
  nextLane : CampusTCPTwoProgressMonitor.Lane
  observed : CampusTCPTwoProgressMonitor.Lane.ofGap
    (CampusTCPGapProgressMonitor.observeAssignment lane.toGap actual true .dataTicket) = nextLane
  ticket : DataTicket initial native value.move.after part nextLane
  ticketEq : ticket.ticket = value.ticket
  ticketID : ticket.ticket.id = current.report.final.work.nextID
  ticketOutput : ticket.output.index = path.output.index
  ticketProduced : ticket.output.produced = path.output.produced

structure AckAssigned (live : Live initial current sent timeouts received)
    (path : AckIngress initial current count lane) (native : NativeEnv cut gateway initial.gatewayState.session.entry)
    (actual : Step input) extends Assigned live path.toIngress native actual where
  event : actual.event = .assign path.output.index (native.ingress sender.other)
  nextLane : CampusTCPTwoProgressMonitor.Lane
  observed : CampusTCPTwoProgressMonitor.Lane.ofGap
    (CampusTCPGapProgressMonitor.observeAssignment lane.toGap actual false .ackTicket) = nextLane
  ticket : AckTicket initial native value.move.after count nextLane
  ticketEq : ticket.ticket = value.ticket
  ticketID : ticket.ticket.id = current.report.final.work.nextID
  ticketOutput : ticket.output.index = path.output.index
  ticketProduced : ticket.output.produced = path.output.produced

theorem assign_data_at (live : Live initial current sent timeouts received)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (path : DataIngress initial current part lane) :
    ∃ actual, Nonempty (DataAssigned live path native actual) := by
  obtain ⟨actual, ⟨assigned⟩⟩ := assign_at live space native path.toIngress
  let afterLane : CampusTCPTwoProgressMonitor.Lane :=
    ⟨.dataTicket, { lane.refs with dataTicket := some assigned.value.ticket.id }⟩
  have observed : CampusTCPTwoProgressMonitor.Lane.ofGap
      (CampusTCPGapProgressMonitor.observeAssignment lane.toGap actual true .dataTicket) = afterLane := by
    simp only [CampusTCPGapProgressMonitor.observeAssignment,
      CampusTCPRoundMonitorFacts.AssignmentFacts.find_new assigned.value.facts,
      CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap]
    rfl
  let ticket : DataTicket initial native assigned.value.move.after part afterLane := {
    output := assigned.output
    ticket := assigned.value.ticket
    pending := assigned.value.pending
    outputIndex := assigned.outputIndex.symm
    produced := assigned.produced.symm
    gateway := assigned.value.ticket_gateway
    ingress := by change native.ingress path.output.produced.actor = _; rw [path.output.actor]
    phase := rfl
    outputRef := by change lane.refs.dataOutput = some assigned.output.index; rw [assigned.outputIndex]; exact path.outputRef
    ticketRef := rfl }
  exact ⟨actual, ⟨{
    toAssigned := assigned
    event := by simpa only [path.output.actor] using assigned.value.facts.event
    nextLane := afterLane
    observed
    ticket
    ticketEq := rfl
    ticketID := rfl
    ticketOutput := assigned.outputIndex
    ticketProduced := assigned.produced }⟩⟩

theorem assign_ack_at (live : Live initial current sent timeouts received)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (path : AckIngress initial current count lane) :
    ∃ actual, Nonempty (AckAssigned live path native actual) := by
  obtain ⟨actual, ⟨assigned⟩⟩ := assign_at live space native path.toIngress
  let afterLane : CampusTCPTwoProgressMonitor.Lane :=
    ⟨.ackTicket, { lane.refs with ackTicket := some assigned.value.ticket.id }⟩
  have observed : CampusTCPTwoProgressMonitor.Lane.ofGap
      (CampusTCPGapProgressMonitor.observeAssignment lane.toGap actual false .ackTicket) = afterLane := by
    simp only [CampusTCPGapProgressMonitor.observeAssignment,
      CampusTCPRoundMonitorFacts.AssignmentFacts.find_new assigned.value.facts,
      CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap]
    rfl
  let ticket : AckTicket initial native assigned.value.move.after count afterLane := {
    output := assigned.output
    ticket := assigned.value.ticket
    pending := assigned.value.pending
    outputIndex := assigned.outputIndex.symm
    produced := assigned.produced.symm
    gateway := assigned.value.ticket_gateway
    ingress := by change native.ingress path.output.produced.actor = _; rw [path.output.actor]
    phase := rfl
    outputRef := by change lane.refs.ackOutput = some assigned.output.index; rw [assigned.outputIndex]; exact path.outputRef
    ticketRef := rfl }
  exact ⟨actual, ⟨{
    toAssigned := assigned
    event := by simpa only [path.output.actor] using assigned.value.facts.event
    nextLane := afterLane
    observed
    ticket
    ticketEq := rfl
    ticketID := rfl
    ticketOutput := assigned.outputIndex
    ticketProduced := assigned.produced }⟩⟩

theorem Assigned.step_eq {live : Live initial current sent timeouts received}
    {path : Ingress current actor fields} {chosen : Step input} (assigned : Assigned live path native chosen)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .assign path.output.index (native.ingress path.output.produced.actor)) : chosen = actual :=
  CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
    (assigned.value.move.beforeEq.trans before.symm) (assigned.value.facts.event.trans event.symm)

theorem DataAssigned.step_eq {live : Live initial current sent timeouts received}
    {path : DataIngress initial current part lane} {chosen : Step input} (assigned : DataAssigned live path native chosen)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .assign path.output.index (native.ingress sender)) : chosen = actual :=
  CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
    (assigned.value.move.beforeEq.trans before.symm) (assigned.event.trans event.symm)

theorem AckAssigned.step_eq {live : Live initial current sent timeouts received}
    {path : AckIngress initial current count lane} {chosen : Step input} (assigned : AckAssigned live path native chosen)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .assign path.output.index (native.ingress sender.other)) : chosen = actual :=
  CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
    (assigned.value.move.beforeEq.trans before.symm) (assigned.event.trans event.symm)

end Netlib.Check.CampusTCPTwoProgressPathsAssign
