import Netlib.Check.CampusTCPTwoProgressNetwork
import Netlib.Check.CampusTCPTwoProgressGatewayReady

/-!
# Gateway range state after actual services

Each processing witness comes from the selected stored service.
The current cut receives its actual tracker and admission state.
-/

namespace Netlib.Check.CampusTCPTwoProgressServiceState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressNetwork (ServiceMove)
open CampusTCPTwoProgressGatewayState (View)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)}
variable {hit : FlowNAT.Hit} {session : Admission.Session} {actual : Step input} {served : Served input}
variable {emission : WireForwarding.Emission served.ticket.value.source.packet} {emitted : served.evidence.output = some emission}

def processingAt (processing : CampusTCPService.Processing context before source zone) (same : before = next) :
    CampusTCPService.Processing context next source zone := same ▸ processing

theorem processingAt_outcome (processing : CampusTCPService.Processing context before source zone) (same : before = next) :
    (processingAt processing same).outcome = processing.outcome := by cases same; rfl

theorem processingAt_admission (processing : CampusTCPService.Processing context before source zone) (same : before = next) :
    (processingAt processing same).nextAdmission = processing.nextAdmission := by cases same; rfl

theorem processingAt_attachment (processing : CampusTCPService.Processing context before source zone) (same : before = next) :
    (processingAt processing same).prepared.attachment = processing.prepared.attachment := by cases same; rfl

private theorem before_eq (value : ServiceMove initial current item hit session actual served emission emitted) :
    served.before = beforeService input current.report.final gateway := by
  rw [value.facts.current, value.selected]

private theorem admission_after (value : ServiceMove initial current item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : value.ordinaryEvidence.processing = some processing) :
    (beforeService input value.move.after.report.final gateway).admission =
      (processingAt processing (before_eq value)).nextAdmission := by
  rw [value.after_ordinary_before processing present, processingAt_admission]
  rfl

private theorem tracker_after (value : ServiceMove initial current item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : value.ordinaryEvidence.processing = some processing) :
    (beforeService input value.move.after.report.final gateway).tracker =
      (processingAt processing (before_eq value)).outcome.state := by
  rw [value.after_ordinary_before processing present, processingAt_outcome]
  rfl

theorem lower_service (view : View initial current)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (direction : hit.direction = sender.direction)
    (ready : Admission.FreshReady view.gateway.session sender.direction served.ticket.value.source.packet.segment)
    (missing : view.ranges.lowerRun = none)
    (position : Seq.distance (view.gateway.session.lane sender.direction).base
      served.ticket.value.source.packet.segment.sequence = initial.geometry.«prefix»)
    (payload : served.ticket.value.source.packet.segment.payload = lower) :
    ∃ result : View initial value.move.after, result.ranges.upperRun = view.ranges.upperRun ∧
      ∃ run, result.ranges.lowerRun = some run ∧
        run.sourceID = (view.gateway.session.lane sender.direction).coverage.nextID ∧
        run.metadata = (beforeService input current.report.final gateway).admission.observations.length ∧
        run.position = initial.geometry.«prefix» ∧ run.bytes = lower := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.ordinary_processing
  let selected := processingAt processing (before_eq value)
  have selectedDirection : selected.prepared.attachment.direction = sender.direction := by
    rw [processingAt_attachment]
    exact attached.trans direction
  have selectedReady : Admission.FreshReady view.gateway.session selected.prepared.attachment.direction
      served.ticket.value.source.packet.segment := by rw [selectedDirection]; exact ready
  exact view.lower_service selected selectedDirection selectedReady missing position payload
    (admission_after value processing present) (tracker_after value processing present)

theorem upper_service (view : View initial current)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (direction : hit.direction = sender.direction)
    (ready : Admission.FreshReady view.gateway.session sender.direction served.ticket.value.source.packet.segment)
    (missing : view.ranges.upperRun = none)
    (position : Seq.distance (view.gateway.session.lane sender.direction).base
      served.ticket.value.source.packet.segment.sequence = initial.geometry.«prefix» + lower.length)
    (payload : served.ticket.value.source.packet.segment.payload = upper) :
    ∃ result : View initial value.move.after, result.ranges.lowerRun = view.ranges.lowerRun ∧
      ∃ run, result.ranges.upperRun = some run ∧
        run.sourceID = (view.gateway.session.lane sender.direction).coverage.nextID ∧
        run.metadata = (beforeService input current.report.final gateway).admission.observations.length ∧
        run.position = initial.geometry.«prefix» + lower.length ∧ run.bytes = upper := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.ordinary_processing
  let selected := processingAt processing (before_eq value)
  have selectedDirection : selected.prepared.attachment.direction = sender.direction := by
    rw [processingAt_attachment]
    exact attached.trans direction
  have selectedReady : Admission.FreshReady view.gateway.session selected.prepared.attachment.direction
      served.ticket.value.source.packet.segment := by rw [selectedDirection]; exact ready
  exact view.upper_service selected selectedDirection selectedReady missing position payload
    (admission_after value processing present) (tracker_after value processing present)

theorem empty_service (view : View initial current)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (empty : served.ticket.value.source.packet.segment.payload = []) :
    ∃ result : View initial value.move.after, result.ranges.lowerRun = view.ranges.lowerRun ∧
      result.ranges.upperRun = view.ranges.upperRun := by
  obtain ⟨processing, present, _, _, _, _⟩ := value.ordinary_processing
  exact view.empty_service (processingAt processing (before_eq value)) empty
    (admission_after value processing present) (tracker_after value processing present)

theorem repeat_service (view : View initial current)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (known : Admission.KnownRange (view.gateway.session.lane hit.direction) view.gateway.session.entry hit.direction
      served.ticket.value.source.packet.segment (beforeService input current.report.final gateway).admission.observations) :
    ∃ result : View initial value.move.after, result.ranges.lowerRun = view.ranges.lowerRun ∧
      result.ranges.upperRun = view.ranges.upperRun := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.ordinary_processing
  let selected := processingAt processing (before_eq value)
  have selectedDirection : selected.prepared.attachment.direction = hit.direction := by
    rw [processingAt_attachment]
    exact attached
  apply view.repeat_service selected
  · rw [selectedDirection]
    exact known
  · exact admission_after value processing present
  · exact tracker_after value processing present

end Netlib.Check.CampusTCPTwoProgressServiceState
