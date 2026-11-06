import Netlib.Check.CampusTCPTwoProgressRead
import Netlib.Check.CampusTCPTwoProgressWriteOrigins

namespace Netlib.Check.CampusTCPTwoProgressRead

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart (TwoWriteInitial)
open CampusTCPGapProgressStart (seed endpoint_chain seed_empty_held)
open CampusTCPGapProgressOrigins (seed_empty_unread seed_empty_sent seed_empty_pending endpoint_order)

variable {input : Input} {complete : TCPHandshake.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {first : S.Original initial .lower} {second : S.Original initial .upper} {timeouts : Nat}

abbrev ReadOrigin (done : Completed initial current first second timeouts) (index : Nat) (byte : UInt8) :=
  CampusTCPGapFacts.ReadOrigin current.report (seed complete sender) (applicationSteps current.endpoints sender)
    sender.other (applicationSteps current.endpoints sender.other) done.operation index byte

theorem Completed.receives (_done : Completed initial current first second timeouts) :
    Nonempty (CampusTCPFacts.Receives current.report (applicationSteps current.endpoints sender) sender.other
      (applicationSteps current.endpoints sender.other)) := by
  have actual := CampusTCPRecoveryRoundOrigins.Report.receives current.report complete current.endpoints current.connection sender.other
  cases sender <;> exact actual

theorem Completed.read_origin (done : Completed initial current first second timeouts)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    Nonempty (ReadOrigin done index byte) := by
  obtain ⟨receives⟩ := done.receives
  have history : ApplicationTrace.DeliveryHistory (applicationSteps current.endpoints sender)
      (applicationSteps current.endpoints sender.other) :=
    ⟨endpoint_order current sender, endpoint_order current sender.other, receives.delivered⟩
  obtain ⟨member, _, event, read⟩ := done.history.exact_read
  apply CampusTCPGapFacts.read_origin (endpoint_chain current sender.other) (endpoint_chain current sender) history receives
    (seed_empty_unread complete sender.other) (seed_empty_held complete sender.other)
    (seed_empty_sent complete sender) (seed_empty_pending complete sender)
    done.operation member (lower ++ upper).length event index byte
  rw [read]
  exact selected

variable {done : Completed initial current first second timeouts} {index : Nat} {byte : UInt8}

def ReadOrigin.issuer (origin : ReadOrigin done index byte) : T.Step := origin.read.origin.origin.issuer

def ReadOrigin.allocation (origin : ReadOrigin done index byte) : ApplicationTrace.ActualAllocation origin.issuer :=
  origin.read.origin.origin.allocation

def ReadOrigin.localIndex (origin : ReadOrigin done index byte) : Nat := origin.read.origin.localIndex

def ReadOrigin.run (origin : ReadOrigin done index byte) : ReceiveReassembly.Run := origin.read.origin.run

theorem ReadOrigin.issuer_fields (origin : ReadOrigin done index byte) :
    origin.issuer ∈ applicationSteps current.endpoints sender.other ∧
      origin.issuer.event = .receive origin.allocation.input ∧
      origin.issuer.allocation = some origin.allocation ∧
      origin.run = origin.allocation.store.allocated ∧
      origin.run.receipt = origin.issuer.before.receiveStore.nextID ∧
      origin.run.metadata = ⟨origin.allocation.input.packet.segment, origin.allocation.input.packet.header, origin.issuer.before.now⟩ ∧
      origin.allocation.input.packet.segment.payload[origin.localIndex]? = some byte :=
  ⟨origin.read.origin.origin.issuer_member, origin.allocation.event, origin.read.origin.origin.selected,
    origin.read.origin.origin.allocated, origin.read.origin.origin.fields.2.2.1,
    origin.read.origin.origin.fields.2.1, origin.read.origin.input_byte⟩

theorem ReadOrigin.coordinates (origin : ReadOrigin done index byte) :
    (origin.read.prior.flatMap ApplicationTrace.Step.readBytes).length + index =
        (origin.read.releasePrior.flatMap ApplicationTrace.Step.releasedPayload).length + origin.read.releaseIndex ∧
      origin.read.releaseIndex = ReceiveStore.size origin.read.origin.prior + origin.localIndex ∧
      origin.run.position + origin.localIndex = origin.read.release.before.receiveStore.frontier + origin.read.releaseIndex :=
  ⟨origin.read.position, origin.read.origin.position, origin.read.origin.coordinate⟩

theorem ReadOrigin.receipt_input (origin : ReadOrigin done index byte) :
    origin.delivery.receive.receipt.received = origin.allocation.input := by
  have same := ApplicationTrace.Event.receive.inj (origin.delivery.receive.event.symm.trans origin.allocation.event)
  exact origin.delivery.receive.same.trans same

theorem ReadOrigin.joint_fields (origin : ReadOrigin done index byte) :
    origin.delivery.receive.joint.step ∈ current.report.steps ∧
      origin.delivery.receive.joint.step.result.application = some (sender.other, origin.issuer) ∧
      origin.delivery.receive.joint.step.result.receipt = some origin.delivery.receive.receipt ∧
      origin.delivery.service.joint.step ∈ current.report.steps ∧
      origin.delivery.service.joint.step.result.service = some origin.delivery.receive.receipt.served :=
  ⟨origin.delivery.receive.joint.member, origin.delivery.receive.applied, origin.delivery.receive.recorded,
    origin.delivery.service.joint.member, origin.delivery.service.present⟩

theorem ReadOrigin.source_fields (origin : ReadOrigin done index byte) :
    origin.attempt.step ∈ applicationSteps current.endpoints sender ∧
      origin.attempt.step.result.output = some origin.attempt.output ∧
      origin.attempt.output.packet.segment.payload[origin.localIndex]? = some byte := by
  refine ⟨origin.attempt.member, origin.attempt.origin.actual, ?_⟩
  rw [← origin.path.fields.1]
  exact origin.read.origin.input_byte

theorem ReadOrigin.application_source (origin : ReadOrigin done index byte) :
    ∃ sourceStep output outputOrigin,
      origin.delivery.receive.receipt.served.ticket.value.produced = .application sender sourceStep output outputOrigin ∧
        origin.attempt.step = sourceStep ∧ origin.attempt.output = output := by
  obtain ⟨sourceActor, sourceStep, output, outputOrigin, produced, actor, step, packet⟩ := origin.delivery.applicationSource
  have same : sourceActor = sender := by cases sender <;> exact actor
  rw [same] at produced
  exact ⟨sourceStep, output, outputOrigin, produced,
    (congrArg (fun attempt => attempt.step) origin.actualSource).trans step,
    (congrArg (fun attempt => attempt.output) origin.actualSource).trans packet⟩

theorem ReadOrigin.times (origin : ReadOrigin done index byte) :
    origin.attempt.step.stamp < origin.issuer.stamp ∧ origin.issuer.stamp ≤ origin.read.release.stamp ∧
      origin.read.release.stamp < done.operation.stamp :=
  ⟨origin.earlier, origin.receiptBeforeRelease, origin.read.earlier⟩

theorem Completed.compliant (_done : Completed initial current first second timeouts)
    (prior : cut.report.compliant = true) (suffix : List (Step input))
    (history : current.report.steps = cut.report.steps ++ suffix)
    (passed : ∀ actual ∈ suffix, actual.result.passed = true) : current.report.compliant = true :=
  CampusTCPRecoveryRoundOrigins.compliant_of_suffix cut.report current.report current.supported prior suffix history passed

theorem ReadOrigin.permissions (origin : ReadOrigin done index byte)
    (prior : cut.report.compliant = true) (suffix : List (Step input))
    (history : current.report.steps = cut.report.steps ++ suffix)
    (passed : ∀ actual ∈ suffix, actual.result.passed = true) :
    CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  CampusTCPRoundOrigins.service_permissions current.report (done.compliant prior suffix history passed)
    origin.delivery.service.joint.step origin.delivery.service.joint.member origin.delivery.receive.receipt.served
    origin.delivery.service.present origin.delivery.receive.receipt.emission origin.delivery.receive.receipt.emitted

theorem Completed.read_permissions (done : Completed initial current first second timeouts)
    (prior : cut.report.compliant = true) (suffix : List (Step input))
    (history : current.report.steps = cut.report.steps ++ suffix)
    (passed : ∀ actual ∈ suffix, actual.result.passed = true)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : ReadOrigin done index byte,
      CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served := by
  obtain ⟨origin⟩ := done.read_origin index byte selected
  exact ⟨origin, origin.permissions prior suffix history passed⟩

end Netlib.Check.CampusTCPTwoProgressRead
