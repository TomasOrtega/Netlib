import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPGapFacts
import Netlib.Check.CampusTCPTransferFacts

namespace NetlibTest.TCPReceiveGapCampus

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Actor Connection Report Served)
end M
namespace F
export Check.CampusTCPFacts (At findStep)
end F
namespace G
export Check.CampusTCPGapFacts (Assurance ReadOrigin)
end G
namespace A
export TCP.ApplicationTrace (Step Chain OutputAt RunReceiptOrigin)
end A

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

private def fixturePayload (start count : Nat) : List UInt8 :=
  (List.range count).map (fun index => UInt8.ofNat ((start + index) % 251))

private def endpoint (actor : M.Actor) : M.Connection active passive → Option TCP.Endpoint.State
  | .startup .. | .recovering .. => none
  | .application _ endpoints => some (match actor with | .client => endpoints.client.current | .server => endpoints.server.current)

structure Point (steps : List A.Step) (time : Nat) where
  step : A.Step
  member : step ∈ steps
  stamp : step.stamp = time

private def point (steps : List A.Step) (time : Nat) : Except String (Point steps time) :=
  match found : steps.find? (fun step => decide (step.stamp = time)) with
  | none => .error "The actual endpoint landmark is missing."
  | some step => .ok ⟨step, List.mem_of_find?_eq_some found, by
      have chosen := List.find?_some found
      simpa only [decide_eq_true_eq] using chosen⟩

private def readEvent (step : A.Step) (count : Nat) : Except String { _value : Unit // step.event = .read count } :=
  match event : step.event with
  | .read amount => do
    let same ← verify (amount = count) "The actual read count differs."
    return ⟨(), by simp only [same.property]⟩
  | _ => .error "The selected operation is not a read."

private def timeoutEvent (step : A.Step) : Except String { _value : Unit // step.event = .timeout true } :=
  match step.event with
  | .timeout true => .ok ⟨(), rfl⟩
  | _ => .error "The selected operation is not a permitted timeout."

structure ReceiptSample (report : M.Report input events) (peer : List A.Step) (actor : M.Actor)
    (steps : List A.Step) (release reader : A.Step) where
  run : TCP.ReceiveReassembly.Run
  released : run ∈ release.releasedRuns
  origin : A.RunReceiptOrigin steps run
  delivery : Check.CampusTCPFacts.ApplicationDelivery report peer actor origin.issuer
  index : Nat
  readIndex : Nat
  byte : UInt8
  selected : run.bytes[index]? = some byte
  readSelected : reader.readBytes[readIndex]? = some byte
  coordinate : run.position + index = (reader.before.receiveStore.frontier - reader.before.core.received.length) + readIndex

private structure SampleShape where
  readIndex : Nat
  receipt : Nat
  index : Nat
  issuer : Nat
  attempt : Nat
  receivedAt : Nat
  standby : Bool
  deriving DecidableEq

private def ReceiptSample.shape (value : ReceiptSample report peer actor steps release reader) :
    SampleShape :=
  ⟨value.readIndex, value.run.receipt, value.index, value.origin.issuer.stamp,
    value.delivery.source.step.stamp, value.run.metadata.receivedAt,
    value.delivery.receive.receipt.served.ticket.value.gateway == .standby⟩

private def receiptSample (report : M.Report input events) (peer : List A.Step) (actor : M.Actor)
    (chain : A.Chain seed steps final) (empty : seed.receiveStore.held = [])
    (release : Point steps time) (reader : Point steps readTime) (receipt index readIndex : Nat) :
    Except String (ReceiptSample report peer actor steps release.step reader.step) := do
  match found : release.step.releasedRuns.find? (fun run => decide (run.receipt = receipt)) with
  | none => throw "The released receipt sample is missing."
  | some run =>
    have released := List.mem_of_find?_eq_some found
    let origin ← TCP.ApplicationTrace.releasedReceiptOrigin chain empty release.step release.member run released
    let delivery ← Check.CampusTCPFacts.applicationDelivery report peer actor origin.issuer
    match selected : run.bytes[index]? with
    | none => throw "The receipt sample index is outside its actual input."
    | some byte =>
      let readSelected ← verify (reader.step.readBytes[readIndex]? = some byte) "The receipt byte differs from the actual read."
      let coordinate ← verify (run.position + index =
        (reader.step.before.receiveStore.frontier - reader.step.before.core.received.length) + readIndex)
        "The receipt sample has a different read position."
      return ⟨run, released, origin, delivery, index, readIndex, byte, selected, readSelected.property, coordinate.property⟩

private def heldRun (release : A.Step) (run : TCP.ReceiveReassembly.Run) :
    Except String { _value : Unit // run ∈ release.before.receiveStore.held } :=
  match found : release.before.receiveStore.held.find? (fun candidate => decide (candidate = run)) with
  | none => .error "The original receipt run is absent from held storage."
  | some candidate => .ok ⟨(), by
      have same : candidate = run := by simpa only [decide_eq_true_eq] using List.find?_some found
      exact same ▸ List.mem_of_find?_eq_some found⟩

theorem ReceiptSample.no_future (value : ReceiptSample report peer actor steps release reader)
    (chain : A.Chain seed steps final) (empty : seed.receiveStore.held = [])
    (member : release ∈ steps) (ordered : TCP.ApplicationTrace.Chronological steps) :
    value.origin.issuer.stamp ≤ release.stamp :=
  value.origin.no_later chain empty release member value.released ordered

theorem ReceiptSample.held_earlier (value : ReceiptSample report peer actor steps release reader)
    (chain : A.Chain seed steps final) (empty : seed.receiveStore.held = [])
    (member : release ∈ steps) (ordered : TCP.ApplicationTrace.Chronological steps)
    (held : value.run ∈ release.before.receiveStore.held) : value.origin.issuer.stamp < release.stamp :=
  value.origin.held_earlier chain empty release member value.released held ordered

theorem ReceiptSample.write_origin (value : ReceiptSample report peer actor steps release reader)
    (chain : A.Chain initial peer final) (emptySent : initial.core.sent = []) (emptyPending : initial.pending = [])
    (ordered : TCP.ApplicationTrace.Chronological peer) :
    Nonempty (TCP.ApplicationTrace.AttemptByteOrigin initial peer value.delivery.source value.index value.byte) := by
  have inputEq := TCP.ApplicationTrace.Event.receive.inj
    (value.origin.allocation.event.symm.trans value.delivery.receive.event)
  have selected := value.selected
  rw [value.origin.fields.1, inputEq, value.delivery.path.fields.1] at selected
  exact value.delivery.source.byte_origin chain emptySent emptyPending ordered value.index value.byte selected

private def heldShape (step : A.Step) (count : Nat) : Prop :=
  step.result.state.receiveStore.heldBytes = count ∧ step.result.state.core.received = [] ∧
    step.result.state.core.receiveNext = step.before.core.receiveNext ∧ step.releasedPayload = [] ∧
    step.result.state.reservationFree = 4096 ∧ step.result.state.physicalFree = 4096 - count

private instance (step : A.Step) (count : Nat) : Decidable (heldShape step count) := by unfold heldShape; infer_instance

private def releaseShape (step : A.Step) (novel released : Nat) (bytes : List UInt8) : Prop :=
  step.result.decision = .accepted (.receive 0 novel) ∧ step.acceptedPayload.length = novel ∧
    step.releasedPayload = bytes ∧ step.releasedPayload.length = released ∧
    step.result.state.receiveStore.held = [] ∧ step.result.state.core.receiveNext = step.before.core.receiveNext.add released

private instance (step : A.Step) (novel released : Nat) (bytes : List UInt8) : Decidable (releaseShape step novel released bytes) := by
  unfold releaseShape; infer_instance

structure RecoveryCase (steps : List A.Step) (time : Nat) where
  point : Point steps time
  before : TCP.Recovery.State
  after : TCP.Recovery.State
  stored : point.step.before.recovery = some before
  updated : point.step.result.state.recovery = some after

private def recoveryCase (steps : List A.Step) (time : Nat) : Except String (RecoveryCase steps time) := do
  let selected ← point steps time
  match stored : selected.step.before.recovery, updated : selected.step.result.state.recovery with
  | some before, some after => return ⟨selected, before, after, stored, updated⟩
  | _, _ => throw "The recovery landmark has no actual timer state."

private def retryShape (value : RecoveryCase steps time) (count : Nat) : Prop :=
  value.point.step.result.decision = .accepted (.retry count) ∧
    value.point.step.emitted = [] ∧ value.after.rto = 2 * value.before.rto ∧
    value.point.step.result.state.core = value.point.step.before.core

private instance (value : RecoveryCase steps time) (count : Nat) : Decidable (retryShape value count) := by
  unfold retryShape; infer_instance

private def karnShape (value : RecoveryCase steps time) (count : Nat) : Prop :=
  value.point.step.result.decision = .accepted (.receive count 0) ∧
    value.before.outstanding.any (·.retried) = true ∧ TCP.Recovery.sample value.before count = none ∧
    value.after.estimator = value.before.estimator ∧ value.after.lastSample = value.before.lastSample ∧
    value.after.deadline = none ∧ TCP.Recovery.flight value.after = 0 ∧
    value.point.step.result.state.core.sent = []

private instance (value : RecoveryCase steps time) (count : Nat) : Decidable (karnShape value count) := by
  unfold karnShape; infer_instance

structure Demonstration (input : Check.CampusTCP.Input) where
  report : M.Report input.model input.events
  gap : G.Assurance report
  transfer : Check.CampusTCPTransferFacts.Assurance report
  forwardHeld : Point gap.application.endpoints.server.steps 38
  forwardRelease : Point gap.application.endpoints.server.steps 59
  forwardRead : Point gap.application.endpoints.server.steps 65
  reverseHeld : Point gap.application.endpoints.client.steps 73
  reverseRelease : Point gap.application.endpoints.client.steps 84
  reverseRead : Point gap.application.endpoints.client.steps 93
  held400 : heldShape forwardHeld.step 400
  held600 : heldShape reverseHeld.step 600
  released800 : releaseShape forwardRelease.step 400 800 (fixturePayload 17 400 ++ fixturePayload 33 400)
  released1200 : releaseShape reverseRelease.step 600 1200 (fixturePayload 81 600 ++ fixturePayload 97 600)
  read800 : forwardRead.step.event = .read 800 ∧ forwardRead.step.readBytes = fixturePayload 17 400 ++ fixturePayload 33 400
  read1200 : reverseRead.step.event = .read 1200 ∧ reverseRead.step.readBytes = fixturePayload 81 600 ++ fixturePayload 97 600
  forwardSamples : List (ReceiptSample report gap.application.endpoints.client.steps .server
    gap.application.endpoints.server.steps forwardRelease.step forwardRead.step)
  reverseSamples : List (ReceiptSample report gap.application.endpoints.server.steps .client
    gap.application.endpoints.client.steps reverseRelease.step reverseRead.step)
  forwardSources : forwardSamples.map ReceiptSample.shape =
    [⟨0, 1, 0, 59, 55, 1100, true⟩, ⟨399, 1, 399, 59, 55, 1100, true⟩,
      ⟨400, 0, 0, 38, 35, 100, false⟩, ⟨799, 0, 399, 38, 35, 100, false⟩]
  reverseSources : reverseSamples.map ReceiptSample.shape =
    [⟨0, 1, 0, 84, 80, 2100, true⟩, ⟨599, 1, 599, 84, 80, 2100, true⟩,
      ⟨600, 0, 0, 73, 70, 1200, true⟩, ⟨1199, 0, 599, 73, 70, 1200, true⟩]
  forwardRetry : RecoveryCase gap.application.endpoints.client.steps 55
  reverseRetry : RecoveryCase gap.application.endpoints.server.steps 80
  forwardAck : RecoveryCase gap.application.endpoints.client.steps 64
  reverseAck : RecoveryCase gap.application.endpoints.server.steps 89
  retryEvents : forwardRetry.point.step.event = .timeout true ∧ reverseRetry.point.step.event = .timeout true
  retried400 : retryShape forwardRetry 400
  retried600 : retryShape reverseRetry 600
  retired800 : karnShape forwardAck 800
  retired1200 : karnShape reverseAck 1200
  preservedHeld : (endpoint .server transfer.step.before.connection).map (·.receiveStore) = some forwardHeld.step.result.state.receiveStore
  copiedCut : transfer.installation.checkpoint.snapshot.cut = 7
  denied : F.At report 96
  deniedService : M.Served input.model
  deniedPresent : denied.step.result.service = some deniedService
  revoked : (Check.SessionFirewall.stateAt input.model.context.authentication denied.step.before.authentication).auth.authorized = false

theorem Demonstration.transfer_preserves_held (value : Demonstration input) :
    (endpoint .server value.transfer.step.result.state.connection).map (·.receiveStore) =
      some value.forwardHeld.step.result.state.receiveStore := by
  rw [value.transfer.origin.connection]
  exact value.preservedHeld

theorem Demonstration.server_read_origin (value : Demonstration input) (index : Nat) (byte : UInt8)
    (selected : value.forwardRead.step.readBytes[index]? = some byte) :
    Nonempty (G.ReadOrigin value.report value.gap.application.complete.certificate.activeSeed
      value.gap.application.endpoints.client.steps .server value.gap.application.endpoints.server.steps
      value.forwardRead.step index byte) :=
  value.gap.toEvidence.server_read_origin value.forwardRead.step value.forwardRead.member 800 value.read800.1 index byte selected

theorem Demonstration.client_read_origin (value : Demonstration input) (index : Nat) (byte : UInt8)
    (selected : value.reverseRead.step.readBytes[index]? = some byte) :
    Nonempty (G.ReadOrigin value.report value.gap.application.complete.certificate.passiveSeed
      value.gap.application.endpoints.server.steps .client value.gap.application.endpoints.client.steps
      value.reverseRead.step index byte) :=
  value.gap.toEvidence.client_read_origin value.reverseRead.step value.reverseRead.member 1200 value.read1200.1 index byte selected

theorem Demonstration.logoff_denies_output (value : Demonstration input) : value.deniedService.evidence.output = none :=
  Check.CampusTCPFacts.service_output_none_of_unauthorized value.report value.gap.application.compliant
    value.denied.step value.denied.member value.deniedService value.deniedPresent value.revoked

private def demonstrate (input : Check.CampusTCP.Input) : Except String (Demonstration input) := do
  let report ← input.check.mapError (·.message)
  let evidence ← Check.CampusTCPGapFacts.evidence report
  let gap ← Check.CampusTCPGapFacts.assure evidence
  let transfer ← Check.CampusTCPTransferFacts.assure report
  let forwardHeld ← point gap.application.endpoints.server.steps 38
  let forwardRelease ← point gap.application.endpoints.server.steps 59
  let forwardRead ← point gap.application.endpoints.server.steps 65
  let reverseHeld ← point gap.application.endpoints.client.steps 73
  let reverseRelease ← point gap.application.endpoints.client.steps 84
  let reverseRead ← point gap.application.endpoints.client.steps 93
  let held400 ← verify (heldShape forwardHeld.step 400) "The forward held storage differs."
  let held600 ← verify (heldShape reverseHeld.step 600) "The reverse held storage differs."
  let released800 ← verify (releaseShape forwardRelease.step 400 800 (fixturePayload 17 400 ++ fixturePayload 33 400)) "The forward ordered release differs."
  let released1200 ← verify (releaseShape reverseRelease.step 600 1200 (fixturePayload 81 600 ++ fixturePayload 97 600)) "The reverse ordered release differs."
  let read800Event ← readEvent forwardRead.step 800
  let read800 ← verify (forwardRead.step.readBytes = fixturePayload 17 400 ++ fixturePayload 33 400) "The server read differs."
  let read1200Event ← readEvent reverseRead.step 1200
  let read1200 ← verify (reverseRead.step.readBytes = fixturePayload 81 600 ++ fixturePayload 97 600) "The client read differs."
  let forwardSamples ← [(1, 0, 0), (1, 399, 399), (0, 0, 400), (0, 399, 799)].mapM (fun (receipt, index, readIndex) =>
    receiptSample report gap.application.endpoints.client.steps .server gap.application.endpoints.server.chain gap.server.empty
      forwardRelease forwardRead receipt index readIndex)
  let reverseSamples ← [(1, 0, 0), (1, 599, 599), (0, 0, 600), (0, 599, 1199)].mapM (fun (receipt, index, readIndex) =>
    receiptSample report gap.application.endpoints.server.steps .client gap.application.endpoints.client.chain gap.client.empty
      reverseRelease reverseRead receipt index readIndex)
  let forwardSources ← verify (forwardSamples.map ReceiptSample.shape =
    [⟨0, 1, 0, 59, 55, 1100, true⟩, ⟨399, 1, 399, 59, 55, 1100, true⟩,
      ⟨400, 0, 0, 38, 35, 100, false⟩, ⟨799, 0, 399, 38, 35, 100, false⟩]) "The forward receipt source differs."
  let reverseSources ← verify (reverseSamples.map ReceiptSample.shape =
    [⟨0, 1, 0, 84, 80, 2100, true⟩, ⟨599, 1, 599, 84, 80, 2100, true⟩,
      ⟨600, 0, 0, 73, 70, 1200, true⟩, ⟨1199, 0, 599, 73, 70, 1200, true⟩]) "The reverse receipt source differs."
  let forwardRetry ← recoveryCase gap.application.endpoints.client.steps 55
  let reverseRetry ← recoveryCase gap.application.endpoints.server.steps 80
  let forwardAck ← recoveryCase gap.application.endpoints.client.steps 64
  let reverseAck ← recoveryCase gap.application.endpoints.server.steps 89
  let forwardRetryEvent ← timeoutEvent forwardRetry.point.step
  let reverseRetryEvent ← timeoutEvent reverseRetry.point.step
  let retried400 ← verify (retryShape forwardRetry 400) "The forward RTO retry differs."
  let retried600 ← verify (retryShape reverseRetry 600) "The reverse RTO retry differs."
  let retired800 ← verify (karnShape forwardAck 800) "The forward ACK or Karn exclusion differs."
  let retired1200 ← verify (karnShape reverseAck 1200) "The reverse ACK or Karn exclusion differs."
  let preservedHeld ← verify ((endpoint .server transfer.step.before.connection).map (·.receiveStore) =
    some forwardHeld.step.result.state.receiveStore) "The receiver did not retain held data through transfer."
  let copiedCut ← verify (transfer.installation.checkpoint.snapshot.cut = 7) "The installed checkpoint cut differs."
  let denied ← F.findStep report 96
  match deniedPresent : denied.step.result.service with
  | none => throw "The Logoff service is missing."
  | some deniedService =>
    let revoked ← verify ((Check.SessionFirewall.stateAt input.model.context.authentication denied.step.before.authentication).auth.authorized = false)
      "The final service did not use revoked authentication."
    return ⟨report, gap, transfer, forwardHeld, forwardRelease, forwardRead, reverseHeld, reverseRelease, reverseRead,
      held400.property, held600.property, released800.property, released1200.property, ⟨read800Event.property, read800.property⟩, ⟨read1200Event.property, read1200.property⟩,
      forwardSamples, reverseSamples, forwardSources.property, reverseSources.property,
      forwardRetry, reverseRetry, forwardAck, reverseAck, ⟨forwardRetryEvent.property, reverseRetryEvent.property⟩, retried400.property, retried600.property, retired800.property, retired1200.property,
      preservedHeld.property, copiedCut.property, denied, deniedService, deniedPresent, revoked.property⟩

private structure HeaderClock where
  receipt : Nat
  receivedAt : Nat
  acknowledged : Nat
  deriving DecidableEq

private def headerClocks (state : TCP.Endpoint.State) (input : TCP.EstablishedReceive.Input) : List HeaderClock :=
  (TCP.Endpoint.receiveEffect state input).headers.map (fun header =>
    ⟨header.run.receipt, header.run.metadata.receivedAt, header.acknowledged⟩)

private def deferredTimer (value : RecoveryCase steps time) : Prop :=
  value.point.step.before.now = 1100 ∧ value.before.now = 1100 ∧ value.after.now = 1100 ∧
    value.point.step.result.decision = .accepted (.receive 200 400) ∧
    value.after.lastSample = some ⟨0, 100, 150⟩ ∧ value.after.estimator = some (TCP.RTO.first 50) ∧
    value.after.rto = 1000 ∧ value.after.deadline = some 2100 ∧ TCP.Recovery.flight value.after = 200 ∧
    value.point.step.result.state.core.sent.length = 200

private instance (value : RecoveryCase steps time) : Decidable (deferredTimer value) := by unfold deferredTimer; infer_instance

structure DeferredDemonstration (input : Check.CampusTCP.Input) where
  report : M.Report input.model input.events
  gap : G.Assurance report
  transfer : Check.CampusTCPTransferFacts.Assurance report
  held : Point gap.application.endpoints.server.steps 48
  release : RecoveryCase gap.application.endpoints.server.steps 65
  reader : Point gap.application.endpoints.server.steps 71
  allocation : TCP.ApplicationTrace.ActualAllocation release.point.step
  selected : release.point.step.allocation = some allocation
  headers : headerClocks release.point.step.before allocation.input = [⟨1, 1100, 0⟩, ⟨0, 150, 200⟩]
  timer : deferredTimer release
  held400 : heldShape held.step 400
  released : release.point.step.releasedPayload.length = 800
  receipt : ReceiptSample report gap.application.endpoints.client.steps .server gap.application.endpoints.server.steps release.point.step reader.step
  source : receipt.shape = ⟨400, 0, 0, 48, 45, 150, false⟩
  readEvent : reader.step.event = .read 800
  preservedHeld : (endpoint .server transfer.step.before.connection).map (·.receiveStore) = some held.step.result.state.receiveStore

theorem DeferredDemonstration.transfer_preserves_held (value : DeferredDemonstration input) :
    (endpoint .server value.transfer.step.result.state.connection).map (·.receiveStore) =
      some value.held.step.result.state.receiveStore := by
  rw [value.transfer.origin.connection]
  exact value.preservedHeld

theorem DeferredDemonstration.queued_read_origin (value : DeferredDemonstration input) :
    Nonempty (G.ReadOrigin value.report value.gap.application.complete.certificate.activeSeed
      value.gap.application.endpoints.client.steps .server value.gap.application.endpoints.server.steps
      value.reader.step value.receipt.readIndex value.receipt.byte) :=
  value.gap.toEvidence.server_read_origin value.reader.step value.reader.member 800 value.readEvent
    value.receipt.readIndex value.receipt.byte value.receipt.readSelected

private def deferredDemonstrate (input : Check.CampusTCP.Input) : Except String (DeferredDemonstration input) := do
  let report ← input.check.mapError (·.message)
  let evidence ← Check.CampusTCPGapFacts.evidence report
  let gap ← Check.CampusTCPGapFacts.assure evidence
  let transfer ← Check.CampusTCPTransferFacts.assure report
  let held ← point gap.application.endpoints.server.steps 48
  let release ← recoveryCase gap.application.endpoints.server.steps 65
  let reader ← point gap.application.endpoints.server.steps 71
  match selected : release.point.step.allocation with
  | none => throw "The deferred header release has no actual allocation."
  | some allocation =>
    let headers ← verify (headerClocks release.point.step.before allocation.input = [⟨1, 1100, 0⟩, ⟨0, 150, 200⟩])
      "The release did not retain each original header clock."
    let timer ← verify (deferredTimer release) "The deferred receipt sample or current timer deadline differs."
    let held400 ← verify (heldShape held.step 400) "The deferred receipt was not held above the gap."
    let released ← verify (release.point.step.releasedPayload.length = 800) "The deferred release byte count differs."
    let receipt ← receiptSample report gap.application.endpoints.client.steps .server gap.application.endpoints.server.chain
      gap.server.empty release.point reader 0 0 400
    let source ← verify (receipt.shape = ⟨400, 0, 0, 48, 45, 150, false⟩) "The deferred receipt source or local clock differs."
    let readEvent ← readEvent reader.step 800
    let preservedHeld ← verify ((endpoint .server transfer.step.before.connection).map (·.receiveStore) =
      some held.step.result.state.receiveStore) "The deferred receipt changed at transfer."
    return ⟨report, gap, transfer, held, release, reader, allocation, selected, headers.property, timer.property,
      held400.property, released.property, receipt, source.property, readEvent.property, preservedHeld.property⟩

def run : IO Unit := do
  let input ← match Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-receive-gaps/trace.json") with
    | .ok input => pure input
    | .error reason => throw (IO.userError reason)
  let value ← match demonstrate input with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  let _ := value.transfer_preserves_held
  let _ := value.logoff_denies_output
  let _ := value.gap.application_prefix
  let empty := value.gap.application.complete.certificate.empty
  for sample in value.forwardSamples do
    let _ := value.server_read_origin sample.readIndex sample.byte sample.readSelected
    let _ := sample.no_future value.gap.application.endpoints.server.chain value.gap.server.empty
      value.forwardRelease.member value.gap.application.forward.receiverOrder
    let _ := sample.write_origin value.gap.application.endpoints.client.chain empty.2.1 empty.1
      value.gap.application.forward.senderOrder
    if sample.run.receipt == 0 then
      let held ← match heldRun value.forwardRelease.step sample.run with
        | .ok value => pure value
        | .error reason => throw (IO.userError reason)
      let _ := sample.held_earlier value.gap.application.endpoints.server.chain value.gap.server.empty
        value.forwardRelease.member value.gap.application.forward.receiverOrder held.property
      pure ()
  for sample in value.reverseSamples do
    let _ := value.client_read_origin sample.readIndex sample.byte sample.readSelected
    let _ := sample.no_future value.gap.application.endpoints.client.chain value.gap.client.empty
      value.reverseRelease.member value.gap.application.backward.receiverOrder
    let _ := sample.write_origin value.gap.application.endpoints.server.chain empty.2.2.2.2.1 empty.2.2.2.1
      value.gap.application.backward.senderOrder
    if sample.run.receipt == 0 then
      let held ← match heldRun value.reverseRelease.step sample.run with
        | .ok value => pure value
        | .error reason => throw (IO.userError reason)
      let _ := sample.held_earlier value.gap.application.endpoints.client.chain value.gap.client.empty
        value.reverseRelease.member value.gap.application.backward.receiverOrder held.property
      pure ()
  unless value.report.steps.length == 97 && value.report.remaining.isEmpty &&
      value.deniedService.ticket.value.gateway == .standby && value.deniedService.evidence.output.isNone do
    throw (IO.userError "The receive-gap campus trace must complete and deny the final standby output.")
  let deferredInput ← match Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-receive-gaps/deferred-clock.json") with
    | .ok input => pure input
    | .error reason => throw (IO.userError reason)
  let deferred ← match deferredDemonstrate deferredInput with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  let _ := deferred.transfer_preserves_held
  let _ := deferred.queued_read_origin
  let held ← match heldRun deferred.release.point.step deferred.receipt.run with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  let _ := deferred.receipt.held_earlier deferred.gap.application.endpoints.server.chain deferred.gap.server.empty
    deferred.release.point.member deferred.gap.application.forward.receiverOrder held.property
  let empty := deferred.gap.application.complete.certificate.empty
  let _ := deferred.receipt.write_origin deferred.gap.application.endpoints.client.chain empty.2.1 empty.1
    deferred.gap.application.forward.senderOrder
  unless deferred.report.steps.length == 80 && deferred.report.remaining.isEmpty do
    throw (IO.userError "The deferred receipt-clock trace must complete all actual events.")
  IO.println "Checked campus TCP receive-gap tests passed."

end NetlibTest.TCPReceiveGapCampus
