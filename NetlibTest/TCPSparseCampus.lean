import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPGapFacts
import Netlib.Check.CampusTCPTransferFacts
import Netlib.Protocol.TCP.AdmissionRecoveryFacts
import Netlib.Protocol.TCP.CheckpointCoverageFacts

namespace NetlibTest.TCPSparseCampus

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Actor Cursor Connection Report Served)
end M
namespace F
export Check.CampusTCPFacts (At findStep)
end F
namespace G
export Check.CampusTCPGapFacts (Assurance ReadOrigin)
end G
namespace A
export TCP.ApplicationTrace (Step Chain RunReceiptOrigin)
end A

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

private def payload : List UInt8 :=
  (List.range 800).map (fun index => UInt8.ofNat ((index * 29 + 7 + (index / 200) * 13) % 256))

private def seed (gap : G.Assurance report) : M.Actor → TCP.Endpoint.State
  | .client => gap.application.complete.certificate.activeSeed
  | .server => gap.application.complete.certificate.passiveSeed

private def cursor (gap : G.Assurance report) : (actor : M.Actor) → M.Cursor (seed gap actor)
  | .client => gap.application.endpoints.client
  | .server => gap.application.endpoints.server

private theorem emptyStore (gap : G.Assurance report) (actor : M.Actor) : (seed gap actor).receiveStore.held = [] := by
  cases actor
  · exact gap.client.empty
  · exact gap.server.empty

private def endpoint (actor : M.Actor) : M.Connection active passive → Option TCP.Endpoint.State
  | .startup .. => none
  | .application _ endpoints => some (match actor with | .client => endpoints.client.current | .server => endpoints.server.current)

structure Point (steps : List A.Step) (time : Nat) where
  step : A.Step
  member : step ∈ steps
  stamp : step.stamp = time

private def point (steps : List A.Step) (time : Nat) : Except String (Point steps time) :=
  match found : steps.find? (fun step => decide (step.stamp = time)) with
  | none => .error "The actual endpoint operation is missing."
  | some step => .ok ⟨step, List.mem_of_find?_eq_some found, by
      simpa only [decide_eq_true_eq] using List.find?_some found⟩

private def readEvent (step : A.Step) : Except String { _value : Unit // step.event = .read 800 } :=
  match event : step.event with
  | .read count => do
    let same ← verify (count = 800) "The actual read count differs."
    return ⟨(), by simp only [same.property]⟩
  | _ => .error "The actual read operation is missing."

private def timeoutEvent (step : A.Step) : Except String { _value : Unit // step.event = .timeout true } :=
  match step.event with
  | .timeout true => .ok ⟨(), rfl⟩
  | _ => .error "The actual permitted timer event is missing."

structure GatewayPoint (report : M.Report input events) where
  time : Nat
  joint : F.At report time
  served : M.Served input
  present : joint.step.result.service = some served
  before : TCP.Admission.Session
  beforePhase : served.before.admission.phase = .data before
  after : TCP.Admission.Session
  afterPhase : served.evidence.admission.phase = .data after

private def gatewayPoint (report : M.Report input events) (time : Nat) : Except String (GatewayPoint report) := do
  let joint ← F.findStep report time
  match present : joint.step.result.service with
  | none => throw "The actual sparse gateway service is missing."
  | some served =>
    match beforePhase : served.before.admission.phase, afterPhase : served.evidence.admission.phase with
    | .data before, .data after => return ⟨time, joint, served, present, before, beforePhase, after, afterPhase⟩
    | _, _ => throw "The sparse service has no checked data history."

private structure GatewayShape where
  time : Nat
  beforeFrontier : Nat
  afterFrontier : Nat
  highEnd : Nat
  uniqueBytes : Nat
  standby : Bool
  output : Bool
  deriving DecidableEq

private def GatewayPoint.shape (value : GatewayPoint report) (sender : M.Actor) : GatewayShape :=
  ⟨value.time, (value.before.lane sender.direction).observed, (value.after.lane sender.direction).observed,
    (value.after.lane sender.direction).highEnd, (value.after.lane sender.direction).uniqueBytes,
    value.served.ticket.value.gateway == .standby, value.served.evidence.output.isSome⟩

private def GatewayPoint.unseenStart (value : GatewayPoint report) (sender : M.Actor) : Bool :=
  !decide ((value.before.lane sender.direction).coverage.Covers
    (TCP.Seq.distance (value.before.lane sender.direction).base value.served.ticket.value.source.packet.segment.sequence))

private structure RangeShape where
  position : Nat
  count : Nat
  source : Nat
  observation : Nat
  deriving DecidableEq

private def rangeShapes (lane : TCP.Admission.Lane) : List RangeShape :=
  lane.coverage.runs.map (fun run => ⟨run.position, run.bytes.length, run.sourceID, run.metadata⟩)

structure ReceiptSample (report : M.Report input events) (peer : List A.Step) (actor : M.Actor)
    (steps : List A.Step) (reader : A.Step) where
  release : A.Step
  releasedAt : Nat
  releaseMember : release ∈ steps
  releaseStamp : release.stamp = releasedAt
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
  inputIndex : Nat
  receiptAt : Nat
  attemptAt : Nat
  releaseAt : Nat
  standby : Bool
  deriving DecidableEq

private def ReceiptSample.shape (value : ReceiptSample report peer actor steps reader) : SampleShape :=
  ⟨value.readIndex, value.run.receipt, value.index, value.origin.issuer.stamp,
    value.delivery.source.step.stamp, value.releasedAt,
    value.delivery.receive.receipt.served.ticket.value.gateway == .standby⟩

private def receiptSample (report : M.Report input events) (peer : List A.Step) (actor : M.Actor)
    (chain : A.Chain initial steps final) (empty : initial.receiveStore.held = [])
    (reader : A.Step) (time receipt index readIndex : Nat) :
    Except String (ReceiptSample report peer actor steps reader) := do
  let release ← point steps time
  match found : release.step.releasedRuns.find? (fun run => decide (run.receipt = receipt)) with
  | none => throw "The original receipt is absent from its actual release."
  | some run =>
    have released := List.mem_of_find?_eq_some found
    let origin ← TCP.ApplicationTrace.releasedReceiptOrigin chain empty release.step release.member run released
    let delivery ← Check.CampusTCPFacts.applicationDelivery report peer actor origin.issuer
    match selected : run.bytes[index]? with
    | none => throw "The sample index is outside its actual receipt."
    | some byte =>
      let readSelected ← verify (reader.readBytes[readIndex]? = some byte) "The actual read byte differs."
      let coordinate ← verify (run.position + index =
        (reader.before.receiveStore.frontier - reader.before.core.received.length) + readIndex)
        "The byte has a different stream position."
      return ⟨release.step, time, release.member, release.stamp, run, released, origin, delivery,
        index, readIndex, byte, selected, readSelected.property, coordinate.property⟩

structure RecoveryPoint (steps : List A.Step) (time : Nat) where
  point : Point steps time
  before : TCP.Recovery.State
  after : TCP.Recovery.State
  stored : point.step.before.recovery = some before
  updated : point.step.result.state.recovery = some after

private def recoveryPoint (steps : List A.Step) (time : Nat) : Except String (RecoveryPoint steps time) := do
  let value ← point steps time
  match stored : value.step.before.recovery, updated : value.step.result.state.recovery with
  | some before, some after => return ⟨value, before, after, stored, updated⟩
  | _, _ => throw "The actual timer operation has no recovery state."

private def retryShape (value : RecoveryPoint steps time) : Prop :=
  value.point.step.result.decision = .accepted (.retry 200) ∧
    value.point.step.emitted = [] ∧ value.point.step.before.core = value.point.step.result.state.core ∧
    value.after.rto = 2 * value.before.rto

private instance (value : RecoveryPoint steps time) : Decidable (retryShape value) := by unfold retryShape; infer_instance

private def ackShape (value : RecoveryPoint steps time) (remaining : Nat) : Prop :=
  value.point.step.result.decision = .accepted (.receive 400 0) ∧ TCP.Recovery.flight value.after = remaining ∧
    value.before.outstanding.any (·.retried) = true ∧ TCP.Recovery.sample value.before 400 = none ∧
    value.after.estimator = value.before.estimator ∧ value.after.lastSample = value.before.lastSample

private instance (value : RecoveryPoint steps time) (remaining : Nat) : Decidable (ackShape value remaining) := by
  unfold ackShape; infer_instance

private def releaseShape (value : A.Step) (held : Nat) : Prop :=
  value.result.decision = .accepted (.receive 0 200) ∧ value.acceptedPayload.length = 200 ∧
    value.releasedPayload.length = 400 ∧ value.result.state.receiveStore.heldBytes = held ∧
    value.result.state.core.receiveNext = value.before.core.receiveNext.add 400

private instance (value : A.Step) (held : Nat) : Decidable (releaseShape value held) := by unfold releaseShape; infer_instance

structure CoverageSample {gateway : TCP.Checkpoint.Gateway} (history : TCP.Checkpoint.History gateway)
    (session : TCP.Admission.Session) (direction : TCP.Admission.Direction) where
  run : TCP.Admission.Coverage.Run Nat
  member : run ∈ (session.lane direction).coverage.runs
  origin : TCP.Checkpoint.CoverageOrigin history session direction run
  index : Nat
  byte : UInt8
  selected : run.bytes[index]? = some byte

private structure CoverageShape where
  position : Nat
  source : Nat
  observation : Nat
  priorCut : Nat
  index : Nat
  byte : UInt8
  deriving DecidableEq

private def CoverageSample.shape (value : CoverageSample history session direction) : CoverageShape :=
  ⟨value.run.position, value.run.sourceID, value.run.metadata, value.origin.observation.prior.length, value.index, value.byte⟩

private def coverageSample (history : TCP.Checkpoint.History gateway) (session : TCP.Admission.Session)
    (phase : gateway.admission.phase = .data session) (direction : TCP.Admission.Direction) (source index : Nat) :
    Except String (CoverageSample history session direction) := do
  match found : (session.lane direction).coverage.runs.find? (fun run => decide (run.sourceID = source)) with
  | none => throw "The actual first-source range is missing."
  | some run =>
    have member := List.mem_of_find?_eq_some found
    let origin := history.coverageOrigin session phase direction run member
    match selected : run.bytes[index]? with
    | none => throw "The source sample is outside its actual original range."
    | some byte => return ⟨run, member, origin, index, byte, selected⟩

theorem CoverageSample.actual_byte (value : CoverageSample history session direction) :
    value.origin.observation.transition.request.source.packet.segment.payload[value.index]? = some value.byte :=
  value.origin.byte value.index value.byte value.selected

theorem CoverageSample.actual_index (value : CoverageSample history session direction) :
    value.run.metadata = value.origin.observation.before.admission.observations.length := value.origin.index

theorem CoverageSample.actual_earlier (value : CoverageSample history session direction) :
    value.origin.observation.prior.length < history.length := value.origin.earlier

structure Demonstration (input : Check.CampusTCP.Input) (sender : M.Actor) where
  report : M.Report input.model input.events
  gap : G.Assurance report
  transfer : Check.CampusTCPTransferFacts.Assurance report
  gateways : List (GatewayPoint report)
  geometry : gateways.map (fun value => value.shape sender) =
    [⟨37, 0, 0, 800, 200, false, true⟩, ⟨45, 0, 0, 800, 400, false, true⟩,
      ⟨62, 0, 400, 800, 600, true, true⟩, ⟨73, 400, 800, 800, 800, true, true⟩]
  unseen : gateways.all (fun value => value.unseenStart sender) = true
  source : TCP.Admission.Session
  sourcePhase : transfer.installation.checkpoint.snapshot.source.admission.phase = .data source
  sourceRuns : rangeShapes (source.lane sender.direction) = [⟨200, 200, 1, 5⟩, ⟨600, 200, 0, 3⟩]
  sourceFrontier : (source.lane sender.direction).observed = 0
  copiedCut : transfer.installation.checkpoint.snapshot.cut = 7
  held : Point (cursor gap sender.other).steps 46
  held400 : held.step.result.state.receiveStore.heldBytes = 400 ∧ held.step.result.state.core.received = []
  preservedHeld : (endpoint sender.other transfer.step.before.connection).map (·.receiveStore) =
    some held.step.result.state.receiveStore
  firstRelease : Point (cursor gap sender.other).steps 63
  secondRelease : Point (cursor gap sender.other).steps 74
  partialRelease : releaseShape firstRelease.step 200 ∧ firstRelease.step.releasedRuns.map (·.receipt) = [2, 1]
  fullRelease : releaseShape secondRelease.step 0 ∧ secondRelease.step.releasedRuns.map (·.receipt) = [3, 0]
  firstRetry : RecoveryPoint (cursor gap sender).steps 60
  secondRetry : RecoveryPoint (cursor gap sender).steps 71
  retryEvents : firstRetry.point.step.event = .timeout true ∧ secondRetry.point.step.event = .timeout true
  retries : retryShape firstRetry ∧ retryShape secondRetry
  firstAck : RecoveryPoint (cursor gap sender).steps 68
  secondAck : RecoveryPoint (cursor gap sender).steps 79
  retirement : ackShape firstAck 400 ∧ ackShape secondAck 0 ∧ firstAck.after.deadline = some 3200 ∧ secondAck.after.deadline = none
  reader : Point (cursor gap sender.other).steps 80
  readEvent : reader.step.event = .read 800
  readBytes : reader.step.readBytes = payload
  readOnce : (cursor gap sender.other).steps.flatMap TCP.ApplicationTrace.Step.readBytes = payload
  samples : List (ReceiptSample report (cursor gap sender).steps sender.other (cursor gap sender.other).steps reader.step)
  sampleSources : samples.map ReceiptSample.shape =
    [⟨0, 2, 0, 63, 60, 63, true⟩, ⟨199, 2, 199, 63, 60, 63, true⟩,
      ⟨200, 1, 0, 46, 33, 63, false⟩, ⟨399, 1, 199, 46, 33, 63, false⟩,
      ⟨400, 3, 0, 74, 71, 74, true⟩, ⟨599, 3, 199, 74, 71, 74, true⟩,
      ⟨600, 0, 0, 38, 35, 74, false⟩, ⟨799, 0, 199, 38, 35, 74, false⟩]
  copiedSources : List (CoverageSample transfer.installation.checkpoint.snapshot.history source sender.direction)
  copiedOrigins : copiedSources.map CoverageSample.shape =
    [⟨200, 1, 5, 5, 0, 188⟩, ⟨200, 1, 5, 5, 199, 71⟩,
      ⟨600, 0, 3, 3, 0, 38⟩, ⟨600, 0, 3, 3, 199, 177⟩]
  finalSession : TCP.Admission.Session
  finalPhase : report.final.standby.transport.admission.phase = .data finalSession
  finalSources : List (CoverageSample report.final.standby.history finalSession sender.direction)
  finalOrigins : finalSources.map CoverageSample.shape =
    [⟨0, 2, 7, 7, 0, 7⟩, ⟨0, 2, 7, 7, 199, 146⟩,
      ⟨200, 1, 5, 5, 0, 188⟩, ⟨200, 1, 5, 5, 199, 71⟩,
      ⟨400, 3, 9, 9, 0, 113⟩, ⟨400, 3, 9, 9, 199, 252⟩,
      ⟨600, 0, 3, 3, 0, 38⟩, ⟨600, 0, 3, 3, 199, 177⟩]

theorem Demonstration.unseen_gateway_start (value : Demonstration input sender)
    (gateway : GatewayPoint value.report) (member : gateway ∈ value.gateways) :
    ¬(gateway.before.lane sender.direction).coverage.Covers
      (TCP.Seq.distance (gateway.before.lane sender.direction).base gateway.served.ticket.value.source.packet.segment.sequence) := by
  have checked := List.all_eq_true.mp value.unseen gateway member
  intro covered
  simp [GatewayPoint.unseenStart, covered] at checked

theorem Demonstration.transfer_preserves_held (value : Demonstration input sender) :
    (endpoint sender.other value.transfer.step.result.state.connection).map (·.receiveStore) =
      some value.held.step.result.state.receiveStore := by
  rw [value.transfer.origin.connection]
  exact value.preservedHeld

theorem Demonstration.transfer_copies_coverage (value : Demonstration input sender) :
    value.transfer.step.result.state.standby.transport.admission = value.transfer.installation.checkpoint.snapshot.source.admission :=
  congrArg TCP.Checkpoint.Gateway.admission value.transfer.origin.copied

theorem Demonstration.read_origin (value : Demonstration input sender) (index : Nat) (byte : UInt8)
    (selected : value.reader.step.readBytes[index]? = some byte) :
    Nonempty (G.ReadOrigin value.report (seed value.gap sender) (cursor value.gap sender).steps sender.other
      (cursor value.gap sender.other).steps value.reader.step index byte) := by
  cases sender
  · exact value.gap.toEvidence.server_read_origin value.reader.step value.reader.member 800 value.readEvent index byte selected
  · exact value.gap.toEvidence.client_read_origin value.reader.step value.reader.member 800 value.readEvent index byte selected

private def demonstrate (input : Check.CampusTCP.Input) (sender : M.Actor) : Except String (Demonstration input sender) := do
  let report ← input.check.mapError (·.message)
  let gap ← Check.CampusTCPGapFacts.assure (← Check.CampusTCPGapFacts.evidence report)
  let transfer ← Check.CampusTCPTransferFacts.assure report
  let gateways ← [37, 45, 62, 73].mapM (gatewayPoint report)
  let geometry ← verify (gateways.map (fun value => value.shape sender) =
    [⟨37, 0, 0, 800, 200, false, true⟩, ⟨45, 0, 0, 800, 400, false, true⟩,
      ⟨62, 0, 400, 800, 600, true, true⟩, ⟨73, 400, 800, 800, 800, true, true⟩]) "The actual sparse gateway geometry differs."
  let unseen ← verify (gateways.all (fun value => value.unseenStart sender) = true)
    "A claimed new gateway source already covered its first byte."
  match sourcePhase : transfer.installation.checkpoint.snapshot.source.admission.phase with
  | .data source =>
    let sourceRuns ← verify (rangeShapes (source.lane sender.direction) = [⟨200, 200, 1, 5⟩, ⟨600, 200, 0, 3⟩]) "The copied first-source ranges differ."
    let sourceFrontier ← verify ((source.lane sender.direction).observed = 0) "The checkpoint filled an unseen hole."
    let copiedCut ← verify (transfer.installation.checkpoint.snapshot.cut = 7) "The actual checkpoint cut differs."
    let held ← point (cursor gap sender.other).steps 46
    let held400 ← verify (held.step.result.state.receiveStore.heldBytes = 400 ∧ held.step.result.state.core.received = []) "The host held storage differs."
    let preservedHeld ← verify ((endpoint sender.other transfer.step.before.connection).map (·.receiveStore) =
      some held.step.result.state.receiveStore) "Host storage changed before gateway installation."
    let firstRelease ← point (cursor gap sender.other).steps 63
    let secondRelease ← point (cursor gap sender.other).steps 74
    let partialRelease ← verify (releaseShape firstRelease.step 200 ∧ firstRelease.step.releasedRuns.map (·.receipt) = [2, 1]) "The first actual hole fill differs."
    let fullRelease ← verify (releaseShape secondRelease.step 0 ∧ secondRelease.step.releasedRuns.map (·.receipt) = [3, 0]) "The second actual hole fill differs."
    let firstRetry ← recoveryPoint (cursor gap sender).steps 60
    let secondRetry ← recoveryPoint (cursor gap sender).steps 71
    let firstRetryEvent ← timeoutEvent firstRetry.point.step
    let secondRetryEvent ← timeoutEvent secondRetry.point.step
    let retries ← verify (retryShape firstRetry ∧ retryShape secondRetry) "The actual timer retries differ."
    let firstAck ← recoveryPoint (cursor gap sender).steps 68
    let secondAck ← recoveryPoint (cursor gap sender).steps 79
    let retirement ← verify (ackShape firstAck 400 ∧ ackShape secondAck 0 ∧ firstAck.after.deadline = some 3200 ∧ secondAck.after.deadline = none) "The actual ACK retirement or Karn exclusion differs."
    let reader ← point (cursor gap sender.other).steps 80
    let readEvent ← readEvent reader.step
    let readBytes ← verify (reader.step.readBytes = payload) "The actual read bytes differ."
    let readOnce ← verify ((cursor gap sender.other).steps.flatMap TCP.ApplicationTrace.Step.readBytes = payload) "Application reads duplicated or lost bytes."
    let samples ← [(63, 2, 0, 0), (63, 2, 199, 199), (63, 1, 0, 200), (63, 1, 199, 399),
      (74, 3, 0, 400), (74, 3, 199, 599), (74, 0, 0, 600), (74, 0, 199, 799)].mapM
      (fun (time, receipt, index, readIndex) => receiptSample report (cursor gap sender).steps sender.other
        (cursor gap sender.other).chain (emptyStore gap sender.other) reader.step time receipt index readIndex)
    let sampleSources ← verify (samples.map ReceiptSample.shape =
      [⟨0, 2, 0, 63, 60, 63, true⟩, ⟨199, 2, 199, 63, 60, 63, true⟩,
        ⟨200, 1, 0, 46, 33, 63, false⟩, ⟨399, 1, 199, 46, 33, 63, false⟩,
        ⟨400, 3, 0, 74, 71, 74, true⟩, ⟨599, 3, 199, 74, 71, 74, true⟩,
        ⟨600, 0, 0, 38, 35, 74, false⟩, ⟨799, 0, 199, 38, 35, 74, false⟩]) "The actual byte sources differ."
    let copiedSources ← [(1, 0), (1, 199), (0, 0), (0, 199)].mapM (fun (sourceID, index) =>
      coverageSample transfer.installation.checkpoint.snapshot.history source sourcePhase sender.direction sourceID index)
    let copiedOrigins ← verify (copiedSources.map CoverageSample.shape =
      [⟨200, 1, 5, 5, 0, 188⟩, ⟨200, 1, 5, 5, 199, 71⟩,
        ⟨600, 0, 3, 3, 0, 38⟩, ⟨600, 0, 3, 3, 199, 177⟩]) "The copied actual gateway origins differ."
    match finalPhase : report.final.standby.transport.admission.phase with
    | .data finalSession =>
      let finalSources ← [(2, 0), (2, 199), (1, 0), (1, 199), (3, 0), (3, 199), (0, 0), (0, 199)].mapM
        (fun (sourceID, index) => coverageSample report.final.standby.history finalSession finalPhase sender.direction sourceID index)
      let finalOrigins ← verify (finalSources.map CoverageSample.shape =
        [⟨0, 2, 7, 7, 0, 7⟩, ⟨0, 2, 7, 7, 199, 146⟩,
          ⟨200, 1, 5, 5, 0, 188⟩, ⟨200, 1, 5, 5, 199, 71⟩,
          ⟨400, 3, 9, 9, 0, 113⟩, ⟨400, 3, 9, 9, 199, 252⟩,
          ⟨600, 0, 3, 3, 0, 38⟩, ⟨600, 0, 3, 3, 199, 177⟩]) "The actual standby source origins differ."
      return ⟨report, gap, transfer, gateways, geometry.property, unseen.property, source, sourcePhase, sourceRuns.property,
        sourceFrontier.property, copiedCut.property, held, held400.property, preservedHeld.property,
        firstRelease, secondRelease, partialRelease.property, fullRelease.property, firstRetry, secondRetry,
        ⟨firstRetryEvent.property, secondRetryEvent.property⟩, retries.property, firstAck, secondAck, retirement.property, reader, readEvent.property, readBytes.property,
        readOnce.property, samples, sampleSources.property, copiedSources, copiedOrigins.property,
        finalSession, finalPhase, finalSources, finalOrigins.property⟩
    | _ => throw "The final standby has no actual sparse data history."
  | _ => throw "The checkpoint has no actual established coverage."

def run : IO Unit := do
  let fixtures : List (String × M.Actor) := [("trace", .client), ("reverse", .server), ("wrap", .client)]
  for (name, sender) in fixtures do
    let input ← match Check.CampusTCP.Input.parse (← IO.FS.readFile s!"examples/tcp-sparse-admission/{name}.json") with
      | .ok value => pure value
      | .error reason => throw (IO.userError reason)
    let value ← match demonstrate input sender with
      | .ok value => pure value
      | .error reason => throw (IO.userError reason)
    let _ := value.transfer_preserves_held
    let _ := value.transfer_copies_coverage
    for sample in value.samples do
      let _ := value.read_origin sample.readIndex sample.byte sample.readSelected
    for sample in value.copiedSources do
      let _ := sample.actual_byte
      let _ := sample.actual_index
      let _ := sample.actual_earlier
    for sample in value.finalSources do
      let _ := sample.actual_byte
      let _ := sample.actual_index
      let _ := sample.actual_earlier
    unless value.report.steps.length == 81 && value.report.remaining.isEmpty do
      throw (IO.userError "The actual sparse campus trace did not finish all 81 operations.")
  IO.println "Checked sparse campus TCP tests passed."

end NetlibTest.TCPSparseCampus
