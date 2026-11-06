import Netlib.Check.CampusTCP

namespace NetlibTest.CampusTCPCustody

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Report)
end M
namespace F
export Check.CampusTCPFacts (Assurance At assure findStep)
end F
namespace C
export Check.CampusTCPCustodyFacts (Sources)
end C

private def payload (start count : Nat) : List UInt8 :=
  (List.range count).map (fun index => UInt8.ofNat ((start + index) % 251))

structure DropAt (report : M.Report input events) (time id : Nat) where
  joint : F.At report time
  event : joint.step.event = .dropPacket id

theorem DropAt.pending_source {time id : Nat} (value : DropAt report time id) :
    ∃ item ∈ value.joint.step.before.custody.pending, item.id = id := by
  obtain ⟨result, _, _⟩ := Check.CampusTCPCustodyFacts.Step.drop value.joint.step id value.event
  exact ⟨result.item, result.member, result.selected⟩

theorem DropAt.one_loss {time id : Nat} (value : DropAt report time id) :
    value.joint.step.result.state.custody.dropped = value.joint.step.before.custody.dropped + 1 := by
  simpa only [value.event, Check.CampusTCPCustodyFacts.dropEvent, Bool.true_eq, ite_true] using
    Check.CampusTCPCustodyFacts.Step.drop_count value.joint.step

theorem DropAt.no_repeat {time id : Nat} (value : DropAt report time id) :
    Theory.PacketCustody.resolve value.joint.step.result.state.custody id .dropped = .error .notPending :=
  Check.CampusTCPCustodyFacts.Step.drop_not_repeat value.joint.step id value.event
    (Check.CampusTCPCustodyFacts.Report.each_history report value.joint.step value.joint.member)

structure Demonstration (input : Check.CampusTCP.Input) where
  report : M.Report input.model input.events
  application : F.Assurance report
  clientRead : application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
    payload 81 1200 ++ payload 97 1200 ++ payload 113 1200
  serverRead : application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
    payload 17 800 ++ payload 33 800 ++ payload 49 800
  firstData : DropAt report 59 15
  secondData : DropAt report 68 17
  firstACK : DropAt report 89 21
  secondACK : DropAt report 117 29
  losses : report.final.custody.dropped = 4
  pending : report.final.custody.pending.map (·.id) = [43]

theorem Demonstration.sources (value : Demonstration input) : C.Sources value.report.final :=
  Check.CampusTCPCustodyFacts.Report.sources value.report

theorem Demonstration.accounted (value : Demonstration input) :
    value.report.final.custody.pending.length + value.report.final.custody.resolutions.length =
      value.report.final.custody.nextID :=
  Check.CampusTCPCustodyFacts.Report.accounted value.report

theorem Demonstration.read_lengths (value : Demonstration input) :
    (value.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length = 3600 ∧
      (value.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length = 2400 := by
  constructor
  · rw [value.clientRead]
    simp [payload]
  · rw [value.serverRead]
    simp [payload]

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

private def dropAt (report : M.Report input events) (time id : Nat) : Except String (DropAt report time id) := do
  let joint ← F.findStep report time
  match event : joint.step.event with
  | .dropPacket selected =>
    let same ← verify (selected = id) "The actual drop identity differs."
    return ⟨joint, by simpa only [same.property] using event⟩
  | _ => throw "The actual joint operation is not a packet drop."

private def demonstrate (input : Check.CampusTCP.Input) : Except String (Demonstration input) := do
  let report ← input.check.mapError (·.message)
  let application ← F.assure report
  let clientRead ← verify (application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
    payload 81 1200 ++ payload 97 1200 ++ payload 113 1200) "The client read bytes differ."
  let serverRead ← verify (application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
    payload 17 800 ++ payload 33 800 ++ payload 49 800) "The server read bytes differ."
  let firstData ← dropAt report 59 15
  let secondData ← dropAt report 68 17
  let firstACK ← dropAt report 89 21
  let secondACK ← dropAt report 117 29
  let losses ← verify (report.final.custody.dropped = 4) "The actual loss count differs."
  let pending ← verify (report.final.custody.pending.map (·.id) = [43]) "The omitted final link packet must stay pending."
  return ⟨report, application, clientRead.property, serverRead.property, firstData, secondData, firstACK, secondACK,
    losses.property, pending.property⟩

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/packet-custody/trace.json"))
  let value ← load (demonstrate input)
  let _ := value.sources
  let _ := value.accounted
  let _ := value.read_lengths
  let _ := value.application.application_prefix
  let _ := value.firstData.pending_source
  let _ := value.secondData.pending_source
  let _ := value.firstACK.one_loss
  let _ := value.secondACK.one_loss
  let _ := value.firstData.no_repeat
  let _ := value.firstACK.no_repeat
  ensure (value.report.compliant && value.report.steps.length == 175 &&
      value.report.final.custody.count .assigned == 23 && value.report.final.custody.count .delivered == 17 &&
      value.report.final.custody.nextID == 45)
    "Actual drops, completed reads, and one pending packet must share the same checked history."
  IO.println "Campus packet custody tests passed."

end NetlibTest.CampusTCPCustody
