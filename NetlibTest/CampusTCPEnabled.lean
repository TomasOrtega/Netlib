import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPEnabled

namespace NetlibTest.CampusTCPEnabled

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input Actor State Step Event)
end M
namespace E
export Check.CampusTCPEnabled (endpoint applicationSteps send_enabled emitAck_enabled dispatchAck_enabled
  write_enabled read_enabled assignment_after_output RouteReady)
end E

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

private def checkedPrefix (input : Check.CampusTCP.Input) (count : Nat) :
    IO (Check.CampusTCPModel.Report input.model (input.events.take count)) := do
  let report ← load ((input.model.check (input.events.take count)).mapError (·.message))
  ensure (report.compliant && report.steps.length == count) "The actual campus prefix stopped before the selected operation."
  return report

private def earlier (endpoints : Check.CampusTCPModel.Applications complete) (actor : M.Actor)
    (time : Nat) : Except String { _value : Unit //
      ∀ old ∈ E.applicationSteps endpoints actor, old.stamp < time } :=
  verify _ "The selected operation must follow every actual endpoint event."

private instance (before : M.State input) (actor : M.Actor) : Decidable (E.RouteReady before actor) := by
  unfold E.RouteReady
  infer_instance

private def checkAssignment (input : M.Input) (actual : M.Step input)
    (produced : Check.CampusTCPModel.Produced input.active input.passive)
    (present : actual.result.output = some produced) : IO Unit := do
  let route ← load (verify (E.RouteReady actual.result.state produced.actor) "The actual route is not ready.")
  let some specification := (input.deployment (actual.result.state.owner produced.actor)).specifications.find? (fun specification => specification.direction == produced.actor.direction)
    | throw (IO.userError "The actual deployment lacks the selected ingress attachment.")
  let _ := E.assignment_after_output actual produced present route.property specification.ingress
  match _computed : Check.CampusTCPModel.step input actual.result.state
      (.assign actual.before.outputs.length specification.ingress) with
  | .error reason => throw (IO.userError reason.message)
  | .ok effect =>
    ensure (effect.supported && effect.state.work.pending.length == actual.result.state.work.pending.length + 1 &&
        effect.state.custody.count .assigned == actual.result.state.custody.count .assigned + 1)
      "The new actual output must create and consume one ingress packet for its immutable ticket."

private def sendFromStartup (input : Check.CampusTCP.Input) : IO Unit := do
  let report ← checkedPrefix input 32
  match connection : report.final.connection with
  | .startup .. => throw (IO.userError "The selected data send has no checked startup history.")
  | .recovering .. => throw (IO.userError "The ordinary test prefix entered recovery.")
  | .application complete endpoints =>
    let chronological ← load (earlier endpoints .client report.final.time)
    let ready ← load (verify (TCP.Endpoint.SendReady (E.endpoint endpoints .client) 400) "The actual selected application prefix is not sendable.")
    let prepared ← load (verify (TCP.Endpoint.AckPrepared (E.endpoint endpoints .client)) "The actual sender ACK state is not ready.")
    let _ := E.send_enabled report.final complete endpoints connection .client 400 chronological.property ready.property prepared.property
    match computed : Check.CampusTCPModel.step input.model report.final (.send .client 400 true) with
    | .error reason => throw (IO.userError reason.message)
    | .ok effect =>
      match present : effect.output with
      | none => throw (IO.userError "The enabled campus send has no actual output.")
      | some produced =>
        ensure (effect.supported && produced.actor == .client &&
            produced.output.packet.segment.payload == (E.endpoint endpoints .client).pending.take 400 &&
            effect.state.custody.nextID == report.final.custody.nextID + 1)
          "The actual send must retain the selected pending prefix and mint packet custody."
        let joint : M.Step input.model := ⟨report.final, .send .client 400 true, effect, computed⟩
        match recorded : effect.application with
        | some (.client, actual) =>
          let _ := Check.CampusTCPEnabled.Step.application_frame joint complete endpoints connection
            .client (.send 400 true) (.send 400 true) actual recorded
          let serverChronology ← load (earlier endpoints .server report.final.time)
          have allEarlier : Check.CampusTCPEnabled.ApplicationsBefore endpoints report.final.time := by
            intro actor
            cases actor
            · exact chronological.property
            · exact serverChronology.property
          let _ := Check.CampusTCPEnabled.Step.application_chronology joint complete endpoints connection
            .client (.send 400 true) (.send 400 true) actual recorded allEarlier
          pure ()
        | _ => throw (IO.userError "The actual send lost its selected endpoint operation.")
        checkAssignment input.model joint produced present

private def ackAfterReceipt (input : Check.CampusTCP.Input) : IO Unit := do
  let report ← checkedPrefix input 65
  match connection : report.final.connection with
  | .startup .. => throw (IO.userError "The selected ACK has no checked startup history.")
  | .recovering .. => throw (IO.userError "The ordinary test prefix entered recovery.")
  | .application complete endpoints =>
    let chronological ← load (earlier endpoints .client report.final.time)
    let prepared ← load (verify (TCP.Endpoint.AckPrepared (E.endpoint endpoints .client)) "The actual receiver ACK guards fail.")
    let immediate ← load (verify (TCP.Endpoint.ResponseAvailable (E.endpoint endpoints .client) false) "The actual receipt has no ACK credit.")
    let due ← load (verify (TCP.Endpoint.ResponseAvailable (E.endpoint endpoints .client) true) "The actual receipt cause is not due.")
    let _ := E.emitAck_enabled report.final complete endpoints connection .client chronological.property prepared.property immediate.property
    let _ := E.dispatchAck_enabled report.final complete endpoints connection .client chronological.property prepared.property due.property
    match computed : Check.CampusTCPModel.step input.model report.final (.emitAck .client true) with
    | .error reason => throw (IO.userError reason.message)
    | .ok effect =>
      match present : effect.output with
      | none => throw (IO.userError "The enabled dispatcher has no actual output.")
      | some produced =>
        ensure (effect.supported && produced.output.packet.segment.payload.isEmpty &&
            produced.output.packet.segment.acknowledgment == (E.endpoint endpoints .client).core.receiveNext)
          "The alternative explicit ACK action must cover the actual receipt cursor."
        checkAssignment input.model ⟨report.final, .emitAck .client true, effect, computed⟩ produced present

private def writeAndRead (input : Check.CampusTCP.Input) : IO Unit := do
  let beforeWrite ← checkedPrefix input 31
  match connection : beforeWrite.final.connection with
  | .startup .. => throw (IO.userError "The selected write has no checked startup history.")
  | .recovering .. => throw (IO.userError "The ordinary test prefix entered recovery.")
  | .application complete endpoints =>
    let chronological ← load (earlier endpoints .client beforeWrite.final.time)
    let fits ← load (verify ((E.endpoint endpoints .client).pending.length + 2 ≤
      (E.endpoint endpoints .client).pendingLimit) "The selected write does not fit.")
    let _ := E.write_enabled beforeWrite.final complete endpoints connection .client [9, 10] chronological.property fits.property
    let effect ← load ((Check.CampusTCPModel.step input.model beforeWrite.final (.write .client [9, 10])).mapError (·.message))
    ensure (effect.supported && effect.output.isNone && effect.read.isEmpty &&
        effect.state.custody.nextID == beforeWrite.final.custody.nextID)
      "An enabled application write must not invent packet output."
  let beforeRead ← checkedPrefix input 149
  match connection : beforeRead.final.connection with
  | .startup .. => throw (IO.userError "The selected read has no checked startup history.")
  | .recovering .. => throw (IO.userError "The ordinary test prefix entered recovery.")
  | .application complete endpoints =>
    let chronological ← load (earlier endpoints .server beforeRead.final.time)
    let fits ← load (verify (400 ≤ (E.endpoint endpoints .server).core.received.length) "The actual read range is unavailable.")
    let _ := E.read_enabled beforeRead.final complete endpoints connection .server 400 chronological.property fits.property
    let effect ← load ((Check.CampusTCPModel.step input.model beforeRead.final (.read .server 400)).mapError (·.message))
    ensure (effect.supported && effect.output.isNone && effect.read.length == 400 &&
        effect.read == (E.endpoint endpoints .server).core.received.take 400)
      "The enabled application read must return the actual ordered prefix."

def run : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-ack/trace.json"))
  sendFromStartup input
  ackAfterReceipt input
  writeAndRead input
  IO.println "Campus local enabledness tests passed."

end NetlibTest.CampusTCPEnabled
