import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPSchedule

namespace NetlibTest.CampusTCPStartupRecovery

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input State Event Step Report Transit Actor)
end M

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def checked : Except Check.CampusTCPModel.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.message)

private structure Run (input : M.Input) where
  events : List M.Event
  report : M.Report input events
  supported : report.supported = true
  finished : report.remaining = []

private def append (before : Run input) (event : M.Event) : IO (Run input) := do
  match computed : Check.CampusTCPModel.step input before.report.final event with
  | .error reason => throw (IO.userError reason.message)
  | .ok effect =>
    if accepted : effect.supported = true then
      let actual : M.Step input := ⟨before.report.final, event, effect, computed⟩
      let report := Check.CampusTCPSchedule.Report.appendStep before.report before.supported before.finished actual rfl accepted
      return ⟨before.events ++ [event], report,
        Check.CampusTCPSchedule.Report.appendStep_supported before.report before.supported before.finished actual rfl accepted, rfl⟩
    else throw (IO.userError ("The campus startup operation is unsupported: " ++ effect.decision))

private def start (input : Check.CampusTCP.Input) : IO (Run input.model) := do
  let bootEvents := input.events.takeWhile (fun event => match event with | .open .. => false | _ => true)
  let report ← checked (input.model.check bootEvents)
  if supported : report.supported = true then
    if finished : report.remaining = [] then
      let some (.open remote policy) := input.events[bootEvents.length]?
        | throw (IO.userError "The source fixture must contain an actual startup boundary.")
      append ⟨bootEvents, report, supported, finished⟩ (.openRecovering remote policy)
    else throw (IO.userError "The authentication and policy prefix must finish.")
  else throw (IO.userError "The authentication and policy prefix must be supported.")

private def forward (before : Run input) (index : Nat) : IO (Run input × Nat) := do
  let some produced := before.report.final.outputs[index]?
    | throw (IO.userError "The actual endpoint output is missing.")
  let some specification := input.specifications.find? (fun value => value.direction == produced.actor.direction)
    | throw (IO.userError "The actual output direction has no ingress specification.")
  let ticket := before.report.final.work.nextID
  let service := before.report.final.services.length
  let assigned ← append before (.assign index specification.ingress)
  let served ← append assigned (.serve ticket none)
  let some actual := served.report.final.services[service]?
    | throw (IO.userError "The actual gateway service is missing.")
  ensure actual.passed "Current authentication, ingress, route, and forwarding checks must pass."
  return (served, service)

private def deliver (before : Run input) (index : Nat) : IO (Run input) := do
  let some served := before.report.final.services[index]?
    | throw (IO.userError "The selected actual service is missing.")
  let some emission := served.evidence.output
    | throw (IO.userError "The actual service must emit the selected packet.")
  append before (.deliver index emission.bytes true)

private def transmit (before : Run input) (index : Nat) : IO (Run input) := do
  let (served, service) ← forward before index
  deliver served service

private def drop (before : Run input) (selected : M.Transit input → Bool) : IO (Run input × Nat) := do
  let some id := before.report.final.custody.pendingID selected
    | throw (IO.userError "The dropped packet must have actual pending custody.")
  return (← append before (.dropPacket id), id)

private def retry (before : Run input) (actor : M.Actor) : IO (Run input) := do
  let clocked ← append before (.startupClock actor 1000)
  append clocked (.startupTimeout actor 0 true)

private def close (before : Run input) (clientRTO serverRTO earlyClient earlyServer : Nat) : IO (Run input) := do
  ensure (before.report.final.work.pending.isEmpty && before.report.final.custody.pending.isEmpty)
    "All actual startup tickets and packets must be resolved before the drain."
  let drained ← append before .finishStartup
  let some archive := drained.report.final.recoveryArchive
    | throw (IO.userError "The drain must retain its actual startup state and timer handoffs.")
  ensure (archive.activeData.rto == clientRTO && archive.passiveData.rto == serverRTO &&
      archive.client.steps.length == earlyClient && archive.server.steps.length == earlyServer)
    "The archive must retain both timer histories and the actual early ACK operations."
  let client ← append drained (.enableStartupRecovery .client)
  let server ← append client (.enableStartupRecovery .server)
  let clientAck ← append server (.enableAck .client)
  let ready ← append clientAck (.enableAck .server)
  match ready.report.final.connection with
  | .application _ endpoints =>
    ensure (endpoints.client.current.recovery.map (·.rto) == some clientRTO &&
        endpoints.server.current.recovery.map (·.rto) == some serverRTO &&
        endpoints.client.current.sendWL1 == archive.client.current.sendWL1 &&
        endpoints.server.current.sendWL1 == archive.server.current.sendWL1 &&
        (endpoints.client.steps.take earlyClient).map (·.stamp) == archive.client.steps.map (·.stamp) &&
        (endpoints.server.steps.take earlyServer).map (·.stamp) == archive.server.steps.map (·.stamp) &&
        endpoints.client.current.ackReaction.isSome && endpoints.server.current.ackReaction.isSome)
      "Actual endpoint setup must keep the inherited timer, window history, and early ACK prefix."
  | _ => throw (IO.userError "The actual drained connection must enter application execution.")
  return ready

private def dataRound (before : Run input) : IO Unit := do
  let written ← append before (.write .client [97, 98, 99])
  let index := written.report.final.outputs.length
  let sent ← append written (.send .client 3 true)
  let received ← transmit sent index
  let read ← append received (.read .server 3)
  let ackIndex := read.report.final.outputs.length
  let acked ← append read (.emitAck .server true)
  let done ← transmit acked ackIndex
  match done.report.final.connection with
  | .application _ endpoints =>
    ensure ((endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes) == [97, 98, 99] &&
        endpoints.client.current.core.sent.isEmpty &&
        endpoints.client.current.recovery.all (fun recovery => recovery.outstanding.isEmpty) && done.report.compliant)
      "The same campus report must deliver, read, and acknowledge the actual data after startup recovery."
  | _ => throw (IO.userError "Data must use the actual application continuation.")

private def lostSyn (input : Check.CampusTCP.Input) : IO Unit := do
  let opened ← start input
  let (lost, originalID) ← drop opened (fun value => match value with | .ingress index _ => index == 0 | _ => false)
  let retried ← retry lost .client
  let answered ← transmit retried 1
  let acknowledged ← transmit answered 2
  let complete ← transmit acknowledged 3
  ensure (complete.report.final.custody.dropped == 1 && complete.report.final.services.length == 3)
    "A missing first SYN must be one actual packet drop followed by three actual gateway services."
  let ready ← close complete 3000 1000 0 0
  match Check.CampusTCPModel.step input.model ready.report.final (.copyPacket originalID) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "An archived startup packet must not be revived after the drain.")
  dataRound ready

private def lostSynAck (input : Check.CampusTCP.Input) : IO Unit := do
  let opened ← start input
  let answered ← transmit opened 0
  let (served, source) ← forward answered 1
  let (lost, _) ← drop served (fun value => match value with | .link index .. => index == source | _ => false)
  let clientRetry ← retry lost .client
  let reply ← transmit clientRetry 2
  let discarded ← transmit reply 3
  let serverRetry ← retry discarded .server
  let acknowledged ← transmit serverRetry 4
  let complete ← transmit acknowledged 5
  ensure (complete.report.final.custody.dropped == 1 && complete.report.final.services.length == 6 &&
      complete.report.steps.countP (fun actual => match actual.event with | .startupTimeout .. => true | _ => false) == 2)
    "One dropped SYN,ACK must permit both actual SYN timers to expire in the same campus report."
  let ready ← close complete 3000 3000 0 0
  dataRound ready

private def delayedSyn (input : Check.CampusTCP.Input) : IO Unit := do
  let opened ← start input
  let retried ← retry opened .client
  let answered ← transmit retried 1
  let acknowledged ← transmit answered 2
  match Check.CampusTCPModel.step input.model acknowledged.report.final .finishStartup with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "The startup drain must reject unresolved actual controls.")
  let reply ← transmit acknowledged 0
  let early ← transmit reply 4
  let complete ← transmit early 3
  ensure (complete.report.final.custody.dropped == 0 && complete.report.final.services.length == 5)
    "The delayed original SYN must retain its actual later service without a fabricated loss."
  let ready ← close complete 3000 1000 1 0
  dataRound ready

def run : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/campus-tcp/trace.json"))
  lostSyn input
  lostSynAck input
  delayedSyn input
  IO.println "Actual campus startup recovery tests passed."

end NetlibTest.CampusTCPStartupRecovery
