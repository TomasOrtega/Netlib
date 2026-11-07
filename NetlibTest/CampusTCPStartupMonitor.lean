import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPStartupTransferExecution
import Netlib.Check.CampusTCPSchedule

namespace NetlibTest.CampusTCPStartupMonitor

open Netlib Packet Protocol

namespace M
export Check.CampusTCPModel (Input Event Step Report Actor Gateway)
end M
namespace W
export Check.CampusTCPStartupTransferExecution
  (Monitor initial nextDemand allowed observe actions check monitorAt)
end W
namespace C
export Check.CampusTCPStartupTransferMonitor (Config)
end C

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private structure Run (input : M.Input) (config : C.Config) where
  events : List M.Event
  report : M.Report input events
  supported : report.supported = true
  finished : report.remaining = []
  monitor : W.Monitor input

private def append (before : Run input config) (event : M.Event) : IO (Run input config) := do
  ensure (W.allowed config before.report.final before.monitor event)
    "The startup monitor must permit the selected current operation."
  match computed : Check.CampusTCPModel.step input before.report.final event with
  | .error reason => throw (IO.userError reason.message)
  | .ok effect =>
    if accepted : effect.supported = true then
      ensure effect.passed "The actual startup operation must pass its current checks."
      let actual : M.Step input := ⟨before.report.final, event, effect, computed⟩
      let report := Check.CampusTCPSchedule.Report.appendStep before.report before.supported before.finished actual rfl accepted
      return ⟨before.events ++ [event], report,
        Check.CampusTCPSchedule.Report.appendStep_supported before.report before.supported before.finished actual rfl accepted,
        rfl, W.observe config before.monitor actual⟩
    else throw (IO.userError effect.decision)

private def ingress (input : M.Input) (gateway : M.Gateway) (actor : M.Actor) : Except String IngressAttachment.InterfaceRef := do
  let some specification := (input.deployment gateway).specifications.find? (fun value => value.direction == actor.direction)
    | throw "The actual gateway has no ingress specification for this direction."
  return specification.ingress

private def configuration (input : Check.CampusTCP.Input) : Except String C.Config := do
  let preparation := input.events.takeWhile (fun event => match event with | .open .. => false | _ => true)
  let some (.open remote true) := input.events[preparation.length]?
    | throw "The fixture must contain a permitted startup boundary."
  let pc ← ingress input.model .primary .client
  let ps ← ingress input.model .primary .server
  let sc ← ingress input.model .standby .client
  let ss ← ingress input.model .standby .server
  return {
    startup := ⟨preparation, remote⟩
    transfer := {
      lower := [97], upper := [98], reverseLower := [99], reverseUpper := [100]
      quantum := 1000, lossAllowance := 2
      ingress := fun gateway actor => match gateway, actor with
        | .primary, .client => pc | .primary, .server => ps
        | .standby, .client => sc | .standby, .server => ss
      executionNS := (input.model.deployment .standby).executionNS } }

private def start (input : M.Input) (config : C.Config) : IO (Run input config) := do
  let initial : Run input config := ⟨[], ⟨input.initial, [], [], .done _⟩, rfl, rfl, W.initial config⟩
  let prepared ← config.startup.preparation.foldlM append initial
  append prepared (.openRecovering config.startup.remote true)

private def demand (run : Run input config) (event : M.Event) : IO Unit :=
  ensure (decide (W.nextDemand config run.report.final run.monitor = some (.startup event)))
    "The protected startup demand must retain its actual path or timer."

private def forward (before : Run input config) (index : Nat) : IO (Run input config × Nat) := do
  let some produced := before.report.final.outputs[index]?
    | throw (IO.userError "The actual endpoint output is missing.")
  let ticket := before.report.final.work.nextID
  let service := before.report.final.services.length
  let assigned ← append before (.assign index (config.transfer.ingress .primary produced.actor))
  let served ← append assigned (.serve ticket none)
  return (served, service)

private def deliver (before : Run input config) (index : Nat) : IO (Run input config) := do
  let some served := before.report.final.services[index]?
    | throw (IO.userError "The selected actual service is missing.")
  let some emission := served.evidence.output
    | throw (IO.userError "The selected actual service must emit its packet.")
  append before (.deliver index emission.bytes true)

private def transmit (before : Run input config) (index : Nat) : IO (Run input config) := do
  let (served, service) ← forward before index
  deliver served service

private def drop (before : Run input config) (selected : Check.CampusTCPModel.Transit input → Bool) : IO (Run input config) := do
  let some id := before.report.final.custody.pendingID selected
    | throw (IO.userError "The selected loss must resolve an actual pending packet.")
  append before (.dropPacket id)

private def retry (before : Run input config) (actor : M.Actor) : IO (Run input config) := do
  let clocked ← append before (.startupClock actor 1000)
  append clocked (.startupTimeout actor 0 true)

private def finish (before : Run input config) (activeRTO passiveRTO losses : Nat) : IO Unit := do
  let drained ← append before .finishStartup
  let client ← append drained (.enableStartupRecovery .client)
  let server ← append client (.enableStartupRecovery .server)
  let clientAck ← append server (.enableAck .client)
  let serverAck ← append clientAck (.enableAck .server)
  let written ← append serverAck (.write .client (config.transfer.lower ++ config.transfer.upper))
  match written.monitor with
  | .data handoff monitor =>
    ensure (handoff.startupDrops == losses && written.report.final.custody.dropped == losses &&
        handoff.archive.activeData.rto == activeRTO && handoff.archive.passiveData.rto == passiveRTO &&
        monitor == .initial && W.actions config input.initial (W.initial config) written.report.steps &&
        W.check config input.initial (W.initial config) written.report.steps 12)
      "The actual handoff must keep both timer histories, all startup losses, and the whole Actions and service checks."
  | _ => throw (IO.userError "The actual setup write must select the data monitor.")

private def protectedWait (input : M.Input) (config : C.Config) : IO Unit := do
  let opened ← start input config
  let lost ← drop opened (fun value => match value with | .ingress index _ => index == 0 | _ => false)
  demand lost (.startupClock .client 1000)
  ensure (!W.allowed config lost.report.final lost.monitor (.startupClock .client 500))
    "A partial protected clock step must not reset its absolute serving target."
  let stalled ← (List.range 10).foldlM (fun run _ => append run (.startupClock .server 0)) lost
  demand stalled (.startupClock .client 1000)
  ensure (!W.check config input.initial (W.initial config) stalled.report.steps 8)
    "An unserved protected wait must fail the same whole bounded-service check."
  let retried ← retry stalled .client
  demand retried (.assign 1 (config.transfer.ingress .primary .client))
  let answered ← transmit retried 1
  let acknowledged ← transmit answered 2
  let complete ← transmit acknowledged 3
  finish complete 3000 1000 1

private def twoTimers (input : M.Input) (config : C.Config) : IO Unit := do
  let opened ← start input config
  let answered ← transmit opened 0
  let (served, index) ← forward answered 1
  let lost ← drop served (fun value => match value with | .link service .. => service == index | _ => false)
  demand lost (.startupClock .server 1000)
  let clientRetry ← retry lost .client
  demand clientRetry (.startupClock .server 1000)
  let reply ← transmit clientRetry 2
  let discarded ← transmit reply 3
  demand discarded (.startupClock .server 1000)
  let serverRetry ← retry discarded .server
  demand serverRetry (.assign 4 (config.transfer.ingress .primary .server))
  let acknowledged ← transmit serverRetry 4
  let complete ← transmit acknowledged 5
  ensure (complete.report.final.custody.dropped == 1 &&
      complete.report.steps.countP (fun actual => match actual.event with | .startupTimeout .. => true | _ => false) == 2)
    "One actual lost SYN,ACK must permit both real timers to expire."
  finish complete 3000 3000 1

private def delayedOriginal (input : M.Input) (config : C.Config) : IO Unit := do
  let opened ← start input config
  let retried ← retry opened .client
  demand retried (.assign 0 (config.transfer.ingress .primary .client))
  let answered ← transmit retried 1
  let reply ← transmit answered 0
  let discarded ← transmit reply 3
  demand discarded (.assign 2 (config.transfer.ingress .primary .server))
  let acknowledged ← transmit discarded 2
  let complete ← transmit acknowledged 4
  ensure (complete.report.final.custody.dropped == 0 && complete.report.final.services.length == 5)
    "A delayed original SYN and its early bare ACK must retain five actual services without a loss."
  finish complete 3000 1000 0

def run : IO Unit := do
  let source ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/campus-tcp-transfer/trace.json"))
  let config ← load (configuration source)
  protectedWait source.model config
  twoTimers source.model config
  delayedOriginal source.model config
  IO.println "Actual protected startup monitor tests passed."

end NetlibTest.CampusTCPStartupMonitor
