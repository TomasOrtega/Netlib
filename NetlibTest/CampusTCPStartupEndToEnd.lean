import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPStartupTransferExecution
import Netlib.Check.CampusTCPSchedule
import Netlib.Check.CampusTCPTransferFacts
import NetlibTest.CampusTCPRecoveryRound
import NetlibTest.CampusTCPGapProgressInitial

namespace NetlibTest.CampusTCPStartupEndToEnd

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

private def appendStep (before : Run input config) (event : M.Event) : IO (Run input config × M.Step input) := do
  ensure (W.allowed config before.report.final before.monitor event)
    "The startup monitor must permit the selected current operation."
  match computed : Check.CampusTCPModel.step input before.report.final event with
  | .error reason => throw (IO.userError reason.message)
  | .ok effect =>
    if accepted : effect.supported = true then
      ensure effect.passed "The actual startup operation must pass its current checks."
      let actual : M.Step input := ⟨before.report.final, event, effect, computed⟩
      let report := Check.CampusTCPSchedule.Report.appendStep before.report before.supported before.finished actual rfl accepted
      return (⟨before.events ++ [event], report,
        Check.CampusTCPSchedule.Report.appendStep_supported before.report before.supported before.finished actual rfl accepted,
        rfl, W.observe config before.monitor actual⟩, actual)
    else throw (IO.userError effect.decision)

private def append (before : Run input config) (event : M.Event) : IO (Run input config) := do
  return (← appendStep before event).1

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

private def endpoint (state : Check.CampusTCPModel.State input) (actor : M.Actor) : IO TCP.Endpoint.State :=
  load (NetlibTest.CampusTCPRecoveryRound.endpoint state actor)

private def history (state : Check.CampusTCPModel.State input) (actor : M.Actor) : IO (List TCP.ApplicationTrace.Step) :=
  match state.connection with
  | .application _ endpoints => pure (Check.CampusTCPEnabled.applicationSteps endpoints actor)
  | _ => throw (IO.userError "The actual connection must retain its established application cursors.")

private def dropIDs (steps : List (M.Step input)) : List Nat := steps.filterMap fun actual =>
  match actual.event with | .dropPacket id => some id | _ => none

private def startupTimeouts (steps : List (M.Step input)) : Nat := steps.countP fun actual =>
  match actual.event with | .startupTimeout _ _ true => true | _ => false

private def dataTimeouts (steps : List (M.Step input)) : Nat := steps.countP fun actual =>
  match actual.event with | .timeout _ true => true | _ => false

private def operations (steps : List (M.Step input)) (actor : M.Actor) : List TCP.ApplicationTrace.Step :=
  steps.filterMap fun actual => match actual.result.application with
    | some (selected, operation) => if selected == actor then some operation else none
    | none => none

private def twoTimers (input : M.Input) (config : C.Config) : IO (Run input config × Nat) := do
  let opened ← start input config
  let answered ← transmit opened 0
  let (served, originalSynAck) ← forward answered 1
  let lost ← drop served (fun value => match value with | .link index .. => index == originalSynAck | _ => false)
  let clientRetry ← retry lost .client
  let reply ← transmit clientRetry 2
  let discarded ← transmit reply 3
  let serverRetry ← retry discarded .server
  let acknowledged ← transmit serverRetry 4
  let complete ← transmit acknowledged 5
  ensure (complete.report.final.custody.dropped == 1 && startupTimeouts complete.report.steps == 2 &&
      complete.report.final.work.pending.isEmpty && complete.report.final.custody.pending.isEmpty)
    "One dropped SYNACK must retain both actual timer expiries and resolve every startup job."
  let drained ← append complete .finishStartup
  let some archive := drained.report.final.recoveryArchive
    | throw (IO.userError "The actual startup drain must retain its complete recovery archive.")
  ensure (archive.activeData.rto == 3000 && archive.passiveData.rto == 3000 &&
      archive.activeData.synRetransmitted && archive.passiveData.synRetransmitted &&
      archive.current.emissions.length == 6 && archive.current.receipts.length == 5)
    "The archive must retain both real retry histories and their Karn handoffs."
  let indices := archive.current.emissions.map (·.index)
  ensure (indices.eraseDups == indices && archive.current.receipts.all (fun receipt =>
      receipt.source.index < receipt.index && indices.contains receipt.source.index) &&
      drained.report.final.outputs.all (fun produced => match produced with
        | .recovery actual occurrence _ => actual.index == occurrence.index
        | _ => false))
    "Startup source event stamps must retain actual occurrences independently of output and service slots."
  let client ← append drained (.enableStartupRecovery .client)
  let server ← append client (.enableStartupRecovery .server)
  let clientAck ← append server (.enableAck .client)
  let serverAck ← append clientAck (.enableAck .server)
  let written ← append serverAck (.write .client (config.transfer.lower ++ config.transfer.upper))
  match written.monitor with
  | .data handoff monitor =>
    ensure (handoff.startupDrops == 1 && handoff.archive.current.emissions.length == 6 &&
        handoff.archive.activeData == archive.activeData && handoff.archive.passiveData == archive.passiveData && monitor == .initial)
      "The selected write must retain the same startup archive and only one remaining loss credit."
  | _ => throw (IO.userError "The actual write must enter the data monitor.")
  return (written, originalSynAck)

private def localEvent : Check.CampusTCPTwoProgressMonitor.Demand → Except String M.Event
  | .single demand => .ok demand.event
  | .originalChoice lower upper =>
    match upper.or lower with
    | some demand => .ok demand.event
    | none => .error "The actual original choice has no current action."

private def dataEvent (config : Check.CampusTCPTwoTransferMonitor.Config) :
    Check.CampusTCPTwoTransferMonitor.Demand → Except String M.Event
  | .exchange (.forward demand) | .exchange (.reverse demand) => localEvent demand
  | .exchange (.reverseWrite actor bytes) => .ok (.write actor bytes)
  | .transfer control => .ok (control.event config)
  | .drain ticket => .ok (.serve ticket none)

private def reject (effect : Except Check.CampusTCPModel.Error α) (message : String) : IO Unit :=
  match effect with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def controlFrames (actual : M.Step input) : IO Unit := do
  for actor in ([.client, .server] : List M.Actor) do
    let old ← endpoint actual.before actor
    let next ← endpoint actual.result.state actor
    let oldSteps ← history actual.before actor
    let nextSteps ← history actual.result.state actor
    ensure (old == next && oldSteps == nextSteps)
      "Transfer controls must retain the same actual endpoint state and complete local history."
  ensure (actual.before.custody.pending.map (·.id) == actual.result.state.custody.pending.map (·.id) &&
      actual.before.work.pending.map (·.id) == actual.result.state.work.pending.map (·.id) &&
      actual.result.output.isNone && actual.result.receipt.isNone && actual.result.read.isEmpty)
    "Transfer controls must retain the current packets and work without an invented operation."
  match event : actual.event with
  | .stageCheckpoint =>
    let some checkpoint := actual.result.checkpoint
      | throw (IO.userError "The actual capture must record its current checkpoint.")
    ensure (checkpoint.snapshot.source.same actual.before.primary.transport &&
        checkpoint.snapshot.cut == actual.before.primary.history.length)
      "Capture must select the actual mixed startup and data transport history."
  | .installCheckpoint ns =>
    match present : actual.result.installation with
    | none => throw (IO.userError "The actual install result must remain recorded.")
    | some installed =>
      let _ := Check.CampusTCPTransferFacts.installation_origin actual ns event installed present
      ensure (actual.before.outstanding .primary == 0 && actual.result.state.primarySealed &&
          actual.result.state.standby.transport.same installed.checkpoint.snapshot.source)
        "Installation must copy the drained actual primary snapshot and seal its source."
  | .fencePrimary => ensure actual.result.state.primaryFenced "The actual primary must be fenced."
  | .resume =>
    ensure (!actual.result.state.assignmentPaused && actual.result.state.primaryFenced)
      "Resumption must retain the primary fence."
  | _ => pure ()

private def timeoutFrames (actual : M.Step input) : IO Unit := do
  let before ← endpoint actual.before .client
  let after ← endpoint actual.result.state .client
  let some old := before.recovery | throw (IO.userError "The actual timeout needs its retained sender recovery.")
  let some next := after.recovery | throw (IO.userError "The timeout must retain the updated sender recovery.")
  let head :: tail := old.outstanding | throw (IO.userError "The actual timeout must select the current head.")
  let some produced := actual.result.output | throw (IO.userError "The actual timeout must emit its head retry.")
  ensure (old.rto == 3000 && old.now == 4000 &&
      produced.output.packet.segment.payload == before.core.sent.take head.count &&
      next.outstanding == { head with lastAt := old.now, retried := true } :: tail &&
      next.rto == 6000 && next.estimator == old.estimator && next.lastSample == old.lastSample &&
      next.nextId == old.nextId && next.frontier == old.frontier)
    "The covering-ACK loss must expire the inherited RTO and preserve actual head, tail, and Karn metadata."

private def continueData (initial : Run input config) (oldService : Nat) : IO (Run input config) := do
  let mut current := initial
  let dataStart := initial.report.steps.length
  let oldClient ← endpoint initial.report.final .client
  let oldServer ← endpoint initial.report.final .server
  let mut dataDropped := false
  let mut gapAck := false
  let mut nativeChecked := false
  let mut replayChecked := false
  let mut held : Option (Check.CampusTCPModel.State input) := none
  let mut heldPacket : Option Nat := none
  let mut forwardWriter : Option TCP.ApplicationTrace.Step := none
  let mut reverseWriter : Option TCP.ApplicationTrace.Step := none
  for operation in operations initial.report.steps .client do
    if operation.event == .write (config.transfer.lower ++ config.transfer.upper) then forwardWriter := some operation
  for _ in List.range 2048 do
    match current.monitor with
    | .data handoff monitor =>
      unless monitor.mode == .finished && monitor.exchange.mode == .done do
        ensure (monitor.mode != .invalid && monitor.exchange.mode != .invalid)
          "The same whole monitor must retain its actual transfer phase."
        let dataConfig := config.transfer.data handoff
        let localConfig := dataConfig.at current.report.final
        if monitor.mode == .armed && Check.CampusTCPTwoTransferMonitor.transferDue monitor.exchange then
          let receiver ← endpoint current.report.final .server
          let sender ← endpoint current.report.final .client
          ensure (monitor.exchange.forward.upper.phase == .done && monitor.exchange.forward.lower.phase == .dataIngress &&
              receiver.core.received.isEmpty && receiver.receiveStore.held.flatMap (·.bytes) == config.transfer.upper &&
              sender.core.sent == config.transfer.lower ++ config.transfer.upper)
            "The real transfer cut must retain held upper and the pending lower original."
          held := some current.report.final
          heldPacket := Check.CampusTCPTwoProgressMonitor.exposedPacket localConfig.forward current.report.final monitor.exchange.forward.lower
        if monitor.mode == .install then
          reject (Check.CampusTCPModel.step input current.report.final
            (.installCheckpoint { config.transfer.executionNS with birth := config.transfer.executionNS.birth + 1 }))
            "Installation into another namespace lifetime must reject the actual checkpoint."
        let some demanded := Check.CampusTCPTwoTransferMonitor.nextDemand dataConfig current.report.final monitor
          | throw (IO.userError "The unfinished actual data phase must have a current demand.")
        let mut loss : Option Nat := none
        if !dataDropped && monitor.mode == .finished && monitor.exchange.mode == .forward then
          if let some lane := monitor.exchange.forward.ack then
            if lane.phase == .ackIngress then
              let receiver ← endpoint current.report.final .server
              if receiver.core.received == config.transfer.lower ++ config.transfer.upper then
                loss := Check.CampusTCPTwoProgressMonitor.exposedPacket localConfig.forward current.report.final lane
        let event ← match loss with
          | some id => pure (.dropPacket id)
          | none => load (dataEvent dataConfig demanded)
        let oldLength := current.report.steps.length
        let (moved, actual) ← appendStep current event
        ensure (moved.report.steps.length == oldLength + 1)
          "Every selected operation must append exactly the same actual campus step."
        if loss.isSome then
          ensure (actual.result.state.custody.dropped == 2 && monitor.exchange.forward.drops.isEmpty)
            "The covering ACK must spend only the one remaining whole-report loss."
          dataDropped := true
        match demanded, event with
        | .transfer _, .advanceClock .. => pure ()
        | .transfer _, _ => controlFrames actual
        | _, _ => pure ()
        match event with
        | .timeout .client true => timeoutFrames actual
        | .deliver .. =>
          if monitor.exchange.mode == .forward then
            if let some lane := monitor.exchange.forward.ack then
              if lane.phase == .ackLink then
                let receiver ← endpoint actual.before .server
                if receiver.core.received.isEmpty then
                  let sender ← endpoint actual.before .client
                  let after ← endpoint actual.result.state .client
                  let some beforeRuntime := sender.recovery | throw (IO.userError "The gap ACK needs the actual sender runtime.")
                  let some afterRuntime := after.recovery | throw (IO.userError "The gap ACK must retain actual sender recovery.")
                  ensure (beforeRuntime.rto == 3000 && afterRuntime.rto == 3000 &&
                      afterRuntime.duplicateAcks == beforeRuntime.duplicateAcks + 1 && monitor.exchange.forward.drops.isEmpty)
                    "The zero ACK must retain the inherited timer and create no loss credit."
                  gapAck := true
        | .write .server bytes =>
          ensure (monitor.exchange.mode == .needWrite && bytes == config.transfer.reverseLower ++ config.transfer.reverseUpper)
            "The actual reverse write must follow the forward read."
          match actual.result.application with
          | some (.server, writer) => reverseWriter := some writer
          | _ => throw (IO.userError "The actual reverse write must retain its stored local operation.")
        | _ => pure ()
        if actual.before.primaryFenced then
          if let some served := actual.result.service then
            ensure (served.ticket.value.gateway == .standby)
              "Every real service after the primary fence must use standby."
        current := moved
        match current.monitor with
        | .data _ next =>
          if next.mode == .finished && !nativeChecked then
            let some old := held | throw (IO.userError "The actual held transfer state must remain retained.")
            ensure (current.report.final.owner .client == .standby && current.report.final.owner .server == .standby &&
                current.report.final.primaryFenced && current.report.final.primarySealed &&
                current.report.final.standby.transport.same old.primary.transport &&
                Check.CampusTCPTwoProgressMonitor.exposedPacket (dataConfig.at current.report.final).forward
                  current.report.final next.exchange.forward.lower == heldPacket)
              "The actual standby must retain the copied state and original lower custody."
            for actor in ([.client, .server] : List M.Actor) do
              let before ← endpoint old actor
              let after ← endpoint current.report.final actor
              ensure (before == after) "The seven actual controls must retain both endpoint states."
            nativeChecked := true
          if next.mode == .finished && !replayChecked then
            let some served := current.report.final.services[oldService]?
              | throw (IO.userError "The dropped original SYNACK service must remain in actual history.")
            let some emission := served.evidence.output
              | throw (IO.userError "The dropped original SYNACK must retain its real emitted bytes.")
            reject (Check.CampusTCPModel.step input current.report.final (.deliver oldService emission.bytes true))
              "A dropped startup link must not revive after the actual drain and transfer."
            replayChecked := true
        | _ => throw (IO.userError "The data continuation must retain its same handoff.")
    | _ => throw (IO.userError "The continuation must remain in the whole data monitor.")
  let .data handoff monitor := current.monitor
    | throw (IO.userError "The completed report must retain the original startup handoff.")
  ensure (monitor.mode == .finished && monitor.exchange.mode == .done && dataDropped && gapAck && nativeChecked && replayChecked)
    "The same report must complete startup, held-gap transfer, and both reads."
  let dataSteps := current.report.steps.drop dataStart
  let ids := dropIDs current.report.steps
  ensure (ids.length == 2 && ids.eraseDups == ids && current.report.final.custody.dropped == 2 &&
      startupTimeouts current.report.steps == 2 && dataTimeouts dataSteps == 1 && monitor.exchange.timeouts == 1 &&
      monitor.exchange.drops == dropIDs dataSteps && handoff.startupDrops == 1 &&
      monitor.exchange.slots == dataSteps.length && current.report.steps.all (fun actual => match actual.event with | .copyPacket .. => false | _ => true))
    "The complete history must retain two startup expiries, one data expiry, and two distinct shared losses."
  let expected : List Check.CampusTCPTwoTransferMonitor.Control := [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume]
  ensure (monitor.controls.map (·.1) == expected && current.report.final.work.pending.isEmpty && current.report.final.custody.pending.isEmpty)
    "All seven controls must be ordered and all actual packet work retired."
  let client := operations current.report.steps .client
  let server := operations current.report.steps .server
  let some firstWriter := forwardWriter | throw (IO.userError "The selected actual forward write is missing.")
  let some secondWriter := reverseWriter | throw (IO.userError "The selected actual reverse write is missing.")
  let finalClientHistory ← history current.report.final .client
  let finalServerHistory ← history current.report.final .server
  let readSteps := current.report.steps.filter fun actual => !actual.result.read.isEmpty
  ensure (server.flatMap TCP.ApplicationTrace.Step.readBytes == config.transfer.lower ++ config.transfer.upper &&
      client.flatMap TCP.ApplicationTrace.Step.readBytes == config.transfer.reverseLower ++ config.transfer.reverseUpper &&
      finalClientHistory.any (fun operation => operation == firstWriter) && finalServerHistory.any (fun operation => operation == secondWriter) &&
      readSteps.map (·.result.read) == [config.transfer.lower ++ config.transfer.upper, config.transfer.reverseLower ++ config.transfer.reverseUpper])
    "Both exact reads and their selected actual writers must remain in the same ordered report."
  for actor in ([.client, .server] : List M.Actor) do
    let before := if actor == .client then oldClient else oldServer
    let after ← endpoint current.report.final actor
    let some oldRecovery := before.recovery | throw (IO.userError "The setup runtime must remain available.")
    let some recovery := after.recovery | throw (IO.userError "Final recovery must remain enabled.")
    ensure (after.pending.isEmpty && after.core.sent.isEmpty && after.core.received.isEmpty && after.receiveStore.held.isEmpty &&
        recovery.outstanding.isEmpty && recovery.deadline.isNone && recovery.nextId == oldRecovery.nextId + 2 &&
        recovery.frontier == oldRecovery.frontier + 2 && after.receiveStore.frontier == before.receiveStore.frontier + 2 &&
        after.receiveStore.nextID == before.receiveStore.nextID + 2)
      "Both final endpoints must retire the real record and allocation identities."
  ensure (W.actions config input.initial (W.initial config) current.report.steps)
    "The one complete actual report must pass its whole action check."
  ensure (W.check config input.initial (W.initial config) current.report.steps 12)
    "The one complete actual report must pass its whole B12 service check."
  IO.println s!"Startup through transfer: {current.report.steps.length} actual slots, 2 shared drops, 2 startup expiries and 1 data expiry."
  return current

structure Completed where
  source : Check.CampusTCP.Input
  config : C.Config
  events : List M.Event
  report : M.Report source.model events
  supported : report.supported = true
  finished : report.remaining = []

def completedInput (source : Check.CampusTCP.Input) : IO Completed := do
  let config ← load (configuration source)
  let (written, oldService) ← twoTimers source.model config
  let completed ← continueData written oldService
  return ⟨source, config, completed.events, completed.report, completed.supported, completed.finished⟩

def runInput (source : Check.CampusTCP.Input) : IO Unit := do
  let _ ← completedInput source

def run : IO Unit := do
  let source ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/campus-tcp-transfer/trace.json"))
  runInput source

end NetlibTest.CampusTCPStartupEndToEnd
