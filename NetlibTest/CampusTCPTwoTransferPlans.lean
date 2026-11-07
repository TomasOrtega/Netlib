import NetlibTest.CampusTCPTwoProgressInitial
import Netlib.Check.CampusTCPTwoExchangeSetup
import Netlib.Check.CampusTCPTwoTransferMonitor
import Netlib.Check.CampusTCPTransferFacts

/-!
# Actual two-way exchanges through a held-gap transfer

The seven controls retain the same endpoints and pending lower output.
Each continuation uses one stored report and one shared loss allowance.
-/

namespace NetlibTest.CampusTCPTwoTransferPlans

open Netlib Packet Protocol

namespace M
export Check.CampusTCPModel (Input State Event Step Actor Gateway)
end M
namespace R
export NetlibTest.CampusTCPRecoveryRound (Checked appendOne endpoint ensure load verify)
end R
namespace I
export NetlibTest.CampusTCPTwoProgressInitial (Witness construct)
export NetlibTest.CampusTCPGapProgressInitial (fixturePayload)
end I
namespace T
export Check.CampusTCPTwoTransferMonitor
  (Config Monitor Demand Control nextDemand allowed observe actions check check_correct controlDemand transferDue)
end T
namespace X
export Check.CampusTCPTwoExchangeMonitor (Demand)
end X
namespace L
export Check.CampusTCPTwoProgressMonitor (Demand exposedPacket)
end L

private inductive Loss where
  | lowerIngress | coveringAck | gapAck | reverseLower | reverseUpper | earlyLowerIngress
  deriving Repr, BEq, DecidableEq

private structure Plan where
  name : String
  losses : List Loss := []
  stale : Bool := false
  pendingPrimary : Bool := false
  postReadClocks : Nat := 0

private def ingress (input : M.Input) (gateway : M.Gateway) (actor : M.Actor) : Except String IngressAttachment.InterfaceRef := do
  let some value := (input.deployment gateway).specifications.find? (fun value => value.direction == actor.direction)
    | throw "The current gateway has no selected ingress specification."
  return value.ingress

private def configuration {input : M.Input} {events : List M.Event} {report : Check.CampusTCPModel.Report input events}
    {count : Nat} {lower upper : List UInt8}
    (witness : I.Witness report count .client .primary lower upper) : Except String T.Config := do
  let pc ← ingress input .primary .client
  let ps ← ingress input .primary .server
  let sc ← ingress input .standby .client
  let ss ← ingress input .standby .server
  return {
    exchange := Check.CampusTCPTwoExchangeSetup.config witness.initial witness.native 10 2
      (I.fixturePayload 81 600) (I.fixturePayload 97 600)
    ingress := fun gateway actor => match gateway, actor with
      | .primary, .client => pc | .primary, .server => ps
      | .standby, .client => sc | .standby, .server => ss
    executionNS := (input.deployment .standby).executionNS }

private def localEvent : L.Demand → Except String M.Event
  | .single demand => .ok demand.event
  | .originalChoice lower upper =>
    match upper.or lower with
    | some demand => .ok demand.event
    | none => .error "The current original choice has no event."

private def exchangeEvent : X.Demand → Except String M.Event
  | .forward demand | .reverse demand => localEvent demand
  | .reverseWrite actor bytes => .ok (.write actor bytes)

private def demandEvent (config : T.Config) : T.Demand → Except String M.Event
  | .exchange demand => exchangeEvent demand
  | .transfer control => .ok (control.event config)
  | .drain ticket => .ok (.serve ticket none)

private def history (state : M.State input) (actor : M.Actor) : Except String (List TCP.ApplicationTrace.Step) :=
  match state.connection with
  | .startup .. => .error "The actual connection is not established."
  | .application _ endpoints => .ok (Check.CampusTCPEnabled.applicationSteps endpoints actor)

private def dropIDs (steps : List (M.Step input)) : List Nat := steps.filterMap fun actual =>
  match actual.event with | .dropPacket id => some id | _ => none

private def timeoutCount (steps : List (M.Step input)) : Nat :=
  (steps.filter fun actual => match actual.event with | .timeout _ true => true | _ => false).length

private def operations (steps : List (M.Step input)) (actor : M.Actor) : List TCP.ApplicationTrace.Step :=
  steps.filterMap fun actual => match actual.result.application with
    | some (selected, value) => if selected == actor then some value else none
    | none => none

private def selectedLoss (config : T.Config) (state : M.State input) (monitor : T.Monitor) (loss : Loss) : IO (Option Nat) := do
  let current := config.at state
  if loss == .earlyLowerIngress then
    if monitor.mode == .armed && monitor.exchange.mode == .forward &&
        monitor.exchange.forward.lower.phase == .dataIngress && monitor.exchange.forward.upper.phase == .needSend then
      return L.exposedPacket current.forward state monitor.exchange.forward.lower
    return none
  if monitor.mode != .finished then return none
  match loss with
  | .lowerIngress =>
    if monitor.exchange.mode == .forward && monitor.exchange.forward.lower.phase == .dataIngress then
      return L.exposedPacket current.forward state monitor.exchange.forward.lower
    return none
  | .coveringAck | .gapAck =>
    unless monitor.exchange.mode == .forward do return none
    let some lane := monitor.exchange.forward.ack | return none
    unless lane.phase == .ackIngress do return none
    let receiver ← R.load (R.endpoint state .server)
    let covered := receiver.core.received.length == current.forward.bytes.length
    if (loss == .coveringAck && covered) || (loss == .gapAck && receiver.core.received.isEmpty) then
      return L.exposedPacket current.forward state lane
    return none
  | .reverseLower =>
    if monitor.exchange.mode == .reverse && monitor.exchange.reverse.lower.phase == .dataIngress then
      return L.exposedPacket (current.reverse monitor.exchange.forward.drops.length) state monitor.exchange.reverse.lower
    return none
  | .reverseUpper =>
    if monitor.exchange.mode == .reverse && monitor.exchange.reverse.upper.phase == .dataIngress then
      return L.exposedPacket (current.reverse monitor.exchange.forward.drops.length) state monitor.exchange.reverse.upper
    return none
  | .earlyLowerIngress => return none

private def reject (value : Except Check.CampusTCPModel.Error α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def controlFrames (actual : M.Step input) : IO Unit := do
  for actor in ([.client, .server] : List M.Actor) do
    let before ← R.load (R.endpoint actual.before actor)
    let after ← R.load (R.endpoint actual.result.state actor)
    let oldHistory ← R.load (history actual.before actor)
    let newHistory ← R.load (history actual.result.state actor)
    R.ensure (before == after && oldHistory == newHistory)
      "A transfer control must retain the complete actual endpoint and application history."
  R.ensure (actual.before.custody.pending.map (·.id) == actual.result.state.custody.pending.map (·.id) &&
      actual.before.work.pending.map (·.id) == actual.result.state.work.pending.map (·.id) &&
      actual.result.output.isNone && actual.result.receipt.isNone && actual.result.read.isEmpty)
    "A transfer control must retain pending custody and tickets without a new packet or read."
  match event : actual.event with
  | .stageCheckpoint =>
    match present : actual.result.checkpoint with
    | none => throw (IO.userError "The actual capture has no checkpoint.")
    | some checkpoint =>
      let _ := Check.CampusTCPTransferFacts.checkpoint_origin actual event checkpoint present
      R.ensure (checkpoint.snapshot.source.same actual.before.primary.transport &&
          checkpoint.snapshot.cut == actual.before.primary.history.length)
        "Capture must retain the actual current primary transport cut."
  | .installCheckpoint ns =>
    match present : actual.result.installation with
    | none => throw (IO.userError "The actual installation result is absent.")
    | some value =>
      let _ := Check.CampusTCPTransferFacts.installation_origin actual ns event value present
      R.ensure (actual.before.outstanding .primary == 0 && actual.result.state.primarySealed &&
          actual.result.state.standby.transport.same value.checkpoint.snapshot.source)
        "Installation must copy the drained actual checkpoint and seal its primary source."
  | .fencePrimary =>
    let _ := Check.CampusTCPTransferFacts.fence_origin actual event
    R.ensure (actual.result.state.primaryFenced) "The actual primary must be fenced."
  | .resume =>
    let _ := Check.CampusTCPTransferFacts.resume_origin actual event
    R.ensure (!actual.result.state.assignmentPaused && actual.result.state.primaryFenced)
      "Actual assignment resumption must retain the primary fence."
  | _ => pure ()

private def checkTimeout (actual : M.Step input) (actor : M.Actor) : IO Unit := do
  let before ← R.load (R.endpoint actual.before actor)
  let after ← R.load (R.endpoint actual.result.state actor)
  let some old := before.recovery | throw (IO.userError "The actual timeout has no old recovery.")
  let some next := after.recovery | throw (IO.userError "The actual timeout has no new recovery.")
  let head :: tail := old.outstanding | throw (IO.userError "The actual timeout has no head.")
  let some output := actual.result.output | throw (IO.userError "The actual timeout has no packet.")
  R.ensure (output.output.packet.segment.payload == before.core.sent.take head.count &&
      next.outstanding == { head with lastAt := old.now, retried := true } :: tail &&
      next.nextId == old.nextId && next.frontier == old.frontier && next.rto == 2 * old.rto &&
      next.estimator == old.estimator && next.lastSample == old.lastSample)
    "Timeout must use the same actual head and retain its prior recovery history."

private def runCase (input : Check.CampusTCP.Input) (plan : Plan) : IO Unit := do
  let initialEvents := if plan.stale then input.events.take 31 ++ [.stageCheckpoint] ++ (input.events.drop 31).take 1
    else input.events.take 32
  let report ← match input.model.check initialEvents with
    | .error reason => throw (IO.userError reason.message)
    | .ok report => pure report
  let lower := I.fixturePayload 17 400
  let upper := I.fixturePayload 33 400
  let reverseBytes := I.fixturePayload 81 600 ++ I.fixturePayload 97 600
  let witness ← R.load (I.construct report report.steps.length .client .primary lower upper)
  let config ← R.load (configuration witness)
  let earlyLower := plan.losses.contains .earlyLowerIngress
  let mut current := witness.checked
  let mut monitor : T.Monitor := .initial
  let mut remaining := plan.losses
  let mut held : Option (M.State input.model) := none
  let mut heldPacket : Option Nat := none
  let mut heldOutput : Option Nat := none
  let mut staleChecked := false
  let mut nativeChecked := false
  let mut reverseWriter : Option TCP.ApplicationTrace.Step := none
  let mut zeroCreditChecked := false
  let mut drainedLower := false
  let mut upperAfterTransfer := false
  let mut upperAssignedAfterTransfer := false
  let mut postReadClocks := 0
  for _ in List.range 2048 do
    unless monitor.mode == .finished && monitor.exchange.mode == .done do
      R.ensure (!(monitor.mode == .invalid)) "The transfer selector must retain its actual phase."
      if monitor.mode == .armed && T.transferDue monitor.exchange then
        let sender ← R.load (R.endpoint current.report.final .client)
        let receiver ← R.load (R.endpoint current.report.final .server)
        let some recovery := sender.recovery | throw (IO.userError "The held cut has no sender recovery.")
        let some output := monitor.exchange.forward.lower.refs.dataOutput
          | throw (IO.userError "The original lower output reference is absent at transfer.")
        let packet := L.exposedPacket (config.at current.report.final).forward current.report.final monitor.exchange.forward.lower
        if earlyLower then
          let senderHistory ← R.load (history current.report.final .client)
          R.ensure (current.recorded.length == 2 && monitor.exchange.forward.lower.phase == .done &&
              monitor.exchange.forward.upper.phase == .needSend && monitor.exchange.forward.upper.refs.dataOutput.isNone &&
              current.report.final.outputs.length == witness.current.cut.report.final.outputs.length + 1 &&
              sender.pending == upper && sender.core.sent == lower && recovery.outstanding.length == 1 &&
              receiver.core.received.isEmpty && receiver.receiveStore.held.isEmpty &&
              current.report.final.outstanding .primary == 0 && packet.isNone &&
              senderHistory.any (fun operation => operation == witness.initial.write.writer))
            "An early lower drop must trigger transfer before the selected batch emits upper."
        else
          let location := if plan.pendingPrimary then
              current.recorded.length == 6 && monitor.exchange.forward.lower.phase == .dataTicket &&
                current.report.final.outstanding .primary == 1 && packet.isNone
            else current.recorded.length == 5 && monitor.exchange.forward.lower.phase == .dataIngress &&
              current.report.final.outstanding .primary == 0 && packet.isSome
          R.ensure (location && monitor.exchange.forward.upper.phase == .done && sender.core.sent == lower ++ upper &&
              sender.pending.isEmpty && recovery.outstanding.length == 2 && receiver.core.received.isEmpty &&
              receiver.receiveStore.held.flatMap (·.bytes) == upper)
            "The actual transfer cut must retain held upper, both original records, and the selected lower path."
        held := some current.report.final
        heldPacket := packet
        heldOutput := some output
      if plan.stale && monitor.mode == .capture && !staleChecked then
        let some checkpoint := current.report.final.cache | throw (IO.userError "The old actual checkpoint is absent.")
        R.ensure (!(current.report.final.primary.transport.same checkpoint.snapshot.source))
          "The intervening upper service must make the old actual capture stale."
        match Check.CampusTCPModel.step input.model current.report.final (.installCheckpoint config.executionNS) with
        | .error reason =>
          R.ensure (reason.message == TCP.Checkpoint.Error.staleSource.message)
            "The actual stale installation must fail its source comparison."
        | .ok _ => throw (IO.userError "A stale capture must not install after the actual upper service.")
        staleChecked := true
      if monitor.mode == .install then
        reject (Check.CampusTCPModel.step input.model current.report.final
          (.installCheckpoint { config.executionNS with birth := config.executionNS.birth + 1 }))
          "A different actual target namespace lifetime must reject installation."
      let some demand := T.nextDemand config current.report.final monitor
        | throw (IO.userError "The current transfer exchange has no demand.")
      if monitor.mode == .finished && monitor.exchange.mode == .reverse && monitor.exchange.forward.drops.length == 2 then
        for lane in [monitor.exchange.reverse.lower, monitor.exchange.reverse.upper, monitor.exchange.reverse.retry] do
          if let some id := L.exposedPacket ((config.at current.report.final).reverse 2) current.report.final lane then
            R.ensure (!(T.allowed config current.report.final monitor (.dropPacket id)))
              "The reverse selector must reject a drop after global credit is exhausted."
            zeroCreditChecked := true
      let loss ← match remaining with
        | [] => pure none
        | selected :: _ => selectedLoss config current.report.final monitor selected
      let event ← match loss with
        | some id => pure (.dropPacket id)
        | none =>
          if monitor.exchange.mode == .needWrite && postReadClocks < plan.postReadClocks then
            let actor : M.Actor := if postReadClocks % 2 == 0 then .client else .server
            let state ← R.load (R.endpoint current.report.final actor)
            pure (.advanceClock actor (state.now + 10))
          else if plan.pendingPrimary && monitor.mode == .armed && monitor.exchange.mode == .forward &&
              monitor.exchange.forward.lower.phase == .dataIngress && monitor.exchange.forward.upper.phase == .dataIngress then
            let some lowerDemand := Check.CampusTCPTwoProgressMonitor.laneDemand
                (config.at current.report.final).forward current.report.final monitor.exchange.forward monitor.exchange.forward.lower
              | throw (IO.userError "The actual lower ingress has no assignment demand.")
            pure lowerDemand.event
          else R.load (demandEvent config demand)
      R.ensure (T.allowed config current.report.final monitor event) "Each actual transfer exchange event must pass its current guard."
      let moved ← R.appendOne current event
      if plan.pendingPrimary && moved.actual.before.assignmentPaused then
        if let some served := moved.actual.result.service then
          R.ensure (some served.ticket.value.outputIndex == heldOutput && served.ticket.value.gateway == .primary &&
              moved.actual.result.state.outstanding .primary == 0)
            "The actual paused drain must service the retained lower primary ticket."
          drainedLower := true
      match demand, loss with
      | .transfer _, none => controlFrames moved.actual
      | _, _ => pure ()
      match event with
      | .timeout actor true => checkTimeout moved.actual actor
      | .advanceClock actor millis =>
        if monitor.exchange.mode == .needWrite then
          let before ← R.load (R.endpoint moved.actual.before actor)
          let after ← R.load (R.endpoint moved.actual.result.state actor)
          let peerBefore ← R.load (R.endpoint moved.actual.before actor.other)
          let peerAfter ← R.load (R.endpoint moved.actual.result.state actor.other)
          R.ensure (millis == before.now + 10 &&
              after == { before with recovery := before.recovery.map (fun recovery => { recovery with now := millis }) } &&
              peerAfter == peerBefore)
            "A clock before the reverse write must retain both actual endpoint histories and recovery fields."
          postReadClocks := postReadClocks + 1
      | .send .client count true =>
        if earlyLower && monitor.mode == .finished && monitor.exchange.mode == .forward then
          let some output := moved.actual.result.output | throw (IO.userError "The actual upper send has no output.")
          R.ensure (monitor.exchange.forward.upper.phase == .needSend && count == upper.length &&
              output.output.packet.segment.payload == upper && moved.actual.before.owner .client == .standby)
            "The deferred upper send must use the same batch at the actual standby owner."
          upperAfterTransfer := true
      | .assign output selectedIngress =>
        if earlyLower && monitor.mode == .finished && monitor.exchange.mode == .forward &&
            monitor.exchange.forward.upper.phase == .dataIngress then
          R.ensure (monitor.exchange.forward.upper.refs.dataOutput == some output &&
              selectedIngress == config.ingress .standby .client && moved.actual.before.owner .client == .standby)
            "The deferred upper assignment must use the actual standby ingress."
          upperAssignedAfterTransfer := true
      | .write .server bytes =>
        R.ensure (monitor.exchange.mode == .needWrite && bytes == reverseBytes)
          "The actual reverse write must follow the completed forward read."
        match moved.actual.result.application with
        | some (.server, writer) => reverseWriter := some writer
        | _ => throw (IO.userError "The real reverse write has no stored server operation.")
      | _ => pure ()
      monitor := T.observe config monitor moved.actual
      current := moved.next
      if loss.isSome then remaining := remaining.drop 1
      if monitor.mode == .finished && !nativeChecked then
        let some before := held | throw (IO.userError "The actual held transfer cut was not retained.")
        let some output := heldOutput | throw (IO.userError "The actual lower output reference was not retained.")
        for actor in ([.client, .server] : List M.Actor) do
          let old ← R.load (R.endpoint before actor)
          let next ← R.load (R.endpoint current.report.final actor)
          R.ensure (old == next) "All seven controls must retain the same actual endpoint state."
        let retainedPath := if earlyLower then
            monitor.exchange.forward.lower.phase == .done && monitor.exchange.forward.upper.phase == .needSend &&
              current.report.final.outputs.length == before.outputs.length &&
              current.report.final.standby.transport.same before.primary.transport
          else if plan.pendingPrimary then
            drainedLower && monitor.exchange.forward.lower.phase == .dataLink &&
              current.report.final.outstanding .primary == 0 &&
              current.report.final.standby.transport.same current.report.final.primary.transport
          else current.report.final.custody.pendingID (Check.CampusTCPModel.Transit.ingressAt output) == heldPacket &&
            current.report.final.standby.transport.same before.primary.transport
        R.ensure (current.report.final.owner .client == .standby && current.report.final.owner .server == .standby &&
            current.report.final.primaryFenced && current.report.final.primarySealed && retainedPath)
          "The installed standby must retain the actual copied ranges and current lower path."
        for actor in ([.client, .server] : List M.Actor) do
          let _ ← R.load (CampusTCPRoundTheorem.native (input.model.contextFor .standby)
            (Check.CampusTCPModel.beforeService input.model current.report.final .standby)
            (config.ingress .standby actor) witness.initial.gatewayState.session.entry actor.direction actor.nextHop)
        nativeChecked := true
      if fenced : moved.actual.before.primaryFenced = true then
        match present : moved.actual.result.service with
        | none => pure ()
        | some served =>
          let _ := Check.CampusTCPTransferFacts.service_after_fence moved.actual served present fenced
          R.ensure (served.ticket.value.gateway == .standby) "Every actual service after the fence must use standby."
  R.ensure (monitor.mode == .finished && monitor.exchange.mode == .done && remaining.isEmpty && nativeChecked &&
      (!plan.stale || staleChecked)) "The same actual exchange must complete after its seven controls and selected losses."
  if earlyLower then
    R.ensure (upperAfterTransfer && upperAssignedAfterTransfer)
      "The same early-drop trace must emit and assign upper only after transfer."
  R.ensure (postReadClocks == plan.postReadClocks)
    "The same actual report must include every selected clock before the reverse write."
  let expected : List T.Control := [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume]
  R.ensure (monitor.controls.map (·.1) == expected && monitor.exchange.slots == current.recorded.length)
    "The same whole monitor must retain all seven actual control slots."
  let ids := dropIDs current.recorded
  R.ensure (ids == monitor.exchange.drops && ids.eraseDups == ids && ids.length == plan.losses.length &&
      ids.length ≤ 2 && timeoutCount current.recorded == monitor.exchange.timeouts &&
      monitor.exchange.timeouts ≤ ids.length &&
      monitor.exchange.drops == monitor.exchange.forward.drops ++ monitor.exchange.reverse.drops)
    "Transfer and reverse write must retain one shared actual drop and timeout history."
  if monitor.exchange.forward.drops.length == 2 then
    R.ensure zeroCreditChecked "A zero-credit reverse packet must exercise actual drop rejection."
  for actor in ([.client, .server] : List M.Actor) do
    let state ← R.load (R.endpoint current.report.final actor)
    let old ← R.load (R.endpoint witness.current.cut.report.final actor)
    let some recovery := state.recovery | throw (IO.userError "The final actual endpoint has no recovery.")
    let some oldRecovery := old.recovery | throw (IO.userError "The initial actual endpoint has no recovery.")
    let sent := if actor == .client then (lower ++ upper).length else reverseBytes.length
    let received := if actor == .client then reverseBytes.length else (lower ++ upper).length
    R.ensure (state.pending.isEmpty && state.core.sent.isEmpty && state.core.received.isEmpty && state.receiveStore.held.isEmpty &&
        recovery.outstanding.isEmpty && recovery.deadline.isNone && recovery.lastTimedOut.isNone && recovery.timeoutCount == 0 &&
        recovery.nextId == oldRecovery.nextId + 2 && recovery.frontier == oldRecovery.frontier + sent &&
        state.receiveStore.frontier == old.receiveStore.frontier + received && state.receiveStore.nextID == old.receiveStore.nextID + 2)
      "Both final actual endpoints must retain retired ledgers and empty new byte stores."
  let client := operations current.recorded .client
  let server := operations current.recorded .server
  let some writer := reverseWriter | throw (IO.userError "The same actual reverse writer was not retained.")
  let clientHistory ← R.load (history current.report.final .client)
  let reads := current.recorded.filterMap fun actual => match actual.event with
    | .read actor count => some (actor, count) | _ => none
  let writes := current.recorded.filterMap fun actual => match actual.event with
    | .write actor bytes => some (actor, bytes) | _ => none
  R.ensure (server.flatMap TCP.ApplicationTrace.Step.readBytes == lower ++ upper &&
      client.flatMap TCP.ApplicationTrace.Step.readBytes == reverseBytes &&
      server.flatMap TCP.ApplicationTrace.Step.releasedPayload == lower ++ upper &&
      client.flatMap TCP.ApplicationTrace.Step.releasedPayload == reverseBytes &&
      (server.filter (fun operation => !operation.readBytes.isEmpty)).length == 1 &&
      (client.filter (fun operation => !operation.readBytes.isEmpty)).length == 1 &&
      server.any (fun operation => operation == writer) && writer.event == .write reverseBytes &&
      clientHistory.any (fun operation => operation == witness.initial.write.writer) &&
      reads == [(.server, (lower ++ upper).length), (.client, reverseBytes.length)] && writes == [(.server, reverseBytes)] &&
      current.recorded.all (fun actual => match actual.event with | .copyPacket .. => false | _ => true) &&
      current.report.final.custody.pending.map (·.id) == witness.current.cut.report.final.custody.pending.map (·.id) &&
      current.report.final.work.pending.map (·.id) == witness.current.cut.report.final.work.pending.map (·.id))
    "The actual report must retain the selected writer, both ordered reads, and prior custody without copies."
  let allowed ← R.load (R.verify (T.actions config witness.current.cut.report.final .initial current.recorded = true)
    "The same actual transfer trace must pass its whole action check.")
  let serviced ← R.load (R.verify (T.check config witness.current.cut.report.final .initial current.recorded 3 = true)
    "The same actual transfer trace must pass one whole persistent service check.")
  let _ := (Check.CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp allowed.property
  let _ := (T.check_correct _ _ _ _ _).mp serviced.property
  let _ := current.suffix
  let _ := witness.initial.write.joint
  IO.println s!"Transfer {plan.name}: {current.recorded.length} actual slots, {ids.length} shared drops, {monitor.exchange.timeouts} funded timeouts."

def runInput (input : Check.CampusTCP.Input) : IO Unit := do
  runCase input { name := "held-upper" }
  runCase input { name := "lower-and-covering-ack", losses := [.lowerIngress, .coveringAck] }
  runCase input { name := "gap-ack-and-reverse-upper", losses := [.gapAck, .reverseUpper] }
  runCase input { name := "stale-source", stale := true }
  runCase input { name := "pending-primary-ticket", pendingPrimary := true }
  runCase input { name := "early-lower-drop", losses := [.earlyLowerIngress] }
  runCase input { name := "clocks-before-reverse-write", postReadClocks := 2 }
  runCase input { name := "both-reverse-originals", losses := [.reverseUpper, .reverseLower] }
  IO.println "Campus actual two-way transfer plans passed."

def run : IO Unit := do
  let input ← R.load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-receive-gaps/trace.json"))
  runInput input

end NetlibTest.CampusTCPTwoTransferPlans
