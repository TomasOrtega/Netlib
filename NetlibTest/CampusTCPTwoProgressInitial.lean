import Netlib.Check.CampusTCPTwoProgressStart
import NetlibTest.CampusTCPGapProgressInitial

namespace NetlibTest.CampusTCPTwoProgressInitial

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input Event Report State Step Applications Actor Gateway)
end M
namespace G
export Check.CampusTCPTwoProgressStart
  (StartupBasis WrittenBatch IdleEndpoint WrittenSender EmptyReceiver GatewayStart Geometry TwoWriteInitial NativeEnv)
end G
namespace A
export TCP.ApplicationTrace (Step Event Chain)
end A
namespace R
export NetlibTest.CampusTCPRecoveryRound (verify load Checked ensure)
end R
namespace I
export NetlibTest.CampusTCPGapProgressInitial (Prefix takePrefix fixturePayload)
end I
open I

variable {input : M.Input} {events : List M.Event}
variable {complete : Check.TCPHandshake.Completed input.active input.passive}

private def completeTag : Check.CampusTCPModel.Connection input.active input.passive →
    Option (Check.TCPHandshake.Completed input.active input.passive)
  | .startup .. | .recovering .. => none
  | .application complete _ => some complete

private theorem application_tag (before : M.State input) (endpoints : M.Applications complete)
    (connection : before.connection = .application complete endpoints)
    (actor : M.Actor) (event : A.Event) (effect : Check.CampusTCPModel.Effect input)
    (computed : Check.CampusTCPModel.applyApplication input before actor event = .ok effect) :
    completeTag effect.state.connection = some complete := by
  cases actor
  all_goals
    simp only [Check.CampusTCPModel.applyApplication, connection] at computed
    repeat' first
      | (solve | cases computed; rfl)
      | (cases computed)
      | (split at computed)
      | (dsimp only [Check.CampusTCPModel.parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem startup_tag (before : M.State input) (endpoints : M.Applications complete)
    (connection : before.connection = .application complete endpoints)
    (event : Check.TCPHandshake.Event) (effect : Check.CampusTCPModel.Effect input)
    (computed : Check.CampusTCPModel.startup input before event = .ok effect) :
    completeTag effect.state.connection = some complete := by
  simp only [Check.CampusTCPModel.startup, connection] at computed
  cases computed
  exact congrArg completeTag connection

private theorem enableAck_tag (before : M.State input) (endpoints : M.Applications complete)
    (connection : before.connection = .application complete endpoints)
    (actor : M.Actor) (effect : Check.CampusTCPModel.Effect input)
    (computed : Check.CampusTCPModel.enableAck input before actor = .ok effect) :
    completeTag effect.state.connection = some complete := by
  unfold Check.CampusTCPModel.enableAck at computed
  rw [connection] at computed
  cases actor
  all_goals
    dsimp only at computed
    repeat' first
      | (solve | exact application_tag before endpoints connection _ _ effect computed)
      | cases computed
      | split at computed

private theorem recovery_tag (before : M.State input) (endpoints : M.Applications complete)
    (connection : before.connection = .application complete endpoints)
    (event : Check.CampusTCPModel.C.Event) (effect : Check.CampusTCPModel.Effect input)
    (computed : Check.CampusTCPModel.runRecovery input before event = .ok effect) :
    completeTag effect.state.connection = some complete := by
  simp only [Check.CampusTCPModel.runRecovery, connection] at computed
  cases computed
  exact congrArg completeTag connection

private theorem openRecovery_tag (before : M.State input) (endpoints : M.Applications complete)
    (connection : before.connection = .application complete endpoints)
    (remote : TCP.Handshake.Socket) (policy : Bool) (effect : Check.CampusTCPModel.Effect input)
    (computed : Check.CampusTCPModel.openRecovering input before remote policy = .ok effect) :
    completeTag effect.state.connection = some complete := by
  simp only [Check.CampusTCPModel.openRecovering, connection] at computed
  split at computed
  · cases computed
  · cases computed; exact congrArg completeTag connection

private theorem startupRecovery_tag (before : M.State input) (endpoints : M.Applications complete)
    (connection : before.connection = .application complete endpoints)
    (actor : M.Actor) (effect : Check.CampusTCPModel.Effect input)
    (computed : Check.CampusTCPModel.enableStartupRecovery input before actor = .ok effect) :
    completeTag effect.state.connection = some complete := by
  unfold Check.CampusTCPModel.enableStartupRecovery at computed
  split at computed
  · cases computed; exact congrArg completeTag connection
  · exact application_tag before endpoints connection actor _ effect computed

private theorem finishStartup_tag (before : M.State input) (endpoints : M.Applications complete)
    (connection : before.connection = .application complete endpoints)
    (effect : Check.CampusTCPModel.Effect input)
    (computed : Check.CampusTCPModel.finishStartup input before = .ok effect) :
    completeTag effect.state.connection = some complete := by
  simp only [Check.CampusTCPModel.finishStartup, connection] at computed
  repeat' first
    | (solve | cases computed; exact congrArg completeTag connection)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

@[simp] private theorem write_connection (before : M.State input) (gateway : Check.CampusTCPModel.Gateway)
    (resident : Check.CampusTCPModel.Local) : (before.write gateway resident).connection = before.connection := by
  cases gateway <;> rfl

private theorem core_tag (before : M.State input) (endpoints : M.Applications complete)
    (connection : before.connection = .application complete endpoints)
    (event : M.Event) (effect : Check.CampusTCPModel.Effect input)
    (computed : Check.CampusTCPModel.processCore input before event = .ok effect) :
    completeTag effect.state.connection = some complete := by
  cases event with
  | «open» remote policy => exact startup_tag before endpoints connection _ effect computed
  | openRecovering remote policy => exact openRecovery_tag before endpoints connection remote policy effect computed
  | startupClock actor millis | startupTimeout actor generation policy =>
    exact recovery_tag before endpoints connection _ effect computed
  | finishStartup => exact finishStartup_tag before endpoints connection effect computed
  | enableStartupRecovery actor => exact startupRecovery_tag before endpoints connection actor effect computed
  | write actor bytes | send actor count policy | enableRecovery actor | dispatchAck actor policy
  | advanceClock actor millis | timeout actor policy | read actor count | emitAck actor policy =>
    exact application_tag before endpoints connection actor _ effect computed
  | enableAck actor => exact enableAck_tag before endpoints connection actor effect computed
  | copyPacket id | dropPacket id =>
    cases computed
    exact congrArg completeTag connection
  | _ =>
    simp only [Check.CampusTCPModel.processCore, Check.CampusTCPModel.installConfiguration,
      Check.CampusTCPModel.stageAttachment, Check.CampusTCPModel.installIngress,
      Check.CampusTCPModel.transferControl] at computed
    repeat' first
      | (solve | simpa only [completeTag, Check.CampusTCPModel.unsupported] using congrArg completeTag connection)
      | (solve | cases computed; simpa only [write_connection, completeTag] using congrArg completeTag connection)
      | (solve | cases computed; simpa only [completeTag] using application_tag before endpoints connection _ _ _ (by assumption))
      | (solve | cases computed; simpa only [completeTag] using startup_tag before endpoints connection _ _ (by assumption))
      | (solve | cases computed; simpa only [completeTag] using recovery_tag before endpoints connection _ _ (by assumption))
      | (cases computed)
      | (split at computed)
      | (dsimp only [Check.CampusTCPModel.get, Check.CampusTCPModel.parsed, Except.mapError,
          bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem step_tag (actual : M.Step input) (endpoints : M.Applications complete)
    (connection : actual.before.connection = .application complete endpoints) :
    completeTag actual.result.state.connection = some complete := by
  obtain ⟨effect, custody, computed, same⟩ := actual.processed
  have tag := core_tag actual.before endpoints connection actual.event effect computed
  simpa only [same] using tag

private theorem trace_tag (trace : Check.CampusTCPModel.Trace input before events steps after remaining)
    (endpoints : M.Applications complete) (connection : before.connection = .application complete endpoints) :
    completeTag after.connection = some complete := by
  induction trace generalizing complete with
  | done state => exact congrArg completeTag connection
  | stop head blocked rest => exact step_tag head endpoints connection
  | next head supported rest ih =>
    have tag := step_tag head endpoints connection
    cases connected : head.result.state.connection with
    | startup stage pending => simp only [connected, completeTag, reduceCtorEq] at tag
    | recovering current => simp only [connected, completeTag, reduceCtorEq] at tag
    | application next updated =>
      simp only [connected, completeTag, Option.some.injEq] at tag
      cases tag
      exact ih updated connected

private def startupBasis (report : M.Report input events) (current : Prefix report count) :
    Except String (G.StartupBasis current.cut) := do
  let within ← R.verify (25 ≤ report.steps.length) "The actual startup prefix is incomplete."
  let startup := Check.CampusTCPSchedule.Report.cut report 25 within.property
  let supported ← R.verify (startup.supported = true) "The actual startup prefix contains a scope stop."
  let enough ← R.verify (25 ≤ count) "The data cut precedes actual startup."
  have historyEq : current.cut.report.steps = startup.steps ++ current.cut.report.steps.drop 25 := by
    rw [current.steps]
    change report.steps.take count = report.steps.take 25 ++ (report.steps.take count).drop 25
    calc
      report.steps.take count = (report.steps.take count).take 25 ++ (report.steps.take count).drop 25 :=
        (List.take_append_drop 25 (report.steps.take count)).symm
      _ = _ := by rw [List.take_take, Nat.min_eq_left enough.property]
  match connection : startup.final.connection with
  | .startup .. => throw "The startup prefix is incomplete."
  | .recovering .. => throw "The startup prefix is still recovering startup."
  | .application earlier endpoints =>
    let clientEmpty ← R.verify (endpoints.client.steps = []) "The startup client has prior application operations."
    let serverEmpty ← R.verify (endpoints.server.steps = []) "The startup server has prior application operations."
    let ordinary ← CampusTCPRoundTheorem.ordinary startup
    let history ← Check.CampusTCPFacts.startupHistory startup earlier
    let clean ← CampusTCPRoundTheorem.cleanServices startup earlier ordinary
    match phase : startup.final.primary.transport.admission.phase with
    | .data session =>
      have initialConnection : startup.final.connection = .application earlier (Check.CampusTCPModel.Applications.initial earlier) := by
        rw [connection, Check.CampusTCPRoundSetup.applications_initial endpoints clientEmpty.property serverEmpty.property]
      have suffix := Check.CampusTCPRoundReport.Report.suffix startup current.cut.report current.cut.supported current.cut.finished
        historyEq
      have tag := trace_tag suffix endpoints connection
      have completeEq : earlier = current.complete := by
        rw [current.cut.connection] at tag
        exact (Option.some.inj tag).symm
      have aligned : Check.CampusTCPStartupAlignment.Alignment input earlier session.entry session := by
        obtain ⟨entry, selected, selectedPhase, aligned, _⟩ := (clean.property history).aligned history
        have same : selected = session := TCP.Admission.Phase.data.inj (selectedPhase.symm.trans phase)
        cases same
        simpa only [aligned.entryEq] using aligned
      let basis : Check.CampusTCPGapProgressStart.StartupBasis current.cut := {
        events := _, report := startup, supported := supported.property, finished := rfl
        connection := by cases completeEq; exact initialConnection
        ordinary := ordinary
        history := by simpa only [completeEq] using history
        clean := by cases completeEq; exact clean.property history
        retained := ⟨_, historyEq⟩
        entry := session.entry, session := session
        aligned := by simpa only [completeEq] using aligned
        phase := phase }
      return Check.CampusTCPStartupBasis.Basis.ofOrdinary basis
    | _ => throw "The actual startup gateway is not in the data phase."

def writtenBatch (cut : Check.CampusTCPRound.Cut input complete) (actor : M.Actor)
    (bytes : List UInt8) : Except String (G.WrittenBatch cut actor bytes) := do
  match selected : (Check.CampusTCPEnabled.applicationSteps cut.endpoints actor).reverse with
  | [] => throw "The actual writer history is empty."
  | writer :: reversed =>
    let event ← R.verify (writer.event = .write bytes) "The last actual operation is a different write."
    let accepted ← R.verify (writer.result.decision = .accepted (.write bytes.length))
      "The selected actual write was not accepted in full."
    let pending ← R.verify (writer.before.pending = []) "The writer has old pending bytes."
    let sent ← R.verify (writer.before.core.sent = []) "The writer has old unacknowledged bytes."
    have history : Check.CampusTCPEnabled.applicationSteps cut.endpoints actor = reversed.reverse ++ [writer] := by
      have same := congrArg List.reverse selected
      simpa only [List.reverse_reverse, List.reverse_cons] using same
    return Check.CampusTCPTwoProgressStart.WrittenBatch.ofLast writer reversed.reverse history event.property accepted.property pending.property sent.property

def idleEndpoint (cut : Check.CampusTCPRound.Cut input complete) (actor : M.Actor) :
    Except String (G.IdleEndpoint (Check.CampusTCPEnabled.endpoint cut.endpoints actor)) := do
  let state := Check.CampusTCPEnabled.endpoint cut.endpoints actor
  match runtime : state.recovery, ackRuntime : state.ackReaction with
  | some recovery, some reaction =>
    let outstanding ← R.verify (recovery.outstanding = []) "The current endpoint has an outstanding flight."
    let sent ← R.verify (state.core.sent = []) "The current endpoint has unacknowledged stream bytes."
    let deadline ← R.verify (recovery.deadline = none) "The idle endpoint has an active deadline."
    let timedOut ← R.verify (recovery.lastTimedOut = none) "The idle endpoint has an active timed-out head."
    let timeoutCount ← R.verify (recovery.timeoutCount = 0) "The idle endpoint has an active timeout count."
    let duplicate ← R.verify (recovery.duplicateAcks = 0) "The idle endpoint has old duplicate-ACK credit."
    let coherent ← R.verify (TCP.Endpoint.RecoveryCoherent state) "The current endpoint recovery is incoherent."
    let prepared ← R.verify (TCP.Endpoint.AckPrepared state) "The current endpoint ACK state is unprepared."
    let storage ← R.verify (TCP.Endpoint.StorageCoherent state) "The current endpoint store is incoherent."
    return ⟨recovery, reaction, runtime, ackRuntime, outstanding.property, sent.property,
      deadline.property, timedOut.property, timeoutCount.property, duplicate.property,
      Check.CampusTCPEnabled.endpoint_valid cut.endpoints actor,
      coherent.property, prepared.property, storage.property⟩
  | _, _ => throw "The current endpoint has no recovery or ACK runtime."

def writtenSender (cut : Check.CampusTCPRound.Cut input complete) (actor : M.Actor)
    (lower upper : List UInt8) : Except String (G.WrittenSender cut actor lower upper) := do
  let idle ← idleEndpoint cut actor
  let state := Check.CampusTCPEnabled.endpoint cut.endpoints actor
  let pending ← R.verify (state.pending = lower ++ upper) "The actual sender pending stream differs."
  let held ← R.verify (state.receiveStore.held = []) "The actual sender has a competing receive gap."
  let window ← R.verify (lower.length + upper.length ≤ state.sendWindow) "The two sends exceed the actual window."
  let mss ← R.verify (lower.length + upper.length ≤ state.effectiveMSS) "The batch exceeds the actual flight limit."
  return ⟨idle, pending.property, held.property, window.property, mss.property⟩

def emptyReceiver (cut : Check.CampusTCPRound.Cut input complete) (actor : M.Actor)
    (bytes : List UInt8) : Except String (G.EmptyReceiver cut actor bytes) := do
  let idle ← idleEndpoint cut actor
  let state := Check.CampusTCPEnabled.endpoint cut.endpoints actor
  let pending ← R.verify (state.pending = []) "The actual receiver has old pending application bytes."
  let unread ← R.verify (state.core.received = []) "The actual receiver has old unread bytes."
  let held ← R.verify (state.receiveStore.held = []) "The actual receiver has a held old range."
  let space ← R.verify (bytes.length ≤ TCP.Endpoint.offeredWindow state) "The actual offered window cannot fit the batch."
  return ⟨idle, pending.property, unread.property, held.property, space.property⟩

def gatewayStart (cut : Check.CampusTCPRound.Cut input complete) (basis : G.StartupBasis cut) (gateway : M.Gateway) :
    Except String (G.GatewayStart cut basis gateway) := do
  let before := Check.CampusTCPModel.beforeService input cut.report.final gateway
  match phase : before.admission.phase with
  | .data session =>
    let entry ← R.verify (session.entry = basis.session.entry) "The current entry differs from actual startup."
    let originalBase ← R.verify (session.original.base = basis.session.original.base) "The current original base differs."
    let replyBase ← R.verify (session.reply.base = basis.session.reply.base) "The current reply base differs."
    let clientMSS ← R.verify (session.clientMSS = basis.session.clientMSS) "The current client MSS differs."
    let serverMSS ← R.verify (session.serverMSS = basis.session.serverMSS) "The current server MSS differs."
    let valid ← R.verify before.tracker.Valid "The actual current tracker is invalid."
    match found : before.tracker.records.find? (fun record => record.entry == session.entry) with
    | none => throw "The actual current session has no tracker record."
    | some record =>
      let same ← R.verify (record.entry = session.entry) "The selected tracker entry differs."
      let confirmed ← R.verify (record.seenReply = true) "The selected tracker binding is unconfirmed."
      return ⟨session, ⟨entry.property, by intro direction; cases direction; exact originalBase.property; exact replyBase.property,
        clientMSS.property, serverMSS.property⟩, phase, valid.property, record,
        List.mem_of_find?_eq_some found, same.property, confirmed.property⟩
  | _ => throw "The actual selected gateway is not in the data phase."

def geometry (start : G.GatewayStart cut basis gateway) (sender : M.Actor) (lower upper : List UInt8) :
    Except String (G.Geometry start sender lower upper) := do
  let session := start.session
  let offset := (session.lane sender.direction).observed
  let senderState := Check.CampusTCPEnabled.endpoint cut.endpoints sender
  let receiverState := Check.CampusTCPEnabled.endpoint cut.endpoints sender.other
  let acknowledged ← R.verify ((session.lane sender.direction).acknowledged = offset)
    "The initial sender lane has unacknowledged old coverage."
  let highEnd ← R.verify ((session.lane sender.direction).highEnd = offset) "The initial sender lane has an old sparse hole."
  let senderCursor ← R.verify (senderState.core.sendNext = (session.lane sender.direction).base.add offset)
    "The current send cursor differs from the actual lane prefix."
  let receiverCursor ← R.verify (receiverState.core.receiveNext = senderState.core.sendNext)
    "The actual receiver cursor differs from the selected batch start."
  let senderAck ← R.verify (senderState.core.receiveNext = (session.peer sender.direction).base.add (session.peer sender.direction).observed)
    "The sender ACK cursor differs from actual opposite coverage."
  let receiverSequence ← R.verify (receiverState.core.sendNext = (session.peer sender.direction).base.add (session.peer sender.direction).highEnd)
    "The receiver send cursor differs from actual opposite coverage."
  let peerComplete ← R.verify ((session.peer sender.direction).observed = (session.peer sender.direction).highEnd)
    "The opposite lane has an old sparse hole."
  let window ← R.verify (lower.length + upper.length ≤ (session.lane sender.direction).peerWindow.val)
    "The new batch exceeds the actual admission window."
  let epoch ← R.verify (offset + lower.length + upper.length + 2 < TCP.Seq.halfSpace) "The selected batch exceeds the current sequence epoch."
  return ⟨offset, acknowledged.property, rfl, highEnd.property, senderCursor.property, receiverCursor.property,
    senderAck.property, receiverSequence.property, peerComplete.property, window.property, epoch.property⟩

private def ingress (input : M.Input) (gateway : M.Gateway) (actor : M.Actor) : Except String IngressAttachment.InterfaceRef := do
  match _found : (input.deployment gateway).specifications.find? (fun value => value.direction == actor.direction) with
  | none => throw "The selected gateway has no actual ingress specification."
  | some specification => return specification.ingress

def nativeEnv (cut : Check.CampusTCPRound.Cut input complete) (gateway : M.Gateway) (entry : NetfilterNAT.Entry) :
    Except String (G.NativeEnv cut gateway entry) := do
  let clientIngress ← ingress input gateway .client
  let serverIngress ← ingress input gateway .server
  let before := Check.CampusTCPModel.beforeService input cut.report.final gateway
  let original ← CampusTCPRoundTheorem.native (input.contextFor gateway) before clientIngress entry .original "server"
  let reply ← CampusTCPRoundTheorem.native (input.contextFor gateway) before serverIngress entry .reply "client"
  let clientOwner ← R.verify (cut.report.final.owner .client = gateway) "The client uses a different actual gateway."
  let serverOwner ← R.verify (cut.report.final.owner .server = gateway) "The server uses a different actual gateway."
  let configured ← R.verify (input.configured gateway = true) "The selected gateway is not configured."
  let unpaused ← R.verify (cut.report.final.assignmentPaused = false) "The actual assignments remain paused."
  let selectedIngress := fun actor => match actor with | .client => clientIngress | .server => serverIngress
  have paths : ∀ actor : M.Actor, Check.CampusTCPRoundGateway.Native (input.contextFor gateway) before
      (selectedIngress actor) entry actor.direction actor.nextHop := by
    intro actor
    cases actor
    · exact original
    · exact reply
  have owners : ∀ actor, cut.report.final.owner actor = gateway := by
    intro actor
    cases actor
    · exact clientOwner.property
    · exact serverOwner.property
  if primary : gateway = .primary then
    let unsealed ← R.verify (cut.report.final.primarySealed = false) "The selected primary is sealed."
    let unfenced ← R.verify (cut.report.final.primaryFenced = false) "The selected primary is fenced."
    let value : G.NativeEnv cut gateway entry := {
      ingress := selectedIngress, paths, owners, configured := configured.property, unpaused := unpaused.property
      primary := fun _ => ⟨unsealed.property, unfenced.property⟩
      standby := by intro standby; cases primary.symm.trans standby }
    return value
  else
    let sealed ← R.verify (cut.report.final.primarySealed = true) "The old primary is not sealed."
    let fenced ← R.verify (cut.report.final.primaryFenced = true) "The old primary is not fenced."
    match installed : cut.report.final.installation with
    | none => throw "The actual standby has no retained checkpoint installation."
    | some installation =>
      let value : G.NativeEnv cut gateway entry := {
        ingress := selectedIngress, paths, owners, configured := configured.property, unpaused := unpaused.property
        primary := by intro selected; exact False.elim (primary selected)
        standby := fun _ => ⟨installation, installed, sealed.property, fenced.property⟩ }
      return value

structure Witness (report : M.Report input events) (count : Nat) (sender : M.Actor) (gateway : M.Gateway)
    (lower upper : List UInt8) where
  current : Prefix report count
  initial : G.TwoWriteInitial current.cut sender gateway lower upper
  native : G.NativeEnv current.cut gateway initial.gatewayState.session.entry
  writerStamp : initial.write.writer.stamp = count - 1

def construct (report : M.Report input events) (count : Nat) (sender : M.Actor) (gateway : M.Gateway)
    (lower upper : List UInt8) : Except String (Witness report count sender gateway lower upper) := do
  let current ← takePrefix report count
  let basis ← startupBasis report current
  let lowerNonempty ← R.verify (lower ≠ []) "The selected lower range is empty."
  let upperNonempty ← R.verify (upper ≠ []) "The selected upper range is empty."
  let write ← writtenBatch current.cut sender (lower ++ upper)
  let writerStamp ← R.verify (write.writer.stamp = count - 1) "The current cut does not end at its actual writer."
  let senderState ← writtenSender current.cut sender lower upper
  let receiverState ← emptyReceiver current.cut sender.other (lower ++ upper)
  let gatewayState ← gatewayStart current.cut basis gateway
  let coordinates ← geometry gatewayState sender lower upper
  let initial : G.TwoWriteInitial current.cut sender gateway lower upper :=
    ⟨basis, lowerNonempty.property, upperNonempty.property, write, senderState, receiverState, gatewayState, coordinates⟩
  let native ← nativeEnv current.cut gateway gatewayState.session.entry
  return ⟨current, initial, native, writerStamp.property⟩

def forward (report : M.Report input events) : Except String
    (Witness report 32 .client .primary (fixturePayload 17 400) (fixturePayload 33 400)) :=
  construct report 32 .client .primary (fixturePayload 17 400) (fixturePayload 33 400)

def reverse (report : M.Report input events) : Except String
    (Witness report 67 .server .standby (fixturePayload 81 600) (fixturePayload 97 600)) :=
  construct report 67 .server .standby (fixturePayload 81 600) (fixturePayload 97 600)

structure Both (report : M.Report input events) where
  forward : Witness report 32 .client .primary (fixturePayload 17 400) (fixturePayload 33 400)
  reverse : Witness report 67 .server .standby (fixturePayload 81 600) (fixturePayload 97 600)

def constructBoth (report : M.Report input events) : Except String (Both report) := do
  return ⟨← forward report, ← reverse report⟩

def Witness.checked (witness : Witness report count sender gateway lower upper) : R.Checked input witness.current.cut.report.final :=
  ⟨witness.current.cut.events, witness.current.cut.report, witness.current.cut.supported, witness.current.cut.finished,
    [], .done witness.current.cut.report.final, by simp⟩

theorem Witness.checked_state (witness : Witness report count sender gateway lower upper) :
    witness.checked.report.final = witness.current.cut.report.final := rfl

theorem Witness.checked_empty (witness : Witness report count sender gateway lower upper) :
    witness.checked.recorded = [] := rfl

structure Prepared (input : Check.CampusTCP.Input) where
  report : M.Report input.model (input.events.take 67)
  witnesses : Both report

def prepare (input : Check.CampusTCP.Input) : IO (Prepared input) := do
  let report ← match input.model.check (input.events.take 67) with
    | .ok report => pure report
    | .error reason => throw (IO.userError reason.message)
  let witnesses ← R.load (constructBoth report)
  return ⟨report, witnesses⟩

def runInput (input : Check.CampusTCP.Input) : IO Unit := do
  let prepared ← prepare input
  let first := prepared.witnesses.forward
  let second := prepared.witnesses.reverse
  R.ensure (first.initial.write.writer.stamp == 31 && second.initial.write.writer.stamp == 66)
    "The two initial cuts must cite their own actual selected writes."
  R.ensure (first.current.cut.report.final.outputs.length == 3 && second.current.cut.report.final.outputs.length == 8)
    "Neither initial witness may contain a future batch output."
  R.ensure (first.initial.senderState.idle.recovery.nextId == 0 && first.initial.senderState.idle.recovery.frontier == 0 &&
    second.initial.senderState.idle.recovery.nextId == 0 && second.initial.senderState.idle.recovery.frontier == 0)
    "The original idle sender ledgers must be retained."
  R.ensure (second.initial.receiverState.idle.recovery.nextId == 2 && second.initial.receiverState.idle.recovery.frontier == 800 &&
    second.initial.receiverState.idle.recovery.rto == 2000)
    "The reverse receiver must retain the completed forward sender's ledger history and backoff."
  let reverseSender := Check.CampusTCPEnabled.endpoint second.current.cut.endpoints .server
  R.ensure (reverseSender.receiveStore.frontier == 800 && reverseSender.receiveStore.nextID == 2 && reverseSender.receiveStore.seenGap)
    "The reverse sender must retain the actual prior receive-store frontier and receipt counter."
  R.ensure ((second.current.cut.report.final.custody.pendingID (Check.CampusTCPModel.Transit.linkAt 3)).isSome &&
    (second.current.cut.report.final.custody.pendingID (Check.CampusTCPModel.Transit.linkAt 6)).isSome)
    "Both old original and copied links must remain pending."
  let _ := first.initial.write.joint
  let _ := second.initial.write.joint
  let _ := first.initial.gatewayState.coverage_sources
  let _ := second.initial.gatewayState.coverage_sources
  let _ := first.checked_state
  let _ := second.checked_state
  let _ := first.checked_empty
  let _ := second.checked_empty
  IO.println "Constructed actual two-record initial witnesses at cuts 32 and 67."

def run : IO Unit := do
  let input ← R.load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-receive-gaps/trace.json"))
  runInput input

end NetlibTest.CampusTCPTwoProgressInitial
