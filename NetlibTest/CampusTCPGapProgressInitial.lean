import Netlib.Check.CampusTCPGapProgressWire
import Netlib.Check.CampusTCPGapProgressMonitor
import Netlib.Check.CampusTCPGapProgressSetup
import Netlib.Check.CampusTCPGapProgressReceiver
import NetlibTest.CampusTCPRecoveryRound

namespace NetlibTest.CampusTCPGapProgressInitial

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input Event Report State Step Applications Actor Produced)
end M
namespace G
export Check.CampusTCPGapProgressStart
  (StartupBasis Identity GatewayStart LowerRange Original WriteBatch SenderStart HeldStart PendingLower GapInitial NativeEnv)
end G
namespace A
export TCP.ApplicationTrace (Step OutputAt Event Chain)
end A
namespace R
export NetlibTest.CampusTCPRecoveryRound (verify load Checked checkpoint)
end R

variable {input : M.Input} {events : List M.Event}
variable {complete : Check.TCPHandshake.Completed input.active input.passive}

private theorem input_eq (first second : TCP.EstablishedReceive.Input) (same : first.bytes = second.bytes) : first = second := by
  cases first with
  | mk firstBytes firstPacket firstChecked =>
    cases second with
    | mk secondBytes secondPacket secondChecked =>
      cases same
      have packets := Except.ok.inj (firstChecked.symm.trans secondChecked)
      cases packets
      rfl

private instance : DecidableEq TCP.EstablishedReceive.Input := fun first second =>
  if same : first.bytes = second.bytes then .isTrue (input_eq first second same)
  else .isFalse (by intro equal; exact same (congrArg TCP.EstablishedReceive.Input.bytes equal))

deriving instance DecidableEq for TCP.ApplicationTrace.Event
deriving instance DecidableEq for TCP.Endpoint.Result
deriving instance DecidableEq for TCP.ApplicationTrace.Step

structure Prefix (report : M.Report input events) (count : Nat) where
  complete : Check.TCPHandshake.Completed input.active input.passive
  cut : Check.CampusTCPRound.Cut input complete
  steps : cut.report.steps = report.steps.take count
  state : cut.report.final = Check.CampusTCPSchedule.stateAt input.initial report.steps count

def takePrefix (report : M.Report input events) (count : Nat) : Except String (Prefix report count) := do
  let within ← R.verify (count ≤ report.steps.length) "The actual gap prefix is incomplete."
  let part := Check.CampusTCPSchedule.Report.cut report count within.property
  let accepted ← R.verify (part.supported = true) "The actual gap prefix contains a scope stop."
  match connected : part.final.connection with
  | .startup .. => throw "The actual gap prefix has no completed startup."
  | .application complete endpoints =>
    let cut : Check.CampusTCPRound.Cut input complete := ⟨_, part, accepted.property, rfl, endpoints, connected⟩
    return ⟨complete, cut, rfl, rfl⟩

private def sendEvent (step : A.Step) (count : Nat) : Except String { _value : Unit // step.event = .send count true } := do
  let same ← R.verify (step.event = .send count true) "The selected original send event differs."
  return ⟨(), same.property⟩

def original (cut : Check.CampusTCPRound.Cut input complete) (actor : M.Actor) (bytes : List UInt8)
    (stamp index : Nat) : Except String (G.Original cut actor bytes) := do
  let selected ← TCP.ApplicationTrace.findOutput (Check.CampusTCPEnabled.applicationSteps cut.endpoints actor) stamp
  let event ← sendEvent selected.val.step bytes.length
  let payload ← R.verify (selected.val.output.packet.segment.payload = bytes) "The original payload differs."
  match stored : cut.report.final.outputs[index]? with
  | none => throw "The original output index is absent."
  | some produced =>
    match application : produced with
    | .startup .. => throw "The selected output is a startup packet."
    | .application sourceActor operation output origin =>
      let sameActor ← R.verify (sourceActor = actor) "The original output actor differs."
      let sameStep ← R.verify (operation = selected.val.step) "The output does not cite the selected actual send."
      let sameOutput ← R.verify (output = selected.val.output) "The output packet differs from the selected actual send."
      return ⟨selected.val, event.property, payload.property, index, produced, stored, by
        rw [application]
        cases sameActor.property
        cases sameStep.property
        cases sameOutput.property
        rfl⟩

private structure Split (steps : List A.Step) (stamp : Nat) where
  prior : List A.Step
  step : A.Step
  later : List A.Step
  history : steps = prior ++ step :: later
  selected : step.stamp = stamp

private def split (steps : List A.Step) (stamp : Nat) : Except String (Split steps stamp) :=
  match steps with
  | [] => throw "The actual endpoint history split is absent."
  | head :: tail => do
    if same : head.stamp = stamp then return ⟨[], head, tail, rfl, same⟩
    else
      let found ← split tail stamp
      return ⟨head :: found.prior, found.step, found.later, by simp only [found.history, List.cons_append], found.selected⟩

def writeBatch (cut : Check.CampusTCPRound.Cut input complete) (actor : M.Actor) (lower upper : List UInt8)
    (first : G.Original cut actor lower) (second : G.Original cut actor upper) (stamp : Nat) :
    Except String (G.WriteBatch cut actor lower upper first second) := do
  let found ← split first.attempt.prior stamp
  let upperWriter ← split second.attempt.prior stamp
  let sameWriter ← R.verify (upperWriter.step = found.step) "The two originals do not cite one actual writer."
  let upperFirst ← split upperWriter.later first.attempt.step.stamp
  let sameFirst ← R.verify (upperFirst.step = first.attempt.step) "The upper original has a different earlier send."
  let samePrior ← R.verify (upperWriter.prior = found.prior) "The writer has a different actual prefix."
  let sameLower ← R.verify (upperFirst.prior = found.later) "The lower send has a different actual prefix."
  let event ← R.verify (found.step.event = .write (lower ++ upper)) "The selected writer event differs."
  let accepted ← R.verify (found.step.result.decision = .accepted (.write (lower.length + upper.length)))
    "The selected write was not accepted in full."
  let pending ← R.verify (found.step.before.pending = []) "The writer has old pending bytes."
  let sent ← R.verify (found.step.before.core.sent = []) "The writer has old unacknowledged bytes."
  let lowerWritten ← R.verify (found.later.flatMap TCP.ApplicationTrace.Step.written = []) "A write intervenes before the lower send."
  let upperWritten ← R.verify (upperFirst.later.flatMap TCP.ApplicationTrace.Step.written = []) "A write intervenes before the upper send."
  let lowerEmitted ← R.verify (found.later.flatMap TCP.ApplicationTrace.Step.emitted = []) "Another send precedes the lower original."
  let upperEmitted ← R.verify (upperFirst.later.flatMap TCP.ApplicationTrace.Step.emitted = []) "Another send precedes the upper original."
  have upperSplit : second.attempt.prior = found.prior ++ found.step :: (found.later ++ first.attempt.step :: upperFirst.later) := by
    calc
      second.attempt.prior = upperWriter.prior ++ upperWriter.step :: upperWriter.later := upperWriter.history
      _ = upperWriter.prior ++ upperWriter.step :: (upperFirst.prior ++ upperFirst.step :: upperFirst.later) :=
        congrArg (fun tail => upperWriter.prior ++ upperWriter.step :: tail) upperFirst.history
      _ = _ := by rw [sameWriter.property, sameFirst.property, samePrior.property, sameLower.property]
  have lowerAfter : TCP.ApplicationTrace.Chain found.step.result.state found.later first.attempt.step.before := by
    have chain := Check.CampusTCPGapProgressStart.endpoint_chain cut actor
    rw [first.attempt.same] at chain
    have preceding := chain.cut.1
    rw [found.history] at preceding
    exact preceding.cut.2
  have upperAfter : TCP.ApplicationTrace.Chain first.attempt.step.result.state upperFirst.later second.attempt.step.before := by
    have chain := Check.CampusTCPGapProgressStart.endpoint_chain cut actor
    rw [second.attempt.same] at chain
    have preceding := chain.cut.1
    rw [upperSplit] at preceding
    exact preceding.cut.2.cut.2
  return ⟨found.step, found.prior, found.later, upperFirst.later, found.history, upperSplit,
    event.property, accepted.property, pending.property, sent.property,
    lowerAfter, upperAfter,
    lowerWritten.property, upperWritten.property, lowerEmitted.property, upperEmitted.property⟩

private def completeTag : Check.CampusTCPModel.Connection input.active input.passive →
    Option (Check.TCPHandshake.Completed input.active input.passive)
  | .startup .. => none
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
    split at computed
    · exact application_tag before endpoints connection _ _ effect computed
    · cases computed

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
      let basis : G.StartupBasis current.cut := {
        events := _, report := startup, supported := supported.property, finished := rfl
        connection := by cases completeEq; exact initialConnection
        ordinary := ordinary
        history := by simpa only [completeEq] using history
        clean := by cases completeEq; exact clean.property history
        retained := ⟨_, historyEq⟩
        entry := session.entry, session := session
        aligned := by simpa only [completeEq] using aligned
        phase := phase }
      return basis
    | _ => throw "The actual startup gateway is not in the data phase."

def senderStart (cut : Check.CampusTCPRound.Cut input complete) (actor : M.Actor) (lower upper : List UInt8)
    (first : G.Original cut actor lower) (second : G.Original cut actor upper) :
    Except String (G.SenderStart cut actor lower upper first second) := do
  let state := Check.CampusTCPEnabled.endpoint cut.endpoints actor
  match runtime : state.recovery, ackRuntime : state.ackReaction with
  | some recovery, some reaction =>
    match ledger : recovery.outstanding with
    | [head, tail] =>
      let ackEmpty ← R.verify (reaction.work.pending = []) "The current sender ackEmpty guard differs."
      let window ← R.verify (lower.length ≤ state.sendWindow) "The current sender window guard differs."
      let headCount ← R.verify (head.count = lower.length) "The current sender headCount guard differs."
      let tailCount ← R.verify (tail.count = upper.length) "The current sender tailCount guard differs."
      let sent ← R.verify (state.core.sent = lower ++ upper) "The current sender sent guard differs."
      let pending ← R.verify (state.pending = []) "The current sender pending guard differs."
      let emptyHeld ← R.verify (state.receiveStore.held = []) "The current sender emptyHeld guard differs."
      let headSequence ← R.verify (state.core.sendUna = first.attempt.output.packet.segment.sequence) "The current sender headSequence guard differs."
      let headTime ← R.verify (head.sentAt = first.attempt.step.before.now) "The current sender headTime guard differs."
      let tailTime ← R.verify (tail.sentAt = second.attempt.step.before.now) "The current sender tailTime guard differs."
      let headID ← R.verify (head.id = 0) "The current sender headID guard differs."
      let tailID ← R.verify (tail.id = 1) "The current sender tailID guard differs."
      let headStart ← R.verify (head.start = 0) "The current sender headStart guard differs."
      let tailStart ← R.verify (tail.start = lower.length) "The current sender tailStart guard differs."
      let headLast ← R.verify (head.lastAt = head.sentAt) "The current sender headLast guard differs."
      let tailLast ← R.verify (tail.lastAt = tail.sentAt) "The current sender tailLast guard differs."
      let headRetried ← R.verify (head.retried = false) "The current sender headRetried guard differs."
      let tailRetried ← R.verify (tail.retried = false) "The current sender tailRetried guard differs."
      let nextID ← R.verify (recovery.nextId = 2) "The current sender nextID guard differs."
      let frontier ← R.verify (recovery.frontier = lower.length + upper.length) "The current sender frontier guard differs."
      let rto ← R.verify (recovery.rto = 1000) "The current sender rto guard differs."
      let deadline ← R.verify (recovery.deadline = some (head.lastAt + recovery.rto)) "The current sender deadline guard differs."
      let timedOut ← R.verify (recovery.lastTimedOut = none) "The current sender timedOut guard differs."
      let timeoutCount ← R.verify (recovery.timeoutCount = 0) "The current sender timeoutCount guard differs."
      let duplicate ← R.verify (recovery.duplicateAcks = 1) "The current sender duplicate guard differs."
      let coherent ← R.verify (TCP.Endpoint.RecoveryCoherent state) "The current sender coherent guard differs."
      let prepared ← R.verify (TCP.Endpoint.AckPrepared state) "The current sender prepared guard differs."
      let storage ← R.verify (TCP.Endpoint.StorageCoherent state) "The current sender storage guard differs."
      let clocked ← R.verify (recovery.Clocked) "The current sender clocked guard differs."
      return {
        recovery, reaction, head, tail, runtime, ackRuntime, ledger
        valid := Check.CampusTCPEnabled.endpoint_valid cut.endpoints actor
        ackEmpty := ackEmpty.property
        window := window.property
        headCount := headCount.property
        tailCount := tailCount.property
        sent := sent.property
        pending := pending.property
        emptyHeld := emptyHeld.property
        headSequence := headSequence.property
        headTime := headTime.property
        tailTime := tailTime.property
        headID := headID.property
        tailID := tailID.property
        headStart := headStart.property
        tailStart := tailStart.property
        headLast := headLast.property
        tailLast := tailLast.property
        headRetried := headRetried.property
        tailRetried := tailRetried.property
        nextID := nextID.property
        frontier := frontier.property
        rto := rto.property
        deadline := deadline.property
        timedOut := timedOut.property
        timeoutCount := timeoutCount.property
        duplicate := duplicate.property
        coherent := coherent.property
        prepared := prepared.property
        storage := storage.property
        clocked := clocked.property
      }
    | _ => throw "The actual sender does not retain two original records."
  | _, _ => throw "The actual sender has no recovery or ACK runtime."

def heldStart (cut : Check.CampusTCPRound.Cut input complete) (actor : M.Actor) (lower upper : List UInt8) :
    Except String (G.HeldStart cut actor lower upper) := do
  let state := Check.CampusTCPEnabled.endpoint cut.endpoints actor
  match held : state.receiveStore.held with
  | [run] =>
    let position ← R.verify (run.position = lower.length) "The held upper position differs."
    let bytes ← R.verify (run.bytes = upper) "The held upper bytes differ."
    let receipt ← R.verify (run.receipt = 0) "The held receipt identity differs."
    let frontier ← R.verify (state.receiveStore.frontier = 0) "The held stream frontier differs."
    let nextID ← R.verify (state.receiveStore.nextID = 1) "The held receipt counter differs."
    let seenGap ← R.verify (state.receiveStore.seenGap = true) "The actual store has no observed gap."
    let unread ← R.verify (state.core.received = []) "The actual receiver has earlier unread bytes."
    let origin ← TCP.ApplicationTrace.heldRunOrigin (Check.CampusTCPGapProgressStart.endpoint_chain cut actor)
      (Check.CampusTCPGapProgressStart.seed_empty_held complete actor) run (by rw [held]; simp)
    let delivery ← Check.CampusTCPFacts.applicationDelivery cut.report
      (Check.CampusTCPEnabled.applicationSteps cut.endpoints actor.other) actor origin.issuer
    match runtime : state.recovery, ackRuntime : state.ackReaction with
    | some recovery, some reaction =>
      let idle ← R.verify (recovery.outstanding = []) "The receiver has a competing outbound flight."
      let coherent ← R.verify (TCP.Endpoint.RecoveryCoherent state) "The actual receiver recovery is incoherent."
      let prepared ← R.verify (TCP.Endpoint.AckPrepared state) "The actual receiver ACK ledger is unprepared."
      let storage ← R.verify (TCP.Endpoint.StorageCoherent state) "The actual receiver store is incoherent."
      return ⟨run, held, position.property, bytes.property, receipt.property, frontier.property,
        nextID.property, seenGap.property, unread.property, ⟨origin, delivery⟩,
        recovery, reaction, runtime, ackRuntime, idle.property,
        Check.CampusTCPEnabled.endpoint_valid cut.endpoints actor, coherent.property, prepared.property, storage.property⟩
    | _, _ => throw "The actual receiver has no recovery or ACK runtime."
  | _ => throw "The actual receiver does not retain one upper run."

def gatewayStart (cut : Check.CampusTCPRound.Cut input complete) (basis : G.StartupBasis cut) :
    Except String (G.GatewayStart cut basis) := do
  let before := Check.CampusTCPModel.beforeService input cut.report.final .standby
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
  | _ => throw "The actual standby admission is not in the data phase."

def lowerRange (start : G.GatewayStart cut basis) (actor : M.Actor) (lower : List UInt8) :
    Except String (G.LowerRange start actor lower) := do
  match found : (start.seed.lane actor.direction).coverage.runs.find? (fun run => run.position == 0) with
  | none => throw "The actual current coverage has no lower original."
  | some run =>
    let position ← R.verify (run.position = 0) "The selected current lower position differs."
    let bytes ← R.verify (run.bytes = lower) "The selected current lower bytes differ."
    return ⟨run, List.mem_of_find?_eq_some found, position.property, bytes.property⟩

private def sameOriginal (produced : M.Produced input.active input.passive) (original : G.Original cut actor lower) :
    Except String { _value : Unit // produced = original.produced } := do
  match present : produced with
  | .startup .. => throw "The selected lower service has a startup source."
  | .application sourceActor operation output origin =>
    let sameActor ← R.verify (sourceActor = actor) "The selected lower service actor differs."
    let sameStep ← R.verify (operation = original.attempt.step) "The selected lower service cites a different send."
    let sameOutput ← R.verify (output = original.attempt.output) "The selected lower service packet differs."
    return ⟨(), by
      rw [present, original.application]
      cases sameActor.property
      cases sameStep.property
      cases sameOutput.property
      rfl⟩

def pendingLower (cut : Check.CampusTCPRound.Cut input complete) (original : G.Original cut actor lower)
    (index : Nat) : Except String (G.PendingLower cut original) := do
  match stored : cut.report.final.services[index]? with
  | none => throw "The actual lower service is absent."
  | some served =>
    let source ← sameOriginal served.ticket.value.produced original
    match emitted : served.evidence.output with
    | none => throw "The actual lower service has no stored emission."
    | some emission =>
      match pending : cut.report.final.custody.pendingID (Check.CampusTCPModel.Transit.linkAt index) with
      | none => throw "The actual lower service has no live link identity."
      | some packet => return ⟨index, served, stored, source.property, emission, emitted, packet, pending⟩

private def ingress (_state : M.State input) (actor : M.Actor) : Except String IngressAttachment.InterfaceRef := do
  match _found : (input.deployment .standby).specifications.find? (fun value => value.direction == actor.direction) with
  | none => throw "The actual standby has no selected ingress specification."
  | some specification => return specification.ingress

def nativeEnv (cut : Check.CampusTCPRound.Cut input complete) (entry : NetfilterNAT.Entry) :
    Except String (G.NativeEnv cut entry) := do
  let clientIngress ← ingress cut.report.final .client
  let serverIngress ← ingress cut.report.final .server
  let before := Check.CampusTCPModel.beforeService input cut.report.final .standby
  let original ← CampusTCPRoundTheorem.native (input.contextFor .standby) before clientIngress entry .original "server"
  let reply ← CampusTCPRoundTheorem.native (input.contextFor .standby) before serverIngress entry .reply "client"
  let clientOwner ← R.verify (cut.report.final.owner .client = .standby) "The client does not use the actual standby."
  let serverOwner ← R.verify (cut.report.final.owner .server = .standby) "The server does not use the actual standby."
  let configured ← R.verify (input.configured .standby = true) "The standby is not configured."
  let unpaused ← R.verify (cut.report.final.assignmentPaused = false) "The actual standby remains paused."
  let sealed ← R.verify (cut.report.final.primarySealed = true) "The old primary is not sealed."
  let fenced ← R.verify (cut.report.final.primaryFenced = true) "The old primary is not fenced."
  match installed : cut.report.final.installation with
  | none => throw "The actual standby has no exact checkpoint installation."
  | some installation =>
    return ⟨(fun actor => match actor with | .client => clientIngress | .server => serverIngress),
      (by intro actor; cases actor; exact original; exact reply),
      (by intro actor; cases actor; exact clientOwner.property; exact serverOwner.property),
      configured.property, unpaused.property, installation, installed, sealed.property, fenced.property⟩

structure Witness (report : M.Report input events) (count : Nat) (sender : M.Actor) (lower upper : List UInt8) where
  current : Prefix report count
  initial : G.GapInitial current.cut sender lower upper
  native : G.NativeEnv current.cut initial.gateway.seed.entry
  geometry : Check.CampusTCPGapProgressReceiver.Geometry initial
  wire : Check.CampusTCPGapProgressWire.Geometry initial

def construct (report : M.Report input events) (count : Nat) (sender : M.Actor) (lower upper : List UInt8)
    (writeStamp lowerStamp upperStamp lowerIndex upperIndex serviceIndex : Nat) :
    Except String (Witness report count sender lower upper) := do
  let current ← takePrefix report count
  let basis ← startupBasis report current
  let lowerNonempty ← R.verify (lower ≠ []) "The selected lower range is empty."
  let upperNonempty ← R.verify (upper ≠ []) "The selected upper range is empty."
  let first ← original current.cut sender lower lowerStamp lowerIndex
  let second ← original current.cut sender upper upperStamp upperIndex
  let write ← writeBatch current.cut sender lower upper first second writeStamp
  let flight ← senderStart current.cut sender lower upper first second
  let receiver ← heldStart current.cut sender.other lower upper
  let selected ← pendingLower current.cut first serviceIndex
  let gateway ← gatewayStart current.cut basis
  let range ← lowerRange gateway sender lower
  let initial : G.GapInitial current.cut sender lower upper :=
    ⟨basis, lowerNonempty.property, upperNonempty.property, first, second, write, flight, receiver, selected, gateway, range⟩
  let native ← nativeEnv current.cut gateway.seed.entry
  let state := Check.CampusTCPEnabled.endpoint current.cut.endpoints sender.other
  let lowerSequence ← R.verify (first.attempt.output.packet.segment.sequence = state.core.receiveNext)
    "The actual lower original does not start at the current gap."
  let upperSource ← R.verify (receiver.source.delivery.source.step = second.attempt.step)
    "The held upper receipt does not cite the selected writer's original send."
  let upperTuple ← R.verify (receiver.run.metadata.header = state.core.inbound) "The held upper tuple differs."
  let upperControl ← R.verify (TCP.EstablishedReceive.control receiver.run.metadata.segment = none) "The held upper control scope differs."
  let upperAck ← R.verify (TCP.Flags.ack receiver.run.metadata.segment.flags = true) "The held upper has no ACK flag."
  let upperSequence ← R.verify (receiver.run.metadata.segment.sequence = state.core.receiveNext.add lower.length)
    "The held upper is not adjacent to the actual lower original."
  let upperAckOld ← R.verify (TCP.Seq.distance receiver.run.metadata.segment.acknowledgment state.core.sendUna ≤
    TCP.EstablishedReceive.maxSendWindow) "The held upper ACK is outside the current epoch."
  let upperPast ← R.verify (receiver.run.metadata.receivedAt ≤ state.now) "The held upper receipt is in the future."
  let senderState := Check.CampusTCPEnabled.endpoint current.cut.endpoints sender
  let wireSequence ← R.verify (first.attempt.output.packet.segment.sequence = (gateway.seed.lane sender.direction).base)
    "The actual lower original does not start at the copied sender lane base."
  let observed ← R.verify ((gateway.seed.lane sender.direction).observed = lower.length + upper.length)
    "The actual standby does not know both contiguous selected ranges."
  let senderCursor ← R.verify (senderState.core.receiveNext =
    (gateway.seed.peer sender.direction).base.add (gateway.seed.peer sender.direction).observed)
    "The sender cursor differs from the actual opposite coverage frontier."
  let receiverCursor ← R.verify (state.core.sendNext =
    (gateway.seed.peer sender.direction).base.add (gateway.seed.peer sender.direction).highEnd)
    "The receiver send cursor differs from the actual opposite coverage limit."
  let lowerAck ← R.verify (first.attempt.output.packet.segment.acknowledgment = senderState.core.receiveNext)
    "The selected old lower packet has a different historical ACK cursor."
  let peerComplete ← R.verify ((gateway.seed.peer sender.direction).observed = (gateway.seed.peer sender.direction).highEnd)
    "The opposite lane has an unresolved sparse gap."
  let lowerTarget ← R.verify (selected.emission.target = state.core.inbound)
    "The selected old lower emission has a different actual receiver tuple."
  return ⟨current, initial, native, ⟨lowerSequence.property, upperSource.property, upperTuple.property, upperControl.property,
    upperAck.property, upperSequence.property, upperAckOld.property, upperPast.property⟩,
    ⟨wireSequence.property, observed.property, senderCursor.property, receiverCursor.property, lowerAck.property,
      peerComplete.property, lowerTarget.property⟩⟩

def fixturePayload (start count : Nat) : List UInt8 :=
  (List.range count).map (fun index => UInt8.ofNat ((start + index) % 251))

def forward (report : M.Report input events) : Except String
    (Witness report 54 .client (fixturePayload 17 400) (fixturePayload 33 400)) :=
  construct report 54 .client (fixturePayload 17 400) (fixturePayload 33 400) 31 32 35 3 4 3

def reverse (report : M.Report input events) : Except String
    (Witness report 79 .server (fixturePayload 81 600) (fixturePayload 97 600)) :=
  construct report 79 .server (fixturePayload 81 600) (fixturePayload 97 600) 66 67 70 8 9 9

structure Both (report : M.Report input events) where
  forward : Witness report 54 .client (fixturePayload 17 400) (fixturePayload 33 400)
  reverse : Witness report 79 .server (fixturePayload 81 600) (fixturePayload 97 600)

def constructBoth (report : M.Report input events) : Except String (Both report) := do
  return ⟨← forward report, ← reverse report⟩

def Witness.config (witness : Witness report count sender lower upper) : Check.CampusTCPGapProgressMonitor.Config :=
  Check.CampusTCPGapProgressSetup.config witness.initial witness.native 10 2

def Witness.monitor (witness : Witness report count sender lower upper) : Check.CampusTCPGapProgressMonitor.Monitor :=
  Check.CampusTCPGapProgressSetup.initialMonitor witness.initial

def Witness.checked (witness : Witness report count sender lower upper) : R.Checked input witness.current.cut.report.final :=
  ⟨witness.current.cut.events, witness.current.cut.report, witness.current.cut.supported, witness.current.cut.finished,
    [], .done witness.current.cut.report.final, by simp⟩

theorem Witness.checked_state (witness : Witness report count sender lower upper) :
    witness.checked.report.final = witness.current.cut.report.final := rfl

theorem Witness.config_actual (witness : Witness report count sender lower upper) :
    witness.config = Check.CampusTCPGapProgressSetup.config witness.initial witness.native 10 2 := rfl

theorem Witness.monitor_actual (witness : Witness report count sender lower upper) :
    witness.monitor = Check.CampusTCPGapProgressSetup.initialMonitor witness.initial := rfl

structure Prepared (input : Check.CampusTCP.Input) where
  report : M.Report input.model (input.events.take 79)
  witnesses : Both report

def prepare (input : Check.CampusTCP.Input) : IO (Prepared input) := do
  let report ← match input.model.check (input.events.take 79) with
    | .ok report => pure report
    | .error reason => throw (IO.userError reason.message)
  let witnesses ← R.load (constructBoth report)
  return ⟨report, witnesses⟩

def runInput (input : Check.CampusTCP.Input) : IO Unit := do
  let prepared ← prepare input
  let first := prepared.witnesses.forward
  let second := prepared.witnesses.reverse
  NetlibTest.CampusTCPRecoveryRound.ensure
    (first.initial.selected.packetID == 7 && second.initial.selected.packetID == 19)
    "The selected old lower identities must come from the actual live lookups."
  NetlibTest.CampusTCPRecoveryRound.ensure
    (first.initial.receiver.source.origin.issuer.stamp == 38 &&
      first.initial.receiver.run.metadata.receivedAt == 100 &&
      second.initial.receiver.source.origin.issuer.stamp == 73 &&
      second.initial.receiver.run.metadata.receivedAt == 1200)
    "The held runs must retain their original actual receipt operations and local times."
  NetlibTest.CampusTCPRecoveryRound.ensure
    (first.config.initialRemaining == 1000 && second.config.initialRemaining == 900)
    "The initial wait must use each actual stored deadline and current clock."
  let _ := first.geometry.upperSource
  let _ := second.geometry.upperSource
  let _ := Check.CampusTCPGapProgressWire.initial_link_fields first.wire
  let _ := Check.CampusTCPGapProgressWire.initial_link_fields second.wire
  let _ := first.config_actual
  let _ := second.config_actual
  let _ := first.checked_state
  let _ := second.checked_state
  IO.println "Constructed actual held-gap initial witnesses at cuts 54 and 79."

def run : IO Unit := do
  let input ← R.load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-receive-gaps/trace.json"))
  runInput input

end NetlibTest.CampusTCPGapProgressInitial
