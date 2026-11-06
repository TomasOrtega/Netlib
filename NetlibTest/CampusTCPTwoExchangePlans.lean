import NetlibTest.CampusTCPTwoProgressInitial
import Netlib.Check.CampusTCPTwoProgressRecorded
import Netlib.Check.CampusTCPWriteEnabled
import Netlib.Check.CampusTCPTwoExchangeSetup
import Netlib.Check.CampusTCPTwoExchangeBounded
import Netlib.Check.CampusTCPTwoExchangeActionCheck
import Netlib.Check.CampusTCPTwoExchangeServiceCheck

/-!
# Actual sequential two-record exchanges

Each case continues one report through a real reverse write.
The reverse monitor receives only the unspent shared drop allowance.
-/

namespace NetlibTest.CampusTCPTwoExchangePlans

open Netlib Packet Protocol

deriving instance DecidableEq for Check.CampusTCPModel.Event
namespace M
export Check.CampusTCPModel (Input Event Report State Step Actor Gateway)
end M
namespace R
export NetlibTest.CampusTCPRecoveryRound (Checked appendOne endpoint ensure load verify)
end R
namespace I
export NetlibTest.CampusTCPTwoProgressInitial (Witness construct forward)
export NetlibTest.CampusTCPGapProgressInitial (fixturePayload)
end I
namespace O
export Check.CampusTCPTwoProgressMonitor
  (Monitor Config Demand observe nextDemand exposedPacket allowed actions check actions_correct)
end O
namespace X
export Check.CampusTCPTwoExchangeMonitor (Config Monitor observe monitorAt allowed actions check check_correct Serviced)
end X
namespace AC
export Check.CampusTCPTwoExchangeActionCheck (actions actions_eq)
end AC
namespace SC
export Check.CampusTCPTwoExchangeServiceCheck (check check_eq)
end SC

variable {input : M.Input} {events : List M.Event} {report : M.Report input events} {count : Nat}
variable {sender : M.Actor} {gateway : M.Gateway} {lower upper : List UInt8}

def configuration (witness : I.Witness report count sender gateway lower upper) (allowance : Nat) : O.Config :=
  Check.CampusTCPTwoProgressSetup.config witness.initial witness.native 10 allowance

private inductive Role where
  | lower | upper
  deriving Repr, BEq, DecidableEq

private def originalPacket (config : O.Config) (state : M.State input) (monitor : O.Monitor) (role : Role) : Option Nat := do
  let lane := match role with | .lower => monitor.lower | .upper => monitor.upper
  if lane.phase == .dataIngress then O.exposedPacket config state lane else none

private def exposed (config : O.Config) (state : M.State input) (monitor : O.Monitor) : List Nat :=
  [monitor.lower, monitor.upper, monitor.retry].filterMap (O.exposedPacket config state) ++
    monitor.ack.toList.filterMap (O.exposedPacket config state)

private def demandEvent (upperFirst : Bool) : O.Demand → Except String M.Event
  | .single demand => .ok demand.event
  | .originalChoice lower upper =>
    match (if upperFirst then upper.or lower else lower.or upper) with
    | some demand => .ok demand.event
    | none => .error "The original choice has no current event."

private def dropIDs (steps : List (M.Step input)) : List Nat := steps.filterMap fun actual =>
  match actual.event with | .dropPacket id => some id | _ => none

private def timeoutCount (steps : List (M.Step input)) : Nat :=
  (steps.filter fun actual => match actual.event with | .timeout _ true => true | _ => false).length

private structure WholeCertificate (config : X.Config) (initial : M.State input) (steps : List (M.Step input)) where
  actions : X.actions config initial .initial steps = true
  serviced : X.Serviced config initial .initial steps 3
  done : (steps.foldl (X.observe config) .initial).mode = .done
  slots : (steps.foldl (X.observe config) .initial).slots = steps.length
  drops : (steps.foldl (X.observe config) .initial).drops = dropIDs steps
  timeouts : (steps.foldl (X.observe config) .initial).timeouts = timeoutCount steps

private def receiverOperations (steps : List (M.Step input)) (actor : M.Actor) : List TCP.ApplicationTrace.Step :=
  steps.filterMap fun actual => match actual.result.application with
    | some (selected, operation) => if selected == actor then some operation else none
    | none => none

private theorem checked_history (witness : I.Witness report count sender gateway lower upper)
    (checked : R.Checked input witness.current.cut.report.final)
    (events : checked.events = witness.current.cut.events ++ checked.recorded.map (·.event)) :
    checked.report.steps = witness.current.cut.report.steps ++ checked.recorded := by
  have supported : ∀ actual ∈ witness.current.cut.report.steps, actual.result.supported = true :=
    List.all_eq_true.mp witness.current.cut.supported
  have whole := Check.CampusTCPSchedule.Trace.append_complete witness.current.cut.report.trace
    witness.current.cut.finished supported checked.suffix
  have same : Check.CampusTCPModel.Trace input input.initial checked.events
      (witness.current.cut.report.steps ++ checked.recorded) checked.report.final [] :=
    Eq.mp (congrArg (fun selectedEvents => Check.CampusTCPModel.Trace input input.initial selectedEvents
      (witness.current.cut.report.steps ++ checked.recorded) checked.report.final []) events.symm) whole
  exact (Check.CampusTCPRoundReport.Trace.unique checked.report.trace same).1

private structure LegRun (witness : I.Witness report count sender gateway lower upper) (allowance : Nat) where
  checked : R.Checked input witness.current.cut.report.final
  monitor : O.Monitor
  allowed : O.actions (configuration witness allowance) witness.current.cut.report.final .initial checked.recorded = true
  serviced : O.check (configuration witness allowance) witness.current.cut.report.final .initial checked.recorded 3 = true
  observed : checked.recorded.foldl (O.observe (configuration witness allowance)) .initial = monitor
  done : monitor.mode = .done
  history : checked.report.steps = witness.current.cut.report.steps ++ checked.recorded
  completed : ∃ current : Check.CampusTCPRound.Cut input witness.current.complete,
    current.report.final = checked.report.final ∧ current.report.steps = witness.current.cut.report.steps ++ checked.recorded ∧
      Nonempty (Check.CampusTCPTwoProgressEvidence.Complete witness.initial witness.native 10 allowance current monitor)

private def checkTimeout (actual : M.Step input) (sender : M.Actor) : IO Unit := do
  let before ← R.load (R.endpoint actual.before sender)
  let after ← R.load (R.endpoint actual.result.state sender)
  let some old := before.recovery | throw (IO.userError "The timeout has no old recovery.")
  let some next := after.recovery | throw (IO.userError "The timeout has no new recovery.")
  let head :: tail := old.outstanding | throw (IO.userError "The timeout has no head.")
  let some produced := actual.result.output | throw (IO.userError "The timeout has no output.")
  let expected := if old.lastTimedOut == some head.id then old.timeoutCount + 1 else 1
  R.ensure (produced.output.packet.segment.sequence == before.core.sendUna &&
      produced.output.packet.segment.payload == before.core.sent.take head.count &&
      next.outstanding == { head with lastAt := old.now, retried := true } :: tail &&
      next.timeoutCount == expected && next.lastTimedOut == some head.id &&
      next.nextId == old.nextId && next.frontier == old.frontier &&
      next.rto == 2 * old.rto && next.deadline == some (old.now + 2 * old.rto) &&
      next.estimator == old.estimator && next.lastSample == old.lastSample)
    "The real timeout must retain its head identity, tail, and historical recovery fields."

private def checkPartial (actual : M.Step input) (sender : M.Actor) : IO Unit := do
  let before ← R.load (R.endpoint actual.before sender)
  let after ← R.load (R.endpoint actual.result.state sender)
  let some old := before.recovery | throw (IO.userError "The receipt has no old recovery.")
  let some next := after.recovery | throw (IO.userError "The receipt has no new recovery.")
  match old.outstanding, next.outstanding with
  | [_head, tail], [remaining] =>
    R.ensure (remaining == tail && next.lastTimedOut == old.lastTimedOut && next.timeoutCount == old.timeoutCount &&
        next.deadline == some (next.now + next.rto))
      "Partial ACK retirement must retain the literal upper record and prior timeout credit."
  | _, _ => pure ()

private def runLeg (witness : I.Witness report count sender gateway lower upper) (allowance : Nat)
    (losses : List Role) (upperFirst : Bool) : IO (LegRun witness allowance) := do
  let budget ← R.load (R.verify (allowance ≤ 2) "A leg must use at most the shared allowance.")
  let config := configuration witness allowance
  let mut checked := witness.checked
  let mut monitor : O.Monitor := .initial
  let mut remaining := losses
  let mut denied := false
  for _ in List.range 2048 do
    unless monitor.mode == .done do
      R.ensure (!(monitor.mode == .invalid)) "The continued leg lost its monitor."
      let some demand := O.nextDemand config checked.report.final monitor
        | throw (IO.userError "The continued leg has no current demand.")
      if monitor.drops.length == allowance then
        for id in exposed config checked.report.final monitor do
          R.ensure (!(O.allowed config checked.report.final monitor (.dropPacket id)))
            "No current packet may use exhausted shared drop credit."
          denied := true
      let selected := remaining.findSome? fun role =>
        (originalPacket config checked.report.final monitor role).map (fun id => (role, id))
      let event ← match selected with
        | some (_, id) => pure (.dropPacket id)
        | none => R.load (demandEvent upperFirst demand)
      R.ensure (O.allowed config checked.report.final monitor event) "The continued event must pass its current guard."
      let moved ← R.appendOne checked event
      match event with
      | .timeout actor true => checkTimeout moved.actual actor
      | .deliver .. => checkPartial moved.actual sender
      | _ => pure ()
      monitor := O.observe config monitor moved.actual
      checked := moved.next
      match selected with
      | none => pure ()
      | some (role, _) => remaining := remaining.erase role
  R.ensure (monitor.mode == .done && remaining.isEmpty) "The continued leg did not complete within its finite fuel."
  if allowance == 0 then R.ensure denied "The zero-credit reverse leg must reject an actual exposed drop."
  let receiver ← R.load (R.endpoint checked.report.final sender.other)
  let initialReceiver ← R.load (R.endpoint witness.current.cut.report.final sender.other)
  let finalSender ← R.load (R.endpoint checked.report.final sender)
  let some recovery := finalSender.recovery | throw (IO.userError "The completed sender has no recovery.")
  let operations := receiverOperations checked.recorded sender.other
  let reads := operations.filter (fun operation => !operation.readBytes.isEmpty)
  let ids := dropIDs checked.recorded
  R.ensure (monitor.readBytes == lower ++ upper && ids.length == losses.length && ids == monitor.drops &&
      ids.eraseDups == ids && ids.length ≤ allowance && monitor.retries ≤ ids.length &&
      timeoutCount checked.recorded == monitor.retries)
    "Each leg must retain its actual losses and funded timeout count."
  R.ensure (operations.flatMap TCP.ApplicationTrace.Step.releasedPayload == lower ++ upper &&
      operations.flatMap TCP.ApplicationTrace.Step.readBytes == lower ++ upper && reads.length == 1 &&
      receiver.core.received.isEmpty && receiver.receiveStore.held.isEmpty &&
      receiver.receiveStore.frontier == initialReceiver.receiveStore.frontier + (lower ++ upper).length &&
      receiver.receiveStore.nextID == initialReceiver.receiveStore.nextID + 2)
    "The leg must retain prior receipt allocation history and read the exact new ordered bytes once."
  R.ensure (finalSender.pending.isEmpty && finalSender.core.sent.isEmpty && recovery.outstanding.isEmpty &&
      recovery.deadline.isNone && recovery.lastTimedOut.isNone && recovery.timeoutCount == 0 && recovery.duplicateAcks == 0 &&
      checked.report.final.custody.pending.map (·.id) == witness.current.cut.report.final.custody.pending.map (·.id) &&
      checked.report.final.work.pending.map (·.id) == witness.current.cut.report.final.work.pending.map (·.id) &&
      checked.recorded.all (fun actual => match actual.event with | .copyPacket .. | .write .. => false | _ => true))
    "The leg must retire its actual sender and retain old custody and tickets without extra writes or copies."
  let allowed ← R.load (R.verify (O.actions config witness.current.cut.report.final .initial checked.recorded = true)
    "The same continued suffix must pass the raw action check.")
  let serviced ← R.load (R.verify (O.check config witness.current.cut.report.final .initial checked.recorded 3 = true)
    "The same continued suffix must pass three-slot persistent demand service.")
  let observed ← R.load (R.verify (checked.recorded.foldl (O.observe config) .initial = monitor)
    "The raw monitor must read the same stored suffix.")
  let done ← R.load (R.verify (monitor.mode = .done) "The same suffix must end in Done.")
  let events ← R.load (R.verify (checked.events = witness.current.cut.events ++ checked.recorded.map (·.event))
    "The full report must retain the same actual prefix and suffix events.")
  have history := checked_history witness checked events.property
  have completed : ∃ current : Check.CampusTCPRound.Cut input witness.current.complete,
      current.report.final = checked.report.final ∧ current.report.steps = witness.current.cut.report.steps ++ checked.recorded ∧
        Nonempty (Check.CampusTCPTwoProgressEvidence.Complete witness.initial witness.native 10 allowance current monitor) := by
    obtain ⟨current, final, recorded, ⟨evidence⟩⟩ := Check.CampusTCPTwoProgressRecorded.trace_at budget.property checked.suffix
      ((O.actions_correct _ _ _ _).mp allowed.property) checked.recorded.length (Nat.le_refl _)
    have mode : checked.recorded.foldl (O.observe config) .initial = monitor := observed.property
    have atEnd : Check.CampusTCPTwoProgressMonitor.monitorAt
        (Check.CampusTCPTwoProgressSetup.config witness.initial witness.native 10 allowance)
        .initial checked.recorded checked.recorded.length = monitor :=
      (Check.CampusTCPTwoProgressMonitor.monitorAt_length _ _ _).trans mode
    obtain ⟨value⟩ := Check.CampusTCPTwoProgressInvariant.done_evidence evidence (by rw [atEnd]; exact done.property)
    exact ⟨current, final.trans (Check.CampusTCPSchedule.Trace.last_state checked.suffix),
      by simpa only [List.take_length] using recorded, by simpa only [atEnd] using Nonempty.intro value⟩
  return ⟨checked, monitor, allowed.property, serviced.property, observed.property, done.property, history, completed⟩

private def writeFits (state : M.State input) (actor : M.Actor) (bytes : List UInt8) : Prop :=
  match state.connection with
  | .startup .. => False
  | .application _ endpoints =>
    (Check.CampusTCPEnabled.endpoint endpoints actor).pending.length + bytes.length ≤
      (Check.CampusTCPEnabled.endpoint endpoints actor).pendingLimit

private instance (state : M.State input) (actor : M.Actor) (bytes : List UInt8) : Decidable (writeFits state actor bytes) := by
  unfold writeFits
  split <;> infer_instance

private def runCase (input : Check.CampusTCP.Input) (forwardLoss reverseLoss : Nat) (bounded : Bool := false) : IO Unit := do
  let report ← match input.model.check (input.events.take 32) with
    | .error reason => throw (IO.userError reason.message)
    | .ok report => pure report
  let forward ← R.load (I.forward report)
  let forwardRoles := if forwardLoss == 0 then [] else if forwardLoss == 1 then [Role.lower] else [.lower, .upper]
  let forwardRun ← runLeg forward 2 forwardRoles (forwardLoss == 0 || forwardLoss == 1)
  let remaining := 2 - forwardRun.monitor.drops.length
  R.ensure (remaining == reverseLoss) "The reverse credit must come from the actual forward drop log."
  let reverseLower := I.fixturePayload 81 600
  let reverseUpper := I.fixturePayload 97 600
  let bytes := reverseLower ++ reverseUpper
  let beforeServer ← R.load (R.endpoint forwardRun.checked.report.final .server)
  let beforeClient ← R.load (R.endpoint forwardRun.checked.report.final .client)
  let fits ← R.load (R.verify (writeFits forwardRun.checked.report.final .server bytes) "The actual reverse write must fit current pending storage.")
  let written ← R.appendOne forwardRun.checked (.write .server bytes)
  let afterServer ← R.load (R.endpoint written.next.report.final .server)
  let afterClient ← R.load (R.endpoint written.next.report.final .client)
  R.ensure (afterServer.pending == bytes && afterServer.core == beforeServer.core &&
      afterServer.recovery == beforeServer.recovery && afterServer.ackReaction == beforeServer.ackReaction &&
      afterServer.receiveStore == beforeServer.receiveStore && afterClient.core == beforeClient.core &&
      afterClient.recovery == beforeClient.recovery && afterClient.receiveStore == beforeClient.receiveStore &&
      written.actual.result.output.isNone && written.actual.result.read.isEmpty)
    "The single reverse write must retain actual endpoint histories, recovery, read-created ACK work, and receipt allocations."
  have actualWrite : ∃ current : Check.CampusTCPRound.Cut input.model forward.current.complete,
      ∃ value : Check.CampusTCPTwoProgressEvidence.Complete forward.initial forward.native 10 2 current forwardRun.monitor,
        Nonempty (Check.CampusTCPWriteEnabled.WriteMove current .server bytes written.actual) := by
    obtain ⟨current, final, _, ⟨value⟩⟩ := forwardRun.completed
    have space := fits.property
    rw [← final] at space
    simp only [writeFits, current.connection] at space
    exact ⟨current, value, Check.CampusTCPWriteEnabled.Step.write written.actual current .server bytes
      (written.beforeEq.trans final.symm) written.eventEq space⟩
  let reverse ← R.load (I.construct written.next.report written.next.report.steps.length .server .primary reverseLower reverseUpper)
  let sameInitial ← R.load (R.verify (reverse.current.cut.report.final.time = written.next.report.final.time)
    "The reverse witness must use the actual changed post-write cut.")
  let some (_, writer) := written.actual.result.application | throw (IO.userError "The reverse write has no actual operation.")
  R.ensure (writer == reverse.initial.write.writer && writer.event == .write bytes &&
      reverse.initial.senderState.idle.recovery == beforeServer.recovery.getD reverse.initial.senderState.idle.recovery &&
      reverse.initial.receiverState.idle.recovery == beforeClient.recovery.getD reverse.initial.receiverState.idle.recovery)
    "The reverse witness must retain the exact actual writer and both historical recovery states."
  let reverseRoles := if reverseLoss == 0 then [] else if reverseLoss == 1 then [Role.upper] else [.lower, .upper]
  let reverseRun ← runLeg reverse remaining reverseRoles (reverseLoss == 0)
  let all := forwardRun.checked.recorded ++ [written.actual] ++ reverseRun.checked.recorded
  let ids := dropIDs all
  let reads := all.filterMap fun actual => match actual.event with
    | .read actor amount => some (actor, amount, actual.result.read)
    | _ => none
  let writes := all.filterMap fun actual => match actual.event with | .write actor payload => some (actor, payload) | _ => none
  R.ensure (ids == forwardRun.monitor.drops ++ reverseRun.monitor.drops && ids.eraseDups == ids && ids.length == 2 &&
      forwardRun.monitor.drops.length + reverseRun.monitor.drops.length ≤ 2 && timeoutCount all ≤ ids.length &&
      timeoutCount all == 2 && reads == [(.server, 800, I.fixturePayload 17 400 ++ I.fixturePayload 33 400), (.client, 1200, bytes)] &&
      writes == [(.server, bytes)] && all.all (fun actual => match actual.event with | .copyPacket .. => false | _ => true))
    "One continued exchange must retain its global loss log, funded timeouts, exact read order, and single reverse writer."
  let exchangeConfig := Check.CampusTCPTwoExchangeSetup.config forward.initial forward.native 10 2 reverseLower reverseUpper
  let exchange := all.foldl (X.observe exchangeConfig) .initial
  let wholeAllowed ← R.load (R.verify
    (X.actions exchangeConfig forward.current.cut.report.final .initial all = true)
    "The same whole exchange must pass one raw action check.")
  let wholeServiced ← R.load (R.verify
    (X.check exchangeConfig forward.current.cut.report.final .initial all 3 = true)
    "The same whole exchange must pass one persistent demand service check.")
  R.ensure (AC.actions exchangeConfig forward.current.cut.report.final .initial all ==
        X.actions exchangeConfig forward.current.cut.report.final .initial all &&
      SC.check exchangeConfig forward.current.cut.report.final .initial all 3 ==
        X.check exchangeConfig forward.current.cut.report.final .initial all 3)
    "The fast checkers must agree with both short reference checks."
  R.ensure ((Check.CampusTCPTwoExchangeMonitor.nextDemand exchangeConfig forward.current.cut.report.final .initial).isSome &&
      !(SC.check exchangeConfig forward.current.cut.report.final .initial [] 0) &&
      !(X.check exchangeConfig forward.current.cut.report.final .initial [] 0) &&
      (Check.CampusTCPTwoExchangeMonitor.nextDemand exchangeConfig reverseRun.checked.report.final exchange).isNone &&
      SC.check exchangeConfig reverseRun.checked.report.final exchange [] 0 &&
      X.check exchangeConfig reverseRun.checked.report.final exchange [] 0)
    "Zero-slot service must reject a current initial demand and accept the actual Done state."
  let wholeFacts ← R.load (R.verify (exchange.mode = .done ∧ exchange.slots = all.length ∧
      exchange.drops = ids ∧ exchange.timeouts = timeoutCount all)
    "The whole monitor must retain the actual completed prefix, drop IDs, and timeout count.")
  let certificate : WholeCertificate exchangeConfig forward.current.cut.report.final all := {
    actions := wholeAllowed.property
    serviced := (X.check_correct _ _ _ _ _).mp wholeServiced.property
    done := wholeFacts.property.1
    slots := wholeFacts.property.2.1
    drops := wholeFacts.property.2.2.1
    timeouts := wholeFacts.property.2.2.2 }
  let forwardReadSlot := forwardRun.checked.recorded.length - 1
  let writeSlot := forwardRun.checked.recorded.length
  let reverseReadSlot := all.length - 1
  R.ensure (exchange.forward == forwardRun.monitor && exchange.reverse == reverseRun.monitor &&
      exchange.forwardReadSlot == some forwardReadSlot && exchange.writeSlot == some writeSlot &&
      exchange.reverseReadSlot == some reverseReadSlot && forwardReadSlot < writeSlot &&
      writeSlot < reverseReadSlot && reverseReadSlot < all.length &&
      (all[forwardReadSlot]?.map (fun actual => (actual.event, actual.result.read))) ==
        some (.read .server 800, I.fixturePayload 17 400 ++ I.fixturePayload 33 400) &&
      (all[writeSlot]?.map (·.event)) == some (.write .server bytes) &&
      (all[reverseReadSlot]?.map (fun actual => (actual.event, actual.result.read))) ==
        some (.read .client 1200, bytes))
    "The whole monitor must retain both local logs and the actual forward read, reverse write, and reverse read slots."
  let bridgeEvents ← R.load (R.verify (written.next.events = forward.current.cut.events ++ written.next.recorded.map (·.event))
    "The reverse write must extend the same stored report.")
  have bridgeHistory := checked_history forward written.next bridgeEvents.property
  have whole : reverseRun.checked.report.steps = forward.current.cut.report.steps ++ all := by
    calc
      reverseRun.checked.report.steps = reverse.current.cut.report.steps ++ reverseRun.checked.recorded := reverseRun.history
      _ = written.next.report.steps ++ reverseRun.checked.recorded :=
        congrArg (fun prior => prior ++ reverseRun.checked.recorded) (reverse.current.steps.trans List.take_length)
      _ = (forward.current.cut.report.steps ++ written.next.recorded) ++ reverseRun.checked.recorded :=
        congrArg (fun prior => prior ++ reverseRun.checked.recorded) bridgeHistory
      _ = forward.current.cut.report.steps ++ all := by
        simp only [all, written.recordedEq, List.append_assoc]
  let _ := whole
  let _ := actualWrite
  let _ := sameInitial.property
  let _ := certificate
  IO.println s!"Sequential F{forwardLoss}/R{reverseLoss}: {all.length} actual slots, {ids.length} shared drops, {timeoutCount all} funded timeouts."
  if bounded then
    have reverseStart : reverse.current.cut.report.final = written.next.report.final :=
      reverse.current.state.trans (Check.CampusTCPSchedule.Trace.last_state written.next.report.trace)
    have reverseTrace : Check.CampusTCPModel.Trace input.model written.next.report.final
        (reverseRun.checked.recorded.map (·.event)) reverseRun.checked.recorded reverseRun.checked.report.final [] :=
      Eq.mp (congrArg (fun origin => Check.CampusTCPModel.Trace input.model origin
        (reverseRun.checked.recorded.map (·.event)) reverseRun.checked.recorded reverseRun.checked.report.final []) reverseStart)
        reverseRun.checked.suffix
    have joinedTrace : Check.CampusTCPModel.Trace input.model forward.current.cut.report.final
        (all.map (·.event)) all reverseRun.checked.report.final [] := by
      simpa only [all, written.recordedEq, List.map_append, List.append_assoc] using
        Check.CampusTCPSchedule.Trace.append_complete written.next.suffix rfl written.next.accepted reverseTrace
    let joined : R.Checked input.model forward.current.cut.report.final := {
      events := reverseRun.checked.events
      report := reverseRun.checked.report
      supported := reverseRun.checked.supported
      finished := reverseRun.checked.finished
      recorded := all
      suffix := joinedTrace
      accepted := by
        intro actual member
        have selected : actual ∈ written.next.recorded ++ reverseRun.checked.recorded := by
          simpa only [all, written.recordedEq, List.append_assoc] using member
        rcases List.mem_append.mp selected with before | after
        · exact written.next.accepted actual before
        · exact reverseRun.checked.accepted actual after }
    let required := Check.CampusTCPTwoExchangeBounded.boundSlots forward.initial 10 2 3
    let activeSlots := all.length
    R.ensure (activeSlots ≤ required) "The actual exchange must fit the public slot bound."
    let mut current := joined
    let mut monitor := exchange
    for _ in List.range (required - activeSlots) do
      let state ← R.load (R.endpoint current.report.final .server)
      let event : M.Event := .advanceClock .server state.now
      R.ensure (monitor.mode == .done && X.allowed exchangeConfig current.report.final monitor event)
        "Each real padding clock must be allowed by the whole Done selector."
      let moved ← R.appendOne current event
      monitor := X.observe exchangeConfig monitor moved.actual
      current := moved.next
      R.ensure (monitor.mode == .done) "An actual padding clock must retain whole Done."
    R.ensure (monitor.drops == ids && monitor.timeouts == timeoutCount all && monitor.slots == required &&
        monitor.forwardReadSlot == exchange.forwardReadSlot && monitor.writeSlot == exchange.writeSlot &&
        monitor.reverseReadSlot == exchange.reverseReadSlot &&
        dropIDs current.recorded == ids && timeoutCount current.recorded == timeoutCount all &&
        (current.recorded.drop activeSlots).all (fun actual => match actual.event with
          | .advanceClock .server _ => true | _ => false))
      "Padding must retain both reads, the real writer, and the exact shared loss history."
    let fastAllowed ← R.load (R.verify
      (AC.actions exchangeConfig forward.current.cut.report.final .initial current.recorded = true)
      "The same bounded whole trace must pass its action checker.")
    let allowed : { _value : Unit // X.actions exchangeConfig forward.current.cut.report.final .initial current.recorded = true } :=
      ⟨(), (AC.actions_eq _ _ _ _).symm.trans fastAllowed.property⟩
    let fastServiced ← R.load (R.verify
      (SC.check exchangeConfig forward.current.cut.report.final .initial current.recorded 3 = true)
      "The same bounded whole trace must pass its service checker.")
    let serviced : { _value : Unit // X.check exchangeConfig forward.current.cut.report.final .initial current.recorded 3 = true } :=
      ⟨(), (SC.check_eq _ _ _ _ _).symm.trans fastServiced.property⟩
    let length ← R.load (R.verify (required = current.recorded.length)
      "The same bounded whole trace must supply exactly every public bound slot.")
    let events ← R.load (R.verify (current.events = forward.current.cut.events ++ current.recorded.map (·.event))
      "The bounded whole report must retain the same actual recorded suffix.")
    have history := checked_history forward current events.property
    let initialSender := Check.CampusTCPEnabled.endpoint forward.current.cut.endpoints .client
    let initialReceiver := Check.CampusTCPEnabled.endpoint forward.current.cut.endpoints .server
    let reserves ← R.load (R.verify
      (initialSender.core.received = [] ∧ bytes.length ≤ initialReceiver.pendingLimit ∧
        reverseLower.length + reverseUpper.length ≤ initialReceiver.effectiveMSS ∧
        reverseLower.length + reverseUpper.length ≤ initialReceiver.sendWindow ∧
        bytes.length ≤ TCP.Endpoint.offeredWindow initialSender ∧
        reverseLower.length + reverseUpper.length ≤ (forward.initial.gatewayState.session.peer .original).peerWindow.val ∧
        Check.CampusTCPTwoReverseGeometry.reversePrefix forward.initial + reverseLower.length + reverseUpper.length + 2 < TCP.Seq.halfSpace ∧
        reverseLower ≠ [] ∧ reverseUpper ≠ [])
      "The original cut must supply the primitive reverse endpoint, window, and sequence reserves.")
    have endpointReserve : Check.CampusTCPTwoReverseReserves.Initial forward.initial reverseLower reverseUpper :=
      ⟨reserves.property.1, reserves.property.2.1, reserves.property.2.2.1,
        reserves.property.2.2.2.1, reserves.property.2.2.2.2.1⟩
    have gatewayReserve : Check.CampusTCPTwoReverseGeometry.Initial forward.initial reverseLower reverseUpper :=
      ⟨reserves.property.2.2.2.2.2.1, reserves.property.2.2.2.2.2.2.1⟩
    let prior ← R.load (R.verify (forward.current.cut.report.compliant = true)
      "The actual initial report must be compliant for both read permission proofs.")
    have completed : Nonempty (Check.CampusTCPTwoExchangeBounded.Result forward.initial forward.native 10 2 3
        reverseLower reverseUpper current.recorded) :=
      Check.CampusTCPTwoExchangeBounded.complete_by_checked (by decide) (by decide) endpointReserve gatewayReserve
        reserves.property.2.2.2.2.2.2.2.1 reserves.property.2.2.2.2.2.2.2.2 current.suffix
        allowed.property serviced.property (Nat.le_of_eq length.property)
    have boundedCertificate : ∃ result : Check.CampusTCPTwoExchangeBounded.Result forward.initial forward.native 10 2 3
        reverseLower reverseUpper current.recorded,
        result.current.report.final = current.report.final ∧ result.current.report.steps = current.report.steps ∧
          (X.monitorAt exchangeConfig .initial current.recorded required).mode = .done ∧
          result.value.forward.completed.operation.readBytes = I.fixturePayload 17 400 ++ I.fixturePayload 33 400 ∧
          result.value.reverse.completed.operation.readBytes = bytes ∧
          result.value.forward.completed.senderFlight.recovery.outstanding = [] ∧
          result.value.reverse.completed.senderFlight.recovery.outstanding = [] ∧
          (∃ first middle last, first < middle ∧ middle < last ∧ last < required ∧
            current.recorded[first]? = some result.value.forward.completed.reader ∧
            current.recorded[middle]? = some result.value.actual ∧
            current.recorded[last]? = some result.value.reverse.completed.reader) ∧
          (((current.recorded.take required).filter Check.CampusTCPTwoExchangeLoss.isTimeoutOutput).length ≤
              ((current.recorded.take required).filter Check.CampusTCPTwoProgressLossHistory.isDrop).length ∧
            ((current.recorded.take required).filter Check.CampusTCPTwoProgressLossHistory.isDrop).length ≤ 2) ∧
          result.value.forward.completed.reader.result.read = I.fixturePayload 17 400 ++ I.fixturePayload 33 400 ∧
          result.value.reverse.completed.reader.result.read = bytes ∧
          result.value.actual.result.application = some (.server, result.value.start.reverseInitial.write.writer) ∧
          (∀ actor, Nonempty (Check.CampusTCPTwoProgressStart.IdleEndpoint
            (Check.CampusTCPEnabled.endpoint result.current.endpoints actor))) ∧
          (∀ actor, (Check.CampusTCPEnabled.endpoint result.current.endpoints actor).now ≤
            (Check.CampusTCPEnabled.endpoint forward.current.cut.endpoints actor).now + required * 10) ∧
          (∀ index byte, (I.fixturePayload 17 400 ++ I.fixturePayload 33 400)[index]? = some byte →
            ∃ origin : Check.CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.forward.completed index byte,
              Nonempty (Check.CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin forward.initial
                origin.attempt origin.read.origin.localIndex byte) ∧
                Check.CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served) ∧
          (∀ index byte, bytes[index]? = some byte →
            ∃ origin : Check.CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.reverse.completed index byte,
              Nonempty (Check.CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin result.value.start.reverseInitial
                origin.attempt origin.read.origin.localIndex byte) ∧
                Check.CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served) := by
      obtain ⟨result⟩ := completed
      refine ⟨result, ?_, ?_, result.value.mode, result.value.forward.completed.localRead,
        result.value.reverse.completed.localRead, result.value.forward.completed.senderFlight.ledger,
        result.value.reverse.completed.senderFlight.ledger, result.reader_slots, result.budget,
        result.forward_bytes, result.reverse_bytes, result.reverse_writer_recorded, result.final_idle,
        (fun actor => result.now_le (by decide) endpointReserve gatewayReserve
          reserves.property.2.2.2.2.2.2.2.1 reserves.property.2.2.2.2.2.2.2.2 current.suffix
          ((Check.CampusTCPTwoExchangeMonitor.actions_correct _ _ _ _).mp allowed.property)
          (Nat.le_of_eq length.property) actor),
        result.forward_read_permissions prior.property, result.reverse_read_permissions prior.property⟩
      · have same := result.final
        change result.current.report.final = Check.CampusTCPSchedule.stateAt forward.current.cut.report.final current.recorded required at same
        rw [length.property] at same
        exact same.trans (Check.CampusTCPSchedule.Trace.last_state current.suffix)
      · have same := result.history
        change result.current.report.steps = forward.current.cut.report.steps ++ current.recorded.take required at same
        rw [length.property, List.take_length] at same
        exact same.trans history.symm
    let _ := boundedCertificate
    IO.println s!"Sequential bounded F{forwardLoss}/R{reverseLoss}: {activeSlots} active slots, {current.recorded.length} actual slots."

def runInput (input : Check.CampusTCP.Input) : IO Unit := do
  runCase input 0 2 true
  runCase input 1 1
  runCase input 2 0 true
  IO.println "Campus actual sequential two-record exchange plans passed."

def run : IO Unit := do
  let input ← R.load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-receive-gaps/trace.json"))
  runInput input

end NetlibTest.CampusTCPTwoExchangePlans
