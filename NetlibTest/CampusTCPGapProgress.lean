import NetlibTest.CampusTCPGapProgressInitial
import Netlib.Check.CampusTCPGapProgressServiceBound
import Netlib.Check.CampusTCPGapProgressRank
import Netlib.Check.CampusTCPGapProgressBounded

namespace NetlibTest.CampusTCPGapProgress

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input Event Report State Step Actor)
end M
namespace R
export NetlibTest.CampusTCPRecoveryRound (Checked appendOne append checkpoint endpoint ensure load verify)
end R
namespace I
export NetlibTest.CampusTCPGapProgressInitial (Witness Both constructBoth)
end I
namespace O
export Check.CampusTCPGapProgressMonitor (Config Monitor Demand observe nextDemand allowed packetAt boundSlots)
end O
namespace B
export Check.CampusTCPGapProgressServiceBound (actions actions_correct check check_correct Serviced)
end B

variable {input : M.Input} {origin : M.State input} {report : M.Report input events}
  {count slots : Nat} {sender : M.Actor} {lower upper : List UInt8}

structure Generated (witness : I.Witness report count sender lower upper) (slots : Nat) where
  suffix : R.Checked input witness.current.cut.report.final
  monitor : O.Monitor
  activeSlots : Nat
  bound : O.boundSlots witness.config 2 = slots
  allowed : B.actions witness.config witness.current.cut.report.final witness.monitor suffix.recorded = true
  serviced : B.check witness.config witness.current.cut.report.final witness.monitor suffix.recorded 2 = true
  enough : slots ≤ suffix.recorded.length
  exactSlots : suffix.recorded.length = slots
  observed : suffix.recorded.foldl (O.observe witness.config) witness.monitor = monitor
  completion : Check.CampusTCPGapProgressProgress.Completed witness.initial witness.native 2
    (suffix.report.final, monitor)
  read : ∃ actual ∈ suffix.recorded.take slots,
    actual.event = .read sender.other (lower ++ upper).length ∧ actual.result.read = lower ++ upper
  origins : Check.CampusTCPGapProgressBounded.SelectedReads witness.initial 2
    (suffix.report.final, monitor)

inductive LossPoint where
  | dataIngress | dataLink | ackIngress | ackLink
  deriving Repr, BEq, DecidableEq

def lossPoint : Check.CampusTCPRoundMonitor.Phase → Option LossPoint
  | .dataIngress => some .dataIngress
  | .dataLink => some .dataLink
  | .ackIngress => some .ackIngress
  | .ackLink => some .ackLink
  | _ => none

def lossWords : List (List LossPoint) :=
  let first := [LossPoint.dataLink, .ackIngress, .ackLink]
  let later := [LossPoint.dataIngress, .dataLink, .ackIngress, .ackLink]
  [[]] ++ first.map (fun point => [point]) ++ first.flatMap (fun a => later.map (fun b => [a, b]))

structure Template (input : M.Input) where
  prepared : R.Checked input input.initial
  witnesses : I.Both prepared.report

def template (input : M.Input) (events : List M.Event) : IO (Template input) := do
  let mut current := NetlibTest.CampusTCPRecoveryRound.initial input
  for event in events.take 79 do
    let selected ← match event with
      | .serve ticket _ => pure (.serve ticket none)
      | .deliver index _ policy => do
        let some served := current.report.final.services[index]?
          | throw (IO.userError "The template delivery has no actual stored service.")
        let some emission := served.evidence.output
          | throw (IO.userError "The template service has no actual emission.")
        pure (.deliver index emission.bytes policy)
      | other => pure other
    current ← R.append current selected
  let witnesses ← R.load (I.constructBoth current.report)
  return ⟨current, witnesses⟩


private def dropIDs (steps : List (M.Step input)) : List Nat := steps.filterMap fun actual =>
  match actual.event with | .dropPacket id => some id | _ => none

private def positiveClock (actor : M.Actor) (actual : M.Step input) : Bool :=
  match actual.event, R.endpoint actual.before actor, R.endpoint actual.result.state actor with
  | .advanceClock selected millis, .ok before, .ok after =>
    selected == actor && actual.result.supported && actual.result.passed && before.now < after.now && after.now == millis
  | _, _, _ => false

private def selectedTag (demand : O.Demand) (monitor : O.Monitor) : Nat :=
  match demand with | .tick .. => 11 | .timeout .. => 12 | _ => monitor.phase.rank

private def stallEvent (config : O.Config) (state : M.State input) (monitor : O.Monitor)
    (demand : O.Demand) : Except String M.Event := do
  let preferred := if monitor.phase == .needAck then config.sender else config.sender.other
  for positive in [true, false] do
    for actor in [preferred, preferred.other] do
      let selectedState ← R.endpoint state actor
      let event : M.Event := .advanceClock actor (selectedState.now + if positive then config.quantum else 0)
      if O.allowed config state monitor event && !Check.CampusTCPGapProgressMonitor.serves demand event then return event
  throw "The generated demand has no permitted actual clock stall."

private def omission (config : O.Config) (monitor : O.Monitor) (prior : R.Checked input origin) : IO Unit := do
  let selectedState ← R.load (R.endpoint prior.report.final config.sender.other)
  let base := R.checkpoint prior
  let first ← R.append base (.advanceClock config.sender.other selectedState.now)
  let second ← R.append first (.advanceClock config.sender.other selectedState.now)
  let allowed ← R.load (R.verify (B.actions config base.report.final monitor second.recorded = true)
    "The omitted demand must retain two permitted actual clock slots.")
  let _ := (B.actions_correct _ _ _ _).mp allowed.property
  let denied ← R.load (R.verify (B.check config base.report.final monitor second.recorded 2 = false)
    "Two omitted slots must fail the selected demand's service bound.")
  have _missing : ¬B.Serviced config base.report.final monitor second.recorded 2 := by
    intro serviced
    have accepted := (B.check_correct _ _ _ _ _).mpr serviced
    rw [denied.property] at accepted
    contradiction
  pure ()

private def rejectedOperation (prior : R.Checked input origin) (event : M.Event)
    (actor : M.Actor) (decision : TCP.Endpoint.Decision) (supported : Bool) : IO Unit := do
  let old ← R.load (R.endpoint prior.report.final actor)
  match Check.CampusTCPModel.step input prior.report.final event with
  | .error reason => throw (IO.userError reason.message)
  | .ok effect =>
    let some operation := effect.application | throw (IO.userError "The guard case has no actual endpoint result.")
    let next ← R.load (R.endpoint effect.state actor)
    R.ensure (operation.2.result.decision == decision && effect.supported == supported && effect.output.isNone && next == old)
      "The guard case must retain its exact rejection without output or endpoint mutation."

private def overdueAck (prior : R.Checked input origin) (actor : M.Actor) : IO Unit := do
  let selectedState ← R.load (R.endpoint prior.report.final actor)
  let some reaction := selectedState.ackReaction | throw (IO.userError "The ACK deadline case needs actual ACK work.")
  let some due := reaction.due | throw (IO.userError "The actual ACK cause has no stored deadline.")
  rejectedOperation prior (.advanceClock actor (due + 1)) actor (.ackUnsupported .deadline) false

private def exhaustedTimeout (prior : R.Checked input origin) (actor : M.Actor) : IO Unit := do
  let selectedState ← R.load (R.endpoint prior.report.final actor)
  let some recovery := selectedState.recovery | throw (IO.userError "The third timeout case needs current recovery.")
  let some due := recovery.deadline | throw (IO.userError "The third timeout case has no timer.")
  let branch ← R.append prior (.advanceClock actor due)
  rejectedOperation branch (.timeout actor true) actor (.recoveryUnsupported .failureHandling) false

private def checkRetry (before after : M.State input) (actual : M.Step input) (sender : M.Actor)
    (lower upper : List UInt8) (attempt : Nat) : IO Unit := do
  let old ← R.load (R.endpoint before sender)
  let next ← R.load (R.endpoint after sender)
  let some prior := old.recovery | throw (IO.userError "A head retry needs the actual old ledger.")
  let some recovery := next.recovery | throw (IO.userError "A head retry must retain recovery.")
  let head :: tail := prior.outstanding | throw (IO.userError "A head retry needs both original ranges.")
  let some produced := actual.result.output | throw (IO.userError "The timeout has no actual retry output.")
  let some operation := actual.result.application | throw (IO.userError "The timeout has no actual selectedState operation.")
  R.ensure (tail.length == 1 && tail.head?.map (·.count) == some upper.length &&
      operation.1 == sender && operation.2.result.decision == .accepted (.retry lower.length) &&
      produced.output.packet.segment.sequence == old.core.sendUna && produced.output.packet.segment.payload == lower &&
      old.core.sent == lower ++ upper && next.core == old.core && next.pending == old.pending && next.receiveStore == old.receiveStore &&
      recovery.outstanding == { head with lastAt := prior.now, retried := true } :: tail &&
      recovery.now == prior.now && recovery.rto == 2 * prior.rto && recovery.deadline == some (prior.now + 2 * prior.rto) &&
      recovery.timeoutCount == attempt && recovery.nextId == prior.nextId && recovery.frontier == prior.frontier &&
      recovery.estimator == prior.estimator && recovery.lastSample == prior.lastSample &&
      TCP.Recovery.sample recovery (lower.length + upper.length) == none)
    "The actual head retry must retain the upper original, bytes, identities, and Karn history."

private def receiverOperations (steps : List (M.Step input)) (actor : M.Actor) : List TCP.ApplicationTrace.Step :=
  steps.filterMap fun actual => match actual.result.application with
    | some (selected, operation) => if selected == actor then some operation else none
    | none => none

private def checkComplete (witness : I.Witness report count sender lower upper)
    (current : R.Checked input witness.current.cut.report.final) (monitor : O.Monitor) (losses : Nat) : IO Unit := do
  let initial := witness.current.cut.report.final
  let final := current.report.final
  let senderState ← R.load (R.endpoint final sender)
  let receiver ← R.load (R.endpoint final sender.other)
  let some recovery := senderState.recovery | throw (IO.userError "Completion must retain the real sender recovery.")
  let oldSender ← R.load (R.endpoint initial sender)
  let some oldRecovery := oldSender.recovery | throw (IO.userError "The initial sender has no recovery.")
  let operations := receiverOperations current.recorded sender.other
  let releases := operations.filter (fun operation => !operation.releasedPayload.isEmpty)
  let reads := operations.filter (fun operation => !operation.readBytes.isEmpty)
  let drops := dropIDs current.recorded
  let oldPending := (initial.custody.pending.map (·.id)).filter (· != witness.initial.selected.packetID)
  R.ensure (senderState.core.sent.isEmpty && senderState.core.sendUna == senderState.core.sendNext &&
      recovery.outstanding.isEmpty && recovery.deadline.isNone && recovery.timeoutCount == 0 && recovery.lastTimedOut.isNone &&
      receiver.core.received.isEmpty && receiver.receiveStore.held.isEmpty &&
      operations.flatMap TCP.ApplicationTrace.Step.releasedPayload == lower ++ upper &&
      operations.flatMap TCP.ApplicationTrace.Step.readBytes == lower ++ upper && releases.length == 1 && reads.length == 1)
    "The actual suffix must release and read both ranges once and retire the whole sender ledger."
  R.ensure (monitor.phase == .done && monitor.refs.readBytes == lower ++ upper && monitor.retries == losses &&
      monitor.drops == drops && drops.length == losses && drops.eraseDups == drops &&
      final.custody.count .dropped == initial.custody.count .dropped + losses &&
      final.custody.pending.map (·.id) == oldPending && final.work.pending.map (·.id) == initial.work.pending.map (·.id) &&
      current.recorded.all (fun actual => match actual.event with | .copyPacket .. => false | _ => true))
    "The whole selected suffix must charge only its drops and retain the old unrelated pending work."
  if 0 < losses then
    R.ensure (recovery.lastSample.isNone && recovery.estimator == oldRecovery.estimator && recovery.rto == oldRecovery.rto * 2 ^ losses)
      "A retried covering ACK must preserve the stored estimator and backed-off RTO."
  R.ensure (current.recorded.any (positiveClock .client) && current.recorded.any (positiveClock .server))
    "Both endpoint clocks must advance through permitted actual operations."

def generate (witness : I.Witness report count sender lower upper) (slots : Nat) (losses : List LossPoint)
    (checkGuards : Bool := false) (zeroWindow : Bool := false) : IO (Generated witness slots) := do
  let config := witness.config
  let mut current := witness.checked
  let mut monitor := witness.monitor
  let mut remaining := losses
  let mut omitted : List Nat := []
  let mut negatives : List Nat := []
  let mut sawZeroRepeat := false
  if checkGuards then
    rejectedOperation current (.timeout sender true) sender (.reject (.recovery .early)) true
    negatives := [4]
  for _ in List.range slots do
    unless monitor.phase == .done do
      R.ensure (!(monitor.phase == .invalid)) "The actual step must retain the held-gap monitor."
      let some demand := O.nextDemand config current.report.final monitor
        | throw (IO.userError "An unfinished held-gap phase has no actual demand.")
      let tag := selectedTag demand monitor
      if checkGuards && !(omitted.contains tag) then
        omission config monitor current
        omitted := omitted ++ [tag]
      if checkGuards && monitor.phase == .needAck && !(negatives.contains 1) then
        overdueAck current sender.other
        negatives := negatives ++ [1]
      let oldRank := monitor.rank config current.report.final
      let stalled ← R.appendOne current (← R.load (stallEvent config current.report.final monitor demand))
      monitor := O.observe config monitor stalled.actual
      current := stalled.next
      let some selected := O.nextDemand config current.report.final monitor
        | throw (IO.userError "The clock stall lost its current demand.")
      R.ensure (demand == selected) "The actual clock stall must retain the exact pending demand."
      let mut event := selected.event
      let mut dropped := none
      match selected, remaining with
      | .resolution _ packet, point :: rest =>
        if lossPoint monitor.phase == some point then
          event := .dropPacket packet
          dropped := some packet
          remaining := rest
      | _, _ => pure ()
      R.ensure (O.allowed config current.report.final monitor event) "The next actual event must pass the schedule guard."
      if checkGuards && selected == .timeout sender && !(negatives.contains 2) then
        rejectedOperation current (.timeout sender false) sender (.reject .policy) true
        R.ensure (!(O.allowed config current.report.final monitor (.timeout sender false))) "Denied retry policy must fail the positive schedule."
        negatives := negatives ++ [2]
      if checkGuards && !monitor.waiting && monitor.drops.length == 2 && !(negatives.contains 3) then
        match O.packetAt monitor with
        | some packet =>
          R.ensure (!(O.allowed config current.report.final monitor (.dropPacket packet))) "A third drop must exceed the whole-task allowance."
          negatives := negatives ++ [3]
        | none => pure ()
      if zeroWindow && monitor.retries > 0 && monitor.phase == .dataTicket then
        match (Check.CampusTCPModel.beforeService input current.report.final .standby).admission.phase with
        | .data session =>
          R.ensure ((session.sender sender.direction).peerWindow.val == 0) "The actual lower retry must reach a zero-window gateway lane."
          sawZeroRepeat := true
        | _ => throw (IO.userError "The actual standby has no current data session.")
      let before := current.report.final
      let moved ← R.appendOne current event
      monitor := O.observe config monitor moved.actual
      current := moved.next
      R.ensure (monitor.rank config current.report.final < oldRank) "Each selected action, drop, or timer service must decrease the real rank."
      match event with
      | .timeout actor true =>
        checkRetry before current.report.final moved.actual actor lower upper monitor.retries
        if checkGuards && monitor.retries == 2 then
          exhaustedTimeout current sender
          negatives := negatives ++ [5]
      | _ => pure ()
      match dropped with
      | none => pure ()
      | some id =>
        match Check.CampusTCPModel.step input current.report.final (.dropPacket id) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "The same old custody identity cannot be dropped twice.")
  R.ensure (remaining.isEmpty && monitor.phase == .done) "The actual suffix must consume its loss word and complete."
  let used := current.recorded.length
  R.ensure (used ≤ slots) "The actual service-2 suffix must fit its concrete slot bound."
  let selectedState ← R.load (R.endpoint current.report.final sender)
  for _ in List.range (slots - used) do
    let event : M.Event := .advanceClock sender selectedState.now
    R.ensure (O.allowed config current.report.final monitor event) "Padding must use an actual permitted same-time clock."
    let padded ← R.appendOne current event
    monitor := O.observe config monitor padded.actual
    current := padded.next
  let bound ← R.load (R.verify (O.boundSlots witness.config 2 = slots) "The supplied slot count differs from the actual initial reserve.")
  let allowed ← R.load (R.verify (B.actions config witness.current.cut.report.final witness.monitor current.recorded = true)
    "Every evaluated suffix slot must pass the actual schedule guards.")
  let serviced ← R.load (R.verify (B.check config witness.current.cut.report.final witness.monitor current.recorded 2 = true)
    "Each persistent demand must be served in at most two evaluated slots.")
  let enough ← R.load (R.verify (slots ≤ current.recorded.length) "The bounded theorem needs the whole supplied slot prefix.")
  let exactSlots ← R.load (R.verify (current.recorded.length = slots) "Only evaluated slots may supply the selected prefix length.")
  let observed ← R.load (R.verify (current.recorded.foldl (O.observe config) witness.monitor = monitor)
    "The final observer must read this same actual stored suffix.")
  let basis : Check.CampusTCPGapProgressBounded.Basis witness.initial 10 2 :=
    ⟨witness.geometry, witness.wire, by decide, by decide⟩
  have sufficient : O.boundSlots witness.config 2 ≤ current.recorded.length := by
    rw [bound.property]
    exact enough.property
  have completion := Check.CampusTCPGapProgressBounded.completes_final_checked
    (native := witness.native) basis current.suffix allowed.property serviced.property sufficient
  have completionAt : Check.CampusTCPGapProgressProgress.Completed witness.initial witness.native 2
      (current.report.final, monitor) := by
    change Check.CampusTCPGapProgressProgress.Completed witness.initial witness.native 2
      (current.report.final, current.recorded.foldl (O.observe config) witness.monitor) at completion
    simpa only [observed.property] using completion
  have actualRead := Check.CampusTCPGapProgressBounded.read_by_checked
    (native := witness.native) basis current.suffix allowed.property serviced.property sufficient
  checkComplete witness current monitor losses.length
  if zeroWindow then R.ensure sawZeroRepeat "The window case must exercise an actual repeated lower range."
  if checkGuards then
    R.ensure (omitted.length == 10) "Omissions must cover eight ordinary phases, timer ticks, and timeout service."
    R.ensure (negatives.length == 5) "Guard cases must cover ACK time, policy, drop credit, early time, and exhausted retries."
  IO.println s!"Held-gap {repr sender} loss word {repr losses}: {used} active slots, {slots} evaluated slots."
  return ⟨current, monitor, used, bound.property, allowed.property, serviced.property, enough.property,
    exactSlots.property, observed.property, completionAt,
    by simpa only [← witness.config_actual, bound.property] using actualRead,
    Check.CampusTCPGapProgressBounded.completed_read_origins completionAt⟩

def run : IO Unit := do
  let input ← R.load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-receive-gaps/trace.json"))
  let prepared ← NetlibTest.CampusTCPGapProgressInitial.prepare input
  R.ensure (lossWords.length == 16) "Each actual cut must cover all sixteen legal loss words."
  for losses in lossWords do
    let guards := losses == [.ackLink, .ackLink]
    let _ ← generate prepared.witnesses.forward 644 losses guards
    let _ ← generate prepared.witnesses.reverse 624 losses guards
  let closed := { input.model with
    active := { input.model.active with capacity := 1200 }
    passive := { input.model.passive with capacity := 800 } }
  let zero ← template closed input.events
  let _ ← generate zero.witnesses.forward 644 [.ackLink] false true
  let _ ← generate zero.witnesses.reverse 624 [.ackLink] false true
  let wrapped := { input.model with
    active := { input.model.active with iss := TCP.Seq.ofNat (TCP.Seq.modulus - 200) }
    passive := { input.model.passive with iss := TCP.Seq.ofNat (TCP.Seq.modulus - 400) } }
  let wrapping ← template wrapped input.events
  let _ ← generate wrapping.witnesses.forward 644 [.ackLink, .ackLink]
  let _ ← generate wrapping.witnesses.reverse 624 [.ackLink, .ackLink]
  IO.println "Campus generated held-gap progress suffixes passed."

end NetlibTest.CampusTCPGapProgress
