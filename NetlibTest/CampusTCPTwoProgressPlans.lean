import NetlibTest.CampusTCPTwoProgressInitial
import Netlib.Check.CampusTCPTwoProgressSetup
import Netlib.Check.CampusTCPTwoProgressBounded

namespace NetlibTest.CampusTCPTwoProgressPlans

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input Event Report State Step Actor Gateway)
end M
namespace R
export NetlibTest.CampusTCPRecoveryRound (Checked appendOne endpoint ensure load verify)
end R
namespace I
export NetlibTest.CampusTCPTwoProgressInitial (Witness prepare)
end I
namespace O
export Check.CampusTCPTwoProgressMonitor
  (Config Monitor Lane Demand observe nextDemand allowed exposedPacket actions check actions_correct check_correct)
end O
namespace G
export Check.CampusTCPGapProgressMonitor (Demand)
end G

variable {input : M.Input} {report : M.Report input events} {count : Nat}
variable {sender : M.Actor} {gateway : M.Gateway} {lower upper : List UInt8}

def configuration (witness : I.Witness report count sender gateway lower upper) : O.Config :=
  Check.CampusTCPTwoProgressSetup.config witness.initial witness.native 10 2

private def exactRead (sender : M.Actor) (bytes : List UInt8) (actual : M.Step input) : Bool :=
  match actual.event with
  | .read actor size => actor == sender.other && size == bytes.length && actual.result.read == bytes
  | _ => false

private def retired (state : M.State input) (sender : M.Actor) : Bool :=
  match R.endpoint state sender with
  | .error _ => false
  | .ok endpoint =>
    match endpoint.recovery with
    | none => false
    | some recovery => endpoint.core.sent.isEmpty && endpoint.pending.isEmpty && recovery.outstanding.isEmpty &&
        endpoint.core.sendUna == endpoint.core.sendNext && recovery.deadline.isNone &&
        recovery.lastTimedOut.isNone && recovery.timeoutCount == 0

structure Generated (witness : I.Witness report count sender gateway lower upper) where
  suffix : R.Checked input witness.current.cut.report.final
  monitor : O.Monitor
  passed : suffix.recorded.all (fun actual => actual.result.supported && actual.result.passed) = true
  allowed : O.actions (configuration witness) witness.current.cut.report.final .initial suffix.recorded = true
  serviced : O.check (configuration witness) witness.current.cut.report.final .initial suffix.recorded 3 = true
  observed : suffix.recorded.foldl (O.observe (configuration witness)) .initial = monitor
  read : suffix.recorded.any (exactRead sender (lower ++ upper)) = true
  retirement : retired suffix.report.final sender = true

private inductive Edge where
  | ingress | link
  deriving Repr, BEq, DecidableEq

private inductive Path where
  | lowerData | upperData | lowerAck | upperAck | retryData (attempt : Nat) | retryAck (attempt : Nat)
  deriving Repr, BEq, DecidableEq

private structure Site where
  path : Path
  edge : Edge
  deriving Repr, BEq, DecidableEq

private structure Plan where
  name : String
  preferUpper : Bool := false
  losses : List Site := []
  timeoutUpper : List Bool := []
  chunks : Nat := 2

private def dataEdge : Check.CampusTCPRoundMonitor.Phase → Option Edge
  | .dataIngress => some .ingress
  | .dataLink => some .link
  | _ => none

private def ackEdge : Check.CampusTCPRoundMonitor.Phase → Option Edge
  | .ackIngress => some .ingress
  | .ackLink => some .link
  | _ => none

private def candidate (config : O.Config) (state : M.State input) (path : Path)
    (edge : Option Edge) (lane : O.Lane) : List (Site × Nat) :=
  (do
    let edge ← edge
    let packet ← O.exposedPacket config state lane
    pure (({ path, edge } : Site), packet)).toList

private def candidates (config : O.Config) (state : M.State input) (monitor : O.Monitor) : List (Site × Nat) :=
  candidate config state .lowerData (dataEdge monitor.lower.phase) monitor.lower ++
    candidate config state .upperData (dataEdge monitor.upper.phase) monitor.upper ++
    candidate config state (.retryData monitor.retries) (dataEdge monitor.retry.phase) monitor.retry ++
    match monitor.ack with
    | none => []
    | some lane =>
      let path := if lane.refs.dataOutput == monitor.lower.refs.dataOutput then Path.lowerAck
        else if lane.refs.dataOutput == monitor.upper.refs.dataOutput then .upperAck else .retryAck monitor.retries
      candidate config state path (ackEdge lane.phase) lane

private def demandEvent (preferUpper : Bool) : O.Demand → Except String M.Event
  | .single demand => .ok demand.event
  | .originalChoice lower upper =>
    match (if preferUpper then upper.or lower else lower.or upper) with
    | some demand => .ok demand.event
    | none => .error "The current original choice has no actual operation."

private def receiverOperations (steps : List (M.Step input)) (actor : M.Actor) : List TCP.ApplicationTrace.Step :=
  steps.filterMap fun actual => match actual.result.application with
    | some (selected, operation) => if selected == actor then some operation else none
    | none => none

private def dropIDs (steps : List (M.Step input)) : List Nat := steps.filterMap fun actual =>
  match actual.event with | .dropPacket id => some id | _ => none

private def timeoutHeads (steps : List (M.Step input)) (sender : M.Actor) : List Nat :=
  steps.filterMap fun actual => match actual.event, R.endpoint actual.before sender with
    | .timeout selected true, .ok state =>
      if selected == sender then state.recovery.bind (fun recovery => recovery.outstanding.head?.map (·.id)) else none
    | _, _ => none

private def checkTimeout (actual : M.Step input) (sender : M.Actor) : IO Unit := do
  let before ← R.load (R.endpoint actual.before sender)
  let after ← R.load (R.endpoint actual.result.state sender)
  let some old := before.recovery | throw (IO.userError "The timeout has no current recovery.")
  let some next := after.recovery | throw (IO.userError "The timeout lost current recovery.")
  let head :: tail := old.outstanding | throw (IO.userError "The timeout has no current head.")
  let some produced := actual.result.output | throw (IO.userError "The timeout has no actual output.")
  let some operation := actual.result.application | throw (IO.userError "The timeout has no actual local step.")
  let expectedCount := if old.lastTimedOut == some head.id then old.timeoutCount + 1 else 1
  R.ensure (operation.1 == sender && operation.2.result.decision == .accepted (.retry head.count) &&
      produced.output.packet.segment.sequence == before.core.sendUna &&
      produced.output.packet.segment.payload == before.core.sent.take head.count &&
      after.core == before.core && after.pending == before.pending && after.receiveStore == before.receiveStore &&
      next.outstanding == { head with lastAt := old.now, retried := true } :: tail &&
      next.timeoutCount == expectedCount && next.lastTimedOut == some head.id &&
      next.rto == 2 * old.rto && next.deadline == some (old.now + 2 * old.rto) &&
      next.nextId == old.nextId && next.frontier == old.frontier &&
      next.estimator == old.estimator && next.lastSample == old.lastSample)
    "The actual timeout must update only the current head and retain the literal tail and estimator."

private def checkPartial (actual : M.Step input) (sender : M.Actor) : IO Unit := do
  let before ← R.load (R.endpoint actual.before sender)
  let after ← R.load (R.endpoint actual.result.state sender)
  let some old := before.recovery | throw (IO.userError "The partial ACK has no old recovery.")
  let some next := after.recovery | throw (IO.userError "The partial ACK has no retained recovery.")
  match old.outstanding, next.outstanding with
  | [_head, tail], [remaining] =>
    R.ensure (remaining == tail && next.lastTimedOut == old.lastTimedOut && next.timeoutCount == old.timeoutCount &&
        next.deadline == some (next.now + next.rto))
      "Partial retirement must preserve the literal tail and prior timeout metadata."
  | _, _ => pure ()

private def verifyFinal (witness : I.Witness report count sender gateway lower upper)
    (plan : Plan) (current : R.Checked input witness.current.cut.report.final) (monitor : O.Monitor) : IO Unit := do
  let initial := witness.current.cut.report.final
  let final := current.report.final
  let operations := receiverOperations current.recorded sender.other
  let releases := operations.filter (fun operation => !operation.releasedPayload.isEmpty)
  let reads := operations.filter (fun operation => !operation.readBytes.isEmpty)
  let dropped := dropIDs current.recorded
  let sends := current.recorded.filterMap fun actual => match actual.event with
    | .send actor size true => some (actor, size)
    | _ => none
  let expectedHeads := plan.timeoutUpper.map (fun upperHead => witness.initial.senderState.idle.recovery.nextId + if upperHead then 1 else 0)
  let receiver ← R.load (R.endpoint final sender.other)
  R.ensure (monitor.mode == .done && monitor.readBytes == lower ++ upper &&
      monitor.retries == expectedHeads.length && timeoutHeads current.recorded sender == expectedHeads &&
      monitor.drops == dropped && dropped.length == plan.losses.length && dropped.length ≤ 2 &&
      monitor.retries ≤ dropped.length && dropped.eraseDups == dropped)
    "The same suffix must retain its exact shared loss log and actual timeout-head sequence."
  R.ensure (operations.flatMap TCP.ApplicationTrace.Step.releasedPayload == lower ++ upper &&
      operations.flatMap TCP.ApplicationTrace.Step.readBytes == lower ++ upper &&
      releases.length == plan.chunks && reads.length == 1 && receiver.core.received.isEmpty && receiver.receiveStore.held.isEmpty)
    "The actual ordered release chunks and one full read must equal the selected batch."
  R.ensure (sends == [(sender, lower.length), (sender, upper.length)] &&
      final.custody.pending.map (·.id) == initial.custody.pending.map (·.id) &&
      final.custody.count .dropped == initial.custody.count .dropped + dropped.length &&
      final.work.pending.map (·.id) == initial.work.pending.map (·.id) &&
      current.recorded.all (fun actual => match actual.event with
        | .copyPacket .. | .write .. => false
        | _ => true))
    "The generated suffix must retain old pending work and use no extra copy or write."
  if plan.losses.isEmpty then
    let payloads := operations.filterMap fun operation => match operation.event with
      | .receive packet => if packet.packet.segment.payload.isEmpty then none else some packet.packet.segment.payload
      | _ => none
    R.ensure (payloads.head? == some (if plan.preferUpper then upper else lower))
      "The lossless plan must use its actual selected first delivery."

private def generate (witness : I.Witness report count sender gateway lower upper) (plan : Plan)
    (announce : Bool := true) : IO (Generated witness) := do
  let config := configuration witness
  let mut current := witness.checked
  let mut monitor : O.Monitor := .initial
  let mut remaining := plan.losses
  let mut deniedThird := false
  for _ in List.range 2048 do
    unless monitor.mode == .done do
      R.ensure (!(monitor.mode == .invalid)) "The actual suffix lost the two-record monitor."
      let some demand := O.nextDemand config current.report.final monitor
        | throw (IO.userError "The unfinished monitor has no current demand.")
      let exposed := candidates config current.report.final monitor
      if monitor.drops.length == 2 then
        for (_, packet) in exposed do
          R.ensure (!(O.allowed config current.report.final monitor (.dropPacket packet)))
            "A third selected drop must exceed the one shared allowance."
          deniedThird := true
      let loss := exposed.find? (fun value => remaining.contains value.1)
      let event ← match loss with
        | some (site, packet) => do
          if site == ⟨.lowerData, .ingress⟩ then
            R.ensure (monitor.upper.phase == .needSend)
              "The lower ingress loss must remain exposed while the upper send is pending."
          pure (.dropPacket packet)
        | none => R.load (demandEvent plan.preferUpper demand)
      R.ensure (O.allowed config current.report.final monitor event) "The generated event must pass the current monitor guard."
      let moved ← R.appendOne current event
      match event with
      | .timeout actor true => checkTimeout moved.actual actor
      | .deliver .. => checkPartial moved.actual sender
      | _ => pure ()
      monitor := O.observe config monitor moved.actual
      current := moved.next
      match loss with
      | none => pure ()
      | some (site, packet) =>
        remaining := remaining.erase site
        match Check.CampusTCPModel.step input current.report.final (.dropPacket packet) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "One consumed custody identity cannot be dropped twice.")
  R.ensure (monitor.mode == .done && remaining.isEmpty) "The finite test fuel ended before this actual plan completed."
  if plan.losses.length == 2 then
    R.ensure deniedThird "The two-loss plan must test exhausted shared drop credit."
  verifyFinal witness plan current monitor
  let passed ← R.load (R.verify (current.recorded.all (fun actual => actual.result.supported && actual.result.passed) = true)
    "Every evaluated suffix step must be supported and passed.")
  let allowed ← R.load (R.verify (O.actions config witness.current.cut.report.final .initial current.recorded = true)
    "The current monitor must allow every stored suffix event.")
  let serviced ← R.load (R.verify (O.check config witness.current.cut.report.final .initial current.recorded 3 = true)
    "Each persistent demand must be served in three evaluated slots.")
  let observed ← R.load (R.verify (current.recorded.foldl (O.observe config) .initial = monitor)
    "The final observer must read this same stored suffix.")
  let read ← R.load (R.verify (current.recorded.any (exactRead sender (lower ++ upper)) = true)
    "The same stored suffix must contain the exact selected read.")
  let retirement ← R.load (R.verify (retired current.report.final sender = true)
    "The same final endpoint must have empty sent, pending, and recovery ledgers.")
  let _ := (O.actions_correct _ _ _ _).mp allowed.property
  let _ := (O.check_correct _ _ _ _ _).mp serviced.property
  if announce then
    IO.println s!"Two-record {repr sender} {plan.name}: {current.recorded.length} evaluated slots, {monitor.retries} timeouts."
  return ⟨current, monitor, passed.property, allowed.property, serviced.property, observed.property, read.property, retirement.property⟩

private def plans : List Plan :=
  let edges := [Edge.ingress, .link]
  [{ name := "lower-first" }, { name := "upper-first", preferUpper := true, chunks := 1 }] ++
    edges.flatMap (fun edge => [
      { name := s!"lower-data-{repr edge}", preferUpper := true, losses := [⟨.lowerData, edge⟩], timeoutUpper := [false], chunks := 1 },
      { name := s!"upper-data-{repr edge}", losses := [⟨.upperData, edge⟩], timeoutUpper := [true] },
      { name := s!"partial-ack-unused-{repr edge}", losses := [⟨.lowerAck, edge⟩] },
      { name := s!"full-ack-{repr edge}", losses := [⟨.upperAck, edge⟩], timeoutUpper := [true] },
      { name := s!"lower-full-ack-{repr edge}", preferUpper := true,
        losses := [⟨.lowerAck, edge⟩], timeoutUpper := [false], chunks := 1 },
      { name := s!"gap-ack-unused-{repr edge}", preferUpper := true, losses := [⟨.upperAck, edge⟩], chunks := 1 },
      { name := s!"retry-data-{repr edge}", preferUpper := true,
        losses := [⟨.lowerData, .ingress⟩, ⟨.retryData 1, edge⟩], timeoutUpper := [false, false], chunks := 1 },
      { name := s!"retry-ack-{repr edge}", preferUpper := true,
        losses := [⟨.lowerData, .ingress⟩, ⟨.retryAck 1, edge⟩], timeoutUpper := [false, false], chunks := 1 },
      { name := s!"tail-retry-data-{repr edge}",
        losses := [⟨.upperAck, .ingress⟩, ⟨.retryData 1, edge⟩], timeoutUpper := [true, true] },
      { name := s!"tail-retry-ack-{repr edge}",
        losses := [⟨.upperData, .ingress⟩, ⟨.retryAck 1, edge⟩], timeoutUpper := [true, true] }]) ++
    edges.flatMap (fun first => edges.flatMap (fun second => [
      { name := s!"partial-ack-and-upper-data-{repr first}-{repr second}",
        losses := [⟨.lowerAck, first⟩, ⟨.upperData, second⟩], timeoutUpper := [false, true] },
      { name := s!"both-originals-{repr first}-{repr second}",
        losses := [⟨.lowerData, first⟩, ⟨.upperData, second⟩], timeoutUpper := [false, true] },
      { name := s!"gap-ack-and-lower-data-{repr first}-{repr second}", preferUpper := true,
        losses := [⟨.upperAck, first⟩, ⟨.lowerData, second⟩], timeoutUpper := [false], chunks := 1 }]))

private structure BoundedCase (witness : I.Witness report count sender gateway lower upper) where
  suffix : R.Checked input witness.current.cut.report.final
  allowed : O.actions (configuration witness) witness.current.cut.report.final .initial suffix.recorded = true
  serviced : O.check (configuration witness) witness.current.cut.report.final .initial suffix.recorded 3 = true
  enough : Check.CampusTCPTwoProgressBounded.boundSlots witness.initial 10 2 3 ≤ suffix.recorded.length
  certificate : ∃ result : Check.CampusTCPTwoProgressBounded.Result witness.initial witness.native 10 2 3 suffix.recorded,
    (∃ slot, slot < Check.CampusTCPTwoProgressBounded.boundSlots witness.initial 10 2 3 ∧
      suffix.recorded[slot]? = some result.value.completed.reader ∧
      result.value.completed.reader.event = .read sender.other (lower ++ upper).length ∧
      result.value.completed.reader.result.read = lower ++ upper) ∧
    result.value.timeouts ≤ 2 ∧
    ∀ index byte, (lower ++ upper)[index]? = some byte →
      ∃ origin : Check.CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.completed index byte,
        Nonempty (Check.CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin witness.initial origin.attempt origin.read.origin.localIndex byte) ∧
          Check.CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served

private def boundedCase (witness : I.Witness report count sender gateway lower upper) : IO (BoundedCase witness) := do
  let plan : Plan := {
    name := "bounded-both-originals"
    losses := [⟨.lowerData, .ingress⟩, ⟨.upperData, .ingress⟩]
    timeoutUpper := [false, true] }
  let generated ← generate witness plan false
  let config := configuration witness
  let required := Check.CampusTCPTwoProgressBounded.boundSlots witness.initial 10 2 3
  let activeSlots := generated.suffix.recorded.length
  let mut current := generated.suffix
  let mut monitor := generated.monitor
  R.ensure (monitor.mode == .done && monitor.retries == 2 && monitor.drops.length == 2)
    "The bounded case must finish both actual head retries before padding."
  R.ensure (activeSlots ≤ required) "The active bounded case must fit the public slot bound."
  for _ in List.range (required - activeSlots) do
    let state ← R.load (R.endpoint current.report.final sender)
    let event : M.Event := .advanceClock sender state.now
    R.ensure (monitor.mode == .done && O.allowed config current.report.final monitor event)
      "Each padding clock must be allowed in the current Done state."
    let moved ← R.appendOne current event
    monitor := O.observe config monitor moved.actual
    current := moved.next
    R.ensure (monitor.mode == .done) "A real padding clock must retain Done."
  let allowed ← R.load (R.verify (O.actions config witness.current.cut.report.final .initial current.recorded = true)
    "The same bounded trace must pass the exact action checker.")
  let serviced ← R.load (R.verify (O.check config witness.current.cut.report.final .initial current.recorded 3 = true)
    "The same bounded trace must pass the exact three-slot service checker.")
  let enough ← R.load (R.verify (Check.CampusTCPTwoProgressBounded.boundSlots witness.initial 10 2 3 ≤ current.recorded.length)
    "The same bounded trace must supply every public bound slot.")
  let prior ← R.load (R.verify (witness.current.cut.report.compliant = true)
    "The actual retained report must be compliant for service permissions.")
  have completion : Nonempty (Check.CampusTCPTwoProgressBounded.Result witness.initial witness.native 10 2 3 current.recorded) :=
    Check.CampusTCPTwoProgressBounded.complete_by_checked (by decide) (by decide) current.suffix
      allowed.property serviced.property enough.property
  have certificate : ∃ result : Check.CampusTCPTwoProgressBounded.Result witness.initial witness.native 10 2 3 current.recorded,
      (∃ slot, slot < Check.CampusTCPTwoProgressBounded.boundSlots witness.initial 10 2 3 ∧
        current.recorded[slot]? = some result.value.completed.reader ∧
        result.value.completed.reader.event = .read sender.other (lower ++ upper).length ∧
        result.value.completed.reader.result.read = lower ++ upper) ∧
      result.value.timeouts ≤ 2 ∧
      ∀ index byte, (lower ++ upper)[index]? = some byte →
        ∃ origin : Check.CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.completed index byte,
          Nonempty (Check.CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin witness.initial origin.attempt origin.read.origin.localIndex byte) ∧
            Check.CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served := by
    obtain ⟨result⟩ := completion
    obtain ⟨slot, within, recorded⟩ := result.reader_slot
    exact ⟨result, ⟨slot, within, recorded, result.read_event, result.read_bytes⟩,
      result.retry_bound, result.read_permissions prior.property⟩
  IO.println s!"Bounded {repr sender}: {activeSlots} active slots, {current.recorded.length} bound slots, two actual head retries."
  return ⟨current, allowed.property, serviced.property, enough.property, certificate⟩

def runInput (input : Check.CampusTCP.Input) : IO Unit := do
  let prepared ← I.prepare input
  for plan in plans do
    let _ ← generate prepared.witnesses.forward plan
    let _ ← generate prepared.witnesses.reverse plan
  IO.println "Campus actual two-record monitor plans passed."
  let _ ← boundedCase prepared.witnesses.forward
  let _ ← boundedCase prepared.witnesses.reverse

def run : IO Unit := do
  let input ← R.load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-receive-gaps/trace.json"))
  runInput input

end NetlibTest.CampusTCPTwoProgressPlans
