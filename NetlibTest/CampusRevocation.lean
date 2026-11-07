import NetlibTest.CampusRevocationFixture
import Netlib.Check.CampusRevocation

namespace NetlibTest.CampusRevocation

open Netlib Packet Protocol
open StatefulFailover (Gateway)
open CampusRevocationFixture

namespace Model
export Netlib.Check.CampusRevocationModel
  (Input State Event Step Datagram Report check stateAt)
end Model

namespace Control
export Netlib.Check.CampusRevocationControl
  (actions service installed ready pending Demand)
end Control

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def rejects (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def atIndex (values : List α) (index : Nat) : IO α :=
  match values[index]? with
  | some value => pure value
  | none => throw (IO.userError s!"Missing revocation fixture index {index}.")

private def stateAt (report : Model.Report input budget events) (slot : Nat) : Model.State :=
  Model.stateAt (Netlib.Check.CampusRevocationModel.Input.initial input) report.steps slot

private def datagram (value : Model.Datagram) (gateway : Gateway) (target : Header)
    (payload : List UInt8) : IO Unit := do
  let decoded ← load (UDP.decodeIPv4 value.bytes)
  ensure (value.gateway == gateway && value.header == target && decoded.header == target &&
    decoded.datagram.payload == payload && value.input.datagram.payload == payload &&
    decoded.ip.packet.ttl == 63 && value.input.ip.packet.ttl == 64 &&
    decoded.ip.packet.tos == 32 && decoded.ip.packet.identification == 4321 &&
    decoded.ip.packet.dontFragment && decoded.datagram.checksum != 0)
    "Every queued emission must retain its actual gateway, translated bytes, payload, metadata, and checksums."

private def missingService (fixture : Fixture) (events : List Model.Event) (ready : Bool)
    (pendingOutputs : Nat) : IO Unit := do
  let targets ← load (Check.CampusRevocationTargets.Targets.check fixture.input 7
    fixture.primaryDeny fixture.standbyDeny)
  let report ← load (Model.check fixture.input events)
  let cut := fixture.logoffSlot + 1
  ensure (report.rawPassed && Control.actions report cut targets &&
    !Control.service report cut targets 2 && Control.ready targets report.final == ready &&
    report.final.queue.pending.length == pendingOutputs)
    "A genuine starved trace must retain its actual outputs and fail bounded persistent-demand service."
  rejects (Check.CampusRevocation.certify report cut 2 fixture.primaryDeny fixture.standbyDeny)
    "A trace with unserved persistent installation or delivery demand must not receive a certificate."

private def sourceRejections (fixture : Fixture) : IO Unit := do
  rejects (Check.CampusRevocationTargets.Targets.check fixture.input 7
    fixture.primaryPermit fixture.standbyDeny)
    "The current revoked prefix must reject a primary permit target."
  rejects (Check.CampusRevocationTargets.Targets.check fixture.input 7
    fixture.primaryDeny fixture.standbyPermit)
    "The current revoked prefix must reject a standby permit target."
  rejects (Check.CampusRevocationTargets.Targets.check fixture.input 6
    fixture.primaryDeny fixture.standbyDeny)
    "A deny source cannot certify the earlier currently permitted prefix."
  let forged := { fixture.primaryDeny with
    forward := { fixture.primaryDeny.forward with rules := fixture.primaryPermit.forward.rules } }
  rejects (Check.CampusRevocationTargets.Target.check fixture.input 7 .primary forged)
    "An installed pipeline with altered literal rules must fail its retained source comparison."
  let active := { fixture.targets .primary with
    pipeline := { (fixture.targets .primary).pipeline with forwardDefault := .permit } }
  rejects (Check.SessionInstallation.check fixture.input.authentication fixture.input.requirements 7
    active fixture.input.handoff.configs 100000)
    "An altered installed fallback must fail its retained source comparison."
  let changed := { fixture.input with handoff := { fixture.input.handoff with
    configs := fixture.input.handoff.configs.map fun source =>
      if source.id == forged.id then forged else source } }
  let checked ← load (Check.SessionInstallation.check changed.authentication changed.requirements 7
    (Check.SafeHandoff.configuration changed.handoff.routing .primary forged) changed.handoff.configs 100000)
  ensure (!checked.passed)
    "A changed source and matching installed permit must still fail current policy equivalence."
  rejects (Check.CampusRevocationTargets.Targets.check changed 7 forged fixture.standbyDeny)
    "Matching changed source metadata cannot certify a policy that permits the revoked scope."

private def packetCalls (fixture : Fixture) (report : Model.Report fixture.input 100000 fixture.events) : IO Unit := do
  let first := fixture.completionCut
  for offset in [:8] do
    let actual ← atIndex report.steps (first + offset)
    match actual.effect.payload with
    | .packet call outcome _ certificate =>
      let selected := offset % 4
      let gateway : Gateway := if selected < 2 then .primary else .standby
      let reverse := offset % 2 == 1
      let fresh := 4 ≤ offset
      let direction : FlowNAT.Direction := if fresh || !reverse then .original else .reply
      let classification : StatefulACL.CTState := if fresh || offset == 0 then .new else .established
      let source := if reverse then fixture.reply else fixture.request
      let afterDestination : Header := if reverse then
          { wire.reverse with destination := original.source, destinationPort := original.sourcePort }
        else { original with destination := wire.destination, destinationPort := wire.destinationPort }
      let before := actual.before.campus.deployment.handoff.gateways
      let after := actual.effect.state.campus.deployment.handoff.gateways
      let expectedSeen := if gateway == .primary && offset < 2 then false else true
      ensure (call.gateway == gateway && call.zone == (if fresh then freshZone else protectedZone) &&
        call.source.bytes == source.bytes && outcome.attachment.fresh == fresh &&
        outcome.attachment.direction == direction && outcome.attachment.classification == classification &&
        outcome.afterDestination == afterDestination && outcome.output.isNone &&
        outcome.disposition == .forwardDrop && certificate.passed &&
        actual.effect.payload.policyPassed == some true && actual.effect.payload.arrivals.isEmpty &&
        (before.table gateway).records == [⟨entry, expectedSeen⟩] &&
        outcome.state.records == [⟨entry, expectedSeen || reverse⟩] &&
        after.table gateway == outcome.state && after.epoch == before.epoch + 1)
        "Cached and fresh attempts must use the actual stored deny policy and persistent table in both directions."
      ensure ((after.table gateway).records.all (fun record =>
        record.entry.flow.originalZone == protectedZone && record.entry.flow.replyZone == protectedZone) &&
        actual.effect.state.queue.pending.isEmpty && actual.effect.served.isEmpty)
        "Fresh denial must retain the protected cached binding and confirm no zone-eight record or queue output."
    | _ => throw (IO.userError "Each post-drain probe must retain its actual wire-packet result and current certificate.")

private def rollback (fixture : Fixture) : IO Unit := do
  let input := { fixture.input with handoff := { fixture.input.handoff with
    events := fixture.input.handoff.events ++ [observe 14 (.install .primary fixture.primaryPermit)] } }
  let call : Netlib.Check.CampusRevocationModel.PacketCall :=
    ⟨.primary, protectedZone, fixture.request, none⟩
  let events := fixture.events ++ [network 14, .packet call]
  let report ← load (Model.check input events)
  let targets ← load (Check.CampusRevocationTargets.Targets.check input 7
    fixture.primaryDeny fixture.standbyDeny)
  ensure (report.rawPassed && !Control.actions report (fixture.logoffSlot + 1) targets &&
    report.final.queue.pending.length == 1)
    "A real rollback to permit must compute its output while failing the revocation action check."
  rejects (Check.CampusRevocation.certify report (fixture.logoffSlot + 1) 2
    fixture.primaryDeny fixture.standbyDeny)
    "A later actual policy rollback must invalidate certification even after an earlier completed drain."
  let actual ← atIndex report.steps (report.steps.length - 1)
  match actual.effect.payload with
  | .packet _ outcome _ certificate =>
    ensure (!certificate.passed && outcome.output.isSome &&
      actual.effect.payload.arrivals.map (·.header) == [wire])
      "The rejected rollback must expose actual stale forwarding instead of replacing it with an observed deny."
  | _ => throw (IO.userError "The rollback counterexample must end with the actual cached packet attempt.")

private def unavailableGateways (fixture : Fixture) : IO Unit := do
  let input := { fixture.input with handoff := { fixture.input.handoff with
    events := fixture.input.handoff.events ++ [
      observe 14 (.handoff .client .standby), observe 15 (.fence .primary)] } }
  let events := fixture.events ++ [network 14, network 15]
  let fenced ← load (Model.check input events)
  ensure (fenced.final.campus.deployment.handoff.gateways.isFenced .primary &&
    !fenced.final.campus.deployment.withdrawn &&
    fenced.final.campus.deployment.handoff.gateways.owners.client == .standby &&
    fenced.final.campus.deployment.handoff.gateways.owners.server == .standby &&
    fenced.final.campus.deployment.handoff.work.pending.isEmpty)
    "The regression must reach an actually fenced primary through route handoff and drained ticket work."
  let call : Netlib.Check.CampusRevocationModel.PacketCall :=
    ⟨.primary, protectedZone, fixture.request, none⟩
  let fencedAccepted := (Netlib.Check.CampusRevocationModel.step input 100000 fenced.final (.packet call)).isOk
  let withdrawn ← load (Model.check input (events ++ [campus .withdraw]))
  ensure (withdrawn.final.campus.deployment.withdrawn &&
    withdrawn.final.campus.deployment.archive == some withdrawn.final.campus.deployment.handoff.gateways.primary)
    "The regression must perform actual withdrawal and retain the exact archived primary table."
  let withdrawnAccepted :=
    (Netlib.Check.CampusRevocationModel.step input 100000 withdrawn.final (.packet call)).isOk
  ensure (!fencedAccepted && !withdrawnAccepted)
    s!"Direct packet processing must reject unavailable gateways: fenced accepted {fencedAccepted}, withdrawn accepted {withdrawnAccepted}."

private def certified (fixture : Fixture) (report : Model.Report fixture.input 100000 fixture.events) :
    IO (Nat × Nat) := do
  let cut := fixture.logoffSlot + 1
  let certificate ← load (Check.CampusRevocation.certify report cut 2 fixture.primaryDeny fixture.standbyDeny)
  let result := certificate.result
  let deadline := Check.CampusRevocationControl.deadline report cut 2
  let currentPrefix := report.cut result.slot result.bounds.2.2
  have _ := result.history
  have _ := result.delivered_bytes
  have _ := result.authentication
  ensure (result.slot == fixture.completionCut && cut ≤ result.slot && result.slot ≤ deadline &&
    result.slot ≤ report.steps.length && report.steps.length < deadline &&
    currentPrefix.steps.length == result.slot && result.current.queue.pending.isEmpty &&
    Control.ready certificate.targets result.current && result.current.campus.authentication == 7 &&
    result.current.queue.delivered.map (·.bytes) ==
      (Netlib.Check.CampusRevocationModel.arrivals (report.steps.take result.slot)).map (·.bytes) &&
    result.current.queue.delivered.map (·.header) == [wire, wire, original.reverse, original.reverse])
    "The public certificate must select the real early drain cut without padding the report to its coarse deadline."
  for gateway in [Gateway.primary, .standby] do
    ensure (Check.CampusRevocationTargets.sameConfiguration
      (result.current.campus.deployment.handoff.configurations gateway) (certificate.targets.get gateway) &&
      Check.CampusRevocationTargets.sameConfiguration (certificate.targets.get gateway) (fixture.targets gateway))
      "The public result must retain each actual installed native source target."
  if selected : (stateAt report cut).campus.deployment.handoff.binding = some entry then
    have _ := result.binding entry selected
    ensure (result.current.campus.deployment.handoff.binding == some entry)
      "The certificate must retain the selected historical NAT binding."
  else throw (IO.userError "The actual trigger cut must retain the protected binding.")
  for slot in [:report.steps.length] do
    if later : result.slot ≤ slot then
      match found : report.steps[slot]? with
      | none => throw (IO.userError "The certified future slot must remain inside the actual report.")
      | some actual =>
        have _ := result.future_arrivals slot later actual found
        have _ := result.future_served slot later actual found
        ensure (actual.effect.payload.arrivals.isEmpty && actual.effect.served.isEmpty &&
          actual.before.queue.pending.isEmpty && Control.ready certificate.targets actual.before)
          "Every actual later attempt must retain the installed barriers and empty arrival and delivery lists."
  rejects (Check.CampusRevocation.certify report cut 0 fixture.primaryDeny fixture.standbyDeny)
    "A zero persistent-service bound must not produce a certificate."
  rejects (Check.CampusRevocation.certify report fixture.logoffSlot 2 fixture.primaryDeny fixture.standbyDeny)
    "The step before actual Logoff must not replace the trigger cut."
  rejects (Check.CampusRevocation.certify report cut 2 fixture.primaryPermit fixture.standbyDeny)
    "The public certificate must reject a target that still permits the revoked application."
  let shortEvents := fixture.preparation ++ [auth 6]
  let short ← load (Model.check fixture.input shortEvents)
  let shortTargets ← load (Check.CampusRevocationTargets.Targets.check fixture.input 7
    fixture.primaryDeny fixture.standbyDeny)
  ensure (Control.actions short cut shortTargets && Control.service short cut shortTargets 2)
    "A finite trace that ends at Logoff has no complete service window after the cut."
  rejects (Check.CampusRevocation.certify short cut 2 fixture.primaryDeny fixture.standbyDeny)
    "A short uncompleted prefix must not receive a certificate from vacuous finite service checks."
  return (result.slot, deadline)

def run : IO Unit := do
  let fixture ← build
  let targets ← load (Check.CampusRevocationTargets.Targets.check fixture.input 7
    fixture.primaryDeny fixture.standbyDeny)
  let report ← load (Model.check fixture.input fixture.events)
  let cut := fixture.logoffSlot + 1
  ensure (report.rawPassed && Control.actions report cut targets && Control.service report cut targets 2)
    "The full actual report must pass raw observations, revocation actions, and bounded service."
  let (completion, deadline) ← certified fixture report
  let prepared := stateAt report fixture.logoffSlot
  ensure (prepared.campus.authentication == 6 && prepared.campus.network == 11 &&
    (Check.SessionInstallation.current fixture.input.authentication prepared.campus.authentication).auth.authorized &&
    prepared.queue.pending.map (·.header) == [wire, original.reverse] &&
    prepared.campus.deployment.handoff.work.pending.map (·.id) == [2] &&
    prepared.campus.deployment.handoff.work.completed.map (·.id) == [0, 1])
    "Preparation must derive both real queues and the outstanding third route ticket under current permission."
  let closed := stateAt report cut
  ensure (closed.campus.authentication == 7 &&
    !(Check.SessionInstallation.current fixture.input.authentication 7).auth.authorized &&
    (Check.SessionInstallation.current fixture.input.authentication 7).session.credential.isNone &&
    !Control.ready targets closed && closed.queue.pending.length == 2)
    "Actual Logoff must clear current permission while retaining the two earlier emissions and both stale policies."
  let stale ← atIndex report.steps fixture.staleSlot
  ensure (stale.effect.payload.rawPassed && stale.effect.payload.policyPassed == some false &&
    stale.effect.payload.arrivals.map (·.header) == [original.reverse])
    "The actual stale standby service must retain matching bytes and the false old current-policy verdict."
  match stale.effect.payload with
  | .campus _ result _ => match result.payload with
    | .network evidence => match evidence.model.served with
      | some served =>
        ensure (served.ticket.id == 2 && served.ticket.value.gateway == .standby &&
          served.ticket.value.source.bytes == fixture.staleReply.bytes &&
          served.configuration.id == fixture.standbyPermit.id && served.outcome.output.isSome)
          "The stale output must follow the actual earlier assignment and stored standby permit."
      | none => throw (IO.userError "The stale interval must retire its real third route ticket.")
    | _ => throw (IO.userError "The stale interval must be a network service operation.")
  | _ => throw (IO.userError "The stale interval must retain the delegated campus operation.")
  let barrier := stateAt report fixture.barrierCut
  ensure (Control.ready targets barrier && barrier.queue.pending.length == 3 &&
    barrier.queue.delivered.length == 1 && barrier.campus.deployment.handoff.binding == some entry &&
    barrier.campus.deployment.handoff.work.pending.isEmpty &&
    barrier.campus.deployment.handoff.work.completed.map (·.id) == [0, 1, 2] &&
    barrier.campus.deployment.handoff.gateways.owners.client == .primary &&
    barrier.campus.deployment.handoff.gateways.owners.server == .standby)
    "Both installed barriers must retain all three earlier emissions, exact route-ticket history, and selected owners."
  datagram (← atIndex barrier.queue.delivered 0) .primary wire fixture.established.packet.datagram.payload
  datagram (← atIndex barrier.queue.pending 0) .primary wire requestPayload
  datagram (← atIndex barrier.queue.pending 1) .standby original.reverse replyPayload
  datagram (← atIndex barrier.queue.pending 2) .standby original.reverse stalePayload
  ensure ((← atIndex barrier.queue.pending 1).bytes != (← atIndex barrier.queue.pending 2).bytes)
    "Equal reply headers must retain two distinct actual payload-bearing FIFO occurrences."
  for offset in [:3] do
    let actual ← atIndex report.steps (fixture.barrierCut + offset)
    let old ← atIndex barrier.queue.pending offset
    ensure (actual.effect.payload.capacity == 1 && actual.effect.served.map (·.bytes) == [old.bytes] &&
      actual.before.queue.pending.length == 3 - offset &&
      actual.effect.state.queue.pending.length == 2 - offset)
      "Each unit delivery must retire exactly the next actual old FIFO occurrence."
  let drained := stateAt report fixture.completionCut
  ensure (drained.queue.pending.isEmpty && drained.queue.delivered.map (·.header) ==
    [wire, wire, original.reverse, original.reverse] &&
    drained.queue.delivered.map (·.bytes) ==
      barrier.queue.delivered.map (·.bytes) ++ barrier.queue.pending.map (·.bytes))
    "The drain cut must retain all earlier delivery history and clear exactly the three barrier-time emissions."
  packetCalls fixture report
  ensure (report.final.queue.pending.isEmpty && report.final.queue.delivered.map (·.bytes) ==
    drained.queue.delivered.map (·.bytes) &&
    report.final.campus.deployment.handoff.gateways.primary.records == [⟨entry, true⟩] &&
    report.final.campus.deployment.handoff.gateways.standby.records == [⟨entry, true⟩])
    "All later denied packets and empty delivery must retain the actual drained history and replied protected tables."
  sourceRejections fixture
  missingService fixture (fixture.preparation ++ [auth 6] ++ List.replicate 4 .idle) false 2
  missingService fixture (fixture.preparation ++ [auth 6, network 11, network 12] ++ List.replicate 4 .idle) false 3
  missingService fixture (fixture.preparation ++ fixture.revocation ++ List.replicate 4 .idle) true 3
  missingService fixture (fixture.preparation ++ fixture.revocation ++ [.deliver 1, .deliver 1] ++
    List.replicate 4 .idle) true 1
  rollback fixture
  unavailableGateways fixture
  IO.println s!"Campus revocation: {report.steps.length} actual slots, completion {completion}, deadline {deadline}, three old outputs drained, eight actual denied packet attempts."

end NetlibTest.CampusRevocation
