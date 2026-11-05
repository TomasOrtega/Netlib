import Netlib.Check.AttachmentCampus

namespace NetlibTest.AttachmentCampus

open Netlib Packet Protocol
open StatefulFailover (Gateway)
open IngressAttachment (NamespaceRef InterfaceRef)
namespace Model
export Netlib.Check.AttachmentCampus (Input State Event Observation Probe GuardConfig Specification
  current process step actualPolicy desiredPolicy originCheck provenanceCheck)
end Model

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def ns (gateway : Gateway) : NamespaceRef := match gateway with
  | .primary => ⟨20, 1⟩
  | .standby => ⟨30, 1⟩
private def port (gateway : Gateway) (index : Nat) (bounded : 0 < index ∧ index ≤ 2147483647) : InterfaceRef :=
  ⟨ns gateway, ⟨index, bounded⟩, 1⟩
private def client (gateway : Gateway) := port gateway 2 (by decide)
private def server (gateway : Gateway) := port gateway 3 (by decide)
private def attacker (gateway : Gateway) := port gateway 4 (by decide)
private def sync (gateway : Gateway) := port gateway 5 (by decide)
private def authPort : InterfaceRef := ⟨⟨10, 1⟩, ⟨2, by decide⟩, 1⟩
private def traffic (header : Header) : Match := {
  source := some ⟨header.source, 32⟩, destination := some ⟨header.destination, 32⟩,
  protocol := some header.protocol, sourcePorts := some (PortRange.single header.sourcePort),
  destinationPorts := some (PortRange.single header.destinationPort) }
private def syncTraffic : Match := {
  protocol := some Packet.Protocol.udp
  destinationPorts := some (PortRange.single 3780) }
private def maintenance : List Compile.IngressAttachment.Maintenance :=
  [⟨sync .primary, syncTraffic⟩, ⟨sync .standby, syncTraffic⟩]

example (input : Model.Input) (state : Model.State) (valid : Check.AttachmentCampus.Provenance input state)
    (attachment : IngressAttachment.ExpectedAttachment) (member : attachment ∈ Check.AttachmentCampus.staged state) :
    attachment.origin.source = Check.SessionInstallation.current input.campus.authentication attachment.origin.after :=
  (valid.1 attachment member).2.2.1

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)
private def load : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)
private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def predicate (left right : Lean.Json) : Lean.Json := Lean.Json.mkObj [
  ("match", Lean.Json.mkObj [("op", .str "=="), ("left", left), ("right", right)])]
private def metadata (key : String) : Lean.Json := Lean.Json.mkObj [("meta", Lean.Json.mkObj [("key", .str key)])]
private def field (protocol name : String) : Lean.Json := Lean.Json.mkObj [
  ("payload", Lean.Json.mkObj [("protocol", .str protocol), ("field", .str name)])]
private def rule (handle index : Nat) (header : Option Header) : Lean.Json :=
  let predicates :=  [predicate (metadata "iif") (Lean.toJson index), predicate (metadata "l4proto") (Lean.toJson (17 : Nat))]
  let tests := match header with
    | some value => [
        predicate (field "ip" "saddr") (.str (Import.PacketFields.addressText value.source)),
        predicate (field "ip" "daddr") (.str (Import.PacketFields.addressText value.destination)),
        predicate (field "udp" "sport") (Lean.toJson value.sourcePort.val),
        predicate (field "udp" "dport") (Lean.toJson value.destinationPort.val)]
    | none => [predicate (field "udp" "dport") (Lean.toJson (3780 : Nat))]
  Lean.Json.mkObj [("rule", Lean.Json.mkObj [
    ("family", .str "ip"), ("table", .str "attachment_test"), ("chain", .str "ingress"),
    ("handle", Lean.toJson handle), ("expr", Lean.toJson (predicates ++ tests ++ [Lean.Json.mkObj [("accept", .null)]]))])]

private def guard (gateway : Gateway) (allow : Bool) : IO Model.GuardConfig := do
  let rules := (if allow then [rule 2 2 (some original), rule 3 3 (some wire.reverse)] else []) ++ [rule 4 5 none]
  let json := Lean.Json.mkObj [("nftables", Lean.toJson ([
    Lean.Json.mkObj [("metainfo", Lean.Json.mkObj [("version", .str "1.1.3"),
      ("release_name", .str "Commodore Bullmoose #4"), ("json_schema_version", Lean.toJson (1 : Nat))])],
    Lean.Json.mkObj [("table", Lean.Json.mkObj [("family", .str "ip"), ("name", .str "attachment_test"), ("handle", Lean.toJson (1 : Nat))])],
    Lean.Json.mkObj [("chain", Lean.Json.mkObj [("family", .str "ip"), ("table", .str "attachment_test"),
      ("name", .str "ingress"), ("handle", Lean.toJson (1 : Nat)), ("type", .str "filter"),
      ("hook", .str "prerouting"), ("prio", Lean.toJson (-300 : Int)), ("policy", .str "drop")])]] ++ rules))]
  let source ← load (Import.NftablesIngress.Snapshot.fromJson (ns gateway) [] json)
  pure ⟨(if gateway = .primary then "primary" else "standby") ++ toString allow, gateway, source⟩

private def source (header : Header) (payload : List UInt8 := [0, 255, 65, 0, 17]) : IO SafeHandoff.Source := do
  let transport ← load (UDP.encode header.source header.destination
    (UDP.computed header.source header.destination header.sourcePort header.destinationPort payload))
  let bytes ← load (IPv4.encode ⟨32, 4321, true, 64, Packet.Protocol.udp, header.source, header.destination, transport⟩)
  match decoded : UDP.decodeIPv4 bytes with
  | .error error => throw (IO.userError error)
  | .ok packet => pure ⟨bytes, packet, decoded⟩

private def emptyObservation : Check.WireForwarding.PacketObservation := ⟨none, none, none, none, none, none, none⟩
private def observe (event : Check.SafeHandoff.Event) : Check.SafeHandoff.Observation := ⟨0, event, none, none, none, .null⟩

private def input (reply : SafeHandoff.Source) : IO Model.Input := do
  let base ← load (Check.CampusDeployment.Bundle.parse (← IO.FS.readFile "examples/campus/bundle.json"))
  let some first := base.input.handoff.events[2]? | throw (IO.userError "Missing pinned establishment input.")
  let .establish _ request _ := first.event | throw (IO.userError "Wrong pinned establishment input.")
  let events := base.input.handoff.events.take 5 ++ [
    observe (.assign .original request (some 0)), observe (.assign .reply reply (some 1)),
    observe (.serve 1 reply emptyObservation), observe (.serve 0 request emptyObservation)]
  let campus := { base.input with handoff := { base.input.handoff with events } }
  let specifications : List Model.Specification := [
    ⟨"a-client", .primary, client .primary, .original, traffic original⟩,
    ⟨"a-server", .primary, server .primary, .reply, traffic wire.reverse⟩,
    ⟨"b-client", .standby, client .standby, .original, traffic original⟩,
    ⟨"b-server", .standby, server .standby, .reply, traffic wire.reverse⟩]
  pure ⟨campus, ns, authPort,
    authPort :: [client .primary, server .primary, attacker .primary, sync .primary,
      client .standby, server .standby, attacker .standby, sync .standby],
    specifications, [← guard .primary true, ← guard .standby true, ← guard .primary false, ← guard .standby false]⟩

private def perform (input : Model.Input) (before : Model.State) (event : Model.Event)
    (expected : Bool := true) : IO Model.State := do
  let result ← load (Model.step input 100000 before ⟨0, event, .null⟩)
  ensure (result.state.check input && result.transition.detail.passed == expected)
    "The actual transition must preserve invariants and retain the expected observation verdict."
  pure result.state

private def authenticationPrefix (input : Model.Input) : IO Model.State := do
  let mut state := input.initial
  for index in [:19] do state ← perform input state (.authentication index)
  state ← perform input state (.network 0 none none)
  perform input state (.network 1 none none)

private def staged (input : Model.Input) (before : Model.State) : IO Model.State := do
  let mut state := before
  for specification in input.specifications do state ← perform input state (.stage specification.id)
  perform input state (.maintenance maintenance)

private def install (input : Model.Input) (state : Model.State) (gateway : Gateway) (allow : Bool) : IO Model.State := do
  let configured ← guard gateway allow
  perform input state (.installGuard configured.id)

private def prepared (input : Model.Input) : IO Model.State := do
  let authenticated ← authenticationPrefix input
  reject (Model.step input 100000 authenticated ⟨0, .protect, .null⟩)
    "Naturally empty tracking does not replace the explicit reset marker."
  let reset ← perform input authenticated .reset
  let staged ← staged input reset
  reject (Model.step input 100000 staged ⟨0, .stage "a-client", .null⟩)
    "One specification cannot manufacture multiple historical attachment origins."
  reject (Model.step input 100000 staged ⟨0, .maintenance [⟨attacker .primary, traffic original⟩], .null⟩)
    "A static maintenance exception cannot overlap protected application traffic."
  reject (Model.step input 100000 staged ⟨0, .protect, .null⟩)
    "The protected suffix requires actual guards at both gateways."
  let first ← install input staged .primary true
  reject (Model.step input 100000 first ⟨0, .protect, .null⟩)
    "Installing one guard does not install its standby counterpart."
  let second ← install input first .standby true
  perform input second .protect

private def probe (input : Model.Input) (before : Model.State) (gateway : Gateway) (ingress : InterfaceRef)
    (direction : FlowNAT.Direction) (source : SafeHandoff.Source) (decision : Bool)
    (observed : Check.WireForwarding.PacketObservation) (passed : Bool := true) : IO Model.State := do
  perform input before (.probe ⟨gateway, ingress, direction, source, decision, observed, none, none⟩) passed

private def baseline (input : Model.Input) : IO Unit := do
  let authenticated ← authenticationPrefix input
  let some observation := input.campus.handoff.events[2]? | throw (IO.userError "Missing establishment observation.")
  let .establish _ request observed := observation.event | throw (IO.userError "Wrong establishment observation.")
  let impersonated ← probe input authenticated .primary (attacker .primary) .original request true observed
  ensure (impersonated.deployment.handoff.gateways.primary == unreplied &&
    impersonated.deployment.handoff.binding.isNone && (impersonated.owners .primary).isNone && !impersonated.enforced)
    "The unsafe installed header-only prelude must expose actual impersonated tracking without inventing historical ownership."
  reject (Model.step input 100000 impersonated ⟨0, .protect, .null⟩)
    "A protected suffix must require the explicit empty-table reset."
  let cleared ← perform input impersonated .reset
  ensure (cleared.resetObserved && cleared.deployment.handoff.gateways.primary == .initial &&
    cleared.deployment.handoff.gateways.standby == .initial)
    "Reset must erase the actual unsafe baseline before protecting a new binding."

private def provenance (input : Model.Input) (state : Model.State) : IO Unit := do
  let some first := state.attachments.head? | throw (IO.userError "Missing staged attachment.")
  ensure (first.value.origin.after == 19 && first.value.origin.source ==
    Check.SessionInstallation.current input.campus.authentication 19 && Model.originCheck input state first.value)
    "Staged ownership must come from the consumed authentication prefix, not an independently supplied session snapshot."
  let forged := { first with value := { first.value with origin := { first.value.origin with
    source := { first.value.origin.source with session := { first.value.origin.source.session with now := 1 } } } } }
  let altered := { state with attachments := forged :: state.attachments.tail }
  ensure (!(altered.check input) && !(Model.provenanceCheck input altered))
    "A plausible session with altered source state cannot replace the actual origin prefix."
  reject (Model.step input 100000 altered ⟨0, .reset, .null⟩)
    "Forged attachment source state must be rejected before any transition."
  let future := { first with value := { first.value with origin := { first.value.origin with after := 20 } } }
  ensure (!(({ state with attachments := future :: state.attachments.tail } : Model.State).check input))
    "An attachment cannot claim a future authentication prefix."
  let inventedRound := { first with value := { first.value with origin := { first.value.origin with
    source := { first.value.origin.source with auth := { first.value.origin.source.auth with
      round := first.value.origin.source.auth.round + 1 } } } } }
  ensure (!(({ state with attachments := inventedRound :: state.attachments.tail } : Model.State).check input))
    "A claimed authentication round must come from the exact recorded EAP prefix."
  let owner : IngressAttachment.OwnedBinding := ⟨entry, first.value.origin⟩
  ensure (!(({ state with owners := fun gateway => if gateway = .primary then some owner else none } : Model.State).check input))
    "Historical ownership cannot name a record absent from the actual ordinary table."
  let reused := { client .primary with birth := 2 }
  let live := state.live.map (fun value => if value = client .primary then reused else value)
  let changed := { state with live }
  ensure (changed.check input && !(IngressPolicy.check (Model.actualPolicy changed .primary) (Model.desiredPolicy input changed .primary)))
    "A reused numeric index keeps its installed permit while the desired lifetime attachment becomes stale."
  reject (Model.step input 100000 state ⟨0, .maintenance [⟨attacker .primary, traffic original⟩], .null⟩)
    "Maintenance cannot introduce application bypasses after enforcement."

private def protectedFlow (input : Model.Input) (request reply : SafeHandoff.Source) : IO Model.State := do
  let ready ← prepared input
  provenance input ready
  let rejected ← probe input ready .primary (attacker .primary) .original request false emptyObservation
  let rejected ← probe input rejected .standby (attacker .standby) .original request false emptyObservation
  ensure (rejected.deployment.handoff.gateways.primary == .initial)
    "Fresh spoofing must be rejected before an ordinary attachment creates a row."
  let established ← perform input rejected (.network 2 (some (client .primary)) (some true))
  let cached ← probe input established .primary (attacker .primary) .original request false emptyObservation
  let forged ← probe input cached .primary (attacker .primary) .reply reply false emptyObservation
  ensure (forged.deployment.handoff.gateways.primary == unreplied && (forged.owners .primary).any (fun owner =>
    owner.entry == entry && owner.origin.after == 19))
    "Cached and forged-reply rejection must preserve exact tracking and the original client's historical ownership."
  let selected ← perform input forged (.network 3 none none)
  let committed ← perform input selected (.network 4 none none)
  ensure ((committed.owners .standby).any (fun owner => (committed.owners .primary).any (fun source =>
    owner.entry == source.entry && owner.origin == source.origin)) && committed.deployment.handoff.gateways.standby == unreplied)
    "Ordinary replication must inherit actual historical ownership without fabricating server authentication."
  let committed ← probe input committed .standby (attacker .standby) .original request false emptyObservation
  let committed ← probe input committed .standby (attacker .standby) .reply reply false emptyObservation
  ensure (committed.deployment.handoff.gateways.standby == unreplied)
    "Copied reply tuples cannot bypass the standby's actual ingress guard."
  let one ← perform input committed (.network 5 none none)
  perform input one (.network 6 none none)

private def logoff (input : Model.Input) (pending : Model.State) (reply : SafeHandoff.Source) : IO Unit := do
  let closed ← perform input pending (.authentication 19)
  ensure (closed.check input && !(Model.current input closed).state.session.permits input.campus.authentication.context input.campus.application)
    "Logoff must revoke current permission while preserving valid historical origin records."
  let staleResult ← load (Model.step input 100000 closed
    ⟨0, .probe ⟨.primary, server .primary, .reply, reply, true, emptyObservation, none, none⟩, .null⟩)
  match staleResult.transition.detail with
  | .probe _ gate (.processed _ _ _ _ certificate) =>
    ensure (gate.checked.decision && !gate.checked.guardEquivalent && !certificate.passed && !staleResult.transition.detail.passed)
      "The stale installed permit must disagree with both current ingress intent and current ordinary-session policy."
  | _ => throw (IO.userError "A stale actual permit must reach the actual ordinary probe.")
  let stale := staleResult.state
  ensure (stale.deployment.handoff.gateways.primary == replied && stale.deployment.handoff.work.pending.map (·.id) == [0, 1])
    "A stale actual permit must compute real reply tracking while reporting its current-session and output mismatch."
  let denied ← install input closed .primary false
  let wrongObservation ← perform input denied (.network 7 (some (server .primary)) (some true)) false
  ensure (wrongObservation.deployment.handoff.gateways.primary == unreplied &&
    wrongObservation.deployment.handoff.work.pending.map (·.id) == [0])
    "An incorrect observed verdict cannot replace the actual rejection or its ticket retirement."
  let retired ← perform input denied (.network 7 (some (server .primary)) (some false))
  ensure (retired.deployment.handoff.gateways.primary == unreplied && retired.deployment.handoff.gateways.standby == unreplied &&
    retired.deployment.handoff.work.pending.map (·.id) == [0] && retired.deployment.handoff.work.completed.map (·.id) == [1])
    "A guarded reply must retire its actual ticket before ordinary tracking and bypass the stale ordinary permit."
  let finished ← perform input retired (.network 8 (some (client .primary)) (some false))
  ensure (finished.deployment.handoff.work.pending.isEmpty && finished.deployment.handoff.work.completed.map (·.id) == [1, 0] &&
    finished.deployment.handoff.gateways.primary == unreplied)
    "Original and reply tickets may be rejected out of order without ordinary CT mutation."
  reject (Model.step input 100000 finished ⟨0, .network 8 (some (client .primary)) (some false), .null⟩)
    "A consumed network observation cannot be reused to retire another ticket."
  let extended := { input with campus := { input.campus with handoff := { input.campus.handoff with
    events := input.campus.handoff.events ++ [observe (.handoff .client .standby),
      observe (.handoff .server .standby), observe (.fence .primary)] } } }
  let moved ← perform extended finished (.network 9 none none)
  let moved ← perform extended moved (.network 10 none none)
  let fenced ← perform extended moved (.network 11 none none)
  let archived ← perform extended fenced .withdraw
  ensure (archived.deployment.archive == some unreplied && (archived.owners .primary).isSome &&
    (archived.owners .standby).isSome && !archived.live.any (fun value => decide (value.ns = ns .primary)))
    "Withdrawal archives the actual primary table while preserving historical ownership and removing primary interface lifetimes."
  let configured ← guard .primary false
  reject (Model.step extended 100000 archived ⟨0, .installGuard configured.id, .null⟩)
    "A withdrawn primary cannot receive live ingress configuration."
  reject (Model.step extended 100000 archived
    ⟨0, .probe ⟨.primary, server .primary, .reply, reply, false, emptyObservation, none, none⟩, .null⟩)
    "Historical primary metadata cannot authorize a postwithdrawal live packet probe."
  let denied ← install extended archived .standby false
  let rejected ← probe extended denied .standby (attacker .standby) .reply reply false emptyObservation
  ensure (rejected.deployment.archive == some unreplied && rejected.deployment.handoff.gateways.standby == unreplied)
    "Live standby rejection must preserve the historical primary archive and both protected records."

private def routeRole (input : Model.Input) : IO Unit := do
  let routing := input.campus.handoff.routing
  let primary := { routing.primary with
    routes := routing.primary.routes.map (fun route => { route with output := route.output.map (fun output => { output with nextNode := "wrong-role" }) })
    bindings := routing.primary.bindings.map (fun output => { output with nextNode := "wrong-role" }) }
  let events := input.campus.handoff.events.map (fun observation => match observation.event with
    | .establish zone source observed => { observation with event := .establish zone source { observed with nextHop := none } }
    | _ => observation)
  let altered := { input with campus := { input.campus with handoff := { input.campus.handoff with
    routing := { routing with primary }, events } } }
  let before ← prepared altered
  let result ← load (Model.step altered 100000 before ⟨0, .network 2 (some (client .primary)) (some true), .null⟩)
  match result.transition.detail with
  | .ordinary evidence gate =>
    ensure (evidence.passed && gate.all Check.AttachmentCampus.Gate.passed &&
      evidence.applicationMatches && !evidence.topologyMatches && !result.transition.detail.passed)
      "Unchanged packet bytes and omitted observed next-hop metadata must not hide an incorrect computed endpoint role."
  | _ => throw (IO.userError "The wrong-role route must still perform actual ordinary processing.")

def run : IO Unit := do
  let reply ← source wire.reverse
  let input ← input reply
  let some observation := input.campus.handoff.events[2]? | throw (IO.userError "Missing establishment observation.")
  let .establish _ request _ := observation.event | throw (IO.userError "Wrong establishment observation.")
  baseline input
  let pending ← protectedFlow input request reply
  logoff input pending reply
  routeRole input

end NetlibTest.AttachmentCampus
