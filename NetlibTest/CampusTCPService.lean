import Netlib.Check.CampusTCPService
import Netlib.Protocol.TCP.ControlOutput

namespace NetlibTest.CampusTCPService

open Netlib Packet Protocol
namespace S
export Netlib.Check.CampusTCPService (Context Before Evidence run current current_safe packetInput)
end S

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.tcp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.tcp, 40000, 9000⟩
private def ns : IngressAttachment.NamespaceRef := ⟨1, 1⟩
private def client : IngressAttachment.InterfaceRef := ⟨ns, ⟨1, by decide⟩, 1⟩
private def server : IngressAttachment.InterfaceRef := ⟨ns, ⟨2, by decide⟩, 1⟩
private def authPort : IngressAttachment.InterfaceRef := ⟨⟨2, 1⟩, ⟨1, by decide⟩, 1⟩
private def scope : Scope := ⟨"campus-application", "use"⟩

private def traffic (header : Header) : Match := {
  source := some ⟨header.source, 32⟩, destination := some ⟨header.destination, 32⟩
  protocol := some header.protocol, sourcePorts := some (PortRange.single header.sourcePort)
  destinationPorts := some (PortRange.single header.destinationPort) }

example (context : S.Context) (before : S.Before) (source : TCP.WireForwarding.Source) (zone : Nat)
    (ingress : IngressAttachment.InterfaceRef) (value : S.Evidence context before source zone ingress)
    (passed : value.passed = true) (denied : ∀ requirement ∈ context.requirements,
      (S.current context before).state.session.permits context.authentication.context requirement.scope = false) :
    value.output = none := value.output_none_of_denied passed denied

example (context : S.Context) (before : S.Before) (source : TCP.WireForwarding.Source) (zone : Nat)
    (ingress : IngressAttachment.InterfaceRef) (value : S.Evidence context before source zone ingress)
    (denied : value.checks.decision source = false) :
    value.tracker = before.tracker ∧ value.admission = before.admission ∧ value.output = none := value.early_preserves denied

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def read (name : String) : IO Lean.Json := do
  load (Import.Json.parse (← IO.FS.readFile ("examples/campus-tcp/" ++ name ++ ".json")))

private def guard (id : String) : IO Import.NftablesIngress.Snapshot := do
  let rows ← load ((← read "guards").getArr?)
  let some row := rows.toList.find? (fun row => (row.getObjValAs? String "id").toOption == some id)
    | throw (IO.userError "The selected ingress guard is absent.")
  let source ← load (row.getObjVal? "source")
  let selectedNS ← load (Import.NftablesIngress.namespaceFromJson (← load (source.getObjVal? "namespace")))
  let bindings ← load (Import.NftablesIngress.bindingsFromJson selectedNS (← load (source.getObjVal? "bindings")))
  load (Import.NftablesIngress.Snapshot.fromJson selectedNS bindings (← load (source.getObjVal? "ruleset")))

structure Fixture where
  context : S.Context
  before : S.Before
  denyConfig : Check.ConntrackLifecycle.Config
  denyGuard : Import.NftablesIngress.Snapshot

private def fixture : IO Fixture := do
  let authentication ← load (Check.EAP.Input.fromJson (← read "authentication"))
  let requirements ← load (Check.SessionFirewall.requirementsFromJson (← read "requirements"))
  let routing ← load (Check.ConntrackLifecycle.routingFromJson (← read "routing"))
  let rows ← load ((← read "configs").getArr?)
  let configs ← load (rows.toList.zipIdx.mapM fun (row, index) => Check.ConntrackLifecycle.Config.fromJson row index)
  let some permit := configs.find? (·.id == "permit") | throw (IO.userError "The permit configuration is absent.")
  let some deny := configs.find? (·.id == "deny") | throw (IO.userError "The deny configuration is absent.")
  let context : S.Context := ⟨authentication, requirements, routing, configs, ns, [traffic original, traffic wire.reverse]⟩
  let before : S.Before := ⟨7, permit, ← guard "permit", [authPort, client, server], [], .initial, .initial⟩
  let first ← load ((IngressAttachment.stage (S.current context before) (S.current_safe context before)
    authPort client .original scope (traffic original)).mapError (·.describe))
  let second ← load ((IngressAttachment.stage (S.current context before) (S.current_safe context before)
    authPort server .reply scope (traffic wire.reverse)).mapError (·.describe))
  ensure authentication.check.compliant "The constructed authentication observations must match their computed states."
  pure ⟨context, { before with attachments := [first, second] }, deny, ← guard "deny"⟩

private def control (header : Header) (sequence acknowledgment : Nat) (flags : UInt8) : IO TCP.WireForwarding.Source := do
  let output ← load (TCP.ControlOutput.emit header (TCP.Seq.ofNat sequence) (TCP.Seq.ofNat acknowledgment) flags 8)
  pure (TCP.WireForwarding.Source.ofInput output)

private def data (sequence : Nat) (payload : List UInt8) : IO TCP.WireForwarding.Source := do
  let state : TCP.EstablishedReceive.State :=
    ⟨original.reverse, TCP.Seq.ofNat 201, 8, [], TCP.Seq.ofNat sequence, TCP.Seq.ofNat sequence, []⟩
  let output ← load (TCP.Output.emit state payload)
  pure (TCP.WireForwarding.Source.ofInput output)

private def service (context : S.Context) (before : S.Before) (source : TCP.WireForwarding.Source)
    (ingress : IngressAttachment.InterfaceRef) : IO (S.Evidence context before source 0 ingress) :=
  load ((S.run context before source 0 ingress).mapError (·.message))

private def advance (before : S.Before) (value : S.Evidence context before source zone ingress) : S.Before :=
  { before with tracker := value.tracker, admission := value.admission }

private def ordinary (fixture : Fixture) : IO S.Before := do
  let syn ← control original 100 0 2
  let first ← service fixture.context fixture.before syn client
  ensure (first.passed && first.output.isSome && first.tracker.records.length == 1 &&
      first.admission.phase.name == "syn" && first.admission.observations.length == 1)
    "An admitted SYN must use the actual NAT candidate, current policies, and checked output."
  let some emitted := first.output | throw (IO.userError "The SYN output is absent.")
  ensure (emitted.target == wire && emitted.decoded.ip.packet.ttl == 63)
    "The SYN must use the selected NAT tuple and one TTL decrease."
  let afterSyn := advance fixture.before first
  let synAck ← control wire.reverse 200 101 18
  let second ← service fixture.context afterSyn synAck server
  ensure (second.passed && second.output.isSome && second.admission.phase.name == "synAck" &&
      second.tracker.records.all (·.seenReply))
    "The SYN,ACK must use the existing reverse binding and retain the reply observation."
  let afterSynAck := advance afterSyn second
  let ack ← control original 101 201 16
  let third ← service fixture.context afterSynAck ack client
  ensure (third.passed && third.output.isSome && third.admission.phase.name == "data")
    "The final ACK must advance the checked TCP history through the same gateway."
  let established := advance afterSynAck third
  let packet ← data 101 [42]
  let fourth ← service fixture.context established packet client
  ensure (fourth.passed && fourth.output.isSome && fourth.admission.observations.length == 4)
    "The data output must use the actual installed policies and the earlier startup history."
  pure (advance established fourth)

private def revocation (fixture : Fixture) (before : S.Before) : IO Unit := do
  let queued ← data 102 [43]
  let denied := { before with after := 8, configuration := fixture.denyConfig, guard := fixture.denyGuard }
  let result ← service fixture.context denied queued client
  ensure (result.passed && result.output.isNone && result.processing.isNone && result.tracker == before.tracker &&
      result.admission.observations == before.admission.observations)
    "The current deny guard must block queued data and preserve the existing cached binding and TCP history."
  let stale := { before with after := 8 }
  let actual ← service fixture.context stale queued client
  ensure (!actual.passed && !actual.checks.forward.passed && !actual.checks.guard.passed && actual.output.isSome &&
      actual.admission.observations.length == before.admission.observations.length + 1)
    "Stale installed permit policies must retain their actual output and report the current-policy mismatch."

private def negative (fixture : Fixture) : IO Unit := do
  let syn ← control original 100 0 2
  let denied := { fixture.before with configuration := fixture.denyConfig }
  let forwardDrop ← service fixture.context denied syn client
  ensure (!forwardDrop.passed && forwardDrop.output.isNone && forwardDrop.processing.isSome &&
      forwardDrop.tracker.records.isEmpty && forwardDrop.admission.phase.name == "empty")
    "Actual forward denial must prevent fresh confirmation and retain the failed policy comparison."
  let low := TCP.WireForwarding.Source.ofInput (syn.asInput.rewrite original 1 rfl)
  let expired ← service fixture.context fixture.before low client
  ensure (expired.passed && expired.output.isNone && expired.tracker.records.isEmpty && expired.admission.phase.name == "empty")
    "TTL expiry must not confirm a fresh TCP entry or retain an unconfirmed startup history."
  let missing := { client with birth := 2 }
  match S.run fixture.context fixture.before syn 0 missing with
  | .error (.input _) => pure ()
  | _ => throw (IO.userError "A replaced ingress lifetime must fail before packet processing.")
  match S.run fixture.context { fixture.before with after := 9 } syn 0 client with
  | .error (.input _) => pure ()
  | _ => throw (IO.userError "A service prefix cannot exceed the actual authentication history.")
  let ack ← control original 101 201 16
  match S.run fixture.context fixture.before ack 0 client with
  | .error (.unsupported .flags) => pure ()
  | _ => throw (IO.userError "An ACK without earlier startup history must produce an unsupported result.")

def run : IO Unit := do
  let value ← fixture
  let before ← ordinary value
  revocation value before
  negative value
  IO.println "Campus TCP service tests passed."

end NetlibTest.CampusTCPService
