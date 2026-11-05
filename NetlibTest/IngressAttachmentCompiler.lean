import Netlib.Compile.IngressAttachment

namespace NetlibTest.IngressAttachmentCompiler
open Netlib Packet Protocol
open Protocol.IngressAttachment
namespace Compiler
export Netlib.Compile.IngressAttachment (Maintenance LiveUnique liveUnique compile checkDisjoint checkDisjointBudget)
end Compiler

private def context : Context := ⟨"verified-client", "campus-application", "campus-authority"⟩
private def scope : Scope := ⟨"campus-application", "use"⟩
private def token : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def events (round : Nat) : List EAPSession.Event := [
  .authentication .start, .authentication (.server (.request 1 13 [0x20])),
  .authentication (.peer (.response 1 13 [0])), .authentication (.server (.success 1)),
  .authentication (.method ⟨round, context.consumer, 13, true, some "selected method evidence"⟩),
  .application (.install token), .application (.advance 5), .application (.request scope)]
private def session : EAPSession.State := EAPSession.run context .initial (events 1)
private theorem session_safe : session.Safe context := EAPSession.run_safe context _ _ (EAPSession.initial_safe context)
private def nsA : NamespaceRef := ⟨20, 1⟩
private def nsB : NamespaceRef := ⟨30, 1⟩
private def auth : InterfaceRef := ⟨⟨10, 1⟩, ⟨2, by decide⟩, 1⟩
private def clientA : InterfaceRef := ⟨nsA, ⟨2, by decide⟩, 1⟩
private def serverA : InterfaceRef := ⟨nsA, ⟨3, by decide⟩, 1⟩
private def attackerA : InterfaceRef := ⟨nsA, ⟨4, by decide⟩, 1⟩
private def syncA : InterfaceRef := ⟨nsA, ⟨5, by decide⟩, 1⟩
private def clientB : InterfaceRef := ⟨nsB, ⟨2, by decide⟩, 1⟩
private def serverB : InterfaceRef := ⟨nsB, ⟨3, by decide⟩, 1⟩
private def syncB : InterfaceRef := ⟨nsB, ⟨5, by decide⟩, 1⟩
private def current : Current :=
  ⟨context, (events 1).length, session, [auth, clientA, serverA, attackerA, syncA, clientB, serverB, syncB]⟩
private theorem current_safe : current.Safe := session_safe
private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def reply : Header := ⟨3325256706, 3405803777, Packet.Protocol.udp, 9000, 40000⟩
private def synchronization : Header := ⟨184549378, 184549377, Packet.Protocol.udp, 45678, 3780⟩
private def otherSynchronization : Header := ⟨184549377, 184549378, Packet.Protocol.udp, 45679, 3780⟩
private def traffic (header : Header) : Match := {
  source := some ⟨header.source, 32⟩, destination := some ⟨header.destination, 32⟩,
  protocol := some header.protocol, sourcePorts := some (PortRange.single header.sourcePort),
  destinationPorts := some (PortRange.single header.destinationPort) }
private def synchronizationTraffic (header : Header) : Match := { traffic header with sourcePorts := none }
private def maintenance : List Compiler.Maintenance :=
  [⟨syncA, synchronizationTraffic synchronization⟩, ⟨syncB, synchronizationTraffic otherSynchronization⟩]
private def application : List Match := [traffic original, traffic reply]

example (view : Current) (executionNS : NamespaceRef) (attachments : List ExpectedAttachment)
    (control : List Compiler.Maintenance) (input : Input) (unique : Compiler.LiveUnique view)
    (live : input.ingress ∈ view.live) (sameNS : input.ingress.ns = executionNS) :
    (Compiler.compile view executionNS attachments control).allows input.ingress.ifindex.val input.header = true ↔
      (∃ attachment ∈ attachments, Protocol.IngressAttachment.allows view attachment input = true) ∨
      (∃ entry ∈ control, entry.allows view input = true) :=
  Compile.IngressAttachment.compile_allows view executionNS attachments control input unique live sameNS

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expected (port : InterfaceRef) (direction : FlowNAT.Direction) (header : Header) : IO ExpectedAttachment := do
  match stage current current_safe auth port direction scope (traffic header) with
  | .error error => throw (IO.userError error.describe)
  | .ok attachment => pure attachment

private def policyTests (originalA : ExpectedAttachment) (attachments : List ExpectedAttachment) : IO Unit := do
  let policy := Compiler.compile current nsA attachments maintenance
  ensure (Compiler.liveUnique current) "The live inventory must have unique namespace and numeric interface identities."
  ensure (policy.fallback == .deny && policy.rules.length == 3)
    "The selected namespace must contain only two application permits and its live synchronization permit, followed by deny."
  for port in [clientA, serverA, attackerA, syncA] do
    for header in [original, reply, synchronization, otherSynchronization,
        { synchronization with sourcePort := 1 }, { synchronization with destinationPort := 3781 },
        { synchronization with protocol := Packet.Protocol.tcp }, { original with sourcePort := 41001 }] do
      let wanted := (decide (port = clientA) && header == original) ||
        (decide (port = serverA) && header == reply) ||
        (decide (port = syncA) && (synchronizationTraffic synchronization).accepts header)
      ensure (policy.allows port.ifindex.val header == wanted)
        "Compiled numeric guards must retain exact client, server, and synchronization ingress classes without accepting header impersonation."
  for index in [0, 1, 4, 6, 2147483647, 1099511627776] do
    for header in [original, reply, synchronization] do
      ensure (!(policy.allows index header)) "Unspecified numeric ingress contexts must retain the deny fallback."
  let foreign := { originalA with ingress := clientB, traffic := {} }
  ensure ((Compiler.compile current nsA [foreign] []).rules.isEmpty)
    "Even a live broad attachment from another namespace cannot enter the selected kernel namespace's rules."
  let headerOnly := { policy with rules := policy.rules.map (fun rule => { rule with ingress := none }) }
  ensure (headerOnly.allows attackerA.ifindex.val original && !Packet.IngressPolicy.check headerOnly policy)
    "A header-only installed permit must remain a computed impersonation and fail complete interface/header equivalence."
  let permuted := { policy with rules := policy.rules.reverse }
  ensure (Packet.IngressPolicy.check permuted policy)
    "Permuting permit-only rules must preserve every numeric context and header decision."

private def staleTests (originalA : ExpectedAttachment) (attachments : List ExpectedAttachment) : IO Unit := do
  let installed := Compiler.compile current nsA attachments maintenance
  let closed := { current with after := current.after + 1, state := EAPSession.step context session (.authentication .logoff) }
  let desired := Compiler.compile closed nsA attachments maintenance
  ensure (desired.rules.length == 1 && desired.allows syncA.ifindex.val synchronization &&
    !(desired.allows clientA.ifindex.val original) && installed.allows clientA.ifindex.val original &&
    !Packet.IngressPolicy.check installed desired)
    "Logoff must remove application permits while retaining live FTFW traffic and exposing an unchanged installed application's stale accept."
  let renewed := { current with after := current.after + (events 2).length, state := EAPSession.run context session (events 2) }
  ensure (renewed.state.session.permits context scope &&
    !(Compiler.compile renewed nsA attachments maintenance).allows clientA.ifindex.val original)
    "A newly authorized round cannot preserve the previous round's application attachments."
  let reused := { clientA with birth := 2 }
  let reusedView := { current with live := [auth, reused, serverA, syncA] }
  let reusedDesired := Compiler.compile reusedView nsA attachments maintenance
  ensure (installed.allows reused.ifindex.val original && !(reusedDesired.allows reused.ifindex.val original) &&
    !Packet.IngressPolicy.check installed reusedDesired)
    "Reused numeric indices must expose stale installed accepts because dead lifetime references are filtered from desired compilation."
  let deadAuth := { current with live := [clientA, serverA, syncA] }
  ensure (!(Compiler.compile deadAuth nsA attachments maintenance).allows clientA.ifindex.val original &&
    (Compiler.compile deadAuth nsA attachments maintenance).allows syncA.ifindex.val synchronization)
    "Dead authentication ports must remove application attachment permits without changing independent live synchronization requirements."
  let deadSync := { current with live := [auth, clientA, serverA] }
  ensure (!(Compiler.compile deadSync nsA attachments maintenance).allows syncA.ifindex.val synchronization)
    "A dead synchronization interface cannot retain a numeric permit through its old lifetime reference."
  let invalidLive := { current with live := reused :: current.live }
  ensure (!Compiler.liveUnique invalidLive) "Conflicting live interface lifetimes must fail the executable uniqueness check."
  ensure ((Compiler.compile invalidLive nsA attachments []).allows reused.ifindex.val original &&
    !(Protocol.IngressAttachment.allows invalidLive originalA ⟨reused, original⟩))
    "Two claimed live lifetimes sharing one namespace and index violate the uniqueness premise needed for numeric-to-owner soundness."

private def separationTests : IO Unit := do
  ensure (Compiler.checkDisjoint maintenance application)
    "FTFW UDP destination port 3780 must be disjoint from both declared application tuple classes."
  let overlap : List Compiler.Maintenance := [⟨syncA, traffic original⟩]
  ensure (!Compiler.checkDisjoint overlap application && !Compiler.checkDisjoint [⟨syncA, {}⟩] application)
    "A maintenance class overlapping an application header must fail independently of interface separation or current EAP denial."
  ensure (Compiler.checkDisjoint [] application && Compiler.checkDisjoint maintenance [])
    "Empty maintenance or application sets must preserve the complete disjointness meaning."
  match Compiler.checkDisjointBudget maintenance application 0 with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "An exhausted partition budget cannot report disjointness.")
  match Compiler.checkDisjointBudget maintenance application 100000 with
  | .ok true => pure ()
  | _ => throw (IO.userError "A sufficient partition budget must certify the selected disjoint maintenance classes.")

def run : IO Unit := do
  let originalA ← expected clientA .original original
  let replyA ← expected serverA .reply reply
  let originalB ← expected clientB .original original
  let replyB ← expected serverB .reply reply
  let attachments := [originalA, replyA, originalB, replyB]
  policyTests originalA attachments
  staleTests originalA attachments
  separationTests

end NetlibTest.IngressAttachmentCompiler
