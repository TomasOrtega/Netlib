import Netlib.Compile.FragmentAttachment
import Netlib.Protocol.UDP

namespace NetlibTest.FragmentAttachment

open Netlib Packet Protocol
open Protocol.IngressAttachment
namespace Compiler
export Netlib.Compile.FragmentAttachment (Input Maintenance compile allows maintenanceAllows coarse checkDisjoint checkDisjointBudget)
end Compiler

private def context : Context := ⟨"verified-client", "campus-application", "campus-authority"⟩
private def scope : Scope := ⟨"campus-application", "use"⟩
private def credential : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def events (round : Nat) : List EAPSession.Event := [
  .authentication .start, .authentication (.server (.request 1 13 [0x20])),
  .authentication (.peer (.response 1 13 [0])), .authentication (.server (.success 1)),
  .authentication (.method ⟨round, context.consumer, 13, true, some "selected method evidence"⟩),
  .application (.install credential), .application (.advance 5), .application (.request scope)]
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
private def maintenance : List Compiler.Maintenance :=
  [⟨syncA, traffic synchronization⟩, ⟨syncB, traffic otherSynchronization⟩]
private def application : List Match := [traffic original, traffic reply]

example (view : Current) (executionNS : NamespaceRef) (attachments : List ExpectedAttachment)
    (control : List Compiler.Maintenance) :
    IngressPolicy.NoPorts (Compiler.compile view executionNS attachments control) :=
  Compile.FragmentAttachment.compile_noPorts view executionNS attachments control

example (policy : IngressPolicy.Policy) (fields : IngressPolicy.NoPorts policy) (index : Nat)
    (first second : Header) (same : Packet.IPv4Envelope.ofHeader first = Packet.IPv4Envelope.ofHeader second) :
    policy.allows index first = policy.allows index second :=
  IngressPolicy.noPorts_port_independent policy fields index first second same

example (view : Current) (executionNS : NamespaceRef) (attachments : List ExpectedAttachment)
    (control : List Compiler.Maintenance) (input : Compiler.Input) (unique : Compile.IngressAttachment.LiveUnique view)
    (live : input.ingress ∈ view.live) (sameNS : input.ingress.ns = executionNS) :
    (Compiler.compile view executionNS attachments control).allows input.ingress.ifindex.val input.envelope.toHeader = true ↔
      (∃ attachment ∈ attachments, Compiler.allows view attachment input = true) ∨
      (∃ entry ∈ control, Compiler.maintenanceAllows view entry input = true) :=
  Compile.FragmentAttachment.compile_allows view executionNS attachments control input unique live sameNS

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)
private def load : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)
private def expected (port : InterfaceRef) (direction : FlowNAT.Direction) (header : Header) : IO ExpectedAttachment :=
  load ((stage current current_safe auth port direction scope (traffic header)).mapError (·.describe))

private def sameIP (first second : Header) : Bool :=
  first.source == second.source && first.destination == second.destination && first.protocol == second.protocol

private def policyTests (originalA : ExpectedAttachment) (attachments : List ExpectedAttachment) : IO Unit := do
  for (ns, clientIndex, serverIndex, syncHeader) in [(nsA, 2, 3, synchronization), (nsB, 2, 3, otherSynchronization)] do
    let policy := Compiler.compile current ns attachments maintenance
    ensure (policy.fallback == .deny && policy.rules.length == 3 && IngressPolicy.noPorts policy)
      "Each namespace must compile two coarse application permits and one port-free synchronization permit, followed by deny."
    for index in [0, 1, 2, 3, 4, 5, 6, 2147483647, 2147483648, 1099511627776] do
      for header in [original, reply, synchronization, otherSynchronization,
          { original with source := 3221225987 }, { original with destination := 3325256706 },
          { original with protocol := Packet.Protocol.tcp }] do
        for sourcePort in ([0, 1, 41000, 65535] : List Port) do
          for destinationPort in ([0, 1, 8080, 65535] : List Port) do
            let selected := { header with sourcePort, destinationPort }
            let wanted := (index == clientIndex && sameIP selected original) ||
              (index == serverIndex && sameIP selected reply) || (index == 5 && sameIP selected syncHeader)
            ensure (policy.allows index selected == wanted)
              "Numeric guards must depend on exact ingress, IPv4 addresses, and protocol, never transport-port availability."
    let permuted := { policy with rules := policy.rules.reverse }
    ensure (IngressPolicy.check permuted policy) "Permit-only rule reordering must preserve every numeric context and header decision."
    let headerOnly := { policy with rules := policy.rules.map (fun rule => { rule with ingress := none }) }
    ensure (headerOnly.allows attackerA.ifindex.val original && !IngressPolicy.check headerOnly policy)
      "An installed header-only guard must expose actual coarse spoofing and fail complete numeric-interface equivalence."
    let portRead := { policy with rules := policy.rules.map (fun rule => { rule with
      traffic := { rule.traffic with destinationPorts := some PortRange.all } }) }
    ensure (IngressPolicy.check portRead policy && !IngressPolicy.noPorts portRead)
      "Header equivalence alone cannot certify absence of transport-field reads before defragmentation."
  let wrongPorts := { original with sourcePort := 1, destinationPort := 9 }
  ensure (Compiler.allows current originalA ⟨clientA, Packet.IPv4Envelope.ofHeader wrongPorts⟩ &&
    !(Protocol.IngressAttachment.allows current originalA ⟨clientA, wrongPorts⟩))
    "Coarse fragment permission must not claim the finer completed UDP tuple is authorized."
  let foreign := { originalA with ingress := clientB, traffic := {} }
  ensure ((Compiler.compile current nsA [foreign] []).rules.isEmpty)
    "A broad attachment in another namespace cannot enter this namespace's actual numeric rules."

private def fragmentTests (originalA : ExpectedAttachment) (attachments : List ExpectedAttachment) : IO Unit := do
  for (header, port) in [(original, clientA), (reply, serverA), (original, clientB), (reply, serverB)] do
    for offset in ([0, 1, 8191] : List (Fin 8192)) do
      let fragment : IPv4Fragment.Packet := ⟨⟨0, 4197, false, 64, header.protocol,
        header.source, header.destination, [255, 255, 0, 1]⟩, true, offset⟩
      let bytes ← load (IPv4InputFragment.encode fragment)
      let envelope ← load (Packet.IPv4Envelope.decode bytes)
      let policy := Compiler.compile current port.ns attachments maintenance
      ensure (policy.allows port.ifindex.val envelope.toHeader && !policy.allows 4 envelope.toHeader)
        "First and noninitial fragments must select the same authorized ingress without reading UDP headers or attacker payload bytes."
  let later : IPv4Fragment.Packet := ⟨⟨0, 4197, false, 64, Packet.Protocol.udp,
    original.source, original.destination, []⟩, false, 1⟩
  let envelope ← load (Packet.IPv4Envelope.decode (← load (IPv4InputFragment.encode later)))
  ensure (Compiler.allows current originalA ⟨clientA, envelope⟩)
    "The guard validates the envelope; empty-data and offset errors remain decisions for the unchanged reassembly transition."

private def staleTests (originalA : ExpectedAttachment) (attachments : List ExpectedAttachment) : IO Unit := do
  let installed := Compiler.compile current nsA attachments maintenance
  let closed := { current with after := current.after + 1, state := EAPSession.step context session (.authentication .logoff) }
  let desired := Compiler.compile closed nsA attachments maintenance
  ensure (installed.allows clientA.ifindex.val original && !(desired.allows clientA.ifindex.val original) &&
    !IngressPolicy.check installed desired && desired.allows syncA.ifindex.val { synchronization with destinationPort := 1 })
    "Logoff must expose a stale installed fragment permit while retaining the independent peer-IP synchronization envelope."
  let renewed := { current with after := current.after + (events 2).length, state := EAPSession.run context session (events 2) }
  ensure (renewed.state.session.permits context scope && !(Compiler.compile renewed nsA attachments maintenance).allows clientA.ifindex.val original)
    "A newly authorized round cannot reuse an earlier fragment attachment."
  let reused := { clientA with birth := 2 }
  let changed := { current with live := [auth, reused, serverA, syncA] }
  ensure (installed.allows reused.ifindex.val original && !(Compiler.compile changed nsA attachments maintenance).allows reused.ifindex.val original &&
    !(Compiler.allows changed originalA ⟨reused, Packet.IPv4Envelope.ofHeader original⟩))
    "A stale installed numeric permit must remain distinct from an exact current interface-lifetime attachment."
  let conflict := { current with live := reused :: current.live }
  ensure (!Compile.IngressAttachment.liveUnique conflict &&
    (Compiler.compile conflict nsA attachments []).allows reused.ifindex.val original &&
    !(Compiler.allows conflict originalA ⟨reused, Packet.IPv4Envelope.ofHeader original⟩))
    "Numeric-to-lifetime soundness requires the supplied live-index uniqueness premise."

private def separationTests : IO Unit := do
  ensure (Compiler.checkDisjoint maintenance application) "Peer synchronization IP envelopes must be globally disjoint from application envelopes."
  let overlapping : List Compiler.Maintenance := [⟨syncA, { traffic original with destinationPorts := some (PortRange.single 3780) }⟩]
  ensure (Compile.IngressAttachment.checkDisjoint overlapping application && !Compiler.checkDisjoint overlapping application)
    "Different UDP ports cannot separate maintenance from application traffic before defragmentation, even on another interface."
  ensure (!Compiler.checkDisjoint [⟨syncA, {}⟩] application && Compiler.checkDisjoint [] application)
    "The coarse global separation check must reject broad maintenance and handle empty allowlists."
  match Compiler.checkDisjointBudget maintenance application 0 with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "An exhausted partition budget cannot certify coarse separation.")
  ensure ((← load (Compiler.checkDisjointBudget maintenance application 100000)))
    "A sufficient partition budget must certify the selected coarse maintenance envelope."

def run : IO Unit := do
  let originalA ← expected clientA .original original
  let replyA ← expected serverA .reply reply
  let originalB ← expected clientB .original original
  let replyB ← expected serverB .reply reply
  let attachments := [originalA, replyA, originalB, replyB]
  policyTests originalA attachments
  fragmentTests originalA attachments
  staleTests originalA attachments
  separationTests

end NetlibTest.FragmentAttachment
