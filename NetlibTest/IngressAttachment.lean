import Netlib.Protocol.IngressAttachment
import Netlib.Protocol.WireForwarding

namespace NetlibTest.IngressAttachment
open Netlib Packet Protocol
open Protocol.IngressAttachment

private def context : Context := ⟨"verified-client", "campus-application", "campus-authority"⟩
private def scope : Scope := ⟨"campus-application", "use"⟩
private def token : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def authentication (round : Nat) : List EAPSession.Event := [
  .authentication .start, .authentication (.server (.request 1 13 [0x20])),
  .authentication (.peer (.response 1 13 [0])), .authentication (.server (.success 1)),
  .authentication (.method ⟨round, context.consumer, 13, true, some "selected method evidence"⟩)]
private def events (round : Nat) : List EAPSession.Event := authentication round ++
  [.application (.install token), .application (.advance 5), .application (.request scope)]
private def session : EAPSession.State := EAPSession.run context .initial (events 1)
private theorem session_safe : session.Safe context := EAPSession.run_safe context _ _ (EAPSession.initial_safe context)
private def authPort : InterfaceRef := ⟨⟨10, 1⟩, ⟨2, by decide⟩, 1⟩
private def clientA : InterfaceRef := ⟨⟨20, 1⟩, ⟨2, by decide⟩, 1⟩
private def serverA : InterfaceRef := ⟨⟨20, 1⟩, ⟨3, by decide⟩, 1⟩
private def attackerA : InterfaceRef := ⟨⟨20, 1⟩, ⟨4, by decide⟩, 1⟩
private def clientB : InterfaceRef := ⟨⟨30, 1⟩, ⟨2, by decide⟩, 1⟩
private def serverB : InterfaceRef := ⟨⟨30, 1⟩, ⟨3, by decide⟩, 1⟩
private def current : Current := ⟨context, (events 1).length, session, [authPort, clientA, serverA, attackerA, clientB, serverB]⟩
private theorem current_safe : current.Safe := session_safe

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def traffic (header : Header) : Match := {
  source := some ⟨header.source, 32⟩, destination := some ⟨header.destination, 32⟩,
  protocol := some header.protocol, sourcePorts := some (PortRange.single header.sourcePort),
  destinationPorts := some (PortRange.single header.destinationPort) }
private def pipeline : ConntrackLifecycle.Pipeline := {
  routes := [⟨⟨wire.destination, 32⟩, some "server"⟩, ⟨⟨original.source, 32⟩, some "client"⟩],
  forward := [], forwardDefault := .permit }

example (view : Current) (safe : view.Safe) (attachment : ExpectedAttachment) (input : Input)
    (accepted : allows view attachment input = true) :
    Session.Valid view.context view.state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext view.context) view.state.auth :=
  allows_permission view safe attachment input accepted

example (before after : ConntrackLifecycle.State) (next : ConntrackLifecycle.State → Except String Nat)
    (accepted : precheck decision before next = .ok (.rejected after)) : decision = false ∧ after = before :=
  precheck_rejected decision before after next accepted

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def expected (port : InterfaceRef) (direction : FlowNAT.Direction) (header : Header) : IO ExpectedAttachment :=
  unwrap ((stage current current_safe authPort port direction scope (traffic header)).mapError (·.describe))

private def packet (header : Header) : IO UDP.DecodedIPv4 := do
  let datagram := UDP.computed header.source header.destination header.sourcePort header.destinationPort [0, 255, 9, 0]
  let bytes ← unwrap (UDP.encode header.source header.destination datagram)
  unwrap (UDP.decodeIPv4 (← unwrap (IPv4.encode ⟨32, 4321, false, 64, Packet.Protocol.udp, header.source, header.destination, bytes⟩)))

private def numericGuard (attachment : ExpectedAttachment) (input : Input) : Bool :=
  decide (input.ingress.ns = attachment.ingress.ns) &&
    decide (input.ingress.ifindex.val = attachment.ingress.ifindex.val) && attachment.traffic.accepts input.header

private def unchanged (decision : Bool) (before : ConntrackLifecycle.State) (input : WireForwarding.Input) : IO Unit := do
  let result ← unwrap ((precheck decision before (fun state => WireForwarding.step pipeline state input)).mapError (·.describe))
  match result with
  | .rejected after => ensure (after == before) "Ingress rejection must preserve the exact confirmed table and have no NAT result."
  | .processed _ => throw (IO.userError "The rejected ingress must not reach attachment or NAT.")

private def liveGuardTests (originalA replyA : ExpectedAttachment) : IO Unit := do
  ensure (allows current originalA ⟨clientA, original⟩ && allows current replyA ⟨serverA, wire.reverse⟩)
    "Current original and reply attachments must match their distinct attributed ingress contexts."
  ensure (originalA.role == .client && replyA.role == .server &&
    decide (replyA.origin = originalA.origin) && replyA.origin.principal == context.consumer)
    "The server reply role must retain the client's historical authentication origin."
  for port in [attackerA, serverA, clientB, serverB] do
    ensure (!(allows current originalA ⟨port, original⟩))
      "Identical authorized IP and transport fields cannot substitute another live ingress identity."
  for port in [clientA, attackerA, clientB, serverB] do
    ensure (!(allows current replyA ⟨port, wire.reverse⟩))
      "A forged reply tuple cannot substitute the expected server ingress."
  for header in [{ original with source := 3221225987 }, { original with destination := wire.destination },
      { original with sourcePort := 41001 }, { original with destinationPort := 8081 },
      { original with protocol := Packet.Protocol.tcp }] do
    ensure (!(allows current originalA ⟨clientA, header⟩))
      "The pre-NAT traffic class must preserve addresses, protocol, and both transport ports."
  ensure (allows current originalA ⟨clientA, original⟩)
    "Identical headers on the same attributed ingress remain indistinguishable; this profile supplies no same-port attacker guarantee."
  let reused := { clientA with birth := 2 }
  let reusedView := { current with live := [authPort, reused, serverA] }
  ensure (!(allows reusedView originalA ⟨reused, original⟩) && numericGuard originalA ⟨reused, original⟩)
    "A stale numeric rule can accept a reused interface index while the exact lifetime attachment rejects it."
  let newNamespace := { clientA with ns := { clientA.ns with birth := 2 } }
  ensure (!(allows { current with live := [authPort, newNamespace] } originalA ⟨newNamespace, original⟩))
    "Namespace lifetime reuse must not inherit an earlier attachment."
  let newAuth := { authPort with birth := 2 }
  ensure (!(allows { current with live := [newAuth, clientA, serverA] } originalA ⟨clientA, original⟩))
    "An unchanged data interface cannot retain a dead authentication-port lifetime."
  ensure (!(allows { current with after := 0 } originalA ⟨clientA, original⟩))
    "An attachment cannot originate in a future authentication prefix."

private def currentSessionTests (originalA : ExpectedAttachment) : IO Unit := do
  for event in [EAPSession.Event.authentication .logoff, .authentication .disconnect, .application .revoke,
      .application (.advance 100)] do
    let state := EAPSession.step context session event
    let view := { current with after := current.after + 1, state }
    ensure (!(allows view originalA ⟨clientA, original⟩) && numericGuard originalA ⟨clientA, original⟩)
      "Current denial must remain distinct from a stale installed numeric permit."
  let renewed := EAPSession.run context session (events 2)
  ensure (renewed.session.permits context scope && renewed.auth.round == 2 &&
    !(allows { current with after := current.after + (events 2).length, state := renewed } originalA ⟨clientA, original⟩))
    "Reauthentication of the same principal cannot reuse an earlier local-round attachment."
  let missing := stage { current with live := [clientA] } current_safe authPort clientA .original scope (traffic original)
  match missing with
  | .error .missingAuthenticationPort => pure ()
  | _ => throw (IO.userError "Attachment staging must require the actual authentication-port lifetime.")

private def precheckTests (originalA replyA : ExpectedAttachment) : IO Unit := do
  let request ← packet original
  let response ← packet wire.reverse
  let fresh : WireForwarding.Input := ⟨0, request, some entry⟩
  let cached : WireForwarding.Input := ⟨0, request, none⟩
  let reverse : WireForwarding.Input := ⟨0, response, none⟩
  unchanged (allows current originalA ⟨attackerA, original⟩) .initial fresh
  unchanged (allows current originalA ⟨attackerA, original⟩) unreplied cached
  unchanged (allows current replyA ⟨clientA, wire.reverse⟩) unreplied reverse
  let ordinary ← unwrap ((WireForwarding.step pipeline unreplied reverse).mapError (·.describe))
  ensure (ordinary.state == replied && ordinary.output.isSome)
    "Without the early guard, the forged reply's ordinary continuation can update seen-reply state and emit translated output."
  let closed := { current with after := current.after + 1, state := EAPSession.step context session (.authentication .logoff) }
  let input : Input := ⟨serverA, wire.reverse⟩
  let desired := allows closed replyA input
  let installed := numericGuard replyA input
  ensure (!desired && installed) "A stale installed guard must remain an observable mismatch after Logoff."
  let actual ← unwrap ((precheck installed unreplied (fun state => WireForwarding.step pipeline state reverse)).mapError (·.describe))
  match actual with
  | .rejected _ => throw (IO.userError "Desired denial must not silently replace the actual installed permit.")
  | .processed outcome =>
    ensure (outcome.state == replied && outcome.output.isSome)
      "The actual stale permit must retain its real tracker and NAT consequences for mismatch reporting."
  let stopped : Except String (Guarded ConntrackLifecycle.State Nat) := precheck false unreplied (fun _ => .error "continuation reached")
  match stopped with
  | .ok (.rejected state) => ensure (state == unreplied) "Early rejection must not evaluate an unsupported continuation."
  | _ => throw (IO.userError "The continuation error must be unreachable behind an actual early rejection.")

private def inheritedOwnerTest (originalA : ExpectedAttachment) : IO Unit := do
  match selectedEq : ConntrackReplication.stage unreplied 17 0 original with
  | .error error => throw (IO.userError error.describe)
  | .ok selection =>
    let owned : OwnedBinding := ⟨entry, originalA.origin⟩
    match ownerEq : selectOwner owned selection with
    | .error error => throw (IO.userError error.describe)
    | .ok source =>
      match committedEq : ConntrackReplication.commit .initial selection 180 with
      | .error error => throw (IO.userError error.describe)
      | .ok installed =>
        have fields := ConntrackReplication.commit_fields _ _ _ _ committedEq
        have sourceFields := selectOwner_fields owned selection source ownerEq
        let inherited := source.inherit installed (by rw [sourceFields.2]; exact fields.2.1)
        ensure (inherited.entry == entry && decide (inherited.origin = originalA.origin) &&
          inherited.origin.after == current.after && inherited.origin.round == 1 &&
          inherited.origin.principal == context.consumer && installed.state == unreplied)
          "Replication must retain historical client ownership while installing the selected ordinary NAT record."

def run : IO Unit := do
  let originalA ← expected clientA .original original
  let replyA ← expected serverA .reply wire.reverse
  liveGuardTests originalA replyA
  currentSessionTests originalA
  precheckTests originalA replyA
  inheritedOwnerTest originalA

end NetlibTest.IngressAttachment
