import Netlib.Check.FragmentAdmission

namespace NetlibTest.FragmentAdmissionCheck

open Netlib Packet Protocol
open Protocol.IngressAttachment
namespace Model
export Netlib.Check.FragmentAdmission (Contract Checked check completedHeader coarseCovered)
end Model

private def context : Context := ⟨"verified-client", "campus-application", "campus-authority"⟩
private def scope : Scope := ⟨"campus-application", "use"⟩
private def credential : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def events (round : Nat) : List EAPSession.Event := [
  .authentication .start, .authentication (.server (.request 1 13 [0x20])),
  .authentication (.peer (.response 1 13 [0])), .authentication (.server (.success 1)),
  .authentication (.method ⟨round, context.consumer, 13, true, some "selected method evidence"⟩),
  .application (.install credential)]
private def authentication : Check.EAP.Input :=
  ⟨context, ⟨⟨2, 0, 0, 0, 0, 2⟩, ⟨2, 0, 0, 0, 0, 1⟩⟩,
    ((events 1 ++ [EAPSession.Event.authentication .logoff] ++ events 3).zipIdx.map fun (event, index) =>
      ⟨index, event, none, none, none, .null⟩), .null⟩
private def ns : NamespaceRef := ⟨20, 1⟩
private def auth : InterfaceRef := ⟨⟨10, 1⟩, ⟨2, by decide⟩, 1⟩
private def client : InterfaceRef := ⟨ns, ⟨2, by decide⟩, 1⟩
private def server : InterfaceRef := ⟨ns, ⟨3, by decide⟩, 1⟩
private def attacker : InterfaceRef := ⟨ns, ⟨4, by decide⟩, 1⟩
private def sync : InterfaceRef := ⟨ns, ⟨5, by decide⟩, 1⟩
private def live : List InterfaceRef := [auth, client, server, attacker, sync]
private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def synchronization : Header := ⟨184549378, 184549377, Packet.Protocol.udp, 45678, 3780⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def traffic (header : Header) : Match := {
  source := some ⟨header.source, 32⟩, destination := some ⟨header.destination, 32⟩,
  protocol := some header.protocol, sourcePorts := some (PortRange.single header.sourcePort),
  destinationPorts := some (PortRange.single header.destinationPort) }
private def application : List Match := [traffic original, traffic wire.reverse]
private def maintenance : List Compile.IngressAttachment.Maintenance := [⟨sync, traffic synchronization⟩]
private def pipeline : ReassemblyForwarding.Pipeline :=
  ⟨⟨⟨[⟨⟨0, 0⟩, some "out"⟩], [], .permit, [], .permit⟩, fun _ => ⟨1500, by decide⟩⟩,
    fun zone header => ⟨⟨header, wire.reverse, zone, zone, 0⟩, true, true⟩⟩
private def policy : IPv4Reassembly.Policy := ⟨30⟩

example (checked : Model.Checked contract active queuePolicy before input early fine)
    (passed : checked.passed = true) (allowed : early.allows input = true) :
    ∃ attachment ∈ contract.attachments, Compile.FragmentAttachment.allows contract.current attachment
      ⟨input.ingress, input.envelope⟩ = true ∧
      Session.Valid contract.current.context contract.current.state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext contract.current.context) contract.current.state.auth ∧
      input.ingress = attachment.ingress ∧ attachment.origin.principal = contract.current.context.consumer :=
  checked.early_permission passed allowed

example (checked : Model.Checked contract active queuePolicy before input early fine)
    (passed : checked.passed = true) (header : Header) (completed : Model.completedHeader checked.result = some header)
    (allowed : fine.allows input.ingress.ifindex.val header = true) :
    ∃ attachment ∈ contract.attachments, IngressAttachment.allows contract.current attachment ⟨input.ingress, header⟩ = true ∧
      Session.Valid contract.current.context contract.current.state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext contract.current.context) contract.current.state.auth ∧
      input.ingress = attachment.ingress ∧ attachment.origin.principal = contract.current.context.consumer :=
  checked.completed_permission passed header completed allowed

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)
private def load : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)
private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def makeContract : IO Model.Contract := do
  let base ← load (Check.FragmentAdmission.Contract.at authentication 6 ns live [] maintenance application)
  let first ← load ((stage base.current base.safe auth client .original scope (traffic original)).mapError (·.describe))
  let second ← load ((stage base.current base.safe auth server .reply scope (traffic wire.reverse)).mapError (·.describe))
  pure { base with attachments := [first, second] }

private def atPrefix (base : Model.Contract) (after : Nat) : IO Model.Contract :=
  load (Check.FragmentAdmission.Contract.at authentication after ns live base.attachments maintenance application)

private def makePacket (header : Header := original) : IO IPv4.Packet := do
  let bytes ← load (UDP.encodeComputed header.source header.destination header.sourcePort header.destinationPort [0, 255, 65, 0, 17, 91, 92, 93, 94])
  pure ⟨42, 4197, false, 64, header.protocol, header.source, header.destination, bytes⟩

private def makeInput (packet : IPv4.Packet) (start count : Nat) (more : Bool) (now : Nat := 1)
    (ingress : InterfaceRef := client) : Protocol.FragmentAdmission.Input :=
  let fragment := IPv4Fragmentation.fragmentPacket packet ⟨start, packet.payload.drop start |>.take count, more⟩
  ⟨now, ingress, ⟨2, 0⟩, 0, ⟨fragment, IPv4Fragment.computedChecksum fragment, []⟩⟩

private def acceptedOutput (checked : Model.Checked contract pipeline policy before input early fine) (expected : Bool) : IO Unit := do
  match checked.result with
  | .accepted evidence => match evidence.completion with
    | .processed _ _ source operation _ =>
      ensure (operation.outcome.output.isSome && source.packet.header == original && checked.state.conntrack == unreplied &&
        checked.passed == expected) "Actual installed permits must retain their computed forwarding and CT effects independently of comparison."
    | _ => throw (IO.userError "Expected actual ordinary processing of the complete datagram.")
  | .rejected .. => throw (IO.userError "Expected the actual installed early permit to run.")

private def prefixTests (base : Model.Contract) : IO Unit := do
  ensure (base.current.after == 6 && base.current.state == EAPSession.run context .initial (events 1) &&
    base.current.state.session.permits context scope)
    "The contract factory must derive the exact EAP state at its bounded authentication prefix."
  reject (Check.FragmentAdmission.Contract.at authentication (authentication.observations.length + 1) ns live base.attachments maintenance application)
    "The factory cannot fabricate a current state beyond the supplied authentication history."
  let closed ← atPrefix base 7
  ensure (!(closed.current.state.session.permits context scope) && closed.current.state.auth.round == 2)
    "The next actual Logoff observation must revoke permission and advance the authentication round."
  let renewed ← atPrefix base authentication.observations.length
  ensure (renewed.current.state.session.permits context scope && renewed.current.state.auth.round == 3 &&
    renewed.early.rules.length == 1)
    "A new authorized round must not reactivate attachments created at the earlier authentication prefix."

private def waitingTests (base : Model.Contract) (packet : IPv4.Packet) (early : Protocol.FragmentAdmission.EarlyGuard) : IO Unit := do
  let first := makeInput packet 0 8 true
  let checked ← load (Model.check base pipeline policy (.initial ns) first early {})
  ensure (checked.passed && checked.earlyEquivalent && !checked.fineEquivalent && checked.fineCovered &&
    (Model.completedHeader checked.result).isNone && checked.state.conntrack.records.isEmpty && checked.state.fragments.queues.length == 1)
    "An unused stale fine policy cannot fail an incomplete family that has no completed transport header."
  let last := makeInput packet 8 (packet.payload.length - 8) false 2
  let completed ← load (Model.check base pipeline policy checked.state last early base.fine)
  acceptedOutput completed true
  ensure (Model.completedHeader completed.result == some original && completed.fineEquivalent && completed.state.fragments.queues.isEmpty)
    "Completion must require the actual fine guard and the declared full tuple class before reporting compliance."
  reject (Model.check base pipeline policy (.initial ns) first early base.fine 0)
    "An exhausted complete-comparison budget must not produce a compliance certificate."

private def staleTests (base : Model.Contract) (packet : IPv4.Packet) (early : Protocol.FragmentAdmission.EarlyGuard) : IO Unit := do
  let closed ← atPrefix base 7
  let first := makeInput packet 0 8 true
  let pending ← load (Model.check closed pipeline policy (.initial ns) first early base.fine)
  ensure (!pending.passed && !pending.earlyEquivalent && pending.state.fragments.queues.length == 1 &&
    pending.state.history.head?.any (fun receipt => receipt.authentication.after == 7 && receipt.guard.allows receipt.input))
    "A stale actual early permit must enqueue real bytes and retain the denied current prefix while reporting mismatch."
  let whole := makeInput packet 0 packet.payload.length false
  let stale ← load (Model.check closed pipeline policy (.initial ns) whole early base.fine)
  acceptedOutput stale false
  ensure (!stale.earlyEquivalent && !stale.fineEquivalent && stale.fineCovered)
    "Stale early and fine permits after Logoff must compute actual CT and NAT instead of replacing them with desired rejection."
  let broadFine := Compile.FragmentAttachment.compile base.current ns base.attachments maintenance
  let overbroad ← load (Model.check base pipeline policy (.initial ns) whole early broadFine)
  acceptedOutput overbroad false
  ensure (overbroad.earlyEquivalent && !overbroad.fineEquivalent && overbroad.fineCovered)
    "A fine guard that omits ports must fail complete header equivalence even when this observed datagram happens to match."
  let denied ← load (Model.check base pipeline policy (.initial ns) whole early {})
  ensure (!denied.passed && !denied.fineEquivalent && denied.state.conntrack.records.isEmpty && denied.state.fragments.queues.isEmpty &&
    Model.completedHeader denied.result == some original)
    "A stale actual fine deny must consume reassembly without substituting the desired permit or confirming a row."

private def coverageTests (base : Model.Contract) (packet : IPv4.Packet) (early : Protocol.FragmentAdmission.EarlyGuard) : IO Unit := do
  let changedClass := { base with application := [traffic { original with sourcePort := 41001 }] }
  let first := makeInput packet 0 8 true
  let pending ← load (Model.check changedClass pipeline policy (.initial ns) first early base.fine)
  ensure (pending.passed && Model.coarseCovered changedClass first)
    "Coarse application coverage cannot distinguish transport ports before a datagram completes."
  let whole := makeInput packet 0 packet.payload.length false
  let completed ← load (Model.check changedClass pipeline policy (.initial ns) whole early base.fine)
  ensure (!completed.passed && !completed.fineCovered && completed.state.conntrack == unreplied)
    "The completed full tuple must satisfy declared application coverage even when both actual guards permit it."
  let syncPacket ← makePacket synchronization
  let syncInput := makeInput syncPacket 0 8 true 1 sync
  let allowedMaintenance ← load (Model.check base pipeline policy (.initial ns) syncInput early base.fine)
  ensure (early.allows syncInput && !Model.coarseCovered base syncInput && !allowedMaintenance.passed)
    "A static synchronization exception cannot earn the application-permission certificate without application-envelope coverage."
  let overlapping := { base with maintenance := [⟨sync, traffic { original with destinationPort := 3780 }⟩] }
  let overlappingEarly ← load (Protocol.FragmentAdmission.EarlyGuard.checked overlapping.early)
  let overlap ← load (Model.check overlapping pipeline policy (.initial ns) whole overlappingEarly overlapping.fine)
  ensure (!overlap.separated && !overlap.passed && overlap.state.conntrack == unreplied)
    "Maintenance separated only by UDP ports must fail the coarse proof while retaining the actual computed packet state."

private def bindingTests (base : Model.Contract) (packet : IPv4.Packet) (early : Protocol.FragmentAdmission.EarlyGuard) : IO Unit := do
  let first := makeInput packet 0 8 true
  let missing := { base with current := { base.current with live := [auth, server, sync] } }
  reject (Model.check missing pipeline policy (.initial ns) first early base.fine)
    "A current prefix cannot supply packet ownership for an absent interface lifetime."
  let reused := { client with birth := 2 }
  reject (Model.check base pipeline policy (.initial ns) (makeInput packet 0 8 true 1 reused) early base.fine)
    "A reused numeric index cannot substitute its unsupported interface birth."
  let conflicting := { base with current := { base.current with live := reused :: live } }
  reject (Model.check conflicting pipeline policy (.initial ns) first early base.fine)
    "Conflicting live references cannot make numeric guards identify an arbitrary lifetime."
  let foreign := { base with ns := { ns with birth := 2 } }
  reject (Model.check foreign pipeline policy (.initial ns) first early base.fine)
    "The contract namespace lifetime must match the actual packet context and active reassembly state."

def run : IO Unit := do
  let base ← makeContract
  let packet ← makePacket
  let early ← load (Protocol.FragmentAdmission.EarlyGuard.checked base.early)
  prefixTests base
  waitingTests base packet early
  staleTests base packet early
  coverageTests base packet early
  bindingTests base packet early

end NetlibTest.FragmentAdmissionCheck
