import Netlib.Protocol.FragmentAdmission
import Netlib.Protocol.FragmentAdmissionFacts
import Netlib.Compile.FragmentAttachment

namespace NetlibTest.FragmentAdmission

open Netlib Packet Protocol
open Protocol.IngressAttachment
namespace Model
export Netlib.Protocol.FragmentAdmission (EarlyGuard Input Receipt State Accepted Result Completion step)
abbrev initial := Netlib.Protocol.FragmentAdmission.State.initial
abbrev checked := Netlib.Protocol.FragmentAdmission.EarlyGuard.checked
end Model

private def context : Context := ⟨"verified-client", "campus-application", "campus-authority"⟩
private def scope : Scope := ⟨"campus-application", "use"⟩
private def credential : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def events (round : Nat) : List EAPSession.Event := [
  .authentication .start, .authentication (.server (.request 1 13 [0x20])),
  .authentication (.peer (.response 1 13 [0])), .authentication (.server (.success 1)),
  .authentication (.method ⟨round, context.consumer, 13, true, some "selected method evidence"⟩),
  .application (.install credential)]
private def session : EAPSession.State := EAPSession.run context .initial (events 1)
private theorem session_safe : session.Safe context := EAPSession.run_safe context _ _ (EAPSession.initial_safe context)
private def ns : NamespaceRef := ⟨20, 1⟩
private def auth : InterfaceRef := ⟨⟨10, 1⟩, ⟨2, by decide⟩, 1⟩
private def client : InterfaceRef := ⟨ns, ⟨2, by decide⟩, 1⟩
private def server : InterfaceRef := ⟨ns, ⟨3, by decide⟩, 1⟩
private def attacker : InterfaceRef := ⟨ns, ⟨4, by decide⟩, 1⟩
private def current : Current := ⟨context, (events 1).length, session, [auth, client, server, attacker]⟩
private theorem current_safe : current.Safe := session_safe
private def closed : Current := { current with
  after := current.after + 1
  state := EAPSession.step context session (.authentication .logoff) }
private def renewed : Current := { current with
  after := current.after + (events 2).length
  state := EAPSession.run context session (events 2) }
private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def policy : IPv4Reassembly.Policy := ⟨30⟩
private def domain : IPv4Reassembly.Domain := ⟨65538, 0⟩
private def data : List UInt8 := (List.range 37).map (fun index => UInt8.ofNat (index * 37))
private def traffic (header : Header) : Match := {
  source := some ⟨header.source, 32⟩, destination := some ⟨header.destination, 32⟩,
  protocol := some header.protocol, sourcePorts := some (PortRange.single header.sourcePort),
  destinationPorts := some (PortRange.single header.destinationPort) }
private def pipeline (permit : Bool := true) : ReassemblyForwarding.Pipeline :=
  ⟨⟨⟨[⟨⟨0, 0⟩, some "out"⟩], [], if permit then .permit else .deny, [], .permit⟩,
    fun _ => ⟨1500, by decide⟩⟩, fun zone header => ⟨⟨header, wire.reverse, zone, zone, 0⟩, true, true⟩⟩

example (accepted : Model.Accepted active queuePolicy before input authentication early fine)
    (output : IPv4Reassembly.Output) (emitted : accepted.result.output = some output)
    (piece : IPv4Reassembly.Piece) (member : piece ∈ output.pieces) :
    ∃ receipt ∈ accepted.state.history, receipt.fragment = piece.fragment :=
  accepted.output_sources output emitted piece member

example (accepted : Model.Accepted active queuePolicy before input authentication early fine)
    (output : IPv4Reassembly.Output) (emitted : accepted.result.output = some output)
    (piece : IPv4Reassembly.Piece) (member : piece ∈ output.pieces) :
    ∃ receipt ∈ accepted.state.history, receipt.fragment = piece.fragment ∧ receipt.input.domain = input.domain ∧
      receipt.input.now ≤ input.now ∧ receipt.guard.allows receipt.input = true :=
  accepted.output_domain_source output emitted piece member

example (accepted : Model.Accepted active queuePolicy before input authentication early fine)
    (output : IPv4Reassembly.Output) (emitted : accepted.result.output = some output)
    (piece : IPv4Reassembly.Piece) (member : piece ∈ output.pieces) :
    ∃ receipt ∈ accepted.state.history, receipt.fragment = piece.fragment ∧ receipt.input.domain = input.domain ∧
      receipt.input.ingress.ns = before.ns ∧ receipt.input.now ≤ input.now ∧
      receipt.input.envelope = Packet.IPv4Envelope.ofPacket output.packet ∧ receipt.guard.allows receipt.input = true :=
  accepted.output_bound_receipt output emitted piece member

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)
private def load : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)
private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def expected (port : InterfaceRef) (direction : FlowNAT.Direction) (header : Header) : IO ExpectedAttachment :=
  load ((stage current current_safe auth port direction scope (traffic header)).mapError (·.describe))

private def packet (header : Header) : IO IPv4.Packet := do
  let bytes ← load (UDP.encodeComputed header.source header.destination header.sourcePort header.destinationPort data)
  pure ⟨42, 4197, false, 64, header.protocol, header.source, header.destination, bytes⟩

private def part (packet : IPv4.Packet) (start count : Nat) (more : Bool) : IPv4Fragment.Decoded :=
  let fragment := IPv4Fragmentation.fragmentPacket packet ⟨start, packet.payload.drop start |>.take count, more⟩
  ⟨fragment, IPv4Fragment.computedChecksum fragment, []⟩

private def family (packet : IPv4.Packet) : List IPv4Fragment.Decoded :=
  [part packet 0 16 true, part packet 16 16 true, part packet 32 (packet.payload.length - 32) false]

private def arrival (fragment : IPv4Fragment.Decoded) (now : Nat) (ingress : InterfaceRef := client)
    (selected : IPv4Reassembly.Domain := domain) : Model.Input := ⟨now, ingress, selected, 0, fragment⟩

private def drive (before : Model.State) (family : List IPv4Fragment.Decoded) (port : InterfaceRef)
    (early : Model.EarlyGuard) (fine : IngressPolicy.Policy) (active : ReassemblyForwarding.Pipeline := pipeline)
    (authentication : Current := current) : IO Model.State := do
  let mut state := before
  let mut completed := 0
  for (fragment, index) in family.zipIdx do
    let input := arrival fragment (before.clock + index + 1) port
    let result ← load (Model.step active policy state input authentication early fine)
    match result with
    | .rejected .. => throw (IO.userError "The selected family must pass its actual early guard.")
    | .accepted accepted =>
      match accepted.completion with
      | .waiting _ =>
        ensure (accepted.state.conntrack == before.conntrack && index + 1 < family.length)
          "Incomplete accepted fragments must remain before ordinary conntrack and NAT."
      | .rejected .. => throw (IO.userError "The selected complete datagram must pass its actual fine guard.")
      | .processed assembled _ source operation _ =>
        completed := completed + 1
        let some output := operation.outcome.output | throw (IO.userError "The selected pipeline must emit the completed datagram.")
        let target := if port = server then original.reverse else wire
        ensure (source.packet.datagram.payload == data && assembled.packet.payload == source.packet.ip.packet.payload &&
          output.decoded.header == target && output.decoded.datagram.payload == data &&
          output.decoded.ip.packet.ttl == 63 && operation.outcome.sizeCap.map (·.val) == some 36 &&
          operation.outcome.disposition == .forwarded &&
          assembled.pieces.all (fun piece => accepted.state.history.any (fun receipt => receipt.fragment == piece.fragment &&
            receipt.input.domain == input.domain && decide (receipt.input.now ≤ input.now) && receipt.guard.allows receipt.input)))
          "Completed output must preserve the ledger's actual fragment payload, NAT target, TTL, and fragment-size cap."
    state := result.state
  ensure (completed == 1 && state.fragments.queues.isEmpty && state.history.length == before.history.length + family.length)
    "A complete accepted family must emit once, erase its queue, and retain every actual early-admission receipt."
  pure state

private def positive (early : Model.EarlyGuard) (fine : IngressPolicy.Policy) (request response : IPv4.Packet) : IO Model.State := do
  let first := part request 0 16 true
  let middle := part request 16 16 true
  let last := part request 32 13 false
  for order in [[first, middle, last], [first, last, middle], [middle, first, last],
      [middle, last, first], [last, first, middle], [last, middle, first]] do
    let finished ← drive (Model.initial ns) order client early fine
    ensure (finished.conntrack == unreplied && finished.history.all (fun receipt => receipt.input.domain == domain &&
      receipt.input.ingress == client && receipt.authentication.after == current.after && receipt.guard.allows receipt.input))
      "Queue keys remain actual user/vif domains; the ledger retains each exact ingress, session prefix, and installed decision."
  let warm ← drive (Model.initial ns) (family request) client early fine
  let returned ← drive warm (family response).reverse server early fine
  ensure (returned.conntrack == replied)
    "An accepted reply family must use the actual established binding and update seen-reply only after fine admission."
  pure warm

private def earlyRejection (early : Model.EarlyGuard) (fine : IngressPolicy.Policy) (request : IPv4.Packet) : IO Unit := do
  let before := Model.initial ns
  let input := arrival (part request 0 16 true) 1 attacker
  let rejected ← load (Model.step pipeline policy before input current early fine)
  match rejected with
  | .accepted _ => throw (IO.userError "The spoofing ingress must fail the actual early guard.")
  | .rejected denied monotonic =>
    have _ := Protocol.FragmentAdmission.Result.early_rejected_unchanged
      (pipeline := pipeline) (policy := policy) (current := current) (fine := fine) denied monotonic
    ensure (rejected.state.fragments == before.fragments && rejected.state.conntrack == before.conntrack &&
      rejected.state.history.isEmpty && rejected.state.clock == 1)
      "Early rejection must preserve queues, exact CT state, and accepted history while advancing only the observation clock."
  let first ← load (Model.step pipeline policy before (arrival (part request 0 16 true) 1) current early fine)
  let late ← load (Model.step pipeline policy first.state (arrival (part request 16 16 true) 31 attacker) current early fine)
  ensure (late.state.fragments == first.state.fragments && late.state.history.length == 1 && late.state.clock == 31)
    "An early-rejected packet cannot refresh, expire, or contribute bytes to an existing queue."
  reject (Model.step pipeline policy late.state (arrival (part request 16 16 true) 2) current early fine)
    "A rejected observation still prevents later events from moving the shared clock backward."
  let fresh ← load (Model.step pipeline policy late.state (arrival (part request 32 13 false) 32) current early fine)
  ensure (fresh.state.fragments.queues.length == 1 && fresh.state.conntrack.records.isEmpty &&
    fresh.state.fragments.queues.all (fun queue => queue.first.isNone && queue.expires == 62))
    "The next actual arrival must age expired data and start a fresh queue generation."
  reject (Model.step pipeline policy before (arrival (part request 0 16 true) 1
    { client with ns := { ns with birth := 2 } }) current early fine)
    "A reused namespace identity with another birth cannot share the live reassembly state."

private def lateRejection (early : Model.EarlyGuard) (fine : IngressPolicy.Policy) (warm : Model.State)
    (response : IPv4.Packet) : IO Unit := do
  let mut before := warm
  for (fragment, index) in (family response).zipIdx do
    let result ← load (Model.step pipeline policy before (arrival fragment (warm.clock + index + 1) server) closed early {})
    match result with
    | .rejected .. => throw (IO.userError "The unchanged actual early permit must remain distinct from current desired denial.")
    | .accepted accepted =>
      match accepted.completion with
      | .waiting _ => pure ()
      | .rejected assembled _ source _ =>
        ensure (assembled.packet.payload == response.payload && source.packet.datagram.payload == data &&
          accepted.state.fragments.queues.isEmpty && accepted.state.conntrack == unreplied &&
          !(closed.state.session.permits context scope))
          "Fine rejection must consume completed reassembly before tracking, so even a cached reply cannot mark seen-reply."
      | .processed .. => throw (IO.userError "The actual fine deny cannot produce an ordinary outcome or classification.")
    before := result.state
  ensure (before.history.length == warm.history.length + 3 && before.conntrack == unreplied)
    "Early permits remain auditable receipts even when the completed datagram fails the later guard."
  let mut filtered := warm
  for (fragment, index) in (family response).zipIdx do
    let result ← load (Model.step (pipeline false) policy filtered (arrival fragment (warm.clock + index + 1) server) current early fine)
    match result with
    | .rejected .. => throw (IO.userError "The early cached reply must pass.")
    | .accepted accepted => match accepted.completion with
      | .processed _ _ _ operation _ =>
        ensure (operation.outcome.disposition == .forwardDrop && operation.outcome.output.isNone && accepted.state.conntrack == replied)
          "Ordinary forward denial differs from fine ingress denial: the prepared reply has already updated seen-reply."
      | _ => pure ()
    filtered := result.state
  ensure (filtered.conntrack == replied) "The actual current ordinary denial must retain its real tracking effects."

private def actualContext (early : Model.EarlyGuard) (fine : IngressPolicy.Policy) (request : IPv4.Packet) : IO Unit := do
  let broadPolicy := { early.policy with rules := early.policy.rules.map (fun rule => { rule with ingress := none }) }
  let broad ← load (Model.checked broadPolicy)
  ensure (!IngressPolicy.check broad.policy early.policy)
    "The actual header-only early policy must fail numeric ownership comparison rather than gain an idealized drop."
  let mut before := Model.initial ns
  for (fragment, index) in (family request).zipIdx do
    let port := if index == 2 then attacker else client
    let result ← load (Model.step pipeline policy before (arrival fragment (index + 1) port) current broad fine)
    match result with
    | .rejected .. => throw (IO.userError "The actual broad early rule accepts both ingress indices.")
    | .accepted accepted => match accepted.completion with
      | .rejected _ _ _ _ =>
        ensure (accepted.state.conntrack.records.isEmpty && accepted.state.fragments.queues.isEmpty)
          "The completing packet's actual interface must select the fine guard, without trusting the offset-zero interface."
      | .processed .. => throw (IO.userError "The completing attacker interface cannot inherit the first fragment's fine permission.")
      | .waiting _ => pure ()
    before := result.state
  let mut mixed := Model.initial ns
  for (fragment, index) in (family request).zipIdx do
    let authentication := if index == 0 then current else if index == 1 then closed else renewed
    let result ← load (Model.step pipeline policy mixed (arrival fragment (index + 1)) authentication early fine)
    mixed := result.state
  ensure (mixed.conntrack == unreplied && mixed.fragments.queues.isEmpty &&
    mixed.history.map (fun receipt => receipt.authentication.state.auth.round) == [2, 2, 1])
    "Actual unchanged permits can assemble across session changes; round labels must not become fictitious Linux queue-key fields."

private def queueSemantics (early : Model.EarlyGuard) (fine : IngressPolicy.Policy) (request : IPv4.Packet) : IO Unit := do
  let first := part request 0 16 true
  let middle := part request 16 16 true
  let last := part request 32 13 false
  let trimmed ← drive (Model.initial ns) [part request 0 19 true, middle, last] client early fine
  ensure (trimmed.history.any (fun receipt => receipt.fragment.packet.payload.length == 19))
    "The ledger must retain original odd-MF bytes while reassembly emits only its normalized payload."
  let firstResult ← load (Model.step pipeline policy (Model.initial ns) (arrival first 1) current early fine)
  let duplicate := part { request with payload := List.replicate request.payload.length 255 } 0 16 true
  let repeated ← load (Model.step pipeline policy firstResult.state (arrival duplicate 2) current early fine)
  match repeated with
  | .rejected .. => throw (IO.userError "The repeated fragment must reach actual reassembly.")
  | .accepted accepted =>
    ensure (accepted.result.disposition == .duplicate && accepted.state.fragments.queues == firstResult.state.fragments.queues &&
      accepted.state.history.length == 2 && accepted.state.history.head?.any (fun receipt => receipt.fragment == duplicate))
      "A contained duplicate adds an actual early receipt while preserving the selected queue bytes and timer."
  let finished ← drive repeated.state [middle, last] client early fine
  ensure (finished.conntrack == unreplied) "Duplicate bytes must not replace the valid UDP payload chosen for completion."
  let overlap ← load (Model.step pipeline policy firstResult.state (arrival (part request 8 16 true) 2) current early fine)
  match overlap with
  | .rejected .. => throw (IO.userError "The overlapping interval must reach actual reassembly.")
  | .accepted accepted =>
    ensure (accepted.result.disposition == .overlap && accepted.result.output.isNone &&
      accepted.state.fragments.queues.isEmpty && accepted.state.conntrack.records.isEmpty && accepted.state.history.length == 2)
      "A queue overlap drop must preserve actual admission receipts without inventing ordinary attachment or output."
  let whole := part request 0 request.payload.length false
  let complete ← load (Model.step pipeline policy (Model.initial ns) (arrival whole 1) current early fine)
  match complete with
  | .rejected .. => throw (IO.userError "The permitted whole packet must pass its early guard.")
  | .accepted accepted => match accepted.completion with
    | .processed assembled _ _ operation _ =>
      ensure (!assembled.reassembled && accepted.state.fragments.queues.isEmpty &&
        accepted.state.conntrack == unreplied && operation.outcome.output.isSome &&
        operation.outcome.sizeCap.map (·.val) == some 1500 && accepted.state.history.length == 1)
        "Whole datagrams must use the same two guards without fabricating a fragment queue or ingress size cap."
    | _ => throw (IO.userError "The whole packet must reach its actual ordinary pipeline.")
  let denied ← load (Model.step pipeline policy (Model.initial ns) (arrival whole 1 attacker) current early fine)
  ensure (denied.state.fragments.queues.isEmpty && denied.state.conntrack.records.isEmpty && denied.state.history.isEmpty)
    "Early rejection must also prevent an otherwise complete datagram from creating a fresh ordinary row."
  reject (Model.step pipeline policy (Model.initial ns) (arrival { first with checksum := first.checksum + 1 } 1) current early fine)
    "A fragment with an invalid IPv4 checksum cannot enter the accepted ledger."

private def wrongPorts (early : Model.EarlyGuard) (fine : IngressPolicy.Policy) : IO Unit := do
  let malformed ← packet { original with sourcePort := 41001 }
  let mut before := Model.initial ns
  let mut rejected := 0
  for (fragment, index) in (family malformed).zipIdx do
    let result ← load (Model.step pipeline policy before (arrival fragment (index + 1)) current early fine)
    match result with
    | .rejected .. => throw (IO.userError "The coarse IPv4 selector cannot inspect the changed UDP source port.")
    | .accepted accepted => match accepted.completion with
      | .rejected _ _ source _ =>
        rejected := rejected + 1
        ensure (source.packet.header.sourcePort == 41001 && source.packet.datagram.payload == data)
          "The full-datagram guard must inspect the actual reassembled transport tuple."
      | .processed .. => throw (IO.userError "Coarse permission cannot authorize the changed complete UDP tuple.")
      | .waiting _ => pure ()
    before := result.state
  ensure (rejected == 1 && before.conntrack.records.isEmpty && before.fragments.queues.isEmpty && before.history.length == 3)
    "Fine tuple rejection must consume the completed queue without confirming a fresh flow."

private def residency (early : Model.EarlyGuard) (fine : IngressPolicy.Policy) (warm : Model.State) (request : IPv4.Packet) : IO Unit := do
  let packet := { request with identification := request.identification + 1 }
  let accepted ← load (Model.step pipeline policy warm (arrival (part packet 0 16 true) (warm.clock + 1)) current early fine)
  let live : Protocol.FragmentAdmission.Residency := ⟨some accepted.state, []⟩
  let successor := { ns with birth := 2 }
  reject (live.fresh successor) "A live namespace must retire before its successor can be created."
  let retired ← load live.retire
  ensure (retired.active.isNone && retired.archive.length == 1 && retired.archive.all (fun state =>
    state.ns == ns && state.fragments.queues == accepted.state.fragments.queues && state.conntrack == unreplied &&
    state.history.length == accepted.state.history.length))
    "Retirement must archive the actual queues, accepted ledger, and ordinary table without claiming a live primary."
  reject retired.retire "A retired namespace cannot be retired twice."
  reject (retired.step pipeline policy (arrival (part packet 32 13 false) (warm.clock + 2)) current early fine)
    "An archived namespace cannot execute a packet operation against its historical queue."
  let denied ← load (Model.checked {})
  reject (retired.step pipeline policy (arrival (part packet 32 13 false) (warm.clock + 2)) current denied fine)
    "Even an early-rejection no-op cannot execute against a retired namespace archive."
  reject (retired.fresh ns) "A retired namespace lifetime cannot reopen its old queue state."
  let replaced ← load (retired.fresh successor)
  let some fresh := replaced.active | throw (IO.userError "The fresh namespace must have an actual empty active state.")
  ensure (fresh.ns == successor && fresh.fragments.queues.isEmpty && fresh.conntrack.records.isEmpty &&
    fresh.history.isEmpty && fresh.clock == 0 && replaced.archive.length == 1)
    "A successor namespace starts without copied fragment buffers, receipts, or ordinary CT records."
  let last ← load (Model.step pipeline policy fresh
    (arrival (part packet 32 13 false) 1 { client with ns := successor }) current early fine)
  ensure (last.state.fragments.queues.length == 1 && last.state.fragments.queues.all (fun queue => queue.first.isNone) &&
    last.state.conntrack.records.isEmpty && replaced.archive.all (fun state => state.fragments.queues == accepted.state.fragments.queues))
    "Matching user/vif and IP fragment identifiers cannot import a retired namespace's missing payload into its successor."

private def sessionResidency (early : Model.EarlyGuard) (fine : IngressPolicy.Policy) (request : IPv4.Packet) : IO Unit := do
  reject (Protocol.FragmentAdmission.SessionResidency.initial ns closed)
    "A namespace cannot initially bind to an unauthorized EAP round."
  let bound ← load (Protocol.FragmentAdmission.SessionResidency.initial ns current)
  let first ← load (bound.step pipeline policy (arrival (part request 0 16 true) 1) current early fine)
  let live := { bound with namespaces := first.state }
  reject (live.step pipeline policy (arrival (part request 32 13 false) 2) closed early fine)
    "Logoff's changed authentication round cannot continue an old live residency."
  reject (live.step pipeline policy (arrival (part request 32 13 false) 2) renewed early fine)
    "Reauthorization requires explicit namespace retirement instead of a hidden round field in the queue key."
  let denied ← load (Model.checked {})
  reject (live.step pipeline policy (arrival (part request 32 13 false) 2) renewed denied fine)
    "A changed round cannot perform a clock-only early rejection against the previous residency."
  let retired ← load live.retire
  reject (retired.step pipeline policy (arrival (part request 32 13 false) 2) current early fine)
    "Retirement must remove the active packet API even when the supplied round matches the archived round."
  let successor := { ns with birth := 2 }
  reject (retired.fresh successor closed) "A fresh residency requires current EAP authorization."
  reject (retired.fresh ns renewed) "A new EAP round cannot reopen the old namespace lifetime."
  let replaced ← load (retired.fresh successor renewed)
  ensure (replaced.round == 2 && replaced.namespaces.archive.length == 1 && replaced.namespaces.active.all (fun state =>
    state.ns == successor && state.fragments.queues.isEmpty && state.history.isEmpty && state.conntrack.records.isEmpty))
    "Explicit retirement and fresh lifetime creation must preserve the old archive and empty every successor packet state."
  let input := arrival (part request 32 13 false) 2 { client with ns := successor }
  let operation : Protocol.FragmentAdmission.ResidentStep pipeline policy replaced.namespaces input renewed early fine ←
    load (replaced.step pipeline policy input renewed early fine)
  ensure (operation.state.archive.length == 1 && operation.state.active.all (fun state =>
    state.fragments.queues.length == 1 && state.fragments.queues.all (fun queue => queue.first.isNone) && state.conntrack.records.isEmpty))
    "A new round's suffix cannot consume payload bytes retained only in the retired namespace archive."

def run : IO Unit := do
  let originalAttachment ← expected client .original original
  let replyAttachment ← expected server .reply wire.reverse
  let attachments := [originalAttachment, replyAttachment]
  let early ← load (Model.checked (Compile.FragmentAttachment.compile current ns attachments []))
  let fine := Compile.IngressAttachment.compile current ns attachments []
  let request ← packet original
  let response ← packet wire.reverse
  let warm ← positive early fine request response
  earlyRejection early fine request
  lateRejection early fine warm response
  actualContext early fine request
  queueSemantics early fine request
  wrongPorts early fine
  residency early fine warm request
  sessionResidency early fine request
  reject (Model.checked { rules := [⟨some 2, traffic original, .permit⟩] })
    "The typed early guard must reject transport reads before any fragment execution."

end NetlibTest.FragmentAdmission
