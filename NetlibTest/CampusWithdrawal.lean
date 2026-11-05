import Netlib.Protocol.CampusWithdrawal

namespace NetlibTest.CampusWithdrawal

open Netlib Packet Protocol
namespace Model
export Netlib.Protocol.CampusWithdrawal (State Event Result step contract Admissible)
end Model
open StatefulFailover (Gateway)

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def payload : List UInt8 := [0, 255, 65, 0, 17]
private def routes : List (Routing.Entry String) :=
  [⟨⟨3325256706, 32⟩, some "server"⟩, ⟨⟨3221225986, 32⟩, some "client"⟩]
private def permit : ConntrackLifecycle.Pipeline := { routes, forward := [], forwardDefault := .permit }
private def deny : ConntrackLifecycle.Pipeline := { routes, forward := [] }
private def configuration (id : String) (pipeline : ConntrackLifecycle.Pipeline) : SafeHandoff.Configuration := ⟨id, pipeline⟩
private def initial : Model.State := .initial (configuration "primary" permit) (configuration "standby" permit)

example (before : Model.State) (event : Model.Event) (safe : before.Safe) (allowed : Model.Admissible before event) :
    ∃ result, Model.step before event = .ok result ∧ result.state.Safe :=
  Protocol.CampusWithdrawal.admissible_progress before event safe allowed

example (trace : Model.contract.Trace before events after) (safe : before.Safe) :
    after.Safe ∧ ∀ event, Model.Admissible after event → ∃ result, Model.step after event = .ok result ∧ result.state.Safe :=
  Protocol.CampusWithdrawal.arbitrary_interleavings trace safe

example (trace : Model.contract.Trace before events after) (withdrawn : before.withdrawn = true) :
    after.withdrawn = true ∧ after.archive = before.archive ∧
      after.handoff.gateways.primary = before.handoff.gateways.primary :=
  Protocol.CampusWithdrawal.trace_archive trace withdrawn

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def source (header : Header) : IO SafeHandoff.Source := do
  let datagram := UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let bytes ← unwrap (IPv4.encode ⟨32, 4321, true, 64, Packet.Protocol.udp, header.source, header.destination, transport⟩)
  match decoded : UDP.decodeIPv4 bytes with
  | .error error => throw (IO.userError error)
  | .ok packet => pure ⟨bytes, packet, decoded⟩

private def step (before : Model.State) (event : Model.Event) : IO Model.Result := do
  let result ← unwrap (Model.step before event)
  ensure result.state.check "Every accepted operation must retain the executable withdrawal invariant."
  pure result

private def operation (before : Model.State) (event : SafeHandoff.Event) : IO Model.Result := do
  let result ← step before (.operation event)
  ensure result.operation.isSome "A delegated operation must retain its actual handoff result."
  pure result

private def rejects (before : Model.State) (event : Model.Event) (expected : String) : IO Unit :=
  match Model.step before event with
  | .error message => ensure (message == expected) s!"Expected {expected}; got {message}."
  | .ok _ => throw (IO.userError "The operation must fail its declared before-state guard.")

private def assigned (result : Model.Result) (id : Nat) (gateway : Gateway) : IO Unit := do
  let some operation := result.operation | throw (IO.userError "Expected the delegated assignment result.")
  let some ticket := operation.admitted | throw (IO.userError "Expected the actual allocated identity.")
  ensure (ticket.id == id && ticket.value.gateway == gateway)
    "The endpoint route read must allocate the expected gateway and fresh identity."

private def served (result : Model.Result) (id : Nat) (gateway : Gateway) (direction : FlowNAT.Direction)
    (classification : StatefulACL.CTState) (disposition : WireForwarding.Disposition) : IO Unit := do
  let some operation := result.operation | throw (IO.userError "Expected the delegated processing result.")
  let some served := operation.served | throw (IO.userError "Expected the selected actual pending ticket.")
  ensure (served.ticket.id == id && served.ticket.value.gateway == gateway &&
    served.outcome.attachment.direction == direction && served.outcome.attachment.classification == classification &&
    served.outcome.disposition == disposition && served.outcome.attachment.entry == entry)
    "Processing must use the actual assigned gateway and its current ordinary tracker classification and policy."
  match served.outcome.output with
  | none => ensure (disposition != .forwarded) "Permitted service must emit actual bytes."
  | some output =>
    let target := if direction == .original then wire else original.reverse
    ensure (disposition == .forwarded && output.decoded.header == target && output.target == target &&
      output.decoded.datagram.payload == payload && output.decoded.ip.packet.ttl == 63 &&
      output.decoded.ip.packet.tos == 32 && output.decoded.ip.packet.identification == 4321)
      "Continuing service must preserve the protected translation, binary payload, and IP metadata with one TTL decrement."
    ensure ((← unwrap (UDP.decodeIPv4 output.bytes)) == output.decoded)
      "The continued packet must decode with valid IPv4 and UDP checksums."

def run : IO Unit := do
  let request ← source original
  let reply ← source wire.reverse
  rejects initial .withdraw "Withdraw only after both routes move, primary work drains, and primary fencing completes."
  let first ← operation initial (.establish ⟨0, request.packet, some entry⟩)
  ensure (first.state.handoff.gateways.primary == unreplied && first.state.handoff.gateways.standby == .initial)
    "The primary packet must establish the selected binding before staging and replication."
  let staged ← operation first.state (.stage 0 original)
  let committed ← operation staged.state (.commit 180)
  let oldRequest ← operation committed.state (.assign .original request)
  assigned oldRequest 0 .primary
  let oldReply ← operation oldRequest.state (.assign .reply reply)
  assigned oldReply 1 .primary
  let client ← operation oldReply.state (.handoff .client .standby)
  let newRequest ← operation client.state (.assign .original request)
  assigned newRequest 2 .standby
  let server ← operation newRequest.state (.handoff .server .standby)
  rejects server.state .withdraw "Withdraw only after both routes move, primary work drains, and primary fencing completes."
  rejects server.state (.operation (.fence .primary))
    "Drain the gateway's outstanding route assignments before fencing it."
  let overtaking ← operation server.state (.serve 2)
  served overtaking 2 .standby .original .new .forwarded
  let revoked ← operation overtaking.state (.install .primary (configuration "primary-deny" deny))
  let denied ← operation revoked.state (.serve 1)
  served denied 1 .primary .reply .established .forwardDrop
  let restored ← operation denied.state (.install .primary (configuration "primary-restored" permit))
  let drained ← operation restored.state (.serve 0)
  served drained 0 .primary .original .established .forwarded
  ensure (drained.state.handoff.outstanding .primary == 0 && drained.state.handoff.gateways.primary == replied)
    "Old assignments must drain through actual processing before physical primary withdrawal."
  rejects drained.state .withdraw "Withdraw only after both routes move, primary work drains, and primary fencing completes."
  let fenced ← operation drained.state (.fence .primary)
  ensure (fenced.state.ready && fenced.state.handoff.gateways.isFenced .primary)
    "Both standby owners, an empty primary workset, and the primary fence establish withdrawal readiness."
  let withdrawn ← step fenced.state .withdraw
  ensure (withdrawn.state.withdrawn && withdrawn.state.archive == some replied && withdrawn.operation.isNone &&
    withdrawn.state.handoff.gateways.primary == replied && withdrawn.state.handoff.gateways.standby == unreplied &&
    withdrawn.state.handoff.gateways.epoch == fenced.state.handoff.gateways.epoch)
    "Withdrawal must archive historical primary state without manufacturing a live kernel update or advancing the handoff epoch."
  rejects withdrawn.state .withdraw "The primary is already withdrawn."
  for forbidden in [SafeHandoff.Event.stage 0 original, .commit 180, .handoff .client .primary,
      .handoff .client .standby, .fence .primary, .install .primary (configuration "forbidden" deny),
      .establish ⟨0, request.packet, some entry⟩] do
    rejects withdrawn.state (.operation forbidden) "The withdrawn primary permits no live operation."
  let finalRequest ← operation withdrawn.state (.assign .original request)
  assigned finalRequest 3 .standby
  let finalReply ← operation finalRequest.state (.assign .reply reply)
  assigned finalReply 4 .standby
  let closed ← operation finalReply.state (.install .standby (configuration "standby-deny" deny))
  let blocked ← operation closed.state (.serve 4)
  served blocked 4 .standby .reply .established .forwardDrop
  let reopened ← operation blocked.state (.install .standby (configuration "standby-permit" permit))
  let continued ← operation reopened.state (.serve 3)
  served continued 3 .standby .original .established .forwarded
  let forgotten ← operation continued.state .forget
  ensure (forgotten.state.archive == some replied && forgotten.state.handoff.gateways.primary == replied &&
    forgotten.state.handoff.gateways.standby == replied && forgotten.state.handoff.work.pending.isEmpty &&
    forgotten.state.handoff.gateways.cache.isNone && forgotten.state.handoff.gateways.isFenced .primary)
    "Live standby processing and cache changes must retain the exact archived primary and exclude its later use."
  let wrongArchive := { forgotten.state with archive := some unreplied }
  ensure (!wrongArchive.check) "A different historical primary snapshot must fail the archival invariant."
  let missingPrimary := { forgotten.state with
    handoff := { forgotten.state.handoff with gateways := { forgotten.state.handoff.gateways with primary := .initial } } }
  ensure (!missingPrimary.check) "The archived model snapshot cannot silently become an empty live-primary observation."

end NetlibTest.CampusWithdrawal
