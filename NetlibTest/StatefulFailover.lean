import Netlib.Protocol.StatefulFailover

namespace NetlibTest.StatefulFailover

open Netlib Packet Protocol
namespace Model
export Netlib.Protocol.StatefulFailover (State Gateway Leg Event Result PacketResult PacketCall step)
end Model

private def initial : Model.State := Netlib.Protocol.StatefulFailover.State.initial

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, translated.reverse, 0, 0, 0⟩, true, true⟩
private def missingReply : NetfilterNAT.Entry :=
  ⟨⟨translated.reverse, translated, 0, 0, 0⟩, false, false⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def requestPayload : List UInt8 := [0, 255, 2, 68]
private def replyPayload : List UInt8 := [9, 0, 255]

private def routes : List (Routing.Entry String) :=
  [⟨⟨3325256706, 32⟩, some "server"⟩, ⟨⟨3221225986, 32⟩, some "client"⟩,
    ⟨⟨3405803777, 32⟩, none⟩]
private def permit : ConntrackLifecycle.Pipeline := { routes, forward := [], forwardDefault := .permit }
private def deny : ConntrackLifecycle.Pipeline := { routes, forward := [] }
private def established : ConntrackLifecycle.Pipeline :=
  { routes, forward := [ConntrackLifecycle.establishedPermit] }

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def packet (header : Header) (payload : List UInt8) : IO UDP.DecodedIPv4 := do
  let datagram := UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let ip : IPv4.Packet := ⟨16, 4660, false, 64, Packet.Protocol.udp, header.source, header.destination, transport⟩
  unwrap (UDP.decodeIPv4 (← unwrap (IPv4.encode ip)))

private def call (gateway : Model.Gateway) (leg : Model.Leg) (pipeline : ConntrackLifecycle.Pipeline)
    (packet : UDP.DecodedIPv4) (candidate : Option NetfilterNAT.Entry := none) : Model.Event :=
  .packet ⟨gateway, leg, pipeline, ⟨0, packet, candidate⟩⟩

private def fails (result : Except String α) (expected : String) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

private def emission (result : Model.Result) (header : Header) (payload : List UInt8) : IO Unit := do
  let some observed := result.packet | throw (IO.userError "Expected an actual packet result.")
  let some output := observed.outcome.output | throw (IO.userError "Expected emitted bytes.")
  ensure (output.target == header && output.decoded.header == header &&
    output.decoded.datagram.payload == payload && output.decoded.ip.packet.ttl == 63 &&
    output.decoded.ip.packet.tos == 16 && output.decoded.ip.packet.identification == 4660)
    "Failover must retain the selected NAT boundary, payload, and IP metadata, and decrement TTL once."
  ensure ((← unwrap (UDP.decodeIPv4 output.bytes)) == output.decoded)
    "The emitted datagram must decode with valid IPv4 and UDP checksums."

private def dropped (result : Model.Result) (disposition : WireForwarding.Disposition)
    (classification : StatefulACL.CTState) (fresh : Bool) : IO Unit := do
  let some observed := result.packet | throw (IO.userError "Expected an actual packet result.")
  ensure (observed.outcome.output.isNone && observed.outcome.disposition == disposition &&
    observed.outcome.attachment.classification == classification && observed.outcome.attachment.fresh == fresh)
    "The selected gateway must report its computed drop and conntrack attachment."

private def handoffTimeline (request reply : UDP.DecodedIPv4) : IO Unit := do
  let first ← unwrap (Model.step initial (call .primary .client permit request (some entry)))
  emission first translated requestPayload
  ensure (first.state.primary == unreplied && first.state.standby == .initial && first.state.cache.isNone)
    "Only the gateway that processed the actual first packet may hold its confirmed record."
  let staged ← unwrap (Model.step first.state (.stage 0 original))
  ensure (staged.state.primary == unreplied && staged.state.standby == .initial &&
    staged.state.cache.map (·.source) == some first.state.primary &&
    staged.state.cache.map (·.sourceEpoch) == some 1 &&
    staged.state.cache.map (·.record.seenReply) == some false)
    "Cache staging must cite the actual primary prefix without installing standby kernel state."
  let clientMoved ← unwrap (Model.step staged.state (.handoff .client .standby))
  ensure (clientMoved.state.owners.client == .standby && clientMoved.state.owners.server == .primary &&
    clientMoved.state.standby == .initial && clientMoved.packet.isNone)
    "Each endpoint route changes separately from replication and packet processing."
  ensure (fails (Model.step clientMoved.state (call .standby .server permit reply))
    "The packet gateway disagrees with the selected endpoint route.")
    "A server packet cannot use the standby before the server route handoff."
  let bothMoved ← unwrap (Model.step clientMoved.state (.handoff .server .standby))
  let fenced ← unwrap (Model.step bothMoved.state (.fence .primary))
  ensure (fenced.state.isFenced .primary && fenced.state.primary == unreplied && fenced.state.standby == .initial)
    "Fencing must preserve both confirmed tables and leave an uncommitted standby empty."
  let missing ← unwrap (Model.step fenced.state (call .standby .server permit reply (some missingReply)))
  dropped missing .routeDrop .new true
  ensure (missing.state.standby == .initial)
    "A missing standby association must follow its actual untranslated blackhole route without confirming a replacement."
  let committed ← unwrap (Model.step missing.state (.commit 180))
  ensure (committed.state.primary == unreplied && committed.state.standby == unreplied &&
    committed.installed.map (·.commitTTL) == some 180 && committed.packet.isNone)
    "Commit must install the selected cached record independently of route ownership."
  ensure (fails (Model.step committed.state (.commit 180))
    "Colliding native commit and destructive retry are outside this profile.")
    "A repeated install must not pretend native collision recovery is atomic or idempotent."
  let blockedOriginal ← unwrap (Model.step committed.state (call .standby .client established request))
  dropped blockedOriginal .forwardDrop .new false
  let deniedReply ← unwrap (Model.step committed.state (call .standby .server deny reply))
  dropped deniedReply .forwardDrop .established false
  ensure (deniedReply.state.standby == replied && deniedReply.state.primary == unreplied)
    "A denied standby reply must mark SEEN_REPLY without changing the fenced primary."
  let permittedReply ← unwrap (Model.step deniedReply.state (call .standby .server permit reply))
  emission permittedReply original.reverse replyPayload
  let continued ← unwrap (Model.step permittedReply.state (call .standby .client established request))
  emission continued translated requestPayload
  let reverse ← unwrap (Model.step continued.state (call .standby .server established reply))
  emission reverse original.reverse replyPayload
  ensure (reverse.state.epoch == 11 && reverse.state.primary == unreplied && reverse.state.standby == replied &&
    reverse.state.cache.map (·.sourceEpoch) == some 1 && reverse.state.cache.map (·.record.seenReply) == some false)
    "Later standby traffic must preserve the earlier cache provenance and advance only the computed ordinary table."

private def staleCache (request reply : UDP.DecodedIPv4) : IO Unit := do
  let first ← unwrap (Model.step initial (call .primary .client permit request (some entry)))
  let cached ← unwrap (Model.step first.state (.stage 0 original))
  let updated ← unwrap (Model.step cached.state (call .primary .server permit reply))
  ensure (updated.state.primary == replied && updated.state.cache.map (·.record.seenReply) == some false)
    "A staged record must not silently track later primary packets."
  let installed ← unwrap (Model.step updated.state (.commit 180))
  ensure (installed.state.standby == unreplied && installed.state.primary == replied)
    "Commit must use the chosen cache epoch rather than a newer primary record."
  let erased ← unwrap (Model.step cached.state (.erase .primary 0 original))
  ensure (erased.state.primary == .initial && erased.state.cache.map (·.record.entry) == some entry)
    "Deleting primary kernel state must not manufacture a cache deletion."
  let retained ← unwrap (Model.step erased.state (.commit 180))
  ensure (retained.state.standby == unreplied)
    "A retained cached record remains an explicit installation source after primary deletion."
  let forgotten ← unwrap (Model.step cached.state .forget)
  ensure (forgotten.state.cache.isNone && forgotten.state.primary == unreplied && forgotten.state.standby == .initial)
    "Forgetting the cache must leave both kernel projections unchanged."
  ensure (fails (Model.step forgotten.state (.commit 180))
    "No staged primary record is available for commitment.")
    "A cache-free commit cannot create a standby initial record."

def run : IO Unit := do
  let request ← packet original requestPayload
  let reply ← packet translated.reverse replyPayload
  ensure (fails (Model.step initial (call .standby .client permit request (some entry)))
    "The packet gateway disagrees with the selected endpoint route.")
    "The packet's actual gateway must match its endpoint route owner."
  ensure (fails (Model.step initial (.commit 180))
    "No staged primary record is available for commitment.")
    "Commit requires a previously selected actual primary record."
  let fenced ← unwrap (Model.step initial (.fence .primary))
  ensure (fails (Model.step fenced.state (call .primary .client permit request (some entry)))
    "The selected gateway is fenced from data forwarding.")
    "A fenced route owner cannot process a data packet."
  handoffTimeline request reply
  staleCache request reply

end NetlibTest.StatefulFailover
