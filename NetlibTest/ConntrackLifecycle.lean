import Netlib.Protocol.ConntrackLifecycle

namespace NetlibTest.ConntrackLifecycle

open Netlib
open Netlib.Packet
open Netlib.Protocol
open Netlib.Protocol.ConntrackLifecycle
open Netlib.Packet.StatefulACL (CTState)

private def original : Header := ⟨3221225986, 3405803778, Protocol.tcp, 32000, 8080⟩
private def aliasEndpoint : Endpoint := ⟨3405803777, 40000⟩
private def backend : Endpoint := ⟨3325256706, 9000⟩
private def wire : Header :=
  (Rewrite.sourceEndpoint aliasEndpoint).apply ((Rewrite.destinationEndpoint backend).apply original)
private def translatedDestination : Header := (Rewrite.destinationEndpoint backend).apply original
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩

private def routes : List (Routing.Entry String) :=
  [⟨⟨backend.address, 32⟩, some "outside"⟩, ⟨⟨original.source, 32⟩, some "inside"⟩]

private def permitBackend : StatefulACL.Rule :=
  ⟨{ destination := some ⟨backend.address, 32⟩, destinationPorts := some (PortRange.single backend.port) },
    some [.new], .permit⟩

private def permitWire : StatefulACL.Rule :=
  ⟨{ source := some ⟨aliasEndpoint.address, 32⟩, sourcePorts := some (PortRange.single aliasEndpoint.port) },
    none, .permit⟩

private def permit : Pipeline := ⟨routes, [permitBackend], .deny, [permitWire], .deny⟩
private def deny : Pipeline := { routes, forward := [] }
private def keepEstablished : Pipeline := { routes, forward := [establishedPermit] }
private def newInput : Input := ⟨0, original, some entry⟩
private def oldInput : Input := ⟨0, original, none⟩
private def replyInput : Input := ⟨0, wire.reverse, none⟩
private def unreplied : State := ⟨[⟨entry, false⟩]⟩
private def replied : State := ⟨[⟨entry, true⟩]⟩
private def newAttachment : Attachment := ⟨entry, .original, .new, true⟩
private def oldAttachment : Attachment := ⟨entry, .original, .new, false⟩
private def establishedAttachment : Attachment := ⟨entry, .original, .established, false⟩
private def replyAttachment : Attachment := ⟨entry, .reply, .established, false⟩

private abbrev View := State × Option Header × Attachment × Disposition

private def view (result : Except Error Outcome) : Except Error View :=
  result.map fun outcome => (outcome.state, outcome.output, outcome.attachment, outcome.disposition)

example : entry.Compatible := (NetfilterNAT.Entry.check_correct _).mp (by decide)
example : unreplied.Valid := (State.check_correct _).mp (by decide)
example : replied.Valid := (State.check_correct _).mp (by decide)

example : view (step deny State.initial newInput) = .ok (State.initial, none, newAttachment, .forwardDrop) := by
  rfl

example : view (step { permit with routes := [] } State.initial newInput) =
    .ok (State.initial, none, newAttachment, .routeDrop) := by rfl

example : view (step { permit with late := [], lateDefault := .deny } State.initial newInput) =
    .ok (State.initial, none, newAttachment, .lateDrop) := by rfl

example : view (step permit State.initial newInput) = .ok (unreplied, some wire, newAttachment, .forwarded) := by
  rfl

example : (step permit State.initial newInput).map (·.afterDestination) = .ok translatedDestination := by rfl
example : (step permit State.initial newInput).map (·.afterSource) = .ok (some wire) := by rfl
example : (step permit State.initial newInput).map (·.nextHop) = .ok (some "outside") := by rfl

example : view (step permit unreplied oldInput) = .ok (unreplied, some wire, oldAttachment, .forwarded) := by
  rfl

example : view (step keepEstablished unreplied oldInput) = .ok (unreplied, none, oldAttachment, .forwardDrop) := by
  rfl

example : view (step deny unreplied replyInput) = .ok (replied, none, replyAttachment, .forwardDrop) := by
  rfl

example : view (step keepEstablished replied oldInput) =
    .ok (replied, some wire, establishedAttachment, .forwarded) := by rfl

example : view (step keepEstablished State.initial newInput) =
    .ok (State.initial, none, newAttachment, .forwardDrop) := by rfl

private def changedEntry : NetfilterNAT.Entry :=
  { entry with flow := { entry.flow with reply :=
      ((Rewrite.sourceEndpoint ⟨aliasEndpoint.address, 40001⟩).apply
        ((Rewrite.destinationEndpoint ⟨backend.address, 9003⟩).apply original)).reverse } }

example : changedEntry.check = true := by rfl

example : view (step permit unreplied { oldInput with candidate := some changedEntry }) =
    .error .unexpectedCandidate := by rfl

private def collisionEntry : NetfilterNAT.Entry :=
  { entry with flow := { entry.flow with original := { original with sourcePort := 32001 } } }
private def collisionInput : Input := ⟨0, collisionEntry.flow.original, some collisionEntry⟩

example : collisionEntry.check = true := by rfl
example : view (step permit unreplied collisionInput) = .error .confirmationCollision := by rfl
example : view (step deny unreplied collisionInput) =
    .ok (unreplied, none, ⟨collisionEntry, .original, .new, true⟩, .forwardDrop) := by rfl

private def episode : Except Error (State × List (Option Header)) := do
  let first ← step permit State.initial newInput
  let droppedReply ← step deny first.state replyInput
  let retained ← step keepEstablished droppedReply.state oldInput
  return (retained.state, [first.output, droppedReply.output, retained.output])

theorem dropped_reply_changes_later_policy : episode = .ok (replied, [some wire, none, some wire]) := by rfl

private def load (result : Except Error Outcome) : IO Outcome :=
  match result with
  | .ok outcome => pure outcome
  | .error error => throw (IO.userError error.describe)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def fails (result : Except Error Outcome) (expected : Error) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

def run : IO Unit := do
  let forwardDrop ← load (step deny State.initial newInput)
  ensure (forwardDrop.output.isNone && forwardDrop.state == State.initial)
    "A fresh forward-filter drop must not confirm the candidate."
  let lateDrop ← load (step { permit with late := [], lateDefault := .deny } State.initial newInput)
  ensure (lateDrop.disposition == .lateDrop && lateDrop.state == State.initial && lateDrop.afterSource == some wire)
    "A late drop must retain the translated observation without confirming the fresh flow."
  let routeDrop ← load (step { permit with routes := [] } State.initial newInput)
  ensure (routeDrop.disposition == .routeDrop && routeDrop.state == State.initial && routeDrop.afterSource.isNone)
    "Route failure must stop before source translation and confirmation."
  let first ← load (step permit State.initial newInput)
  ensure (first.state == unreplied && first.output == some wire)
    "An accepted original must confirm exactly its supplied binding."
  ensure (first.afterDestination == translatedDestination && first.afterSource == some wire && first.nextHop == some "outside")
    "Destination NAT must precede destination routing and forward filtering; source NAT must follow them."
  let repeated ← load (step permit first.state oldInput)
  ensure (repeated.attachment.classification == .new && !repeated.attachment.fresh &&
    repeated.attachment.entry == entry && repeated.output == some wire && repeated.state == first.state)
    "An unreplied original remains NEW and reuses the confirmed binding."
  ensure (fails (step permit first.state { oldInput with candidate := some changedEntry }) .unexpectedCandidate)
    "NEW classification must not permit replacement of a confirmed NAT binding."
  let blockedOriginal ← load (step keepEstablished first.state oldInput)
  ensure (blockedOriginal.output.isNone && blockedOriginal.state == first.state)
    "An unreplied original must not pass an established-only policy."
  let droppedReply ← load (step deny first.state replyInput)
  ensure (droppedReply.output.isNone && droppedReply.attachment.classification == .established && droppedReply.state == replied)
    "The first valid reply must mark seen-reply before a later forward-filter drop."
  let retained ← load (step keepEstablished droppedReply.state oldInput)
  ensure (retained.output == some wire && retained.attachment.classification == .established && retained.state == replied)
    "An early established permit can retain a stored flow after the policy starts denying new traffic."
  let deleted ← load (step keepEstablished State.initial newInput)
  ensure (deleted.output.isNone && deleted.state == State.initial)
    "Deleting the confirmed entry must expose the same tuple as new traffic under the changed policy."
  let replyAllowed ← load (step keepEstablished first.state replyInput)
  ensure (replyAllowed.output == some original.reverse && replyAllowed.nextHop == some "inside")
    "Reply NAT must restore both endpoints and route after inverse source NAT."
  let droppedReplyLate ← load (step { keepEstablished with lateDefault := .deny } first.state replyInput)
  ensure (droppedReplyLate.output.isNone && droppedReplyLate.state == replied &&
    droppedReplyLate.afterSource == some original.reverse)
    "An existing reply update must persist through a late drop."
  let droppedReplyRoute ← load (step { deny with routes := [] } first.state replyInput)
  ensure (droppedReplyRoute.output.isNone && droppedReplyRoute.state == replied)
    "An existing reply update must persist through a route failure."
  ensure (fails (step permit first.state collisionInput) .confirmationCollision)
    "Fresh confirmation must reject a reply-key collision."
  let collisionDropped ← load (step deny first.state collisionInput)
  ensure (collisionDropped.state == first.state && collisionDropped.disposition == .forwardDrop)
    "An unconfirmed dropped candidate must not reserve or collide with confirmed keys."
  ensure (fails (step permit State.initial oldInput) .missingCandidate)
    "A lookup miss requires an explicit candidate."
  ensure (fails (step permit State.initial { newInput with packet := { original with sourcePort := 32001 } }) .candidateMismatch)
    "The fresh candidate must match the original input tuple."
  ensure (fails (step permit State.initial { newInput with candidate := some { entry with sourceNAT := false } }) .incompatibleCandidate)
    "Native NAT flags must agree with changed tuple endpoints."
  ensure (fails (step permit State.initial { newInput with zone := 65536 }) .invalidZone)
    "Lookup zones must fit in 16 bits."
  ensure (fails (step permit State.initial { newInput with packet := { original with protocol := Protocol.icmp } }) .unsupportedTransport)
    "Unsupported transport must fail before attachment."
  ensure (fails (step permit ⟨[⟨entry, false⟩, ⟨entry, true⟩]⟩ oldInput) .invalidState)
    "An ambiguous confirmed table must not be processed."
  let calls : List Call := [⟨permit, newInput⟩, ⟨deny, replyInput⟩, ⟨keepEstablished, oldInput⟩]
  match Netlib.Protocol.ConntrackLifecycle.run State.initial calls with
  | .error error => throw (IO.userError error.describe)
  | .ok (final, outcomes) =>
    ensure (final == replied && outcomes.length == 3 && outcomes.all (·.state.check))
      "An ordered packet trace must preserve table validity through drops and policy updates."
  IO.println "Tracked forwarding lifecycle tests passed."

end NetlibTest.ConntrackLifecycle
