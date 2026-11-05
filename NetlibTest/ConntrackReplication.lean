import Netlib.Protocol.ConntrackReplication

namespace NetlibTest.ConntrackReplication

open Netlib Packet Protocol
open ConntrackLifecycle (Record State)
namespace Rep
export Netlib.Protocol.ConntrackReplication (Error Selection Installed stage commit stage_origin)
end Rep
namespace CT
export Netlib.Protocol.ConntrackLifecycle (Pipeline Input Error Outcome step)
end CT

private def original : Header := ⟨3221225986, 3405803778, Protocol.udp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, translated.reverse, 0, 0, 0⟩, true, true⟩
private def record : Record := ⟨entry, false⟩
private def source : State := ⟨[record]⟩
private def replied : State := ⟨[⟨entry, true⟩]⟩

private def routes : List (Routing.Entry String) :=
  [⟨⟨3325256706, 32⟩, some "server"⟩, ⟨⟨3221225986, 32⟩, some "client"⟩]
private def allow : CT.Pipeline := { routes, forward := [], forwardDefault := .permit }
private def deny : CT.Pipeline := { routes, forward := [] }
private def established : CT.Pipeline :=
  { routes, forward := [⟨{}, some [.established], .permit⟩] }
private def fresh : CT.Input := ⟨0, original, some entry⟩
private def old : CT.Input := ⟨0, original, none⟩
private def reply : CT.Input := ⟨0, translated.reverse, none⟩

private def staged : Except Rep.Error Rep.Selection := do
  let actual ← (CT.step allow State.initial fresh).mapError (fun _ => (.invalidSource : Rep.Error))
  Rep.stage actual.state 7 0 original

private def installed : Except Rep.Error Rep.Installed := do
  Rep.commit State.initial (← staged) 180

example : source.Valid := (State.check_correct _).mp (by decide)
example : (CT.step allow State.initial fresh).map (·.state) = .ok source := by rfl
example : staged.map (·.sourceEpoch) = .ok 7 := by rfl
example : staged.map (·.source) = .ok source := by rfl
example : staged.map (·.record) = .ok record := by rfl
example : installed.map (·.state) = .ok source := by rfl
example : installed.map (·.commitTTL) = .ok 180 := by rfl
example : installed.map (·.selection.recordForInstall.entry.flow.remainingTTL) = .ok 0 := by rfl

example (selection : Rep.Selection) (accepted : Rep.stage source 7 0 original = .ok selection) :
    selection.source = source ∧ selection.sourceEpoch = 7 ∧ selection.record ∈ source.records ∧
      selection.record.entry.flow.key selection.direction = (0, original) :=
  Rep.stage_origin source 7 0 original selection accepted

private def load (result : Except Rep.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def packet (result : Except CT.Error CT.Outcome) : IO CT.Outcome :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def fails (result : Except Rep.Error α) (expected : Rep.Error) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let actual ← packet (CT.step allow State.initial fresh)
  ensure (actual.state == source && actual.output == some translated)
    "Source selection must follow an actual confirmed NAT packet."
  let cached ← load staged
  ensure (cached.sourceEpoch == 7 && cached.source == actual.state && cached.record == record)
    "The cache must retain its source epoch and exact source record."
  let backup ← load installed
  ensure (backup.state == source && backup.commitTTL == 180 &&
    backup.selection.record.entry.flow.remainingTTL == 0)
    "Commit must install the normalized record and retain timeout configuration separately."
  ensure (backup.state.model.translate 0 original == some translated &&
    backup.state.model.translate 0 translated.reverse == some original.reverse)
    "Both direction keys must restore the selected NAT boundary."
  let beforeReply ← packet (CT.step established backup.state old)
  ensure (beforeReply.output.isNone && beforeReply.attachment.classification == .new)
    "An unreplied copied original must remain NEW under current policy."
  let deniedReply ← packet (CT.step deny backup.state reply)
  ensure (deniedReply.output.isNone && deniedReply.state == replied &&
    deniedReply.attachment.classification == .established && !deniedReply.attachment.fresh)
    "A denied reply must reuse the installed binding and mark SEEN_REPLY."
  let later ← packet (CT.step established deniedReply.state old)
  ensure (later.output == some translated && later.attachment.classification == .established)
    "The reply update must affect a later original's current-policy classification."
  let restored ← packet (CT.step established deniedReply.state reply)
  ensure (restored.output == some original.reverse)
    "Reply forwarding must restore the original client and service endpoints."
  let refreshedSource ← packet (CT.step allow actual.state reply)
  ensure (refreshedSource.state == replied && cached.record.seenReply == false)
    "A later source reply must not mutate an earlier staged record."
  let seen ← load (Rep.stage refreshedSource.state 8 0 original)
  let seenBackup ← load (Rep.commit State.initial seen 180)
  let immediate ← packet (CT.step established seenBackup.state old)
  ensure (seen.record.seenReply && immediate.output == some translated)
    "A staged SEEN_REPLY record must preserve established original classification."
  ensure (fails (Rep.stage State.initial 0 0 original) .missingRecord)
    "A cache cannot invent a record absent from the computed source table."
  ensure (fails (Rep.stage ⟨[record, record]⟩ 0 0 original) .invalidSource)
    "Ambiguous source keys must prevent staging."
  let otherZone : Record := { record with entry := { entry with flow :=
    { entry.flow with originalZone := 10, replyZone := 10 } } }
  ensure (fails (Rep.stage ⟨[otherZone]⟩ 0 10 original) .unsupportedProfile)
    "The selected replication profile requires zone zero in both directions."
  let timed : Record := { record with entry := { entry with flow := { entry.flow with remainingTTL := 1 } } }
  ensure (fails (Rep.stage ⟨[timed]⟩ 0 0 original) .unsupportedProfile)
    "Replication must use the normalized ordinary table."
  let tcpOriginal := { original with protocol := Protocol.tcp }
  let tcpReply := { (translated.reverse) with protocol := Protocol.tcp }
  let tcp : Record := ⟨⟨⟨tcpOriginal, tcpReply, 0, 0, 0⟩, true, true⟩, false⟩
  ensure (fails (Rep.stage ⟨[tcp]⟩ 0 0 tcp.entry.flow.original) .unsupportedProfile)
    "TCP replication lies outside this selected native profile."
  ensure (fails (Rep.commit ⟨[record, record]⟩ cached 180) .invalidTarget)
    "An invalid standby table must not receive a modeled installation."
  ensure (fails (Rep.commit State.initial cached 0) .invalidCommitTTL &&
    fails (Rep.commit State.initial cached 4294967296) .invalidCommitTTL)
    "Commit timeout metadata must remain a positive 32-bit value."
  let smallest ← load (Rep.commit State.initial cached 1)
  let largest ← load (Rep.commit State.initial cached 4294967295)
  ensure (smallest.state == largest.state && smallest.state == source)
    "Timeout metadata must not simulate aging or imply a minimum remaining lifetime."
  ensure (fails (Rep.commit backup.state cached 180) .unsupportedCollision)
    "Repeated native commit is outside the collision-free installation profile."
  let originalCollision : Record := { record with entry := { entry with flow :=
    { entry.flow with reply := { translated.reverse with destinationPort := 40001 } } } }
  let replyCollision : Record := { record with entry := { entry with flow :=
    { entry.flow with original := { original with sourcePort := 41001 } } } }
  ensure (fails (Rep.commit ⟨[originalCollision]⟩ cached 180) .unsupportedCollision &&
    fails (Rep.commit ⟨[replyCollision]⟩ cached 180) .unsupportedCollision)
    "Either direction-key collision must refuse this model profile."
  let unrelatedFlow : FlowNAT.Entry := { entry.flow with
    original := { original with sourcePort := 41002 }
    reply := { (translated.reverse) with destinationPort := 40002 } }
  let unrelated : Record := ⟨{ entry with flow := unrelatedFlow }, false⟩
  let preserved ← load (Rep.commit ⟨[unrelated]⟩ cached 180)
  ensure (preserved.state.records == [unrelated, record] &&
    preserved.state.model.translate 0 unrelated.entry.flow.original == some unrelated.entry.flow.reply.reverse)
    "A successful install must preserve unrelated records and their lookup behavior."

end NetlibTest.ConntrackReplication
