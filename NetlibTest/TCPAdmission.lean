import Netlib.Protocol.TCP.Admission
import Netlib.Protocol.TCP.WireForwarding

namespace NetlibTest.TCPAdmission

open Netlib Packet Protocol TCP
namespace A
export Netlib.Protocol.TCP.Admission (State Phase Error Unsupported Result step commit)
end A

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def checked : Except Admission.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.message)

private def tracked : Except ConntrackLifecycle.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.describe)

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.tcp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.tcp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, translated.reverse, 0, 0, 0⟩, true, true⟩

private def permit : ConntrackLifecycle.Pipeline := {
  routes := [⟨⟨3325256706, 32⟩, some "server"⟩, ⟨⟨3221225986, 32⟩, some "client"⟩]
  forward := [], forwardDefault := .permit }

private def packet (header : Header) (sequence acknowledgment : Nat) (flags : UInt8)
    (payload : List UInt8 := []) (window : InternetChecksum.Word := 8)
    (options : List UInt8 := []) (ttl : UInt8 := 64) : IO EstablishedReceive.Input := do
  let segment := computed header.source header.destination {
    sourcePort := header.sourcePort, destinationPort := header.destinationPort,
    sequence := Seq.ofNat sequence, acknowledgment := Seq.ofNat acknowledgment,
    reserved := 0, flags := flags, window := window, checksum := 0, urgentPointer := 0,
    options := options, payload := payload }
  let bytes ← load (IPv4.encode ⟨0, 0, true, ttl, Packet.Protocol.tcp, header.source, header.destination, segment.encodeBytes⟩)
  load (EstablishedReceive.input bytes)

private structure Served where
  gate : Admission.State
  tracker : ConntrackLifecycle.State
  emitted : Bool
  classification : StatefulACL.CTState

private def serve (pipeline : ConntrackLifecycle.Pipeline) (gate : Admission.State)
    (tracker : ConntrackLifecycle.State) (input : EstablishedReceive.Input)
    (candidate : Option NetfilterNAT.Entry := none) : IO Served := do
  let wire : TCP.WireForwarding.Input := ⟨0, input.packet, candidate⟩
  let prepared ← tracked (ConntrackLifecycle.prepare tracker wire.lifecycle)
  let accepted ← checked (Admission.step gate input wire.lifecycle prepared rfl)
  let outcome ← tracked (TCP.WireForwarding.process pipeline wire input.valid prepared)
  let committed ← checked (Admission.commit accepted outcome.state)
  pure ⟨committed, outcome.state, outcome.output.isSome, prepared.attachment.classification⟩

private def rejected (gate : Admission.State) (tracker : ConntrackLifecycle.State)
    (input : EstablishedReceive.Input) (expected : Admission.Unsupported)
    (candidate : Option NetfilterNAT.Entry := none) : IO Unit := do
  let wire : TCP.WireForwarding.Input := ⟨0, input.packet, candidate⟩
  let prepared ← tracked (ConntrackLifecycle.prepare tracker wire.lifecycle)
  match Admission.step gate input wire.lifecycle prepared rfl with
  | .error (.unsupported reason) => ensure (reason == expected) "The admission stop reason is incorrect."
  | .ok _ => throw (IO.userError "An unsupported observation must not acquire admission.")

private def session (gate : Admission.State) : IO Admission.Session :=
  match gate.phase with
  | .data value => pure value
  | _ => throw (IO.userError "The TCP data history is missing.")

private def startup (clientISS serverISS : Nat) : IO Served := do
  let syn ← packet original clientISS 0 2
  let first ← serve permit .initial .initial syn (some entry)
  ensure (first.gate.phase.name == "syn" && first.gate.observations.length == 1 && first.emitted &&
    first.classification == .new && first.tracker.records.all (fun record => !record.seenReply))
    "A new admitted SYN must learn its sequence and confirm the selected entry only after output."
  let synAck ← packet translated.reverse serverISS ((Seq.ofNat clientISS).add 1).val 18
  let second ← serve permit first.gate first.tracker synAck
  ensure (second.gate.phase.name == "synAck" && second.classification == .established &&
    second.tracker.records.all (·.seenReply))
    "The reply firewall classification must remain distinct from the pending startup phase."
  let final ← packet original ((Seq.ofNat clientISS).add 1).val ((Seq.ofNat serverISS).add 1).val 16
  let third ← serve permit second.gate second.tracker final
  let ready ← session third.gate
  ensure (ready.original.base == (Seq.ofNat clientISS).add 1 && ready.reply.base == (Seq.ofNat serverISS).add 1 &&
    ready.original.observed == 0 && ready.reply.observed == 0 && ready.original.acknowledged == 0 &&
    ready.reply.acknowledged == 0 && ready.original.peerWindow.val == 8 && ready.reply.peerWindow.val == 8 &&
    third.gate.observations.length == 3)
    "Startup must derive empty byte epochs after the two actual SYN control positions."
  pure third

private def ordinaryData : IO Unit := do
  let ready ← startup 1000 5000
  let sent ← serve permit ready.gate ready.tracker (← packet original 1001 5001 24 [42, 43])
  let data ← session sent.gate
  ensure (data.original.next.val == 1003 && data.original.outstanding == 2 && data.reply.next.val == 5001)
    "Observed data must advance only its direction's byte epoch."
  let acknowledged ← serve permit sent.gate sent.tracker (← packet translated.reverse 5001 1003 16 [] 4)
  let advanced ← session acknowledged.gate
  ensure (advanced.original.acknowledged == 2 && advanced.original.outstanding == 0 && advanced.original.peerWindow.val == 4)
    "A forward ACK must remove the observed prefix and update the peer window."
  let old ← serve permit acknowledged.gate acknowledged.tracker (← packet translated.reverse 5001 1002 16 [77] 0)
  let retained ← session old.gate
  ensure (retained.reply.observed == 1 && retained.original.acknowledged == 2 && retained.original.peerWindow.val == 4)
    "An old ACK can accompany data but must not replace the peer window."
  let closed ← serve permit old.gate old.tracker (← packet translated.reverse 5002 1003 16 [] 0)
  let zero ← session closed.gate
  ensure (zero.original.peerWindow.val == 0)
    "A duplicate ACK can close the peer window when the freshness condition passes."
  rejected closed.gate closed.tracker (← packet original 1003 5002 16 [44]) .window
  let pureAck ← serve permit closed.gate closed.tracker (← packet original 1003 5002 16)
  let settled ← session pureAck.gate
  ensure (settled.reply.acknowledged == 1 && settled.original.peerWindow.val == 0)
    "A pure ACK remains supported with a zero peer data window."
  let reopened ← serve permit pureAck.gate pureAck.tracker (← packet translated.reverse 5002 1003 16 [] 8)
  let last ← serve permit reopened.gate reopened.tracker (← packet original 1003 5002 16 [44])
  let final ← session last.gate
  ensure (final.original.observed == 3 && final.original.next.val == 1004 && last.gate.observations.length == 10)
    "Reopened space must permit the next exact byte range."
  rejected last.gate last.tracker (← packet original 1003 5002 16) .sequence
  rejected last.gate last.tracker (← packet original 1004 4999 16) .acknowledgment
  rejected last.gate last.tracker (← packet original 1004 5003 16) .acknowledgment
  rejected last.gate last.tracker (← packet original 1004 5002 20) .flags
  rejected last.gate last.tracker (← packet original 1004 5002 16 [] 8 [1, 1, 1, 1]) .options
  rejected last.gate last.tracker (← packet original 1004 5002 16 (List.replicate 537 1)) .data

private def droppedObservations : IO Unit := do
  let syn ← packet original 1000 0 2
  let denied ← serve { permit with forwardDefault := .deny } .initial .initial syn (some entry)
  ensure (denied.gate.phase.name == "empty" && denied.gate.observations.isEmpty &&
    denied.tracker.records.isEmpty && !denied.emitted)
    "A denied fresh SYN must not leave a confirmed admission history."
  let accepted ← serve permit .initial .initial syn (some entry)
  let synAck ← packet translated.reverse 5000 1001 18
  let dropped ← serve { permit with lateDefault := .deny } accepted.gate accepted.tracker synAck
  ensure (!dropped.emitted && dropped.gate.phase.name == "synAck" && dropped.gate.observations.length == 2 &&
    dropped.tracker.records.all (·.seenReply))
    "A valid dropped reply must retain its ingress history and seen-reply update."
  rejected .initial accepted.tracker synAck .missingHistory
  rejected accepted.gate .initial syn .replacement (some entry)
  rejected accepted.gate accepted.tracker syn .direction
  let wire : TCP.WireForwarding.Input := ⟨0, synAck.packet, none⟩
  let prepared ← tracked (ConntrackLifecycle.prepare accepted.tracker wire.lifecycle)
  let admitted ← checked (Admission.step accepted.gate synAck wire.lifecycle prepared rfl)
  match Admission.commit admitted .initial with
  | .error (.unsupported .historyLost) => pure ()
  | _ => throw (IO.userError "Loss of an existing confirmed entry must stop the selected history.")
  rejected .initial .initial (← packet original 1000 0 2 [1]) .data (some entry)

private def windowBounds : IO Unit := do
  let ready ← startup 1000 5000
  let sent ← serve permit ready.gate ready.tracker (← packet original 1001 5001 16 [1, 2])
  let shrunk ← serve permit sent.gate sent.tracker (← packet translated.reverse 5001 1001 16 [] 1)
  let small ← session shrunk.gate
  ensure (small.original.outstanding == 2 && small.original.peerWindow.val == 1 && decide small.original.Valid)
    "A window reduction below outstanding data must preserve a valid byte history."
  rejected shrunk.gate shrunk.tracker (← packet original 1003 5001 16 [3]) .window
  let ack ← serve permit shrunk.gate shrunk.tracker (← packet original 1003 5001 16)
  ensure ((← session ack.gate).original.outstanding == 2)
    "A pure ACK must remain admissible after a window reduction."
  let wide ← serve permit ready.gate ready.tracker (← packet translated.reverse 5001 1001 16 [] 65535)
  let maximum ← serve permit wide.gate wide.tracker (← packet original 1001 5001 16 (List.replicate 536 42))
  let bounded ← session maximum.gate
  ensure (bounded.original.observed == 536 && bounded.original.outstanding == 536)
    "The no-option profile must accept its exact default MSS."

def run : IO Unit := do
  ordinaryData
  droppedObservations
  windowBounds
  for (clientISS, serverISS) in [(0, 0), (4294967295, 5000), (1000, 4294967295), (4294967295, 4294967295)] do
    let ready ← startup clientISS serverISS
    let client := (Seq.ofNat clientISS).add 1
    let server := (Seq.ofNat serverISS).add 1
    let sent ← serve permit ready.gate ready.tracker (← packet original client.val server.val 16 [42])
    let ack ← serve permit sent.gate sent.tracker (← packet translated.reverse server.val (client.add 1).val 16)
    let final ← session ack.gate
    ensure (final.original.observed == 1 && final.original.acknowledged == 1 && final.original.outstanding == 0)
      "Admission byte coordinates must remain exact across serial wrap."
  IO.println "Checked TCP admission history tests passed."

end NetlibTest.TCPAdmission
