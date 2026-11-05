import Netlib.Protocol.TCP.Checkpoint

namespace NetlibTest.TCPCheckpoint

open Netlib Packet Protocol TCP
namespace CP
export Netlib.Protocol.TCP.Checkpoint (Gateway History Request Transition Snapshot Installation Error run capture install)
end CP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def checked : Except Checkpoint.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.message)

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.tcp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.tcp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, translated.reverse, 0, 0, 0⟩, true, true⟩

private def permit : ConntrackLifecycle.Pipeline := {
  routes := [⟨⟨3325256706, 32⟩, some "server"⟩, ⟨⟨3221225986, 32⟩, some "client"⟩]
  forward := [], forwardDefault := .permit }

private def packet (header : Header) (sequence acknowledgment : Nat) (flags : UInt8)
    (payload : List UInt8 := []) (window : InternetChecksum.Word := 8) (options : List UInt8 := []) : IO EstablishedReceive.Input := do
  let segment := computed header.source header.destination {
    sourcePort := header.sourcePort, destinationPort := header.destinationPort,
    sequence := Seq.ofNat sequence, acknowledgment := Seq.ofNat acknowledgment,
    reserved := 0, flags := flags, window := window, checksum := 0, urgentPointer := 0,
    options := options, payload := payload }
  let bytes ← load (IPv4.encode ⟨0, 0, true, 64, Packet.Protocol.tcp, header.source, header.destination, segment.encodeBytes⟩)
  load (EstablishedReceive.input bytes)

private structure Reached where
  gateway : CP.Gateway
  history : CP.History gateway

private def initial : Reached := ⟨.initial, .initial⟩

private def advance (before : Reached) (source : EstablishedReceive.Input)
    (candidate : Option NetfilterNAT.Entry := none) (pipeline : ConntrackLifecycle.Pipeline := permit) : IO Reached := do
  let transition ← checked (CP.run before.gateway pipeline ⟨source, 0, candidate⟩)
  pure ⟨transition.after, .advance before.history transition⟩

private def session (gateway : CP.Gateway) : IO Admission.Session :=
  match gateway.admission.phase with
  | .data value => pure value
  | _ => throw (IO.userError "The reached gateway has no TCP data history.")

private def startup : IO Reached := do
  let first ← advance initial (← packet original 1000 0 2) (some entry)
  match CP.capture first.history with
  | .error .notEstablished => pure ()
  | _ => throw (IO.userError "A pending SYN must not supply an established checkpoint.")
  let second ← advance first (← packet translated.reverse 5000 1001 18)
  match CP.capture second.history with
  | .error .notEstablished => pure ()
  | _ => throw (IO.userError "A pending SYN,ACK must not supply an established checkpoint.")
  advance second (← packet original 1001 5001 16)

private def rejected (result : Except Checkpoint.Error α) (expected : Checkpoint.Error) : IO Unit :=
  match result with
  | .error reason => ensure (reason == expected) "The checkpoint rejection reason is incorrect."
  | .ok _ => throw (IO.userError "The checkpoint operation must reject this state.")

private def continuingBytes : IO Unit := do
  let ready ← startup
  let clientData ← advance ready (← packet original 1001 5001 24 [97, 98, 99])
  let clientAck ← advance clientData (← packet translated.reverse 5001 1004 16)
  let serverData ← advance clientAck (← packet translated.reverse 5001 1004 24 [120, 121])
  let old ← checked (CP.capture serverData.history)
  let drained ← advance serverData (← packet translated.reverse 5003 1004 24 [122])
  rejected (CP.install old drained.history .initial) .staleSource
  let snapshot ← checked (CP.capture drained.history)
  let source ← session snapshot.source
  ensure (snapshot.cut == 7 && snapshot.record.seenReply && snapshot.source.same drained.gateway &&
    source.original.observed == 3 && source.original.acknowledged == 3 && source.reply.observed == 3 &&
    source.reply.acknowledged == 0 && source.reply.outstanding == 3 && source.reply.next.val == 5004)
    "Capture must retain the exact nonempty directional history and unacknowledged reply bytes."
  let installed ← checked (CP.install snapshot drained.history .initial)
  ensure (installed.state.same snapshot.source && installed.state.tracker == drained.gateway.tracker &&
    installed.state.admission.observations == drained.gateway.admission.observations)
    "Installation must copy the full exact tracker and admission pair."
  for direction in [FlowNAT.Direction.original, .reply] do
    ensure (installed.state.tracker.model.lookup (entry.flow.zone direction) (entry.flow.input direction) ==
      some ⟨entry.flow, direction⟩) "Both translated lookup directions must survive installation."
  let deferred ← packet original 1004 5004 16
  let request : CP.Request := ⟨deferred, 0, none⟩
  let continued ← checked (CP.run installed.state permit request)
  let retained ← checked (CP.run snapshot.source permit request)
  ensure (continued.after.same retained.after && continued.outcome.output.isSome)
    "Target continuation must use the exact source cut and actual forwarding computation."
  let afterAck ← session continued.after
  ensure (afterAck.reply.acknowledged == 3 && afterAck.reply.outstanding == 0 &&
    afterAck.original.next.val == 1004 && afterAck.reply.next.val == 5004)
    "The deferred ACK must remove the transferred nonzero reply prefix without a new SYN."
  let target : Reached := ⟨installed.state, installed.history⟩
  let acknowledged : Reached := ⟨continued.after, .advance target.history continued⟩
  let moreClient ← advance acknowledged (← packet original 1004 5004 24 [100])
  let moreServer ← advance moreClient (← packet translated.reverse 5004 1005 24 [123])
  let final ← session moreServer.gateway
  ensure (final.original.observed == 4 && final.reply.observed == 4 && final.original.acknowledged == 4 &&
    moreServer.gateway.admission.observations.length == 10)
    "Later data must extend the inherited byte epochs in each direction."
  rejected (CP.run .initial permit request) (.tracker .missingCandidate)
  let entryOnly : CP.Gateway := ⟨snapshot.source.tracker, .initial⟩
  rejected (CP.run entryOnly permit request) (.admission (.unsupported .missingHistory))
  rejected (CP.install snapshot drained.history entryOnly) .occupiedTarget
  let historyOnly : CP.Gateway := ⟨.initial, snapshot.source.admission⟩
  rejected (CP.install snapshot drained.history historyOnly) .occupiedTarget
  rejected (CP.install snapshot drained.history ready.gateway) .occupiedTarget
  let changedWindow : CP.Gateway := ⟨snapshot.source.tracker, {
    snapshot.source.admission with phase := .data {
      source with original := { source.original with peerWindow := 7 } } }⟩
  ensure (!changedWindow.same snapshot.source)
    "The exact source comparison must detect a changed lane window."
  let changedRecord : CP.Gateway := { snapshot.source with
    tracker := ⟨snapshot.source.tracker.records.map (fun record => { record with seenReply := false })⟩ }
  ensure (!changedRecord.same snapshot.source)
    "The exact source comparison must detect a changed reply observation."
  let explicitDefault : CP.Gateway := ⟨snapshot.source.tracker, {
    snapshot.source.admission with phase := .data { source with clientMSS := .present ⟨536, by decide⟩ } }⟩
  ensure (source.clientMSS.limit == 536 && !explicitDefault.same snapshot.source)
    "An explicit MSS of 536 must remain different from the absent source offer."

private def droppedReply : IO Unit := do
  let ready ← startup
  let sent ← advance ready (← packet original 1001 5001 24 [1, 2])
  let input ← packet translated.reverse 5001 1003 16 [] 4
  let dropped ← checked (CP.run sent.gateway { permit with lateDefault := .deny } ⟨input, 0, none⟩)
  ensure (dropped.outcome.output.isNone)
    "The selected late drop must retain its actual no-output decision."
  let history := Checkpoint.History.advance sent.history dropped
  let snapshot ← checked (CP.capture history)
  let copied ← checked (CP.install snapshot history .initial)
  let admitted ← session copied.state
  ensure (admitted.original.acknowledged == 2 && admitted.original.peerWindow.val == 4 &&
    copied.state.admission.observations.length == 5 && snapshot.record.seenReply)
    "A dropped reply's ACK, peer window, and observation must survive the exact checkpoint."
  let resumed ← checked (CP.run copied.state permit ⟨← packet original 1003 5001 24 [3], 0, none⟩)
  ensure (resumed.outcome.output.isSome && (← session resumed.after).original.observed == 3)
    "Continuation must use the state derived from the dropped reply."

private def mssValue (number : Nat) : IO MSS.Value :=
  match MSS.Value.ofNat number with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.message)

private def startupMSS (client server : MSS.Value) : IO Reached := do
  let first ← advance initial (← packet original 1000 0 2 [] 2048 (MSS.encode client)) (some entry)
  let second ← advance first (← packet translated.reverse 5000 1001 18 [] 2048 (MSS.encode server))
  advance second (← packet original 1001 5001 16 [] 2048)

private def directionalMSS : IO Unit := do
  let clientMSS ← mssValue 700
  let serverMSS ← mssValue 1200
  let ready ← startupMSS clientMSS serverMSS
  let learned ← session ready.gateway
  ensure (learned.clientMSS == .present clientMSS && learned.serverMSS == .present serverMSS &&
      (learned.peerMSS .original).limit == 1200 && (learned.peerMSS .reply).limit == 700)
    "The gateway must learn each direction's limit from the opposite peer advertisement."
  let first ← advance ready (← packet original 1001 5001 24 (List.replicate 600 97) 2048)
  let acknowledged ← advance first (← packet translated.reverse 5001 1601 16 [] 2048)
  let sent ← advance acknowledged (← packet translated.reverse 5001 1601 24 (List.replicate 600 120) 2048)
  let snapshot ← checked (CP.capture sent.history)
  let installed ← checked (CP.install snapshot sent.history .initial)
  match sourcePhase : snapshot.source.admission.phase with
  | .data source =>
    let _ := installed.mss source sourcePhase
    let copied ← session installed.state
    ensure (copied.clientMSS == source.clientMSS && copied.serverMSS == source.serverMSS)
      "The installed checkpoint must retain the two actual learned MSS offers."
    let changedClient ← mssValue 701
    let changed : CP.Gateway := ⟨snapshot.source.tracker, {
      snapshot.source.admission with phase := .data { source with clientMSS := .present changedClient } }⟩
    let altered ← session changed
    ensure (changed.tracker == snapshot.source.tracker &&
        changed.admission.observations == snapshot.source.admission.observations &&
        altered.original == source.original && altered.reply == source.reply && !changed.same snapshot.source)
      "Changing only an MSS offer must invalidate the exact source image."
    let changedServer ← mssValue 1201
    let other : CP.Gateway := ⟨snapshot.source.tracker, {
      snapshot.source.admission with phase := .data { source with serverMSS := .present changedServer } }⟩
    ensure (!other.same snapshot.source)
      "The exact source image must retain the raw MSS offer from the server."
  | _ => throw (IO.userError "The MSS checkpoint must retain established source history.")
  let alternate ← startupMSS (← mssValue 701) serverMSS
  let old ← checked (CP.capture ready.history)
  rejected (CP.install old alternate.history .initial) .staleSource
  let deferred ← packet original 1601 5601 16 [] 2048
  let continued ← checked (CP.run installed.state permit ⟨deferred, 0, none⟩)
  let restored : Reached := ⟨continued.after, .advance installed.history continued⟩
  let larger ← advance restored (← packet original 1601 5601 24 (List.replicate 800 100) 2048)
  let returned ← advance larger (← packet translated.reverse 5601 2401 24 (List.replicate 700 121) 2048)
  let final ← session returned.gateway
  ensure (final.original.observed == 1400 && final.reply.observed == 1300 &&
      final.clientMSS == .present clientMSS && final.serverMSS == .present serverMSS)
    "Continuation above the absent-option default must retain the copied directional MSS limits."
  rejected (CP.run returned.gateway permit ⟨← packet original 2401 6301 24 (List.replicate 1201 1) 2048, 0, none⟩)
    (.admission (.unsupported .data))
  rejected (CP.run returned.gateway permit ⟨← packet translated.reverse 6301 2401 24 (List.replicate 701 1) 2048, 0, none⟩)
    (.admission (.unsupported .data))

private def repeatedRange : IO Unit := do
  let ready ← startup
  let sent ← advance ready (← packet original 1001 5001 16 [1, 2, 3])
  let old ← checked (CP.capture sent.history)
  let repeated ← advance sent (← packet original 1001 5001 16 [1, 2, 3])
  ensure ((← session repeated.gateway).original == (← session sent.gateway).original &&
      repeated.history.length == sent.history.length + 1 && !repeated.gateway.same sent.gateway)
    "A repeated packet must advance the exact history cut while its unique lane remains equal."
  rejected (CP.install old repeated.history .initial) .staleSource
  let snapshot ← checked (CP.capture repeated.history)
  let installed ← checked (CP.install snapshot repeated.history .initial)
  let retry ← checked (CP.run installed.state permit ⟨← packet original 1002 5001 16 [2, 3], 0, none⟩)
  ensure (retry.outcome.output.isSome && (← session retry.after).original.observed == 3)
    "The installed exact observations must justify the earlier range slice on the target."
  let changed : CP.Gateway := { snapshot.source with admission := {
    snapshot.source.admission with observations := snapshot.source.admission.observations.dropLast } }
  ensure (!changed.same snapshot.source)
    "The checkpoint image must retain repeated packet observations as well as byte frontiers."

def run : IO Unit := do
  rejected (CP.capture (Checkpoint.History.initial)) .notEstablished
  continuingBytes
  droppedReply
  directionalMSS
  repeatedRange
  IO.println "Reachable TCP checkpoint tests passed."

end NetlibTest.TCPCheckpoint
