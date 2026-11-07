import Netlib.Protocol.TCP.CheckpointCoverageFacts

namespace NetlibTest.TCPStartupCheckpoint

open Netlib Packet Protocol TCP
namespace CP
export Netlib.Protocol.TCP.Checkpoint (Gateway History Request Transition run capture install)
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

private def wire (header : Header) (sequence acknowledgment : Nat) (flags : UInt8)
    (payload : List UInt8 := []) (window : InternetChecksum.Word := 16)
    (options : List UInt8 := []) (ttl : UInt8 := 64) : IO (List UInt8) := do
  let segment := computed header.source header.destination {
    sourcePort := header.sourcePort, destinationPort := header.destinationPort,
    sequence := Seq.ofNat sequence, acknowledgment := Seq.ofNat acknowledgment,
    reserved := 0, flags := flags, window := window, checksum := 0, urgentPointer := 0,
    options := options, payload := payload }
  load (IPv4.encode ⟨0, 0, true, ttl, Packet.Protocol.tcp, header.source, header.destination, segment.encodeBytes⟩)

private def packet (header : Header) (sequence acknowledgment : Nat) (flags : UInt8)
    (payload : List UInt8 := []) (window : InternetChecksum.Word := 16)
    (options : List UInt8 := []) (ttl : UInt8 := 64) : IO EstablishedReceive.Input := do
  load (EstablishedReceive.input (← wire header sequence acknowledgment flags payload window options ttl))

private structure Reached where
  gateway : CP.Gateway
  history : CP.History gateway

private def initial : Reached := ⟨.initial, .initial⟩

private def advance (before : Reached) (source : EstablishedReceive.Input)
    (candidate : Option NetfilterNAT.Entry := none)
    (mode : AdmissionExecution.Mode := .startupRecovery) : IO Reached := do
  let transition ← checked (CP.run before.gateway permit ⟨source, 0, candidate⟩ mode)
  let some emission := transition.outcome.output
    | throw (IO.userError "The selected startup service must emit an actual packet.")
  let forwarded ← load (EstablishedReceive.input emission.bytes)
  ensure (transition.outcome.disposition == .forwarded &&
      transition.prepared.attachment.entry == entry && transition.outcome.state.records.length == 1 &&
      emission.target == entry.flow.output transition.prepared.attachment.direction &&
      forwarded.packet.header == emission.target &&
      forwarded.packet.segment.sequence == source.packet.segment.sequence &&
      forwarded.packet.segment.acknowledgment == source.packet.segment.acknowledgment &&
      forwarded.packet.segment.flags == source.packet.segment.flags &&
      forwarded.packet.segment.window == source.packet.segment.window &&
      forwarded.packet.segment.options == source.packet.segment.options &&
      forwarded.packet.segment.payload == source.packet.segment.payload &&
      forwarded.packet.ip.packet.ttl.toNat + 1 == source.packet.ip.packet.ttl.toNat)
    "Actual service must confirm the binding and preserve transport fields through checked NAT output."
  let current := Admission.observe transition.request.source transition.request.wire.lifecycle transition.prepared
  ensure (transition.nextAdmission.observations == before.gateway.admission.observations ++ [current] &&
      current.bytes == source.bytes)
    "Every admitted control must append its own current observation."
  pure ⟨transition.after, .advance before.history transition⟩

private def samePhase (before after : Reached) : IO Unit :=
  ensure (Checkpoint.phaseImage before.gateway.admission.phase == Checkpoint.phaseImage after.gateway.admission.phase)
    "A repeated startup control must preserve its phase, fields, and learned MSS offers."

private def rejectAdmission (gateway : CP.Gateway) (source : EstablishedReceive.Input)
    (mode : AdmissionExecution.Mode := .startupRecovery) (expected : Option Admission.Unsupported := none) : IO Unit :=
  match CP.run gateway permit ⟨source, 0, none⟩ mode with
  | .error (.admission (.unsupported reason)) =>
    match expected with
    | none => pure ()
    | some selected => ensure (reason == selected) "Ordinary admission must retain its original error reason."
  | _ => throw (IO.userError "The unsupported startup packet must fail admission.")

private def session (gateway : CP.Gateway) : IO Admission.Session :=
  match gateway.admission.phase with
  | .data value => pure value
  | _ => throw (IO.userError "The mixed startup history must reach the data phase.")

private def observation (reached : Reached) (index : Nat) (source : EstablishedReceive.Input)
    (mode : AdmissionExecution.Mode) (priorLength : Nat) : IO Unit := do
  match selected : reached.gateway.admission.observations[index]? with
  | none => throw (IO.userError "The selected actual observation is missing.")
  | some seen =>
    let origin := reached.history.observationOrigin index seen selected
    have exactBytes : seen.bytes = origin.transition.request.source.bytes := origin.bytes
    have exactSegment : seen.segment = origin.transition.request.source.packet.segment := origin.segment
    have exactPosition : index = origin.before.admission.observations.length := origin.position
    ensure (seen.bytes == source.bytes && origin.transition.request.source.bytes == source.bytes &&
        seen.segment == source.packet.segment && origin.mode == mode && origin.prior.length == priorLength)
      "The observation origin must name the actual current transition, bytes, mode, and preceding cut."
    let _ := exactBytes
    let _ := exactSegment
    let _ := exactPosition

private def mss (value : Nat) : IO MSS.Value :=
  match MSS.Value.ofNat value with
  | .ok selected => pure selected
  | .error reason => throw (IO.userError reason.message)

private def recovered : IO Reached := do
  let client ← mss 700
  let server ← mss 1200
  let syn ← packet original 1000 0 2 [] 16 (MSS.encode client)
  let first ← advance initial syn (some entry)
  ensure (first.gateway.tracker.records == [⟨entry, false⟩])
    "The first emitted SYN must confirm the fresh entry without a reply observation."
  let duplicateSyn ← packet original 1000 0 2 [] 16 (MSS.encode client) 63
  rejectAdmission first.gateway duplicateSyn .ordinary (some .direction)
  let repeated ← advance first duplicateSyn
  samePhase first repeated
  ensure (duplicateSyn.bytes != syn.bytes && repeated.gateway.admission.observations.length == 2)
    "The duplicate must retain its distinct current IP bytes rather than the earlier template bytes."
  observation repeated 1 duplicateSyn .startupRecovery 1
  rejectAdmission first.gateway (← packet original 1000 0 2 [] 15 (MSS.encode client))
  rejectAdmission first.gateway (← packet original 1000 0 2 [] 16 (MSS.encode (← mss 701)))
  rejectAdmission first.gateway (← packet original 1000 0 2 [9] 16 (MSS.encode client))
  let missing : CP.Gateway := { first.gateway with admission := { first.gateway.admission with observations := [] } }
  rejectAdmission missing duplicateSyn
  let bare ← packet translated.reverse 5001 1001 16 [] 24
  rejectAdmission repeated.gateway bare .ordinary (some .flags)
  let barePending ← advance repeated bare
  samePhase repeated barePending
  ensure (barePending.gateway.tracker.records == [⟨entry, true⟩])
    "A bare reply must mark the existing tracker reply without learning missing TCP server fields."
  rejectAdmission barePending.gateway (← packet translated.reverse 5001 1001 20 [] 24)
  let synAck ← packet translated.reverse 5000 1001 18 [] 24 (MSS.encode server)
  let answered ← advance barePending synAck
  let duplicateSynAck ← packet translated.reverse 5000 1001 18 [] 24 (MSS.encode server) 62
  rejectAdmission answered.gateway duplicateSynAck .ordinary (some .direction)
  let echoed ← advance answered duplicateSynAck
  samePhase answered echoed
  observation echoed 4 duplicateSynAck .startupRecovery 4
  rejectAdmission echoed.gateway (← packet translated.reverse 5001 1001 16 [] 23)
  rejectAdmission echoed.gateway (← packet translated.reverse 5002 1001 16 [] 24)
  rejectAdmission echoed.gateway (← packet translated.reverse 5000 1001 18 [] 24 (MSS.encode (← mss 1201)))
  let bareKnown ← advance echoed bare
  samePhase echoed bareKnown
  let finalAck ← packet original 1001 5001 16 [] 16
  let established ← advance bareKnown finalAck
  let lateSyn ← advance established (← packet original 1000 0 2 [] 16 (MSS.encode client) 61)
  samePhase established lateSyn
  let lateSynAck ← advance lateSyn (← packet translated.reverse 5000 1001 18 [] 24 (MSS.encode server) 61)
  samePhase lateSyn lateSynAck
  let windowAck ← advance lateSynAck (← packet translated.reverse 5001 1001 16 [] 18)
  let learned ← session windowAck.gateway
  ensure (windowAck.history.length == 10 && windowAck.gateway.admission.observations.length == 10 &&
      learned.clientMSS == .present client && learned.serverMSS == .present server &&
      learned.original.observed == 0 && learned.reply.observed == 0 &&
      learned.original.peerWindow.val == 18 && learned.original.windowSequence.val == 5001)
    "Recovery controls must preserve empty byte coverage and MSS while data-phase ACKs use legacy window updates."
  pure windowAck

private def continued : IO Unit := do
  let reached ← recovered
  let snapshot ← checked (CP.capture reached.history)
  let installed ← checked (CP.install snapshot reached.history .initial)
  ensure (snapshot.cut == 10 && installed.history.length == 10 && installed.state.same reached.gateway &&
      installed.state.admission.observations == reached.gateway.admission.observations)
    "Capture and installation must retain the exact mixed startup history and all separate observations."
  let target : Reached := ⟨installed.state, installed.history⟩
  let data ← packet original 1001 5001 24 [97, 98, 99] 16
  let sent ← advance target data none .ordinary
  let acknowledged ← advance sent (← packet translated.reverse 5001 1004 16 [] 20) none .ordinary
  let settled ← session acknowledged.gateway
  ensure (acknowledged.history.length == 12 && settled.original.observed == 3 &&
      settled.original.acknowledged == 3 && settled.original.outstanding == 0 && settled.original.peerWindow.val == 20 &&
      settled.clientMSS.limit == 700 && settled.serverMSS.limit == 1200)
    "Ordinary data and ACK service must extend the installed history without another handshake."
  observation acknowledged 10 data .ordinary 10
  match phase : acknowledged.gateway.admission.phase with
  | .data current =>
    match runs : current.original.coverage.runs with
    | [] => throw (IO.userError "The ordinary continuation must retain its actual data coverage source.")
    | head :: _ =>
      have member : head ∈ (current.lane .original).coverage.runs := by
        change head ∈ current.original.coverage.runs
        rw [runs]
        exact List.mem_cons_self
      let origin := acknowledged.history.coverageOrigin current phase .original head member
      have exactPayload : head.bytes = origin.observation.transition.request.source.packet.segment.payload := origin.payload
      have exactIndex : head.metadata = origin.observation.before.admission.observations.length := origin.index
      ensure (head.metadata == 10 && head.bytes == [97, 98, 99] && origin.observation.mode == .ordinary &&
          origin.observation.transition.request.source.bytes == data.bytes)
        "Coverage must cite the actual ordinary data operation after the copied recovery prefix."
      let _ := exactPayload
      let _ := exactIndex
  | _ => throw (IO.userError "Ordinary continuation must remain in the data phase.")

def run : IO Unit := do
  match EstablishedReceive.input (← wire original 1000 0 2 [] 16 [2, 0, 0, 0]) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Malformed option framing must fail before checkpoint execution.")
  continued
  IO.println "Startup recovery checkpoint tests passed."

end NetlibTest.TCPStartupCheckpoint
