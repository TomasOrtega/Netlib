import Netlib.Check.TCPReceive

namespace NetlibTest.TCPReceiveCheck

open Netlib Protocol
open Netlib.Check.TCPReceive

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

private def unwrap : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def item (values : List α) (index : Nat) : IO α :=
  match values[index]? with
  | some value => pure value
  | none => throw (IO.userError "The replay step is missing.")

private def seed : Model.State := {
  inbound := ⟨3221225986, 3325256706, Packet.Protocol.tcp, 41000, 9000⟩
  receiveNext := TCP.Seq.ofNat 100
  capacity := 5
  received := []
  sendUna := TCP.Seq.ofNat 4294967294
  sendNext := TCP.Seq.ofNat 2
  sent := [10, 11, 12, 13] }

private def raw (sequence acknowledgment : Nat) (flags : UInt8) (payload : List UInt8)
    (header : Packet.Header := seed.inbound) (options : List UInt8 := []) : IO (List UInt8) := do
  let segment : TCP.Segment := {
    sourcePort := header.sourcePort
    destinationPort := header.destinationPort
    sequence := TCP.Seq.ofNat sequence
    acknowledgment := TCP.Seq.ofNat acknowledgment
    reserved := 0
    flags
    window := 65535
    checksum := 0
    urgentPointer := 0
    options
    payload }
  let encoded ← unwrap (TCP.encode header.source header.destination (TCP.rechecksum header.source header.destination segment))
  unwrap (IPv4.encode ⟨0x28, 0x1234, true, 64, header.protocol, header.source, header.destination, encoded⟩)

private def seedJson (state : Model.State) : Lean.Json := Lean.Json.mkObj [
  ("inbound", Import.PacketFields.headerJson state.inbound),
  ("receiveNext", Lean.toJson state.receiveNext.val), ("capacity", Lean.toJson state.capacity),
  ("receivedHex", Lean.toJson (Import.EAPOL.bytesToHex state.received)),
  ("sendUna", Lean.toJson state.sendUna.val), ("sendNext", Lean.toJson state.sendNext.val),
  ("sentHex", Lean.toJson (Import.EAPOL.bytesToHex state.sent))]

private def fixture (state : Model.State) (packets : List (List UInt8)) : Lean.Json := Lean.Json.mkObj [
  ("schema", Lean.toJson (1 : Nat)), ("seed", seedJson state),
  ("packetsHex", Lean.toJson (packets.map Import.EAPOL.bytesToHex))]

private def parsed (state : Model.State) (packets : List (List UInt8)) : IO Input :=
  unwrap (Input.parse (fixture state packets).compress)

private def replayTests : IO Unit := do
  let first ← raw 100 0 0x10 [1, 2]
  let oldAck ← raw 102 4294967294 0x10 [3]
  let outside ← raw 200 2 0x10 [99]
  let last ← raw 103 2 0x10 [4]
  let input ← parsed seed [first, oldAck, outside, last]
  let report ← unwrap input.check
  ensure (report.supported && report.steps.length == 4 && report.remaining.isEmpty &&
      report.final.received == [1, 2, 3, 4] && report.final.receiveNext.val == 104 &&
      report.final.sent.isEmpty && report.final.sendUna.val == 2 && report.final.sendNext.val == 2 && report.final.window == 1)
    "The replay must use each computed state and keep the local capacity separate from the peer window."
  let a ← item report.steps 0
  let b ← item report.steps 1
  let c ← item report.steps 2
  let d ← item report.steps 3
  ensure (a.result.decision == .accepted 2 2 && a.result.state.sent == [12, 13] &&
      a.result.state.sendUna.val == 0 && a.result.state.window == 3 &&
      a.result.ack == some ⟨.data, TCP.Seq.ofNat 2, TCP.Seq.ofNat 102, 3⟩)
    "The first data segment must remove the exact sent prefix across sequence wrap."
  ensure (b.before == a.result.state && b.result.decision == .accepted 0 1 && b.result.state.sent == [12, 13])
    "An old ACK must leave the send span unchanged. Valid data must advance reception."
  ensure (c.result.decision == .blocked (.reject .sequence) && c.result.state == b.result.state &&
      c.result.ack == some ⟨.sequence, TCP.Seq.ofNat 2, TCP.Seq.ofNat 103, 2⟩ && d.before == c.result.state)
    "A supported sequence rejection must preserve state and permit the next replay step."
  let rendered := report.renderJson
  let steps ← unwrap ((← unwrap (rendered.getObjVal? "steps")).getArr?)
  let jsonFirst := steps[0]!
  ensure ((← unwrap (rendered.getObjVal? "final")) == stateJson report.final &&
      (← unwrap (rendered.getObjVal? "evaluatedPackets")) == Lean.toJson (4 : Nat) &&
      (← unwrap (jsonFirst.getObjVal? "rawIPv4Hex")) == Lean.toJson (Import.EAPOL.bytesToHex first) &&
      (← unwrap (jsonFirst.getObjVal? "decoded")) == decodedJson a.input.packet &&
      (← unwrap (jsonFirst.getObjVal? "decision")) == decisionJson (.accepted 2 2))
    "The JSON report must expose actual decoded bytes, decisions, and final state."
  let empty ← parsed seed []
  let emptyReport ← unwrap empty.check
  ensure (emptyReport.supported && emptyReport.steps.isEmpty && emptyReport.final == seed)
    "An empty replay must keep its valid seed."

private def rejectionTests : IO Unit := do
  let good ← raw 100 0 0x10 [1]
  let missing ← raw 100 0 0 [9]
  let future ← raw 100 3 0x10 [9]
  let tuple ← raw 100 0 0x14 [9] { seed.inbound with destinationPort := 9001 }
  let cases : List (List UInt8 × Model.Reject × Option Model.AckRequest) := [
    (missing, .missingAck, none), (future, .acknowledgment, some (TCP.EstablishedReceive.request seed .challenge)),
    (tuple, .tuple, none)]
  for (bytes, reason, ack) in cases do
    let input ← parsed seed [bytes, good]
    let report ← unwrap input.check
    let first ← item report.steps 0
    ensure (report.supported && report.steps.length == 2 && first.result.decision == .blocked (.reject reason) &&
        first.result.state == seed && first.result.ack == ack && report.final.received == [1])
      "A supported rejection must not change state or stop the next valid packet."

private def stopTests : IO Unit := do
  let good ← raw 100 0 0x10 [1]
  let trim ← raw 100 0 0x10 [1, 2, 3, 4, 5, 6]
  let outOfOrder ← raw 101 0 0x10 [1]
  let overlap ← raw 99 0 0x10 [1, 2]
  let reset ← raw 100 0 0x14 []
  let options ← raw 200 0 0x10 [] seed.inbound [1, 1, 1, 1]
  let cases : List (List UInt8 × Model.Unsupported) := [
    (trim, .trimming), (outOfOrder, .outOfOrder), (overlap, .trimming), (reset, .reset), (options, .options)]
  for (bytes, reason) in cases do
    let input ← parsed seed [bytes, good, []]
    let report ← unwrap input.check
    let first ← item report.steps 0
    ensure (!report.supported && report.steps.length == 1 && report.remaining == [good, []] &&
        first.result.decision == .blocked (.unsupported reason) && first.result.ack.isNone && report.final == seed)
      "An Unsupported result must stop before later state changes and transport decoding."
  let closed := { seed with capacity := 0 }
  let ackOnly ← raw 100 0 0x10 []
  let controls : List (UInt8 × Model.Unsupported) := [(0x14, .reset), (0x30, .urgent)]
  for (flags, reason) in controls do
    let bytes ← raw 100 0 flags [1]
    let input ← parsed closed [bytes, ackOnly]
    let report ← unwrap input.check
    let first ← item report.steps 0
    ensure (!report.supported && report.steps.length == 1 && report.remaining == [ackOnly] &&
        first.result.decision == .blocked (.unsupported reason) && report.final == closed)
      "Controls at a zero window must stop the replay before omitted endpoint actions."
  let input ← parsed seed [reset]
  let report ← unwrap input.check
  ensure (!report.supported && report.remaining.isEmpty && report.steps.length == 1)
    "An Unsupported last packet must not make the replay supported."

private def parserTests : IO Unit := do
  let bytes ← raw 100 0 0x10 [1]
  let json := fixture seed [bytes]
  for value in [Lean.toJson (0 : Nat), Lean.toJson (2 : Nat), .bool true, .null, .str "1"] do
    reject (Input.fromJson (json.setObjVal! "schema" value)) "The schema must be the integer one."
  reject (Input.parse (json.compress.replace "\"schema\":1" "\"schema\":1.0"))
    "The schema must not accept a decimal JSON number."
  reject (Input.fromJson (json.setObjVal! "final" (stateJson seed)))
    "A caller must not supply a replacement final state."
  let missing := Lean.Json.mkObj [("schema", Lean.toJson (1 : Nat)), ("seed", seedJson seed)]
  reject (Input.fromJson missing) "The parser must require the packet list."
  reject (Input.fromJson (json.setObjVal! "packetsHex" (.str "00"))) "The packet list must be an array."
  reject (Input.fromJson (json.setObjVal! "seed" (stateJson seed)))
    "The seed must not include a supplied receive window."
  for value in ["x", "0", "gg", "00zz"] do
    reject (Input.fromJson (json.setObjVal! "packetsHex" (Lean.toJson [value]))) "Packet hex must have valid syntax."
  for state in [{ seed with capacity := 65536 }, { seed with capacity := 0, received := [1] },
      { seed with sendNext := TCP.Seq.ofNat 3 }, { seed with inbound := { seed.inbound with protocol := Packet.Protocol.udp } },
      { seed with sent := List.replicate 65536 0, sendNext := seed.sendUna.add 65536 }] do
    reject (Input.fromJson (fixture state [bytes])) "Invalid seeds must reject before replay."
    reject (Input.check ⟨state, [bytes]⟩) "The programmatic checker must also reject invalid seeds."
  for key in ["receiveNext", "sendUna", "sendNext"] do
    reject (Input.fromJson (json.setObjVal! "seed" ((seedJson seed).setObjVal! key (Lean.toJson (4294967296 : Nat)))))
      "A seed sequence must be between 0 and 4294967295."
  for key in ["receivedHex", "sentHex"] do
    reject (Input.fromJson (json.setObjVal! "seed" ((seedJson seed).setObjVal! key (.str "zz"))))
      "Seed byte strings must have valid hex syntax."
  let text := json.compress
  reject (Input.parse (text.replace "\"schema\":" "\"schema\":1,\"schema\":"))
    "The parser must reject duplicate root keys."
  reject (Input.parse (text.replace "\"capacity\":" "\"capacity\":5,\"capacity\":"))
    "The parser must reject duplicate seed keys."

private def byteTests : IO Unit := do
  let good ← raw 100 0 0x10 [1, 2]
  for bytes in [[], good.take 19, good.take (good.length - 1),
      (good.toArray.modify 10 (· + 1)).toList, (good.toArray.modify 40 (· + 1)).toList] do
    let input ← parsed seed [bytes]
    reject input.check "Every evaluated packet must pass IPv4 and TCP decoding."
  let changed := (good.toArray.modify 40 (· + 1)).toList
  let reset ← raw 100 0 0x14 []
  let input ← parsed seed [reset, changed]
  let report ← unwrap input.check
  ensure (!report.supported && report.remaining == [changed])
    "An invalid later checksum must remain unevaluated after an Unsupported result."

example (input : Input) (report : Report input) : report.final.Valid := report.final_valid

example (input : Input) (report : Report input) (step : Step) (member : step ∈ report.steps) :
    ∃ prior later,
      report.steps = prior ++ step :: later ∧ Chain input.seed prior step.before ∧
      input.packets = prior.map (fun item => item.input.bytes) ++
        step.input.bytes :: (later.map (fun item => item.input.bytes) ++ report.remaining) ∧
      TCP.decodeIPv4 step.input.bytes = .ok step.input.packet ∧ step.result = Model.receive step.before step.input :=
  report.step_origin step member

example (input : Input) (report : Report input) :
    report.final.received = input.seed.received ++ report.steps.flatMap Step.acceptedPayload := report.received_prefix

def run : IO Unit := do
  replayTests
  rejectionTests
  stopTests
  parserTests
  byteTests

end NetlibTest.TCPReceiveCheck
