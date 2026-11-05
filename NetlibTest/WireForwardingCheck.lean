import Netlib.Check.WireForwarding

namespace NetlibTest.WireForwardingCheck

open Netlib Packet Protocol Check.WireForwarding

example (report : Report routing initial observations) : report.compliant = true ↔ Agreement routing initial observations :=
  report.compliant_iff

example (report : Report routing initial observations) (valid : initial.Valid) :
    report.final.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.Valid := report.trace.valid valid

example (report : Report routing initial observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) (config : Config) (zone : Nat) (packet : WirePacket)
    (observed : PacketObservation) (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .packet config zone packet observed state)
    (output : WirePacket) (seen : observed.output = some output) :
    output.checked.packet.datagram.payload = packet.checked.packet.datagram.payload ∧
      output.checked.packet.ip.packet.ttl.toNat = packet.checked.packet.ip.packet.ttl.toNat - 1 :=
  report.observed_output_payload compliant finding member config zone packet observed state event output seen

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def values (json : Lean.Json) (key : String) : Except String (Array Lean.Json) :=
  json.getObjVal? key >>= Lean.Json.getArr?

private def atIndex (items : List α) (index : Nat) : IO α :=
  match items[index]? with
  | some value => pure value
  | none => throw (IO.userError s!"Expected wire forwarding fixture element {index}.")

private def findPacket (findings : List Finding) (predicate : PacketResult → Bool) : IO Finding :=
  match findings.find? (fun finding => (finding.result.packet.map predicate).getD false) with
  | some finding => pure finding
  | none => throw (IO.userError "Expected the selected wire forwarding packet event.")

private def packetResult (finding : Finding) : IO PacketResult :=
  match finding.result.packet with
  | some packet => pure packet
  | none => throw (IO.userError "Expected a packet result.")

private def changeEvent (json : Lean.Json) (index : Nat) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let events ← values json "events"
  return json.setObjVal! "events" (.arr (events.set! index (change events[index]!)))

private def observed (event : Lean.Json) : Except String Lean.Json := event.getObjVal? "observed"

private def without (json : Lean.Json) (field : String) : Except String Lean.Json := do
  return Lean.Json.mkObj ((← json.getObj?).toList.filter (fun item => item.1 != field))

private def uncheckedMetadata (observation : Lean.Json) : Lean.Json :=
  ["classification", "fresh", "afterDestination", "afterSource", "nextHop", "disposition"].foldl
    (fun value key => value.setObjVal! key .null) observation

private def rewire (raw : String) (ipChange : IPv4.Packet → IPv4.Packet)
    (udpChange : UDP.Datagram → UDP.Datagram) : Except String String := do
  let bytes ← Import.EAPOL.bytesFromHex raw
  let checked ← Check.Wire.checkBytes bytes
  let ip := ipChange checked.packet.ip.packet
  let selected := udpChange checked.packet.datagram
  let datagram := if checked.packet.datagram.checksum = 0 then { selected with checksum := 0 }
    else UDP.computed ip.source ip.destination selected.sourcePort selected.destinationPort selected.payload
  let transport ← UDP.encode ip.source ip.destination datagram
  let encoded ← IPv4.encode { ip with payload := transport }
  let bytes := Import.EthernetIPv4.encode { checked.envelope with payload := encoded ++ checked.packet.ip.padding }
  let _ ← Check.Wire.checkBytes bytes
  return Import.EAPOL.bytesToHex bytes

private def baseTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.parse json.compress)
  let report ← unwrap input.check
  ensure (report.compliant && report.findings.length == input.events.length &&
      report.findings.all (fun finding => finding.result.state.check))
    "The native byte-derived replay and every table prefix must agree and remain valid."
  let expiredReply ← findPacket report.findings fun packet =>
    packet.outcome.disposition == .ttlExpired && packet.outcome.attachment.direction == .reply
  let reply ← packetResult expiredReply
  ensure (reply.outcome.attachment.classification == .established && !reply.outcome.attachment.fresh &&
      reply.outcome.output.isNone && reply.outcome.afterSource.isNone &&
      reply.outcome.state.records.any (·.seenReply))
    "The native TTL-expired first reply must retain seen-reply without selected UDP egress."
  let mut before := input.initial
  let mut erases := 0
  for finding in report.findings do
    match finding.observation.event with
    | .packet config zone wire _ _ =>
      let result ← packetResult finding
      ensure (result.input.zone == zone && result.input.packet.header == wire.checked.header &&
          result.input.candidate.isSome == (before.model.lookup zone wire.checked.header).isNone)
        "Every candidate decision must use the current computed table and header decoded from the exact input bytes."
      if let some emission := result.outcome.output then
        ensure ((← unwrap (UDP.decodeIPv4 emission.bytes)) == emission.decoded &&
            emission.decoded.datagram.payload == wire.checked.packet.datagram.payload &&
            emission.decoded.ip.packet.ttl.toNat + 1 == wire.checked.packet.ip.packet.ttl.toNat)
          "Every actual egress must retain the input payload and decrement the decoded TTL exactly once."
      ensure (result.input.candidate == (packetInput before config zone wire).candidate)
        "A cached flow cannot acquire a replacement NAT candidate."
    | .erase zone wire _ =>
      erases := erases + 1
      let prior := before.model.lookup zone wire.checked.header
      ensure (finding.result.packet.isNone && (finding.result.state.model.lookup zone wire.checked.header).isNone)
        "Erasure must remove the selected byte-derived key without creating a packet result."
      if let some hit := prior then
        ensure ((finding.result.state.model.lookup hit.entry.originalZone hit.entry.original).isNone &&
            (finding.result.state.model.lookup hit.entry.replyZone hit.entry.reply).isNone)
          "Erasing through either direction must remove both tuple lookup keys."
        let replyKey := wire.checked.header == hit.entry.original
        let target := if replyKey then hit.entry.reply else hit.entry.original
        let targetZone := if replyKey then hit.entry.replyZone else hit.entry.originalZone
        let raw := Import.EAPOL.bytesToHex wire.bytes
        let opposite ← unwrap (rewire raw
          (fun ip => { ip with source := target.source, destination := target.destination })
          (fun datagram => { datagram with sourcePort := target.sourcePort, destinationPort := target.destinationPort }))
        let changed ← unwrap (changeEvent json finding.observation.index fun event =>
          event.setObjVal! "raw" (.str opposite) |>.setObjVal! "zone" (Lean.toJson targetZone))
        let oppositeInput ← unwrap (Input.fromJson changed)
        let oppositeReport ← unwrap oppositeInput.check
        ensure (oppositeReport.compliant && oppositeReport.final == report.final)
          "A SYNTHETIC erase through the opposite decoded direction must remove the same flow and retain later behavior."
    before := finding.result.state
  ensure (0 < erases) "The retained replay must exercise administrative erasure."
  let relabeled : Input := { input with events := input.events.map fun observation => { observation with index := 0 } }
  let relabeledReport ← unwrap relabeled.check
  ensure (relabeledReport.compliant && relabeledReport.final == report.final)
    "Source labels cannot replace list order or alter wire-derived execution."

private def mismatchTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← findPacket report.findings fun packet => packet.outcome.output.isSome
  let events ← unwrap (values json "events")
  let source ← unwrap (observed events[first.observation.index]!)
  let raw ← unwrap ((← unwrap (source.getObjVal? "output")).getStr?)
  let changes : List (IPv4.Packet → IPv4.Packet) := [
    fun ip => { ip with tos := ip.tos + 1 },
    fun ip => { ip with identification := ip.identification + 1 },
    fun ip => { ip with dontFragment := !ip.dontFragment },
    fun ip => { ip with ttl := ip.ttl - 1 },
    fun ip => { ip with source := ip.source + 1 }]
  let altered ← changes.mapM fun change => unwrap (rewire raw change id)
  let payloadChanged ← unwrap (rewire raw id fun datagram => { datagram with payload := datagram.payload ++ [255] })
  let portChanged ← unwrap (rewire raw id fun datagram => { datagram with destinationPort := datagram.destinationPort + 1 })
  for raw in altered ++ [payloadChanged, portChanged] do
    let wrong := source.setObjVal! "output" (.str raw)
    let changed ← unwrap (changeEvent json first.observation.index (·.setObjVal! "observed" wrong))
    let actual ← unwrap (Input.fromJson changed)
    let actualReport ← unwrap actual.check
    ensure (!actualReport.compliant && !(← atIndex actualReport.findings first.observation.index).passed &&
        (actualReport.findings.drop (first.observation.index + 1)).all (·.passed) && actualReport.final == report.final)
      "A checksum-valid output mutation must be an observation mismatch and must not overwrite later modeled state."
  let missing ← unwrap (changeEvent json first.observation.index
    (·.setObjVal! "observed" (uncheckedMetadata source |>.setObjVal! "output" .null)))
  let missingInput ← unwrap (Input.fromJson missing)
  ensure (!(← unwrap missingInput.check).compliant)
    "Null intermediate metadata cannot hide a missing selected output."
  let unchecked ← unwrap (changeEvent json first.observation.index
    (·.setObjVal! "observed" (uncheckedMetadata source)))
  let uncheckedInput ← unwrap (Input.fromJson unchecked)
  ensure ((← unwrap uncheckedInput.check).compliant)
    "Null intermediate metadata is explicitly unobserved while checked output and table evidence still match."
  let expiredReply ← findPacket report.findings fun packet =>
    packet.outcome.disposition == .ttlExpired && packet.outcome.attachment.direction == .reply
  let oldState ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/wire-nat/native/before-ttl-one-reply-conntrack.json"))
  let wrongState ← unwrap (changeEvent json expiredReply.observation.index (fun event =>
    event.setObjVal! "state" oldState))
  let changedInput ← unwrap (Input.fromJson wrongState)
  let changedReport ← unwrap changedInput.check
  ensure (!changedReport.compliant && !(← atIndex changedReport.findings expiredReply.observation.index).passed &&
      (changedReport.findings.drop (expiredReply.observation.index + 1)).all (·.passed) && changedReport.final == report.final)
    "An observed unreplied row after the TTL-expired reply must mismatch without undoing the computed seen-reply update."
  let empty ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/wire-nat/native/erased-conntrack.json"))
  let wrongState ← unwrap (changeEvent json first.observation.index fun event =>
    event.setObjVal! "state" empty |>.setObjVal! "observed" (uncheckedMetadata source))
  let changedInput ← unwrap (Input.fromJson wrongState)
  ensure (!(← unwrap changedInput.check).compliant)
    "Null packet metadata cannot disable an explicitly observed wrong conntrack table."

private def parserTests (json : Lean.Json) : IO Unit := do
  let events ← unwrap (values json "events")
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← findPacket report.findings fun _ => true
  let forwarded ← findPacket report.findings fun packet => packet.outcome.output.isSome
  let event := events[first.observation.index]!
  reject (Input.fromJson (json.setObjVal! "schema" (Lean.toJson (2 : Nat)))) "Reject unsupported replay schemas."
  reject (Input.fromJson (json.setObjVal! "header" (.str "override"))) "Reject root header overrides."
  reject (Input.parse "{\"schema\":1,\"schema\":1}") "Reject duplicate JSON fields."
  reject (Input.fromJson (json.setObjVal! "events" (.arr #[]))) "Require at least one packet event."
  reject (Input.fromJson (← unwrap (changeEvent json first.observation.index (·.setObjVal! "packet" (Lean.toJson (0 : Nat))))))
    "The packet header must come from bytes rather than an extra JSON field."
  reject (Input.fromJson (← unwrap (changeEvent json first.observation.index (·.setObjVal! "candidate" .null))))
    "NAT candidates are derived from the current state and selected configuration."
  reject (Input.fromJson (← unwrap (changeEvent json first.observation.index
    (·.setObjVal! "observed" (Lean.Json.mkObj []))))) "Require the full observation shape."
  for zone in [Lean.toJson (65536 : Nat), Lean.toJson (-1 : Int)] do
    reject (Input.fromJson (← unwrap (changeEvent json first.observation.index (·.setObjVal! "zone" zone))))
      "Reject invalid conntrack zone bounds."
  reject (Input.fromJson (← unwrap (changeEvent json first.observation.index (·.setObjVal! "config" (.str "MISSING")))))
    "Reject unknown configuration IDs."
  let configs ← unwrap (values json "configs")
  reject (Input.fromJson (json.setObjVal! "configs" (.arr (configs.push configs[0]!)))) "Reject duplicate configuration IDs."
  reject (Input.fromJson (json.setObjVal! "configs" (.arr (configs.set! 0 (configs[0]!.setObjVal! "id" (.str ""))))))
    "Reject empty configuration IDs."
  reject (Input.fromJson (← unwrap (changeEvent json first.observation.index (·.setObjVal! "type" (.str "flush")))))
    "Reject unsupported state operations."
  let missingState ← unwrap (without event "state")
  reject (Input.fromJson (← unwrap (changeEvent json first.observation.index (fun _ => missingState))))
    "Each event must explicitly declare whether state was observed."
  let raw ← unwrap ((← unwrap (event.getObjVal? "raw")).getStr?)
  let bytes ← unwrap (Import.EAPOL.bytesFromHex raw)
  let corrupt := Import.EAPOL.bytesToHex (bytes.set 24 (bytes[24]! + 1))
  reject (Input.fromJson (← unwrap (changeEvent json first.observation.index (·.setObjVal! "raw" (.str corrupt)))))
    "A corrupted input checksum must be an input error before replay."
  let forwardEvent := events[forwarded.observation.index]!
  let observation ← unwrap (observed forwardEvent)
  let outputRaw ← unwrap ((← unwrap (observation.getObjVal? "output")).getStr?)
  let outputBytes ← unwrap (Import.EAPOL.bytesFromHex outputRaw)
  let corruptOutput := Import.EAPOL.bytesToHex (outputBytes.set 24 (outputBytes[24]! + 1))
  reject (Input.fromJson (← unwrap (changeEvent json forwarded.observation.index (·.setObjVal! "observed"
    (observation.setObjVal! "output" (.str corruptOutput))))))
    "A corrupted observed output checksum must be an input error rather than a semantic mismatch."
  let forwardResult ← packetResult forwarded
  reject (Input.fromJson (← unwrap (changeEvent json forwarded.observation.index (·.setObjVal! "observed"
    (observation.setObjVal! "output" (Import.PacketFields.headerJson forwardResult.input.packet.header))))))
    "An output header JSON object cannot replace checked output bytes."

private def dualZeroTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let finding ← findPacket report.findings fun packet => packet.outcome.output.isSome
  let result ← packetResult finding
  let some emission := result.outcome.output | throw (IO.userError "Expected a wire emission.")
  let identification := IPv4.computedChecksum { emission.decoded.ip.packet with identification := 0 }
  let events ← unwrap (values json "events")
  let event := events[finding.observation.index]!
  let observed ← unwrap (observed event)
  let incoming ← unwrap ((← unwrap (event.getObjVal? "raw")).getStr?)
  let outgoing ← unwrap ((← unwrap (observed.getObjVal? "output")).getStr?)
  let incoming ← unwrap (rewire incoming (fun ip => { ip with identification }) id)
  let outgoing ← unwrap (rewire outgoing (fun ip => { ip with identification }) id)
  let bytes ← unwrap (Import.EAPOL.bytesFromHex outgoing)
  let checked ← unwrap (Check.Wire.checkBytes bytes)
  ensure (checked.packet.ip.checksum == 0) "The synthetic IPv4 dual-zero fixture must compute checksum zero."
  for checksum in ([0, 65535] : List InternetChecksum.Word) do
    let bytes := (bytes.set 24 (InternetChecksum.highByte checksum)).set 25 (InternetChecksum.lowByte checksum)
    let _ ← unwrap (Check.Wire.checkBytes bytes)
    let changed ← unwrap (changeEvent json finding.observation.index fun event =>
      event.setObjVal! "raw" (.str incoming) |>.setObjVal! "observed"
        (observed.setObjVal! "output" (.str (Import.EAPOL.bytesToHex bytes))))
    let actual ← unwrap (Input.fromJson changed)
    ensure ((← unwrap actual.check).compliant)
      "SYNTHETIC valid IPv4 zero checksum representations must compare by packet fields without bypassing byte validation."

def run : IO Unit := do
  let json ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/wire-nat/replay.json"))
  baseTests json
  mismatchTests json
  dualZeroTests json
  parserTests json
  IO.println "Wire forwarding replay checker tests passed."

end NetlibTest.WireForwardingCheck
