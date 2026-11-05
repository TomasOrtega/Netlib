import Netlib.Check.RelatedICMP

namespace NetlibTest.RelatedICMPCheck

open Netlib Packet Protocol Check.RelatedICMP

example (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.compliant_iff

example (report : Report environment initial observations) (valid : initial.Valid) :
    report.final.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.Valid := report.valid valid

example (report : Report environment initial observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) (config : Config) (zone : Nat)
    (packet : ErrorPacket) (observed : ErrorObservation) (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .icmp config zone packet observed state)
    (output : ErrorFamily) (seen : observed.forwarded = some output) :
    ∃ (before : Tracker) (outcome : RelatedICMP.Outcome before (packet.input zone))
      (emission : RelatedICMP.Emission before (packet.input zone)),
      RelatedICMP.step (environment.related config) before (packet.input zone) = .ok outcome ∧
      outcome.output = some emission ∧ finding.result.state = before ∧ OutputFacts before (packet.input zone) output emission :=
  report.observed_output_facts compliant finding member config zone packet observed state event output seen

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def events (json : Lean.Json) : Except String (Array Lean.Json) :=
  json.getObjVal? "events" >>= Lean.Json.getArr?

private def changeEvent (json : Lean.Json) (index : Nat) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let values ← events json
  return json.setObjVal! "events" (.arr (values.set! index (change values[index]!)))

private def changeForwarded (json : Lean.Json) (index : Nat) (output : Lean.Json) : Except String Lean.Json :=
  changeEvent json index fun event => event.setObjVal! "observed"
    (((event.getObjVal? "observed").toOption.get!).setObjVal! "forwarded" output)

private def atIndex (findings : List Finding) (index : Nat) : IO Finding :=
  match findings[index]? with
  | some finding => pure finding
  | none => throw (IO.userError s!"Missing related replay event {index}.")

private def firstForwarded (findings : List Finding) : IO Finding :=
  match findings.find? (fun finding => (finding.result.icmp.map fun packet => packet.outcome.output.isSome).getD false) with
  | some finding => pure finding
  | none => throw (IO.userError "The native replay needs a forwarded received ICMP error.")

private def encodeSource (packet : ErrorPacket) (ipChange : IPv4.Packet → IPv4.Packet)
    (quoteChange : IPv4QuotePrefix.Decoded → IPv4QuotePrefix.Decoded) : Except String Lean.Json := do
  let source := packet.checked.source
  let quote := quoteChange source.quote
  let payload := ICMP.encode ⟨source.icmp.message.kind, IPv4QuotePrefix.bytes quote⟩
  let outer := { ipChange source.ip.packet with payload }
  let encoded ← IPv4.encode outer
  return Lean.toJson (Import.EAPOL.bytesToHex (Import.EthernetIPv4.encode { packet.checked.envelope with payload := encoded }))

private def changeSource (json : Lean.Json) (finding : Finding) (ipChange : IPv4.Packet → IPv4.Packet)
    (quoteChange : IPv4QuotePrefix.Decoded → IPv4QuotePrefix.Decoded) : Except String Lean.Json := do
  let .icmp _ _ packet _ _ := finding.observation.event | throw "Expected received ICMP input."
  let raw ← encodeSource packet ipChange quoteChange
  changeEvent json finding.observation.index (·.setObjVal! "raw" raw)

private def modeledOutput (json : Lean.Json) (index : Nat) : IO (Lean.Json × Finding) := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let finding ← atIndex report.findings index
  let .icmp _ _ packet _ _ := finding.observation.event | throw (IO.userError "Expected received ICMP input.")
  let some computed := finding.result.icmp | throw (IO.userError "Expected modeled ICMP result.")
  let output := (computed.outcome.output.map fun emission => Lean.toJson (emission.family.bytes.map fun payload =>
    Import.EAPOL.bytesToHex (Import.EthernetIPv4.encode { packet.checked.envelope with payload }))).getD (.arr #[])
  return (← unwrap (changeForwarded json index output), finding)

private def rewireFamily (raw : Lean.Json) (mtu : IPv4Fragmentation.MTU)
    (ipChange : IPv4.Packet → IPv4.Packet) (quoteChange : IPv4QuotePrefix.Decoded → IPv4QuotePrefix.Decoded)
    (kindChange : ICMP.Kind → ICMP.Kind := id) : Except String Lean.Json := do
  let bytes ← (← raw.getArr?).toList.mapM fun value => do Import.EAPOL.bytesFromHex (← value.getStr?)
  let family ← checkErrorFamily bytes
  let some first := family.fragments.head? | throw "Expected a nonempty ICMP fragment family."
  let quote := quoteChange family.quote
  let payload := ICMP.encode ⟨kindChange family.icmp.message.kind, IPv4QuotePrefix.bytes quote⟩
  let packet := { ipChange family.packet with payload }
  if bounded : packet.Encodable then
    if allowed : IPv4Fragmentation.Allowed packet mtu then
      let fragments := IPv4Fragmentation.fragment packet mtu bounded allowed
      return Lean.toJson (fragments.bytes.map fun payload =>
        Import.EAPOL.bytesToHex (Import.EthernetIPv4.encode { first.checked.envelope with payload }))
    else throw "The synthetic ICMP packet must permit the selected MTU."
  else throw "The synthetic ICMP packet must fit IPv4."

private def parsedFamily (raw : Lean.Json) : Except String ErrorFamily := do
  checkErrorFamily (← (← raw.getArr?).toList.mapM fun value => do Import.EAPOL.bytesFromHex (← value.getStr?))

private def baseTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  ensure (report.compliant && report.findings.length == 16 && report.findings.all (·.result.state.check))
    "All sixteen native event prefixes must match and retain a valid confirmed table."
  ensure ((report.findings.filter (·.result.udp.isSome)).length == 8 &&
      (report.findings.filter (·.result.icmp.isSome)).length == 7)
    "The ordered mixed replay must include eight UDP packets, seven received ICMP errors and one erase."
  let mut before := input.initial
  for finding in report.findings do
    match finding.observation.event with
    | .icmp _ _ _ _ _ =>
      ensure (finding.result.state == before)
        "RELATED ICMP must never refresh, confirm, mark a reply, create or erase a confirmed record."
    | .udp config zone packet _ _ =>
      let some computed := finding.result.udp | throw (IO.userError "Missing UDP outcome.")
      ensure (computed.input.candidate == (Check.MTUForwarding.packetInput before config zone packet).candidate)
        "UDP candidate allocation must use the computed current table."
    | .erase zone packet _ =>
      ensure ((finding.result.state.model.lookup zone packet.checked.header).isNone)
        "The administrative erase must affect subsequent related lookup."
    before := finding.result.state
  ensure (report.findings.any fun finding => (finding.result.icmp.map fun packet =>
      packet.outcome.disposition == .unrelated && packet.outcome.output.isNone).getD false)
    "An unassociated native error must drop without becoming a new UDP candidate."

private def sourceTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← firstForwarded report.findings
  let index := first.observation.index
  let corrupt : IPv4QuotePrefix.Decoded → IPv4QuotePrefix.Decoded := fun quote =>
    { quote with checksum := ⟨(quote.checksum.val + 1) % 65536, Nat.mod_lt _ (by decide)⟩ }
  let badUDP : IPv4QuotePrefix.Decoded → IPv4QuotePrefix.Decoded := fun quote =>
    { quote with packet := { quote.packet with payload := quote.packet.payload.set 6 (quote.packet.payload[6]! + 1) } }
  let badLength : IPv4QuotePrefix.Decoded → IPv4QuotePrefix.Decoded := fun quote =>
    { quote with declaredLength := 0, packet := { quote.packet with payload := (quote.packet.payload.set 4 0).set 5 0 } }
  let mf : IPv4QuotePrefix.Decoded → IPv4QuotePrefix.Decoded := fun quote =>
    { quote with flags := ⟨quote.flags.val % 8192 + 24576, by have h := Nat.mod_lt quote.flags.val (by decide : 0 < 8192); omega⟩ }
  for change in [corrupt, badUDP, badLength, mf] do
    let changed ← unwrap (changeSource json first id change)
    let (expected, finding) ← modeledOutput changed index
    let some packet := finding.result.icmp | throw (IO.userError "Missing ICMP result.")
    ensure (packet.outcome.disposition == .forwarded && packet.outcome.association.isSome)
      "Bad quoted checksums, lengths and initial MF flags must remain acceptable association data."
    let selected ← unwrap (Input.fromJson expected)
    ensure ((← unwrap selected.check).compliant)
      "A valid outer/ICMP wrapper must preserve the modeled untrusted quotation."
  for change in [fun quote : IPv4QuotePrefix.Decoded => { quote with flags := 1 }] do
    let changed ← unwrap (changeSource json first id change)
    let (expected, finding) ← modeledOutput changed index
    let some packet := finding.result.icmp | throw (IO.userError "Missing ICMP result.")
    ensure (packet.outcome.disposition == .unrelated && packet.outcome.output.isNone)
      "A noninitial quote fragment must not associate through apparent UDP port bytes."
    let selected ← unwrap (Input.fromJson expected)
    ensure ((← unwrap selected.check).compliant) "An unsupported quote must preserve later computed behavior."
  let changed ← unwrap (changeSource json first (fun ip => { ip with destination := ip.destination + 1 }) id)
  let (expected, finding) ← modeledOutput changed index
  let some computed := finding.result.icmp | throw (IO.userError "Missing ICMP result.")
  ensure (computed.outcome.disposition == .unrelated && computed.outcome.output.isNone)
    "The outer destination guard must reject an otherwise matching quote."
  let selected ← unwrap (Input.fromJson expected)
  ensure ((← unwrap selected.check).compliant) "An outer destination miss must leave state unchanged."
  let forged ← unwrap (changeSource json first (fun ip => { ip with source := ip.source + 1 }) id)
  let (expected, finding) ← modeledOutput forged index
  let some computed := finding.result.icmp | throw (IO.userError "Missing ICMP result.")
  ensure (computed.outcome.association.isSome)
    "The outer source must not be treated as authenticated association evidence."
  let selected ← unwrap (Input.fromJson expected)
  ensure ((← unwrap selected.check).compliant) "A forged outer source still follows the selected NAT stages."
  let changed ← unwrap (changeEvent json index (·.setObjVal! "zone" (Lean.toJson (65535 : Nat))))
  let (expected, finding) ← modeledOutput changed index
  let some computed := finding.result.icmp | throw (IO.userError "Missing ICMP result.")
  ensure (computed.outcome.disposition == .unrelated)
    "A matching quotation in a different conntrack zone must miss."
  let selected ← unwrap (Input.fromJson expected)
  ensure ((← unwrap selected.check).compliant) "Zone misses must leave subsequent events unaffected."
  let changed ← unwrap (changeSource json first (fun ip => { ip with ttl := 1 }) id)
  let (expected, finding) ← modeledOutput changed index
  let some computed := finding.result.icmp | throw (IO.userError "Missing ICMP result.")
  ensure (computed.outcome.disposition == .ttlExpired && computed.outcome.output.isNone)
    "Expired received ICMP errors must not generate another control error."
  let selected ← unwrap (Input.fromJson expected)
  ensure ((← unwrap selected.check).compliant) "TTL expiry must leave subsequent events unaffected."

private def outputTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← firstForwarded report.findings
  let index := first.observation.index
  let some computed := first.result.icmp | throw (IO.userError "Missing ICMP result.")
  let some emitted := computed.outcome.output | throw (IO.userError "Missing ICMP emission.")
  let values ← unwrap (events json)
  let raw ← unwrap ((← unwrap (values[index]!.getObjVal? "observed")).getObjVal? "forwarded")
  let changes : List (IPv4.Packet → IPv4.Packet) := [
    fun ip => { ip with ttl := ip.ttl - 1 }, fun ip => { ip with source := ip.source + 1 },
    fun ip => { ip with destination := ip.destination + 1 }, fun ip => { ip with tos := ip.tos + 1 }]
  let altered ← changes.mapM fun change => unwrap (rewireFamily raw emitted.mtu change id)
  let quoted ← unwrap (rewireFamily raw emitted.mtu id fun quote =>
    { quote with packet := { quote.packet with payload := quote.packet.payload.set 7 (quote.packet.payload[7]! + 1) } })
  let residue ← unwrap (rewireFamily raw emitted.mtu id fun quote =>
    { quote with checksum := ⟨(quote.checksum.val + 1) % 65536, Nat.mod_lt _ (by decide)⟩ })
  let declared ← unwrap (rewireFamily raw emitted.mtu id fun quote => { quote with declaredLength := 0 })
  let flags ← unwrap (rewireFamily raw emitted.mtu id fun quote => { quote with flags := 8192 })
  let kind ← unwrap (rewireFamily raw emitted.mtu id id (fun _ => .timeExceeded))
  for output in altered ++ [quoted, residue, declared, flags, kind, .arr #[]] do
    let changed ← unwrap (changeForwarded json index output)
    let selected ← unwrap (Input.fromJson changed)
    let actual ← unwrap selected.check
    ensure (!actual.compliant && !(← atIndex actual.findings index).passed &&
        (actual.findings.drop (index + 1)).all (·.passed) && actual.final == report.final)
      "A well-formed but incorrect ICMP family must mismatch without replacing state or later behavior."
  let fragments ← unwrap raw.getArr?
  let changed ← unwrap (changeForwarded json index (.arr fragments.reverse))
  let selected ← unwrap (Input.fromJson changed)
  ensure ((← unwrap selected.check).compliant) "Output family comparison must ignore capture order."
  let .icmp _ _ source _ _ := first.observation.event | throw (IO.userError "Expected ICMP source.")
  let rawSource := Lean.toJson (Import.EAPOL.bytesToHex (Import.EthernetIPv4.encode
    { source.checked.envelope with source := ⟨1, 2, 3, 4, 5, 6⟩, payload := source.checked.envelope.payload ++ [0, 0] }))
  let changed ← unwrap (changeEvent json index (·.setObjVal! "raw" rawSource))
  let selected ← unwrap (Input.fromJson changed)
  ensure ((← unwrap selected.check).compliant) "Source Ethernet adjacency and trailing padding must not affect protocol comparison."

private def parserTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← firstForwarded report.findings
  let index := first.observation.index
  let .icmp _ _ source _ _ := first.observation.event | throw (IO.userError "Expected ICMP source.")
  for position in [24, 36] do
    let bytes := source.bytes.set position (source.bytes[position]! + 1)
    let changed ← unwrap (changeEvent json index (·.setObjVal! "raw" (Lean.toJson (Import.EAPOL.bytesToHex bytes))))
    reject (Input.fromJson changed) "Invalid outer IPv4 or ICMP checksums must be rejected before replay."
  let values ← unwrap (events json)
  let observed ← unwrap (values[index]!.getObjVal? "observed")
  let raw ← unwrap (observed.getObjVal? "forwarded")
  let fragments ← unwrap raw.getArr?
  for output in [.arr (fragments.push fragments[0]!), .null, .arr #[.str "0"]] do
    reject (Input.fromJson (← unwrap (changeForwarded json index output)))
      "Malformed, duplicate and unsupported output families must be rejected before replay."
  reject (Input.fromJson (← unwrap (changeEvent json index (·.setObjVal! "type" (Lean.toJson "udp")))))
    "The declared UDP event type must agree with checked packet bytes."
  reject (Input.fromJson (← unwrap (changeEvent json 0 (·.setObjVal! "type" (Lean.toJson "icmp")))))
    "The declared ICMP event type must agree with checked packet bytes."
  reject (Input.fromJson (← unwrap (changeEvent json index (·.setObjVal! "zone" (Lean.toJson (65536 : Nat))))))
    "Conntrack zones must fit sixteen bits."
  reject (Input.fromJson (← unwrap (changeEvent json index (·.setObjVal! "observed"
    (observed.setObjVal! "icmpOutput" (.arr #[.str "00"]))))))
    "This received-error capture scope must explicitly exclude locally generated output."
  reject (Input.fromJson (json.setObjVal! "schema" (Lean.toJson (2 : Nat)))) "Unsupported replay schemas must fail."
  reject (Input.fromJson (json.setObjVal! "events" (.arr #[]))) "A mixed replay requires a packet event."
  reject (Input.fromJson (json.setObjVal! "header" .null)) "Root header overrides must be rejected."
  reject (Input.parse "{\"schema\":1,\"schema\":1}") "Duplicate JSON fields must be rejected."

private def checksumTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← firstForwarded report.findings
  let some computed := first.result.icmp | throw (IO.userError "Missing ICMP result.")
  let some emitted := computed.outcome.output | throw (IO.userError "Missing ICMP emission.")
  let values ← unwrap (events json)
  let raw ← unwrap ((← unwrap (values[first.observation.index]!.getObjVal? "observed")).getObjVal? "forwarded")
  let zero ← unwrap (parsedFamily (← unwrap (rewireFamily raw emitted.mtu id fun quote => { quote with checksum := 0 })))
  let negativeZero ← unwrap (parsedFamily (← unwrap (rewireFamily raw emitted.mtu id fun quote => { quote with checksum := 65535 })))
  ensure (decide (zero.value = negativeZero.value))
    "The two one's-complement zero representations must compare equally."
  let firstBad ← unwrap (parsedFamily (← unwrap (rewireFamily raw emitted.mtu id fun quote =>
    { quote with checksum := ⟨(quote.checksum.val + 1) % 65535, by
      have h := Nat.mod_lt (quote.checksum.val + 1) (by decide : 0 < 65535); omega⟩ })))
  let secondBad ← unwrap (parsedFamily (← unwrap (rewireFamily raw emitted.mtu id fun quote =>
    { quote with checksum := ⟨(quote.checksum.val + 2) % 65535, by
      have h := Nat.mod_lt (quote.checksum.val + 2) (by decide : 0 < 65535); omega⟩ })))
  ensure (!InternetChecksum.valid (IPv4QuotePrefix.headerBytes firstBad.quote) &&
      !InternetChecksum.valid (IPv4QuotePrefix.headerBytes secondBad.quote) && decide (firstBad.value ≠ secondBad.value))
    "Distinct invalid inner IPv4 checksums must retain their residue in output comparison."

private def fragmentationTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← firstForwarded report.findings
  let values ← unwrap (events json)
  let selected := values[first.observation.index]!
  let initial ← unwrap (selected.getObjVal? "state")
  ensure (initial != .null) "The native forwarded ICMP boundary must include its frozen table observation."
  let mtus ← unwrap ((← unwrap (json.getObjVal? "mtus")).getArr?)
  let smaller := (json.setObjVal! "initial" initial).setObjVal! "mtus"
    (.arr (mtus.map (·.setObjVal! "mtu" (Lean.toJson (68 : Nat)))))
  let single := smaller.setObjVal! "events" (.arr #[selected])
  let (expected, finding) ← modeledOutput single 0
  let some computed := finding.result.icmp | throw (IO.userError "Missing ICMP result.")
  let some emitted := computed.outcome.output | throw (IO.userError "Missing ICMP emission.")
  ensure (1 < emitted.family.fragments.length && emitted.family.fragments.all (fun fragment => fragment.packet.wireLength ≤ 68))
    "An ICMP-only replay must fragment the complete translated error at the minimum IPv4 MTU."
  let reassembled ← unwrap (IPv4Fragmentation.reassemble emitted.family.fragments.reverse)
  ensure (reassembled == emitted.association.packet)
    "Reordered fragments must reassemble to the emitted ICMP packet without checking the inner UDP datagram."
  let selectedInput ← unwrap (Input.fromJson expected)
  ensure ((← unwrap selectedInput.check).compliant)
    "An ICMP-only trace must use the supplied initial table without a fake UDP attachment."
  let values ← unwrap (events expected)
  let raw ← unwrap ((← unwrap (values[0]!.getObjVal? "observed")).getObjVal? "forwarded")
  let parts ← unwrap raw.getArr?
  let reverseInput ← unwrap (Input.fromJson (← unwrap (changeForwarded expected 0 (.arr parts.reverse))))
  ensure ((← unwrap reverseInput.check).compliant)
    "Generic ICMP family comparison must accept a permutation of a real multi-fragment family."
  reject (Input.fromJson (← unwrap (changeForwarded expected 0 (.arr (parts.extract 1 parts.size)))))
    "An incomplete ICMP fragment family must be rejected."

private def stateTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let some first := report.findings.find? (fun finding =>
      finding.observation.event.stateObservation.isSome && !finding.result.state.records.isEmpty) |
    throw (IO.userError "Expected an observed nonempty native table.")
  let index := first.observation.index
  let values ← unwrap (events json)
  let state ← unwrap (values[index]!.getObjVal? "state")
  let changed ← unwrap (changeEvent json index (·.setObjVal! "state" (state.setObjVal! "entries" (.arr #[]))))
  let selected ← unwrap (Input.fromJson changed)
  let actual ← unwrap selected.check
  ensure (!actual.compliant && !(← atIndex actual.findings index).passed &&
      (actual.findings.drop (index + 1)).all (·.passed) && actual.final == report.final)
    "A wrong observed table must mismatch without becoming the computed state for subsequent events."

def run : IO Unit := do
  let json ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/received-icmp/replay.json"))
  baseTests json
  sourceTests json
  outputTests json
  parserTests json
  checksumTests json
  fragmentationTests json
  stateTests json

end NetlibTest.RelatedICMPCheck
