import Netlib.Check.MTUForwarding

namespace NetlibTest.MTUForwardingCheck

open Netlib Packet Protocol Check.MTUForwarding

example (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.compliant_iff

example (report : Report environment initial observations) (valid : initial.Valid) :
    report.final.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.Valid := report.trace.valid valid

example (report : Report environment initial observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) (config : Config) (zone : Nat) (packet : WirePacket)
    (observed : PacketObservation) (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .packet config zone packet observed state)
    (output : Check.IPv4Fragments.Family) (seen : observed.output = some output) :
    output.datagram.payload = packet.checked.packet.datagram.payload ∧
      output.packet.ttl.toNat = packet.checked.packet.ip.packet.ttl.toNat - 1 :=
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
  | none => throw (IO.userError s!"Expected MTU replay element {index}.")

private def changeEvent (json : Lean.Json) (index : Nat) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let events ← values json "events"
  return json.setObjVal! "events" (.arr (events.set! index (change events[index]!)))

private def changeOutput (json : Lean.Json) (index : Nat) (output : Lean.Json) : Except String Lean.Json :=
  changeEvent json index fun event =>
    event.setObjVal! "observed" ((event.getObjVal? "observed").toOption.get! |>.setObjVal! "output" output)

private def firstFragmented (report : Report environment initial observations) : IO Finding :=
  match report.findings.find? (fun finding =>
      (finding.result.packet.map (fun packet =>
        (packet.outcome.output.map (fun emission => decide (1 < emission.bytes.length))).getD false)).getD false) with
  | some finding => pure finding
  | none => throw (IO.userError "Expected a fragmented native output family.")

private def familyBytes (json : Lean.Json) : Except String (List (List UInt8)) := do
  (← json.getArr?).toList.mapM fun value => do Import.EAPOL.bytesFromHex (← value.getStr?)

private def rewireFamily (raw : Lean.Json) (ipChange : IPv4.Packet → IPv4.Packet)
    (udpChange : UDP.Datagram → UDP.Datagram) : Except String Lean.Json := do
  let bytes ← familyBytes raw
  let family ← Check.IPv4Fragments.checkFamily bytes
  let some first := family.fragments.head? | throw "Expected a nonempty family."
  let ip := ipChange family.packet
  let selected := udpChange family.datagram
  let datagram := if family.datagram.checksum = 0 then { selected with checksum := 0 }
    else UDP.computed ip.source ip.destination selected.sourcePort selected.destinationPort selected.payload
  let transport ← UDP.encode ip.source ip.destination datagram
  let packet := { ip with payload := transport }
  if bounded : packet.Encodable then
    if allowed : packet.dontFragment = true → packet.wireLength ≤ 600 then
      let fragments := IPv4Fragmentation.fragment packet ⟨600, by decide⟩ bounded allowed
      return Lean.toJson (fragments.bytes.map fun payload =>
        Import.EAPOL.bytesToHex (Import.EthernetIPv4.encode { first.checked.envelope with payload }))
    else throw "The synthetic family must permit fragmentation."
  else throw "The synthetic family must fit IPv4."

private def baseTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  ensure (report.compliant && report.findings.length == 13 && report.findings.all (·.result.state.check))
    "The native MTU replay must agree and retain valid state at all thirteen event prefixes."
  let first ← firstFragmented report
  let some packet := first.result.packet | throw (IO.userError "Expected a packet result.")
  let some emission := packet.outcome.output | throw (IO.userError "Expected output fragments.")
  ensure (emission.fragments.fragments.map (·.packet.wireLength) == [596, 596, 76] &&
      emission.transit.decoded.datagram.payload.length == 1200 &&
      (← unwrap (IPv4Fragmentation.reassemble emission.fragments.fragments)) == emission.transit.decoded.ip.packet)
    "The native large request must split into the expected aligned family and recover all 1200 application bytes."
  let mut before := input.initial
  for finding in report.findings do
    match finding.observation.event with
    | .packet config zone wire _ _ =>
      let some result := finding.result.packet | throw (IO.userError "Expected a modeled packet result.")
      ensure (result.input.candidate == (packetInput before config zone wire).candidate)
        "Fresh candidate selection must use the current computed table and byte-derived key."
      if let some output := result.outcome.output then
        for part in output.fragments.fragments do
          ensure (part.packet.wireLength ≤ output.mtu.val)
            "Every actual output fragment must fit the selected effective MTU."
    | .erase zone wire _ =>
      ensure ((finding.result.state.model.lookup zone wire.checked.header).isNone)
        "The administrative erase must remove the selected decoded key."
    before := finding.result.state
  let events ← unwrap (values json "events")
  let raw ← unwrap ((← unwrap (events[first.observation.index]!.getObjVal? "observed")).getObjVal? "output")
  let fragments ← unwrap raw.getArr?
  let reversed ← unwrap (changeOutput json first.observation.index (.arr fragments.reverse))
  let reverseInput ← unwrap (Input.fromJson reversed)
  ensure ((← unwrap reverseInput.check).compliant)
    "Reordered capture fragments must yield the same checked output family."

private def mismatchTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← firstFragmented report
  let events ← unwrap (values json "events")
  let observed ← unwrap (events[first.observation.index]!.getObjVal? "observed")
  let raw ← unwrap (observed.getObjVal? "output")
  let changes : List (IPv4.Packet → IPv4.Packet) := [
    fun ip => { ip with tos := ip.tos + 1 },
    fun ip => { ip with identification := ip.identification + 1 },
    fun ip => { ip with ttl := ip.ttl - 1 },
    fun ip => { ip with source := ip.source + 1 }]
  let altered ← changes.mapM fun change => unwrap (rewireFamily raw change id)
  let payload ← unwrap (rewireFamily raw id fun datagram => { datagram with payload := datagram.payload ++ [255] })
  let port ← unwrap (rewireFamily raw id fun datagram => { datagram with destinationPort := datagram.destinationPort + 1 })
  for output in altered ++ [payload, port, .arr #[]] do
    let changed ← unwrap (changeOutput json first.observation.index output)
    let selected ← unwrap (Input.fromJson changed)
    let actual ← unwrap selected.check
    ensure (!actual.compliant && !(← atIndex actual.findings first.observation.index).passed &&
        (actual.findings.drop (first.observation.index + 1)).all (·.passed) && actual.final == report.final)
      "A SYNTHETIC valid but incorrect family must mismatch without replacing computed state or later behavior."
  let unchecked := ["classification", "fresh", "afterDestination", "afterSource", "nextHop", "disposition", "mtu"].foldl
    (fun value key => value.setObjVal! key .null) observed
  let changed ← unwrap (changeEvent json first.observation.index (·.setObjVal! "observed" unchecked))
  let selected ← unwrap (Input.fromJson changed)
  ensure ((← unwrap selected.check).compliant) "Null intermediate fields must preserve explicit family checks."
  let wrongMTU ← unwrap (changeEvent json first.observation.index
    (·.setObjVal! "observed" (observed.setObjVal! "mtu" (Lean.toJson (601 : Nat)))))
  let selected ← unwrap (Input.fromJson wrongMTU)
  ensure (!(← unwrap selected.check).compliant) "A wrong observed effective MTU must mismatch."

private def parserTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← firstFragmented report
  let events ← unwrap (values json "events")
  let observed ← unwrap (events[first.observation.index]!.getObjVal? "observed")
  let raw ← unwrap (observed.getObjVal? "output")
  let fragments ← unwrap raw.getArr?
  for output in [.arr (fragments.push fragments[0]!), .arr (fragments.extract 0 1 ++ fragments.extract 2 fragments.size), .null,
      .arr #[.str "0"]] do
    reject (Input.fromJson (← unwrap (changeOutput json first.observation.index output)))
      "Malformed, incomplete, and duplicate output families must be rejected before replay."
  let mtus ← unwrap (values json "mtus")
  for changed in [.arr #[], .arr (mtus.push mtus[0]!),
      .arr (mtus.set! 0 (mtus[0]!.setObjVal! "mtu" (Lean.toJson (67 : Nat)))),
      .arr (mtus.set! 0 (mtus[0]!.setObjVal! "mtu" (Lean.toJson (65536 : Nat)))),
      .arr (mtus.set! 0 (mtus[0]!.setObjVal! "nextHop" (.str "unbound")))] do
    reject (Input.fromJson (json.setObjVal! "mtus" changed))
      "MTUs must be complete, unique, bound, and within the validated IPv4 interval."
  reject (Input.fromJson (json.setObjVal! "schema" (Lean.toJson (2 : Nat)))) "Reject unsupported MTU replay schemas."
  reject (Input.fromJson (json.setObjVal! "header" .null)) "Reject root header overrides."
  reject (Input.parse "{\"schema\":1,\"schema\":1}") "Reject duplicate JSON fields."
  reject (Input.fromJson (json.setObjVal! "events" (.arr #[]))) "Require a packet event."
  reject (Input.fromJson (← unwrap (changeEvent json first.observation.index (·.setObjVal! "zone" (Lean.toJson (65536 : Nat))))))
    "Reject zones outside the conntrack key width."

def run : IO Unit := do
  let json ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/mtu/replay.json"))
  baseTests json
  mismatchTests json
  parserTests json

end NetlibTest.MTUForwardingCheck
