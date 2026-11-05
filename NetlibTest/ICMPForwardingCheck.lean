import Netlib.Check.ICMPForwarding

namespace NetlibTest.ICMPForwardingCheck

open Netlib Packet Protocol Check.ICMPForwarding

example (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.compliant_iff

example (report : Report environment initial observations) (valid : initial.Valid) :
    report.final.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.Valid := report.valid valid

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

private def changeEvent (json : Lean.Json) (index : Nat) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let events ← values json "events"
  return json.setObjVal! "events" (.arr (events.set! index (change events[index]!)))

private def changeOutput (json : Lean.Json) (index : Nat) (output : Lean.Json) : Except String Lean.Json :=
  changeEvent json index fun event => event.setObjVal! "observed"
    ((event.getObjVal? "observed").toOption.get! |>.setObjVal! "icmpOutput" output)

private def atIndex (items : List α) (index : Nat) : IO α :=
  match items[index]? with
  | some value => pure value
  | none => throw (IO.userError s!"Expected ICMP event {index}.")

private def firstError (report : Report environment initial observations) (onlyPartial : Bool := false) : IO Finding :=
  match report.findings.find? (fun finding =>
      (finding.observation.icmpOutput.map (fun frame => !onlyPartial || !frame.checked.complete)).getD false) with
  | some finding => pure finding
  | none => throw (IO.userError "Expected a checked native ICMP error.")

private def rewire (raw : String) (ipChange : IPv4.Packet → IPv4.Packet)
    (kindChange : ICMP.Kind → ICMP.Kind := id) (quoteChange : IPv4Quote.Decoded → IPv4Quote.Decoded := id) :
    Except String String := do
  let bytes ← Import.EAPOL.bytesFromHex raw
  let checked ← Check.ICMPError.checkBytes bytes
  let quote := ICMPNAT.recompute (quoteChange checked.quote)
  let message : ICMP.Message := ⟨kindChange checked.icmp.message.kind, IPv4Quote.bytes quote⟩
  let packet := { ipChange checked.ip.packet with payload := ICMP.encode message }
  let encoded ← IPv4.encode packet
  let wire := Import.EthernetIPv4.encode { checked.envelope with payload := encoded }
  let _ ← Check.ICMPError.checkBytes wire
  return Import.EAPOL.bytesToHex wire

private def rawOutput (json : Lean.Json) (index : Nat) : Except String String := do
  let events ← values json "events"
  let observed ← events[index]!.getObjVal? "observed"
  return ← (← values observed "icmpOutput")[0]!.getStr?

private def baseTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  ensure (report.compliant && report.findings.length == 21 && report.findings.all (·.result.state.check))
    "Every native ICMP replay event must agree and preserve ordinary-table validity."
  let errors := report.findings.filter (·.observation.icmpOutput.isSome)
  ensure (errors.length == 12 &&
      (errors.filter fun finding => (finding.observation.icmpOutput.map (·.checked.complete)).getD false).length == 5)
    "The capture must distinguish twelve errors and five complete quoted UDP datagrams."
  for finding in errors do
    let some packet := finding.result.packet | throw (IO.userError "Expected an error packet result.")
    let some emission := packet.outcome.control.output | throw (IO.userError "Expected a computed error emission.")
    let .some observed := finding.observation.icmpOutput | throw (IO.userError "Expected an observed error.")
    ensure (observed.checked.value == emissionValue emission &&
        emission.packet.wireLength ≤ emission.path.mtu.val && emission.packet.wireLength ≤ 576 &&
        emission.packet.ttl == input.environment.profile.outerTtl && !emission.packet.dontFragment &&
        emission.packet.tos == Protocol.ICMPForwarding.errorTos packet.input.transit.packet.ip.packet.tos)
      "Every observed error must match computed quotation, kind, NAT boundary, return MTU, and environment metadata."
  let original ← firstError report
  let raw ← unwrap (rawOutput json original.observation.base.index)
  let changed ← unwrap (rewire raw (fun ip => { ip with identification := ip.identification + 1 }))
  let selected ← unwrap (Input.fromJson (← unwrap (changeOutput json original.observation.base.index (Lean.toJson [changed]))))
  ensure ((← unwrap selected.check).compliant)
    "A SYNTHETIC identification change remains an explicit allocator choice, rather than a claimed allocator proof."

private def mismatchTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let first ← firstError report
  let index := first.observation.base.index
  let raw ← unwrap (rawOutput json index)
  let changes : List (IPv4.Packet → IPv4.Packet) := [
    fun ip => { ip with ttl := ip.ttl - 1 },
    fun ip => { ip with tos := ip.tos + 1 },
    fun ip => { ip with source := ip.source + 1 },
    fun ip => { ip with destination := ip.destination + 1 },
    fun ip => { ip with dontFragment := !ip.dontFragment }]
  let changed ← changes.mapM fun change => unwrap (rewire raw change)
  let kind ← unwrap (rewire raw id (fun _ => .fragmentationNeeded 600))
  let quote ← unwrap (rewire raw id id (fun quote => { quote with packet := { quote.packet with ttl := quote.packet.ttl + 1 } }))
  for output in (changed ++ [kind, quote]).map (fun raw => Lean.toJson [raw]) ++ [.arr #[]] do
    let selected ← unwrap (Input.fromJson (← unwrap (changeOutput json index output)))
    let actual ← unwrap selected.check
    ensure (!actual.compliant && !(← atIndex actual.findings index).passed &&
        (actual.findings.drop (index + 1)).all (·.passed) && actual.final == report.final)
      "A SYNTHETIC checksum-valid error mismatch must not replace computed state or affect later observations."
  let truncated ← firstError report true
  let index := truncated.observation.base.index
  let raw ← unwrap (rawOutput json index)
  let changed ← unwrap (rewire raw id id fun quote =>
    { quote with packet := { quote.packet with payload := quote.packet.payload.reverse.modifyHead (· + 1) |>.reverse } })
  let selected ← unwrap (Input.fromJson (← unwrap (changeOutput json index (Lean.toJson [changed]))))
  ensure (!(← unwrap selected.check).compliant)
    "A changed partial UDP quotation cannot hide behind the absence of full transport checksum validation."
  let events ← unwrap (values json "events")
  let wrongState ← unwrap (changeEvent json 3 (·.setObjVal! "state" (events[0]!.getObjVal? "state").toOption.get!))
  let selected ← unwrap (Input.fromJson wrongState)
  let actual ← unwrap selected.check
  ensure (!actual.compliant && actual.final == report.final && (actual.findings.drop 4).all (·.passed))
    "A wrong native table after a related error must mismatch without undoing the computed reply update."
  let unexpected ← unwrap (Input.fromJson (← unwrap (changeOutput json 2 (Lean.toJson [raw]))))
  ensure (!(← unwrap unexpected.check).compliant) "An observed error cannot force generation on a successful transit event."

private def parserTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let first ← firstError (← unwrap input.check)
  let index := first.observation.base.index
  let raw ← unwrap (rawOutput json index)
  for output in [.null, Lean.toJson [raw, raw], Lean.toJson ["0"], Lean.toJson ["gg"]] do
    reject (Input.fromJson (← unwrap (changeOutput json index output)))
      "Require zero or one complete checked Ethernet ICMP frame."
  let profile ← unwrap (json.getObjVal? "icmpProfile")
  for (key, value) in [("outerTtl", 0), ("outerTtl", 256), ("rateLimit", 1), ("rateMask", 1),
      ("errorsUseInboundIfaddr", 1), ("quoteLimit", 547), ("tosMask", 31), ("tosPrecedence", 0)] do
    reject (Input.fromJson (json.setObjVal! "icmpProfile" (profile.setObjVal! key (Lean.toJson value))))
      "Unsupported ICMP environment settings must not become successful evidence."
  reject (Input.fromJson (json.setObjVal! "icmpProfile" (profile.setObjVal! "outerDontFragment" (Lean.toJson true))))
    "The selected ICMP control socket uses DF-clear output."
  let routing ← unwrap (json.getObjVal? "routing")
  let routes ← unwrap (values routing "routes")
  let withoutSource := routes[0]!.setObjVal! "prefsrc" .null
  reject (Input.fromJson (json.setObjVal! "routing" (routing.setObjVal! "routes" (.arr (routes.set! 0 withoutSource)))))
    "A return route without a usable explicit source is unsupported."
  reject (Input.fromJson (json.setObjVal! "events" (.arr #[]))) "Require a packet event."
  reject (Input.fromJson (json.setObjVal! "header" .null)) "Reject supplied header overrides."
  reject (Input.parse "{\"schema\":1,\"schema\":1}") "Reject duplicate JSON fields."

def run : IO Unit := do
  let json ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/icmp/replay.json"))
  baseTests json
  mismatchTests json
  parserTests json
  IO.println "ICMP forwarding observation tests passed."

end NetlibTest.ICMPForwardingCheck
