import Netlib.Check.PMTU

namespace NetlibTest.PMTUCheck

open Netlib Packet Protocol Check.PMTU

example (report : Report environment start observations) :
    report.compliant = true ↔ Agreement environment start observations := report.compliant_iff

example (report : Report environment start observations) (valid : start.cache.Valid environment.route) :
    report.final.cache.Valid environment.route ∧
      ∀ finding ∈ report.findings, finding.result.state.cache.Valid environment.route := report.valid valid

private def socket : Header := ⟨3221225986, 3325256706, Packet.Protocol.udp, 41000, 9000⟩
private def router : Address := 3221225985
private def attacker : Address := 3405803777

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

private def modifyByte (bytes : List UInt8) (index : Nat) : List UInt8 :=
  bytes.take index ++ (bytes.drop index).modifyHead (· + 1)

private def receiveBytes (quote : Header := socket) (kind : ICMP.Kind := .fragmentationNeeded 600)
    (reporter : Address := router) (badInner : Bool := false) (badUDP : Bool := false) :
    Except String String := do
  let datagram := UDP.computed quote.source quote.destination quote.sourcePort quote.destinationPort
    ((List.range 13).map UInt8.ofNat)
  let transport ← UDP.encode quote.source quote.destination datagram
  let transport := if badUDP then modifyByte transport 6 else transport
  let packet : IPv4.Packet := ⟨0, 1234, true, 63, quote.protocol, quote.source, quote.destination, transport⟩
  let header := IPv4.headerBytes packet (IPv4.computedChecksum packet)
  let header := if badInner then modifyByte header 10 else header
  let quotation := header ++ transport
  let message : ICMP.Message := ⟨kind, quotation⟩
  let outer : IPv4.Packet := ⟨192, 4321, false, 64, Packet.Protocol.icmp, reporter, socket.source, ICMP.encode message⟩
  let bytes ← IPv4.encode outer
  let frame : Import.EthernetIPv4.Envelope := ⟨⟨0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 2⟩, bytes⟩
  return Import.EAPOL.bytesToHex (Import.EthernetIPv4.encode frame)

private def receiveEvent (now : Nat) (raw : String) (mtu : Option Nat) : Lean.Json :=
  Lean.Json.mkObj [("type", Lean.toJson "receive"), ("at", Lean.toJson now),
    ("raw", Lean.toJson raw), ("mtu", Lean.toJson mtu)]

private def queryEvent (now mtu : Nat) : Lean.Json :=
  Lean.Json.mkObj [("type", Lean.toJson "query"), ("at", Lean.toJson now), ("mtu", Lean.toJson mtu)]

private def sendEvent (now payloadLength : Nat) (observed : String) (df : Bool := true) : Lean.Json :=
  Lean.Json.mkObj [("type", Lean.toJson "send"), ("at", Lean.toJson now),
    ("payloadLength", Lean.toJson payloadLength), ("df", Lean.toJson df),
    ("errorsDrained", Lean.toJson true), ("observed", Lean.toJson observed)]

private def fixture (events : List Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("schema", Lean.toJson (1 : Nat)),
    ("route", Lean.Json.mkObj [("mtu", Lean.toJson (4096 : Nat)), ("locked", Lean.toJson false)]),
    ("policy", Lean.Json.mkObj [("minimum", Lean.toJson (552 : Nat)), ("lifetime", Lean.toJson (600 : Nat))]),
    ("socket", Import.PacketFields.headerJson socket), ("events", Lean.toJson events)]

private def auditJson (json : Lean.Json) : IO Bool := do
  let input ← unwrap (Input.fromJson json)
  return (← unwrap input.check).compliant

private def current (input : Input) (report : Report input.environment initial input.events) (now : Nat) : Nat :=
  (report.final.cache.current input.environment.route now).val

private def baseFixture : IO Lean.Json := do
  let native ← unwrap (receiveBytes)
  let forged ← unwrap (receiveBytes socket (.fragmentationNeeded 576) attacker)
  return fixture [queryEvent 0 4096, receiveEvent 100 native (some 600),
    sendEvent 101 1200 "messageSize", sendEvent 101 500 "accepted", receiveEvent 101 forged (some 576),
    queryEvent 102 576, sendEvent 102 549 "messageSize", sendEvent 102 548 "accepted"]

private def changeEvent (json : Lean.Json) (index : Nat) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let events ← (← json.getObjVal? "events").getArr?
  return json.setObjVal! "events" (.arr (events.set! index (change events[index]!)))

private def baseTests : IO Unit := do
  let input ← unwrap (Input.fromJson (← baseFixture))
  let report ← unwrap input.check
  ensure (report.compliant && report.findings.length == 8 && current input report 102 == 576)
    "Host replay must derive the cache from received bytes and compare later PMTU queries and sends."
  match report.final.cache.exception with
  | none => throw (IO.userError "Expected a cached PMTU exception.")
  | some entry =>
    ensure (entry.mtu.val == 576 && !entry.locked && entry.expires == 701)
      "A matching quote from an unauthenticated reporter must reduce the selected socket's cache."
  let rendered := report.renderJson
  ensure ((← unwrap ((← unwrap (rendered.getObjVal? "scope")).getStr?)) == "udp-host-pmtu-feedback")
    "The report must identify its selected host PMTU scope."

private def mismatchTests : IO Unit := do
  let json ← baseFixture
  let input ← unwrap (Input.fromJson json)
  let original ← unwrap input.check
  for (index, key, value) in [(1, "mtu", Lean.toJson (3000 : Nat)),
      (5, "mtu", Lean.toJson (4096 : Nat)), (6, "observed", Lean.toJson "accepted")] do
    let changed ← unwrap (Input.fromJson (← unwrap (changeEvent json index (·.setObjVal! key value))))
    let report ← unwrap changed.check
    ensure (!report.compliant && report.final == original.final &&
        (report.findings.drop (index + 1)).all (·.passed))
      "A mismatched receive, query, or send observation must not replace the computed PMTU cache."

private def lifecycleTests : IO Unit := do
  let six ← unwrap receiveBytes
  let zero ← unwrap (receiveBytes socket (.fragmentationNeeded 0))
  let tiny ← unwrap (receiveBytes socket (.fragmentationNeeded 68))
  let fresh ← unwrap (receiveBytes socket (.fragmentationNeeded 1200))
  let input ← unwrap (Input.fromJson (fixture [receiveEvent 100 six (some 600),
    receiveEvent 399 six (some 600), receiveEvent 400 six (some 600), queryEvent 999 600,
    receiveEvent 999 six (some 600), receiveEvent 1000 zero (some 552), receiveEvent 1001 tiny (some 552),
    queryEvent 1599 552, queryEvent 1600 4096, receiveEvent 1600 fresh (some 1200), queryEvent 2200 4096]))
  let report ← unwrap input.check
  ensure (report.compliant && current input report 2200 == 4096)
    "Host replay must preserve floor locks, half-life refresh, and expiry in its monotonic clock model."
  let lockedRoute := (fixture [receiveEvent 1 six (some 4096)]).setObjVal! "route"
    (Lean.Json.mkObj [("mtu", Lean.toJson (4096 : Nat)), ("locked", Lean.toJson true)])
  ensure (← auditJson lockedRoute) "A locked route must ignore matching PMTU feedback."
  let smallRoute := (fixture [receiveEvent 1 zero (some 68)]).setObjVal! "route"
    (Lean.Json.mkObj [("mtu", Lean.toJson (68 : Nat)), ("locked", Lean.toJson false)])
  ensure (← auditJson smallRoute) "The configured floor must not raise PMTU above the physical route."
  ensure (← auditJson (fixture [receiveEvent 1 six (some 600), sendEvent 2 65508 "invalidLength",
      sendEvent 2 1200 "accepted" false, sendEvent 2 572 "accepted", sendEvent 2 573 "messageSize"]))
    "Send capacity must include IPv4 and UDP headers and reject unrepresentable UDP lengths."

private def associationTests : IO Unit := do
  let first ← unwrap receiveBytes
  for quoted in [{ socket with source := socket.source + 1 }, { socket with destination := socket.destination + 1 },
      { socket with protocol := Packet.Protocol.tcp }, { socket with sourcePort := socket.sourcePort + 1 },
      { socket with destinationPort := socket.destinationPort + 1 }] do
    let unrelated ← unwrap (receiveBytes quoted (.fragmentationNeeded 576))
    ensure (← auditJson (fixture [receiveEvent 1 first (some 600), receiveEvent 2 unrelated (some 600), queryEvent 3 600]))
      "All five quoted fields must match the selected connected UDP socket before a PMTU update."
  let timeout ← unwrap (receiveBytes socket .timeExceeded)
  ensure (← auditJson (fixture [receiveEvent 1 first (some 600), receiveEvent 2 timeout (some 600)]))
    "Time Exceeded must preserve the PMTU cache."
  for (badInner, badUDP) in [(true, false), (false, true), (true, true)] do
    let untrusted ← unwrap (receiveBytes socket (.fragmentationNeeded 576) attacker badInner badUDP)
    let input ← unwrap (Input.fromJson (fixture [receiveEvent 1 untrusted (some 576)]))
    let report ← unwrap input.check
    ensure (report.compliant && current input report 1 == 576)
      "Quoted checksums remain untrusted data while valid outer checksums permit a matching update."
    let some finding := report.findings.head? | throw (IO.userError "Expected a received-feedback finding.")
    let some feedback := finding.result.feedback | throw (IO.userError "Expected source-backed feedback.")
    let quote := feedback.packet.checked.source.quote
    ensure (InternetChecksum.valid (IPv4QuotePrefix.headerBytes quote) == !badInner &&
        (UDP.decode quote.packet.source quote.packet.destination quote.packet.payload).isOk == !badUDP)
      "The checker must retain invalid quoted IPv4 and UDP checksums rather than repair or reject them."

private def parserTests : IO Unit := do
  let json ← baseFixture
  let raw ← unwrap receiveBytes
  reject (Input.fromJson (json.setObjVal! "unused" .null)) "Reject unknown host replay fields."
  reject (Input.parse "{\"schema\":1,\"schema\":1}") "Reject duplicate JSON keys."
  for schema in [0, 2] do
    reject (Input.fromJson (json.setObjVal! "schema" (Lean.toJson schema))) "Require schema one."
  for (key, bad) in [("mtu", 67), ("mtu", 65536)] do
    let route ← unwrap (json.getObjVal? "route")
    reject (Input.fromJson (json.setObjVal! "route" (route.setObjVal! key (Lean.toJson bad))))
      "Physical route MTUs must satisfy the IPv4 bounds."
  let policy ← unwrap (json.getObjVal? "policy")
  for (key, bad) in [("minimum", 67), ("minimum", 65536), ("lifetime", 0)] do
    reject (Input.fromJson (json.setObjVal! "policy" (policy.setObjVal! key (Lean.toJson bad))))
      "The selected policy requires an IPv4 floor and a positive lifetime."
  reject (Input.fromJson (json.setObjVal! "socket"
    (Import.PacketFields.headerJson { socket with protocol := Packet.Protocol.tcp })))
    "Host PMTU replay selects a connected UDP socket."
  for value in [Lean.toJson false, .null, Lean.toJson (1 : Nat)] do
    reject (Input.fromJson (← unwrap (changeEvent json 2 (·.setObjVal! "errorsDrained" value))))
      "Send evidence requires an explicit true pending-error-drain declaration."
  for (key, value) in [("df", Lean.toJson (1 : Nat)), ("observed", Lean.toJson "unknown"),
      ("extra", .null)] do
    reject (Input.fromJson (← unwrap (changeEvent json 2 (·.setObjVal! key value))))
      "Reject unsupported send declarations."
  let backwards ← unwrap (Input.fromJson (fixture [queryEvent 2 4096, queryEvent 1 4096]))
  reject backwards.check "Reject a clock moving backwards during replay."
  for bytes in ["0", "gg", "0000"] do
    reject (Input.fromJson (fixture [receiveEvent 1 bytes none])) "Require checked Ethernet ICMP bytes."
  let bytes ← unwrap (Import.EAPOL.bytesFromHex raw)
  for index in [24, 36] do
    let corrupt := Import.EAPOL.bytesToHex (modifyByte bytes index)
    reject (Input.fromJson (fixture [receiveEvent 1 corrupt none])) "Reject invalid outer IPv4 or ICMP checksums."

private def nativeTests : IO Unit := do
  let json ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/received-icmp/host.json"))
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  ensure (report.compliant && report.findings.length == 19 && input.environment.route.mtu.val == 4096 &&
      input.environment.policy.minimum.val == 552 && input.environment.policy.lifetime == 600 &&
      current input report report.final.lastTime == 576)
    "The nineteen native host observations must agree with the selected route, policy, and 600-to-576 cache reduction."
  let feedbacks := report.findings.filterMap (·.result.feedback)
  ensure (feedbacks.length == 4 && feedbacks.all (·.outcome.isSome))
    "Each captured host ICMP quotation must select the connected UDP socket and Fragmentation Needed update."
  let badIP := feedbacks.filter fun feedback =>
    !InternetChecksum.valid (IPv4QuotePrefix.headerBytes feedback.packet.checked.source.quote)
  let completeUDP := feedbacks.filter fun feedback =>
    let quote := feedback.packet.checked.source.quote
    quote.declaredLength.val == quote.packet.payload.length + 20
  ensure (badIP.length == 1 && completeUDP.length == 1 && completeUDP.all (fun feedback =>
      let quote := feedback.packet.checked.source.quote
      !(UDP.decode quote.packet.source quote.packet.destination quote.packet.payload).isOk))
    "Native evidence must retain one invalid quoted IP checksum and one complete invalid UDP checksum."
  ensure (report.findings.all fun finding =>
      let value := (finding.result.state.cache.current input.environment.route finding.result.state.lastTime).val
      decide (68 ≤ value ∧ value ≤ 4096))
    "Every checked native host observation must retain the physical IPv4 PMTU bounds."
  let changed ← unwrap (Input.fromJson (← unwrap (changeEvent json 3 (·.setObjVal! "mtu" (Lean.toJson (4096 : Nat))))))
  let mismatch ← unwrap changed.check
  ensure (!mismatch.compliant && mismatch.final == report.final && (mismatch.findings.drop 4).all (·.passed))
    "A changed native PMTU observation must mismatch without changing computed state or later observations."

def run : IO Unit := do
  baseTests
  mismatchTests
  lifecycleTests
  associationTests
  parserTests
  nativeTests
  IO.println "Host PMTU observation tests passed."

end NetlibTest.PMTUCheck
