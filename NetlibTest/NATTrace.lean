import Netlib.Check.NATTrace

namespace NetlibTest.NATTrace

open Netlib Netlib.Packet Netlib.Protocol
open Netlib.Check.NATTrace

private def request : Header := ⟨167772170, 3325256724, Protocol.tcp, 50000, 443⟩

private def secondRequest : Header := { request with destination := 3325256725 }

private def allocation : Endpoint := ⟨3405803786, 40000⟩

private def translated (packet : Header) : Header := (Packet.Rewrite.sourceEndpoint allocation).apply packet

private def reply (packet : Header) : Header := (translated packet).reverse

private def policy : Lean.Json := Lean.Json.mkObj [
  ("schema", Lean.toJson (1 : Nat)),
  ("requirements", Lean.toJson [
    Lean.Json.mkObj [("id", Lean.toJson "HTTPS"), ("action", Lean.toJson "permit"),
      ("match", Lean.Json.mkObj [("source", .null), ("destination", .null), ("protocol", Lean.toJson (6 : Nat)),
        ("sourcePorts", .null), ("destinationPorts", Lean.Json.mkObj [
          ("first", Lean.toJson (443 : Nat)), ("last", Lean.toJson (443 : Nat))])])],
    Lean.Json.mkObj [("id", Lean.toJson "NO-SSH"), ("action", Lean.toJson "deny"),
      ("match", Lean.Json.mkObj [("source", .null), ("destination", .null), ("protocol", Lean.toJson (6 : Nat)),
        ("sourcePorts", .null), ("destinationPorts", Lean.Json.mkObj [
          ("first", Lean.toJson (22 : Nat)), ("last", Lean.toJson (22 : Nat))])])]])]

private def outbound (packet : Header) (selected : Endpoint) (expiresAt : Nat) (observed : Option Header)
    (extra : List (String × Lean.Json) := []) : Lean.Json :=
  Lean.Json.mkObj ([
    ("type", Lean.toJson "outbound"), ("packet", Import.PacketFields.headerJson packet),
    ("allocation", Import.PacketFields.endpointJson selected), ("expiresAt", Lean.toJson expiresAt),
    ("observed", Import.PacketFields.optionalHeaderJson observed)] ++ extra)

private def inbound (packet : Header) (observed : Option Header) : Lean.Json :=
  Lean.Json.mkObj [("type", Lean.toJson "inbound"), ("packet", Import.PacketFields.headerJson packet),
    ("observed", Import.PacketFields.optionalHeaderJson observed)]

private def advance (now : Nat) : Lean.Json :=
  Lean.Json.mkObj [("type", Lean.toJson "advance"), ("now", Lean.toJson now)]

private def close (packet : Header) : Lean.Json :=
  Lean.Json.mkObj [("type", Lean.toJson "close"), ("packet", Import.PacketFields.headerJson packet)]

private def flush : Lean.Json := Lean.Json.mkObj [("type", Lean.toJson "flush")]

private def inputJson (events : List Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("schema", Lean.toJson (1 : Nat)), ("policy", policy), ("events", Lean.toJson events)]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (events : List Lean.Json) (passed : Bool) (message : String) : IO Unit := do
  let input ← unwrap (Input.parse (inputJson events).compress)
  let report := input.check
  ensure (report.compliant == passed) message
  ensure (report.findings.map (·.index) == List.range events.length) "The NAT audit lost event provenance."
  ensure (report.findings.length == events.length) "The NAT audit lost a finding."
  let json := report.renderJson
  ensure ((← unwrap ((← unwrap (json.getObjVal? "scope")).getStr?)) == "local-source-napt-trace")
    "The NAT report lost its model scope."

private def positiveTests : IO Unit := do
  let unauthorized := { request with destinationPort := 22 }
  check [
    outbound request allocation 10 (some (translated request)),
    outbound secondRequest allocation 20 (some (translated secondRequest)),
    inbound (reply request) (some request.reverse),
    inbound (reply secondRequest) (some secondRequest.reverse),
    inbound { reply request with source := 3325256726 } none,
    inbound { reply request with sourcePort := 444 } none,
    inbound { reply request with destinationPort := 40001 } none,
    inbound { reply request with protocol := Protocol.udp } none,
    outbound unauthorized allocation 20 none,
    advance 9,
    inbound (reply request) (some request.reverse),
    advance 10,
    inbound (reply request) none,
    inbound (reply secondRequest) (some secondRequest.reverse),
    close secondRequest,
    inbound (reply secondRequest) none,
    flush,
    inbound (reply secondRequest) none] true
    "Valid mapping reuse or an expected denial failed."
  check [outbound request allocation 0 none] true "An already expired allocation was not denied correctly."
  let other := { request with source := 167772171 }
  check [outbound request allocation 10 (some (translated request)), outbound other allocation 10 none] true
    "A correct public-endpoint collision denial failed."
  let changedAllocation : Endpoint := ⟨allocation.address, 40001⟩
  check [outbound request allocation 10 (some (translated request)),
    outbound secondRequest changedAllocation 20 none] true "An existing mapping silently changed its public endpoint."

private def violationTests : IO Unit := do
  let opened := outbound request allocation 10 (some (translated request))
  let forbidden := { request with destinationPort := 22 }
  check [outbound forbidden allocation 10 (some (translated forbidden))] false
    "A forbidden outbound packet was observed as admitted without a violation."
  for badReply in [
      { reply request with source := 3325256726 },
      { reply request with sourcePort := 444 },
      { reply request with destinationPort := 40001 },
      { reply request with protocol := Protocol.udp }] do
    check [opened, inbound badReply (some request.reverse)] false
      "A reply with the wrong peer, port, or protocol was accepted."
  let collision := { request with source := 167772171 }
  check [opened, outbound collision allocation 10 (some (translated collision))] false
    "A conflicting mapping allocation was observed as admitted."
  let altered := { translated request with sourcePort := 40001 }
  check [outbound request allocation 10 (some altered)] false
    "An altered translated packet matched the model output."
  for control in [advance 10, close request, flush] do
    check [opened, control, inbound (reply request) (some request.reverse)] false
      "An expired, closed, or flushed reply remained admitted."
  check [inbound (reply request) (some request.reverse)] false "An unsolicited initial reply was admitted."

private def reject (text message : String) (budget : Nat := 100000) : IO Unit :=
  match Input.parse text budget with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def parserTests : IO Unit := do
  let opened := outbound request allocation 10 (some (translated request))
  let valid := (inputJson [opened]).compress
  reject (inputJson []).compress "An empty NAT trace was accepted."
  reject (inputJson [advance 1, flush]).compress "A control-only NAT trace was accepted."
  reject (inputJson [advance 10, advance 9, opened]).compress "A backward clock was accepted."
  reject (inputJson [outbound request allocation 10 (some (translated request))
    [("authorized", Lean.toJson true)]]).compress "A caller supplied the outbound authorization flag."
  reject (Lean.Json.mkObj [("schema", Lean.toJson (2 : Nat)), ("policy", policy),
    ("events", Lean.toJson [opened])]).compress "An unsupported NAT schema was accepted."
  reject (Lean.Json.mkObj [("schema", Lean.toJson (1 : Nat)), ("policy", policy),
    ("events", Lean.toJson [opened]), ("ignored", .null)]).compress "An unknown input field was ignored."
  reject (inputJson [Lean.Json.mkObj [("type", Lean.toJson "advance"),
    ("now", Lean.toJson (1 : Nat)), ("observed", .null)], opened]).compress
    "A control event accepted packet observation fields."
  reject (inputJson [Lean.Json.mkObj [("type", Lean.toJson "unknown")]]).compress
    "An unknown NAT event was accepted."
  reject (valid.replace "\"schema\":1" "\"schema\":1,\"schema\":1")
    "Duplicate JSON fields were accepted."
  let observedHeader := (Import.PacketFields.optionalHeaderJson (some (translated request))).compress
  let invalidObservation := valid.replace s!"\"observed\":{observedHeader}" "\"observed\":true"
  ensure (invalidObservation != valid) "The observation-type mutation changed no input."
  reject invalidObservation
    "An invalid observation type was accepted."
  reject (valid.replace "\"expiresAt\":10" "\"expiresAt\":-1") "A negative lifetime was accepted."
  reject (valid.replace "\"observed\":" "\"unexpected\":") "A packet event omitted its observed result."
  reject valid "An exhausted policy compilation budget produced a NAT audit input." 0

example (compiled : Compile.ACL.Certified intents) (packet restored : Header)
    (report : Report compiled.rules NAT.State.initial [⟨0, .inbound packet, some restored⟩]) :
    report.compliant = false := by
  cases passed : report.compliant with
  | false => rfl
  | true =>
    obtain ⟨_, _, _, ⟨observation, impossible, _⟩, _, _⟩ :=
      Report.inbound_policy_origin compiled [] [] 0 packet restored report passed
    cases impossible

def run : IO Unit := do
  positiveTests
  violationTests
  parserTests
  IO.println "NAT trace audit tests passed."

end NetlibTest.NATTrace
