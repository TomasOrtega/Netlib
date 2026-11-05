import Netlib.Check.EAP

namespace NetlibTest.EAPCheck

open Netlib Protocol Check.EAP

example (report : Report context initial observations) (safe : initial.Safe context)
    (compliant : report.compliant = true) :
    ∀ finding ∈ report.findings, finding.observation.authorized = some true →
      EAPAuth.State.Ready (EAPSession.authContext context) finding.result.auth :=
  report.observed_authorization_ready safe compliant

example (report : Report context initial observations) (safe : initial.Safe context)
    (compliant : report.compliant = true) :
    ∀ finding ∈ report.findings, finding.observation.accepted = some true →
      ∃ scope, finding.observation.event = .application (.request scope) ∧
        finding.result.session.admitted = some scope ∧ Session.Valid context finding.result.session scope ∧
        EAPAuth.State.Ready (EAPSession.authContext context) finding.result.auth :=
  report.observed_admission_valid safe compliant

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def atIndex (values : List α) (index : Nat) : IO α :=
  match values[index]? with
  | some value => pure value
  | none => throw (IO.userError s!"Expected EAP fixture element {index}.")

private def events (json : Lean.Json) : Except String (Array Lean.Json) :=
  json.getObjVal? "events" >>= Lean.Json.getArr?

private def setEvents (json : Lean.Json) (values : Array Lean.Json) : Lean.Json :=
  json.setObjVal! "events" (.arr values)

private def changed (json : Lean.Json) (index : Nat) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let values ← events json
  return setEvents json (values.set! index (change values[index]!))

private def without (json : Lean.Json) (field : String) : Except String Lean.Json := do
  return Lean.Json.mkObj ((← json.getObj?).toList.filter (fun value => value.1 != field))

private def frameRaw (value : Lean.Json) (change : Import.EAPOL.EthernetFrame → Import.EAPOL.EthernetFrame) :
    Except String Lean.Json := do
  let frame ← Import.EAPOL.parseHex (← (← value.getObjVal? "raw").getStr?)
  let bytes ← Import.EAPOL.encodeEthernet (change frame)
  return value.setObjVal! "raw" (.str (Import.EAPOL.bytesToHex bytes))

private def packet (value : Lean.Json) (next : EAP.Packet) : Except String Lean.Json :=
  frameRaw value fun frame => { frame with frame := { frame.frame with body := .eap ⟨next, []⟩ } }

private def fixtureTests (success failure : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.parse success.compress)
  let report := input.check
  ensure (report.compliant && input.observations.length == 20 && report.findings.length == 20)
    "All retained native success observations must match their ordered model execution."
  let method ← atIndex report.findings 17
  let terminal ← atIndex report.findings 16
  let afterLogoff ← atIndex report.findings 19
  ensure (!terminal.result.auth.authorized && method.result.auth.authorized &&
      method.result.session.authenticated && !afterLogoff.result.auth.authorized &&
      !afterLogoff.result.session.authenticated && !report.final.auth.authorized)
    "Wire Success alone cannot authorize; bound method evidence can, and Logoff clears authorization."
  ensure (method.observation.authorized == some true && method.observation.frame.isNone &&
      afterLogoff.observation.authorized == some false && afterLogoff.observation.frame.isSome)
    "Native method evidence and decoded frame observations must retain distinct provenance."
  let failed ← unwrap (Input.parse failure.compress)
  ensure (failed.check.compliant && failed.observations.length == 16 &&
      failed.check.findings.all (fun finding => !finding.result.auth.authorized))
    "The native wrong-server capture must agree with denial throughout."
  let relabeled : Input := { input with observations := input.observations.map fun observation =>
    { observation with index := 0 } }
  ensure (relabeled.check.compliant && decide (relabeled.check.final = report.final) &&
      decide (relabeled.check.findings.map Finding.result = report.findings.map Finding.result))
    "Source indices label evidence; list order alone must drive state transitions."
  let noisy ← unwrap (Input.fromJson (← unwrap (changed success 0 (·.setObjVal! "authorized" (.bool true)))))
  ensure (!noisy.check.compliant && !(← atIndex noisy.check.findings 0).passed &&
      (noisy.check.findings.drop 1).all (·.passed) && decide (noisy.check.final = report.final))
    "A false observed authorization must not change current or future model state."
  let noisyMethod ← unwrap (Input.fromJson
    (← unwrap (changed success 17 (·.setObjVal! "authorized" (.bool false)))))
  ensure (!noisyMethod.check.compliant && (← atIndex noisyMethod.check.findings 17).result.auth.authorized &&
      (noisyMethod.check.findings.drop 18).all (·.passed) && decide (noisyMethod.check.final = report.final))
    "A false negative observation cannot revoke computed authorization or poison Logoff handling."

private def methodTests (json : Lean.Json) : IO Unit := do
  let values ← unwrap (events json)
  let missing := setEvents json ((values.toList.take 17 ++ values.toList.drop 18).toArray)
  let missing ← unwrap (changed missing 16 (·.setObjVal! "authorized" (.bool true)))
  let input ← unwrap (Input.fromJson missing)
  ensure (!input.check.compliant && !(← atIndex input.check.findings 16).result.auth.authorized &&
      input.check.findings.all (fun finding => !finding.result.auth.authorized))
    "Raw Success without method evidence must fail a claimed authorization."
  for mutation in [
      values[17]!.setObjVal! "round" (Lean.toJson (1 : Nat)),
      values[17]!.setObjVal! "subject" (.str "mallory@campus.example.test"),
      values[17]!.setObjVal! "method" (Lean.toJson (25 : Nat)),
      values[17]!.setObjVal! "accepted" (.bool false)] do
    let input ← unwrap (Input.fromJson (setEvents json (values.set! 17 mutation)))
    ensure (!input.check.compliant && !(← atIndex input.check.findings 17).passed &&
        input.check.findings.all (fun finding => !finding.result.auth.authorized))
      "Stale, wrong-subject, wrong-method, or negative method evidence must not authorize."
  let wrongTerminal ← unwrap (packet values[16]! (.success 99))
  let input ← unwrap (Input.fromJson (setEvents json (values.set! 16 wrongTerminal)))
  ensure (!input.check.compliant && !(← atIndex input.check.findings 17).result.auth.authorized)
    "A trusted method result cannot repair an uncorrelated terminal identifier."

private def scope : Scope := ⟨"synthetic-document", "read"⟩

private def scopeJson : Lean.Json := Lean.Json.mkObj [
  ("resource", .str scope.resource), ("operation", .str scope.operation)]

private def syntheticApplicationTests (json : Lean.Json) : IO Unit := do
  let values ← unwrap (events json)
  let credential := Lean.Json.mkObj [
    ("issuer", .str "campus-authority"), ("subject", .str "alice@campus.example.test"),
    ("audience", .str "campus-application"), ("scopes", Lean.toJson [scopeJson]),
    ("expiresAt", Lean.toJson (100 : Nat)), ("integrity", .bool true)]
  let install := Lean.Json.mkObj [
    ("type", .str "install"), ("credential", credential), ("authorized", .bool true)]
  let request (admitted authorized : Bool) := Lean.Json.mkObj [
    ("type", .str "request"), ("scope", scopeJson), ("accepted", .bool admitted),
    ("authorized", .bool authorized)]
  let synthetic := setEvents json ((values.toList.take 18 ++
    [install, request true true, values[18]!, request false false]).toArray)
  let input ← unwrap (Input.fromJson synthetic)
  ensure (input.check.compliant && (← atIndex input.check.findings 19).result.session.admitted == some scope &&
      (← atIndex input.check.findings 20).result.session.credential.isNone &&
      (← atIndex input.check.findings 21).result.session.admitted.isNone)
    "SYNTHETIC application requests must use bound authorization and deny after native Logoff."
  let wrong ← unwrap (changed synthetic 19 (·.setObjVal! "accepted" (.bool false)))
  let changedInput ← unwrap (Input.fromJson wrong)
  ensure (!changedInput.check.compliant && !(← atIndex changedInput.check.findings 19).passed &&
      decide (changedInput.check.final = input.check.final) &&
      (changedInput.check.findings.drop 20).all (·.passed))
    "SYNTHETIC admission observations must not determine session state or later denial."

private def parserTests (json : Lean.Json) : IO Unit := do
  let values ← unwrap (events json)
  reject (Input.fromJson (json.setObjVal! "schema" (Lean.toJson (2 : Nat))))
    "Unsupported EAP checker schemas must be rejected."
  reject (Input.fromJson (json.setObjVal! "authorized" (.bool true)))
    "Unknown root authorization fields must be rejected."
  reject (Input.parse "{\"schema\":1,\"schema\":1}") "Duplicate JSON keys must be rejected."
  reject (Input.fromJson (← unwrap (changed json 0 (·.setObjVal! "type" (.str "authenticate")))))
    "Application inputs cannot directly inject authentication."
  reject (Input.fromJson (← unwrap (changed json 17 (·.setObjVal! "trusted" (.bool true)))))
    "Unknown method trust fields must be rejected."
  reject (Input.fromJson (← unwrap (changed json 17 (·.setObjVal! "method" (Lean.toJson (256 : Nat))))))
    "A method number must fit in its EAP byte."
  reject (Input.fromJson (setEvents json (values.set! 0 (← unwrap (without values[0]! "authorized")))))
    "Every event must explicitly declare whether authorization was observed."
  let link ← unwrap (json.getObjVal? "link")
  for badPeer in ["01:80:c2:00:00:03", "02:00:00:00:ea:01"] do
    reject (Input.fromJson (json.setObjVal! "link" (link.setObjVal! "peer" (.str badPeer))))
      "Link roles require distinct unicast MACs."
  for raw in ["0", "zz", "00 00", "02000000ea0202000000ea0181000001888e02010000",
      "02000000ea0202000000ea01080002010000", "02000000ea0202000000ea01888e02030000"] do
    reject (Input.fromJson (← unwrap (changed json 2 (·.setObjVal! "raw" (.str raw)))))
      "Malformed hex, VLAN, wrong EtherType, and unsupported EAPOL kinds must be rejected."
  let badSource ← unwrap (frameRaw values[2]! fun frame =>
    { frame with source := ⟨2, 0, 0, 0, 234, 3⟩ })
  reject (Input.fromJson (setEvents json (values.set! 2 badSource)))
    "An unbound Ethernet source must not supply an EAP event."
  let badDestination ← unwrap (frameRaw values[2]! fun frame =>
    { frame with destination := ⟨2, 0, 0, 0, 234, 3⟩ })
  reject (Input.fromJson (setEvents json (values.set! 2 badDestination)))
    "An unrelated Ethernet destination must not supply an EAP event."
  let peerSuccess ← unwrap (packet values[15]! (.success 7))
  reject (Input.fromJson (setEvents json (values.set! 15 peerSuccess)))
    "Peer-originated EAP Success cannot impersonate an authenticator terminal packet."
  let serverResponse ← unwrap (packet values[14]! (.response 7 13 [0]))
  reject (Input.fromJson (setEvents json (values.set! 14 serverResponse)))
    "An authenticator cannot impersonate a peer Response."
  for kind in ([0, 254, 255] : List UInt8) do
    let unsupported ← unwrap (packet values[2]! (.request 1 kind []))
    reject (Input.fromJson (setEvents json (values.set! 2 unsupported)))
      "The selected session profile must reject reserved or expanded EAP method types."
  let advance (now : Lean.Json) := Lean.Json.mkObj [
    ("type", .str "advance"), ("now", now), ("authorized", .null)]
  reject (Input.fromJson (setEvents json (values ++ #[advance (Lean.toJson (2 : Nat)), advance (Lean.toJson (1 : Nat))])))
    "The declared application clock cannot move backward."
  reject (Input.fromJson (setEvents json (values.push (advance (Lean.toJson (-1 : Int))))))
    "A negative application clock must be rejected."
  reject (Input.fromJson (setEvents json #[values[0]!])) "An EAP audit requires raw Ethernet evidence."
  reject (Input.fromJson (setEvents json ((values.toList.take 17).toArray)))
    "An EAP audit requires at least one observed result."

def run : IO Unit := do
  let success ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/eap/success.json"))
  let failure ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/eap/bad-server.json"))
  fixtureTests success failure
  methodTests success
  syntheticApplicationTests success
  parserTests success
  IO.println "EAP session observation checker tests passed."

end NetlibTest.EAPCheck
