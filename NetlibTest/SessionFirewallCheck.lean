import Netlib.Check.SessionFirewall

namespace NetlibTest.SessionFirewallCheck

open Netlib Protocol Packet Check.SessionFirewall

example (report : Report input) (compliant : report.compliant = true) (finding : Finding input)
    (member : finding ∈ report.findings) (state : StatefulACL.CTState) (header : Header)
    (allowed : finding.checkpoint.firewall.permits state header = true) :
    ∃ requirement ∈ input.requirements, requirement.test.Holds header ∧
      Session.Valid input.authentication.context (stateAt input.authentication finding.checkpoint.after).session
        requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
        (stateAt input.authentication finding.checkpoint.after).auth :=
  report.permitted_valid compliant finding member state header allowed

example (finding : Finding input) (passed : finding.passed = true) (requirement : Compile.SessionFirewall.Intent)
    (member : requirement ∈ input.requirements)
    (denied : (stateAt input.authentication finding.checkpoint.after).session.permits
      input.authentication.context requirement.scope = false)
    (state : StatefulACL.CTState) (header : Header) (matched : requirement.test.Holds header) :
    finding.checkpoint.firewall.permits state header = false :=
  finding.denied_requirement passed requirement member denied state header matched

private def object (fields : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj fields

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
  | none => throw (IO.userError s!"Expected session firewall fixture element {index}.")

private def values (json : Lean.Json) (key : String) : Except String (Array Lean.Json) :=
  json.getObjVal? key >>= Lean.Json.getArr?

private def without (json : Lean.Json) (field : String) : Except String Lean.Json := do
  return object ((← json.getObj?).toList.filter (fun value => value.1 != field))

private def block (address : Nat) : Lean.Json := object [
  ("address", Lean.toJson address), ("length", Lean.toJson (32 : Nat))]

private def port : Lean.Json := object [("first", Lean.toJson (443 : Nat)), ("last", Lean.toJson (443 : Nat))]

private def packetMatch (reply : Bool) : Lean.Json := object [
  ("source", block (if reply then 3325256714 else 3221225986)),
  ("destination", block (if reply then 3221225986 else 3325256714)),
  ("protocol", Lean.toJson (6 : Nat)),
  ("sourcePorts", if reply then port else .null), ("destinationPorts", if reply then .null else port)]

private def scope : Lean.Json := object [("resource", .str "reports"), ("operation", .str "read")]

private def requirement (id : String) (reply : Bool) : Lean.Json := object [
  ("id", .str id), ("scope", scope), ("match", packetMatch reply)]

private def intent : Lean.Json := object [
  ("schema", Lean.toJson (1 : Nat)), ("requirements", Lean.toJson [requirement "FORWARD" false, requirement "RETURN" true])]

private def credential : Lean.Json := object [
  ("issuer", .str "campus-authority"), ("subject", .str "alice@campus.example.test"),
  ("audience", .str "campus-application"), ("scopes", Lean.toJson [scope]),
  ("expiresAt", Lean.toJson (100 : Nat)), ("integrity", .bool true)]

private def generated (authentication : Check.EAP.Input) (after : Nat) : IO Lean.Json := do
  let requirements ← unwrap (requirementsFromJson intent)
  match Compile.SessionFirewall.compile authentication.context (stateAt authentication after) requirements with
  | .ok compiled => pure compiled.toJson
  | .error error => throw (IO.userError error.describe)

private def fixture : IO Lean.Json := do
  let native ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/eap/success.json"))
  let events ← unwrap (values native "events")
  let install := object [("type", .str "install"), ("credential", credential), ("authorized", .bool true)]
  let authentication := native.setObjVal! "events" (.arr ((events.toList.take 18 ++ [install] ++ events.toList.drop 18).toArray))
  let input ← unwrap (Check.EAP.Input.fromJson authentication)
  let snapshots ← ([0, 18, 19, 20, 21] : List Nat).mapM fun after => do
    return object [("after", Lean.toJson after), ("firewall", ← generated input after)]
  return object [("schema", Lean.toJson (1 : Nat)), ("authentication", authentication),
    ("intent", intent), ("snapshots", Lean.toJson snapshots)]

private def replaceFirewall (json : Lean.Json) (index : Nat) (firewall : Lean.Json) : Except String Lean.Json := do
  let snapshots ← values json "snapshots"
  return json.setObjVal! "snapshots" (.arr (snapshots.set! index (snapshots[index]!.setObjVal! "firewall" firewall)))

private def nativeObjects (json : Lean.Json) : Except String (Array Lean.Json) := values json "nftables"

private def setObjects (json : Lean.Json) (objects : Array Lean.Json) : Lean.Json := json.setObjVal! "nftables" (.arr objects)

private def staleEstablished (firewall : Lean.Json) : Except String Lean.Json := do
  let objects ← nativeObjects firewall
  let stateMatch := object [("match", object [
    ("op", .str "in"), ("left", object [("ct", object [("key", .str "state")])]), ("right", .str "established")])]
  let rule := object [("rule", object [
    ("family", .str "ip"), ("table", .str "netlib"), ("chain", .str "forward"),
    ("handle", Lean.toJson (999 : Nat)), ("comment", .str "STALE-ESTABLISHED"),
    ("expr", Lean.toJson [stateMatch, object [("accept", .null)]])])]
  return setObjects firewall ((objects.toList.take 3 ++ [rule] ++ objects.toList.drop 3).toArray)

private def baseTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.parse json.compress)
  let report ← unwrap input.check
  ensure (report.compliant && report.findings.length == 5 && input.authentication.check.compliant)
    "The native authentication trace plus SYNTHETIC credential must agree with every supplied current policy."
  ensure (input.snapshots.map (·.after) == [0, 18, 19, 20, 21] && input.snapshots.map (·.index) == [0, 1, 2, 3, 4])
    "Checkpoint prefixes count consumed list events and retain source labels."
  ensure (!(stateAt input.authentication 0).auth.authorized && (stateAt input.authentication 18).auth.authorized &&
      (stateAt input.authentication 18).session.credential.isNone &&
      (stateAt input.authentication 19).session.credential.isSome && !(stateAt input.authentication 20).auth.authorized)
    "Prefix boundaries must distinguish EAP authorization, synthetic credential installation, and Logoff."
  let active ← atIndex report.findings 2
  let afterLogoff ← atIndex report.findings 3
  let outgoing : Header := ⟨3221225986, 3325256714, Packet.Protocol.tcp, 50000, 443⟩
  for state in Check.StatefulRefinement.states do
    ensure (active.checkpoint.firewall.permits state outgoing &&
        active.checkpoint.firewall.permits state outgoing.reverse &&
        !afterLogoff.checkpoint.firewall.permits state outgoing &&
        !afterLogoff.checkpoint.firewall.permits state outgoing.reverse)
      "Exact current policy includes both directions and denies cached classifications after Logoff."
  let relabeled : Input := { input with snapshots := input.snapshots.map fun snapshot => { snapshot with index := 0 } }
  ensure ((← unwrap relabeled.check).compliant)
    "Snapshot source indices cannot substitute for consumed event prefixes."
  let authentication ← unwrap (json.getObjVal? "authentication")
  let events ← unwrap (values authentication "events")
  let changed := authentication.setObjVal! "events" (.arr (events.set! 0 (events[0]!.setObjVal! "authorized" (.bool true))))
  let mismatched ← unwrap (Input.fromJson (json.setObjVal! "authentication" changed))
  let mismatchReport ← unwrap mismatched.check
  ensure (!mismatchReport.compliant && mismatchReport.findings.all Finding.passed &&
      decide (stateAt mismatched.authentication 19 = stateAt input.authentication 19))
    "False EAP observations must fail the joint report without changing generated session state."

private def counterexampleTests (json : Lean.Json) : IO Unit := do
  let snapshots ← unwrap (values json "snapshots")
  let denied ← unwrap (snapshots[3]!.getObjVal? "firewall")
  let stale ← unwrap (replaceFirewall json 3 (← unwrap (staleEstablished denied)))
  let input ← unwrap (Input.fromJson stale)
  let report ← unwrap input.check
  let finding ← atIndex report.findings 3
  ensure (!report.compliant && !finding.passed &&
      !Check.StatefulRefinement.check finding.checkpoint.firewall finding.compiled.statefulSnapshot &&
      Check.StatefulRefinement.check finding.compiled.statefulSnapshot finding.checkpoint.firewall)
    "An established accept after Logoff must fail the unexpected-permit direction of equality."
  match Check.StatefulRefinement.counterexample finding.checkpoint.firewall finding.compiled.statefulSnapshot with
  | none => throw (IO.userError "A stale established accept needs a concrete counterexample.")
  | some witness =>
    ensure (witness.state == .established && finding.checkpoint.firewall.permits witness.state witness.header &&
        !finding.compiled.statefulSnapshot.permits witness.state witness.header)
      "The unexpected permit must identify the exact established context."
  let rendered ← unwrap (values report.renderJson "snapshots")
  ensure ((← unwrap (rendered[3]!.getObjVal? "unexpectedPermit")) != Lean.Json.null &&
      (← unwrap (rendered[3]!.getObjVal? "missingPermit")) == Lean.Json.null)
    "The rendered stale-allow finding must report the unexpected direction and no missing permit."
  let active ← unwrap (snapshots[2]!.getObjVal? "firewall")
  let objects ← unwrap (nativeObjects active)
  let missingReply := setObjects active ((objects.toList.take 4).toArray)
  let input ← unwrap (Input.fromJson (← unwrap (replaceFirewall json 2 missingReply)))
  let report ← unwrap input.check
  let finding ← atIndex report.findings 2
  ensure (!report.compliant && !finding.passed &&
      Check.StatefulRefinement.check finding.checkpoint.firewall finding.compiled.statefulSnapshot &&
      !Check.StatefulRefinement.check finding.compiled.statefulSnapshot finding.checkpoint.firewall)
    "A missing return rule must fail equality even though native policy safely refines the generated policy."
  match Check.StatefulRefinement.counterexample finding.compiled.statefulSnapshot finding.checkpoint.firewall with
  | none => throw (IO.userError "A missing return permit needs a concrete counterexample.")
  | some witness =>
    let replyRequirement ← atIndex input.requirements 1
    ensure (replyRequirement.test.accepts witness.header &&
        finding.compiled.statefulSnapshot.permits witness.state witness.header &&
        !finding.checkpoint.firewall.permits witness.state witness.header)
      "The missing-permit evidence must match the omitted return requirement."
  let rendered ← unwrap (values report.renderJson "snapshots")
  ensure ((← unwrap (rendered[2]!.getObjVal? "unexpectedPermit")) == Lean.Json.null &&
      (← unwrap (rendered[2]!.getObjVal? "missingPermit")) != Lean.Json.null)
    "The rendered missing-return finding must preserve the failed direction of equality."
  let swapped := setObjects active ((objects.toList.take 3 ++ (objects.toList.drop 3).reverse).toArray)
  let reordered ← unwrap (Input.fromJson (← unwrap (replaceFirewall json 2 swapped)))
  ensure ((← unwrap reordered.check).compliant)
    "Equivalent ordering of independent permit rules must preserve exact policy meaning."
  for (field, value) in [("hook", Lean.Json.str "postrouting"), ("prio", Lean.toJson (1 : Nat))] do
    let chain ← unwrap (objects[2]!.getObjVal? "chain")
    let changed := setObjects active (objects.set! 2 (object [("chain", chain.setObjVal! field value)]))
    let input ← unwrap (Input.fromJson (← unwrap (replaceFirewall json 2 changed)))
    reject input.check "A hook or priority mismatch must be an input error, not a policy answer."

private def parserTests (json : Lean.Json) : IO Unit := do
  let snapshots ← unwrap (values json "snapshots")
  reject (Input.fromJson (json.setObjVal! "schema" (Lean.toJson (2 : Nat)))) "Reject unsupported bundle schemas."
  reject (Input.fromJson (json.setObjVal! "trusted" (.bool true))) "Reject unknown bundle fields."
  reject (Input.fromJson (← unwrap (without json "authentication"))) "Require the authentication trace."
  reject (Input.parse "{\"schema\":1,\"schema\":1}") "Reject duplicate JSON keys."
  reject (Input.fromJson (json.setObjVal! "snapshots" (.arr #[]))) "Require at least one deployment checkpoint."
  for after in [Lean.toJson (22 : Nat), Lean.toJson (-1 : Int)] do
    reject (Input.fromJson (json.setObjVal! "snapshots" (.arr #[snapshots[0]!.setObjVal! "after" after])))
      "Reject negative or out-of-trace checkpoint prefixes."
  for bad in [#[snapshots[2]!, snapshots[1]!], #[snapshots[1]!, snapshots[1]!]] do
    reject (Input.fromJson (json.setObjVal! "snapshots" (.arr bad)))
      "Checkpoint prefixes must be strictly increasing, without duplicates."
  reject (Input.fromJson (json.setObjVal! "snapshots" (.arr #[snapshots[0]!.setObjVal! "index" (Lean.toJson (3 : Nat))])))
    "Source indices are generated metadata, not accepted checkpoint controls."
  reject (Input.fromJson (json.setObjVal! "snapshots" (.arr #[← unwrap (without snapshots[0]! "after")])))
    "Each checkpoint must explicitly name its consumed prefix."
  reject (parseRequirements "{\"schema\":1,\"schema\":1,\"requirements\":[]}") "Reject duplicate intent fields."
  let requirements ← unwrap (values intent "requirements")
  reject (requirementsFromJson (intent.setObjVal! "trusted" (.bool true))) "Reject unknown intent fields."
  reject (requirementsFromJson (intent.setObjVal! "requirements" (.arr #[requirements[0]!.setObjVal! "scope"
    (scope.setObjVal! "resource" (.str ""))]))) "Reject empty application scope names."
  let empty := json.setObjVal! "intent" (intent.setObjVal! "requirements" (.arr #[]))
  let input ← unwrap (Input.fromJson empty)
  reject input.check "An empty requirement policy must preserve the source compiler's explicit error."

private def budgetTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let cells := (report.findings.map Finding.cells).sum
  ensure ((← unwrap ((← unwrap (report.renderJson.getObjVal? "partitionCells")).getNat?)) == cells &&
      cells == (report.findings.map Finding.compilationCells).sum +
        (report.findings.map Finding.comparisonCells).sum)
    "The global budget must report both source compilation and bidirectional comparisons."
  reject (input.check 0) "Zero global budget cannot return an equivalence answer."
  reject (input.check (cells - 1)) "A shared budget must cover all checkpoints and both directions."
  ensure ((← unwrap (input.check cells)).compliant)
    "The exact global compilation and comparison cell budget must suffice, including a final deny policy."
  let first ← atIndex input.snapshots 0
  let single : Input := { input with snapshots := [first] }
  let singleReport ← unwrap single.check
  let singleCells := (singleReport.findings.map Finding.cells).sum
  reject (input.check singleCells) "A per-checkpoint budget must not be reused for every checkpoint."

def run : IO Unit := do
  let json ← fixture
  baseTests json
  counterexampleTests json
  parserTests json
  budgetTests json
  IO.println "Session firewall snapshot checker tests passed."

end NetlibTest.SessionFirewallCheck
