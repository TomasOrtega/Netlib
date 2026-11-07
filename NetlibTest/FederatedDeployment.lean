import Netlib.Check.FederatedDeployment
import Netlib.Check.FederatedResult
import Netlib.Check.FederatedGuarantees
import NetlibTest.FederatedDeploymentInputs

namespace NetlibTest.FederatedDeployment

open Netlib Federation
namespace F
export FederatedNativeFixture (Fixture build packet raw partialPortDenied)
end F
namespace I
export FederatedDeploymentInputs (mapVersions writeRequest selectorMismatch missingMust unsafeIntermediate badNativeScope nativeBypass)
end I

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def rejects (value : Except String α) (expected : String) : IO Unit :=
  match value with
  | .error reason => ensure (reason.contains expected) s!"Expected rejection containing '{expected}', got: {reason}"
  | .ok _ => throw (IO.userError s!"The public certificate accepted the negative: {expected}")

private def localPlans (input : Input) : IO Unit := do
  let limits : Native.Limits := ⟨input.cells, input.work⟩
  let _ ← load (LocalPlan.check input.left limits)
  let _ ← load (LocalPlan.check input.right limits)

private def checkPairs (input : Input) (checked : Deployment.Checked input) : IO Unit := do
  ensure (checked.queries.results.map (fun value => value.1.id) ==
      ["APP", "CAMPUS_POLICY", "PROVIDER_POLICY", "MANAGEMENT"])
    "The public certificate must retain all four named queries in order."
  let mut pairs := 0
  for left in List.finRange input.left.versions.length do
    for right in List.finRange input.right.versions.length do
      let _ := checked.local_sources left right
      for stored : packed in checked.queries.results do
        let query := packed.1
        let result := packed.2
        have guarantees := (checked.snapshot (left, right)).results query result stored
        match accepted : result.first.selector.accepts F.packet with
        | false => throw (IO.userError "The public query excludes the selected arbitrary application header.")
        | true =>
          let _ := guarantees.meaning F.packet accepted
          let _ := result.native_correct checked.compatible (checked.left.nativeAt left)
            (checked.right.nativeAt right) F.packet accepted
          if kind : query.kind = .reach then
            let _ := guarantees.reach F.packet accepted kind
            let _ := result.native_walk (checked.left.nativeAt left) (checked.right.nativeAt right) F.packet accepted kind
            ensure (result.witness.length ≥ 6) "Application availability must retain both local paths and the border."
          else if kind : query.kind = .mediated then
            let _ := guarantees.enforcement F.packet accepted kind
            if side : query.gateways.all (fun gateway => decide (gateway.side = Side.left)) = true then
              let _ := guarantees.mediatedOn F.packet accepted kind .left side
              have onlyLeft : ∀ gateway ∈ query.gateways, gateway.side = .left := by
                simpa only [List.all_eq_true, decide_eq_true_eq] using side
              let _ := result.native_mediated_on checked.compatible (checked.left.nativeAt left)
                (checked.right.nativeAt right) F.packet accepted kind .left onlyLeft
              pure ()
            else
              match side : query.gateways.all (fun gateway => decide (gateway.side = Side.right)) with
              | false => throw (IO.userError "A selected policy query mixes the two enforcement roles.")
              | true =>
                let _ := guarantees.mediatedOn F.packet accepted kind .right side
                have onlyRight : ∀ gateway ∈ query.gateways, gateway.side = .right := by
                  simpa only [List.all_eq_true, decide_eq_true_eq] using side
                let _ := result.native_mediated_on checked.compatible (checked.left.nativeAt left)
                  (checked.right.nativeAt right) F.packet accepted kind .right onlyRight
                pure ()
          else pure ()
      pairs := pairs + 1
  ensure (pairs == 9) "Both independently checked three-revision plans must produce all nine native pairs."

theorem every_trace_has_sources (checked : Deployment.Checked input)
    {events : List (Protocol.Transition.ProductLabel input.left.Operation input.right.Operation)}
    {current : input.left.Cursor × input.right.Cursor}
    (trace : (Plan.interleaving input.left input.right).Trace (Plan.jointInitial input.left input.right) events current) :
    Nonempty (Native.Checked input.left.contract (input.left.revisionAt current.1)) ∧
      Nonempty (Native.Checked input.right.contract (input.right.revisionAt current.2)) :=
  LocalPlan.all_checked checked.left checked.right trace

theorem every_pair_has_all_header_queries (checked : Deployment.Checked input)
    (current : input.left.Cursor × input.right.Cursor) (query : Query) (member : query ∈ input.intent.queries) :
    ∃ result : Queries.Result input.left.contract input.right.contract input.intent query,
      ⟨query, result⟩ ∈ checked.queries.results ∧ Deployment.QueryGuarantees input current query result :=
  (checked.snapshot current).query_for query member

theorem every_interleaving_has_guarantees (checked : Deployment.Checked input)
    {events : List (Protocol.Transition.ProductLabel input.left.Operation input.right.Operation)}
    {current : input.left.Cursor × input.right.Cursor}
    (trace : (Plan.interleaving input.left input.right).Trace (Plan.jointInitial input.left input.right) events current) :
    Deployment.ExecutionFacts checked events current := checked.interleaving_guarantees trace

theorem every_prefix_has_guarantees (checked : Deployment.Checked input)
    {prior later : List (Protocol.Transition.ProductLabel input.left.Operation input.right.Operation)}
    {current : input.left.Cursor × input.right.Cursor}
    (trace : (Plan.interleaving input.left input.right).Trace (Plan.jointInitial input.left input.right) (prior ++ later) current) :
    ∃ middle, (Plan.interleaving input.left input.right).Trace (Plan.jointInitial input.left input.right) prior middle ∧
      (Plan.interleaving input.left input.right).Trace middle later current ∧ Deployment.ExecutionFacts checked prior middle :=
  checked.prefix_guarantees trace

private def compatibilityRejections (input : Input) : IO Unit := do
  let changedBorder (change : Border → Border) : Input :=
    { input with intent := { input.intent with borders := input.intent.borders.map change } }
  rejects (Deployment.certify (changedBorder fun border => { border with targetVersion := border.targetVersion + 1 }))
    "target contract version is stale"
  rejects (Deployment.certify (changedBorder fun border => { border with targetDomain := "another-provider" }))
    "target domain differs"
  rejects (Deployment.certify (changedBorder fun border => { border with source := { border.source with node := "pep" } }))
    "source must be an egress"
  rejects (Deployment.certify (changedBorder fun border => { border with target := { border.target with node := "undeclared" } }))
    "target public node is undeclared"
  let selector := I.selectorMismatch input
  localPlans selector
  rejects (Deployment.certify selector) "Peer case differs in selector or request"
  let request := I.writeRequest input
  localPlans request
  rejects (Deployment.certify request) "Peer case differs in selector or request"
  let unknown := { input with intent := { input.intent with queries := input.intent.queries.map fun query =>
    if query.id == "APP" then { query with caseID := "missing-case" } else query } }
  rejects (Deployment.certify unknown) "unknown public case"
  rejects (Deployment.certify { input with cells := 0 }) "cell budget"
  rejects (Deployment.certify { input with work := 0 }) "work estimate"

private def missingMustRejection (input : Input) : IO Unit := do
  let missing := I.missingMust input
  let some oldCase := input.left.contract.case? "app" | throw (IO.userError "The original public case is absent.")
  let some newCase := missing.left.contract.case? "app" | throw (IO.userError "The changed public case is absent.")
  ensure (decide (oldCase.upper = newCase.upper) && newCase.must.isEmpty)
    "The missing-must negative must preserve the entire public upper graph."
  localPlans missing
  rejects (Deployment.certify missing) "no must path"

private def intermediateRejection (input : Input) : IO Unit := do
  let denied ← load (F.partialPortDenied (← F.raw))
  let broken ← load (I.unsafeIntermediate input denied)
  let limits : Native.Limits := ⟨input.cells, input.work⟩
  let _ ← load (Native.check broken.left.contract broken.left.initial limits)
  let some final := broken.left.updates[1]? | throw (IO.userError "The final safe native revision is absent.")
  let _ ← load (Native.check broken.left.contract final limits)
  rejects (Deployment.certify broken) "revision 1"
  rejects (Deployment.certify broken) "50001"

private def parserRejection : IO Unit := do
  let changed ← load (I.badNativeScope (← F.raw))
  rejects (Deployment.certifyJson changed.compress) "Unsupported Linux forwarding scope"
  let unknown := (← F.raw).setObjVal! "ignored" (.bool true)
  rejects (Deployment.certifyJson unknown.compress) "Unknown federation field"
  let text ← IO.FS.readFile FederatedNativeFixture.file
  let duplicate := text.replace "\"scope\": \"two-domain-ipv4-transit\""
    "\"scope\": \"two-domain-ipv4-transit\", \"scope\": \"two-domain-ipv4-transit\""
  ensure (duplicate != text) "The duplicate-key negative must alter the actual fixture text."
  rejects (Deployment.certifyJson duplicate) "Duplicate JSON object key: scope"
  let compact := (← F.raw).compress
  let nested := compact.replace "\"routeVersion\":\"6.19.0\""
    "\"routeVersion\":\"6.19.0\",\"routeVersion\":\"6.19.0\""
  ensure (nested != compact) "The nested duplicate negative must alter the native router source."
  rejects (Deployment.certifyJson nested) "Duplicate JSON object key: routeVersion"

private def genuineBypass : IO Unit := do
  let bypass ← load (I.nativeBypass (← F.raw))
  localPlans bypass
  let compatible ← load (Compatibility.check bypass.left.contract bypass.right.contract bypass.intent)
  let _ := compatible.borders
  for revision in bypass.left.versions do
    let some selected := bypass.left.contract.case? "app" | throw (IO.userError "The bypass case is absent.")
    ensure (revision.snapshot.nativeEdge F.packet selected.request "ingress" "egress" &&
        !revision.snapshot.nativeEdge F.packet selected.request "ingress" "gateway")
      "Every actual campus revision must route directly to the real terminal egress and skip its gateway."
  rejects (Deployment.certify bypass) "Query CAMPUS_POLICY: an upper path bypasses enforcement"
  let queries := bypass.intent.queries.filter (fun query => query.id != "CAMPUS_POLICY")
  let permitted := { bypass with intent := { bypass.intent with queries } }
  let checked ← load (Deployment.certify permitted)
  ensure (checked.queries.results.map (fun value => value.1.id) == ["APP", "PROVIDER_POLICY", "MANAGEMENT"])
    "The real campus bypass must preserve application availability, provider policy, and management isolation."
  for ⟨revision, localChecked⟩ in checked.left.revisions do
    let enforcement := revision.snapshot.intent.select revision.snapshot.intent.enforcement
    ensure (!enforcement.contains "ingress" && !enforcement.contains "egress")
      "The actual bypass endpoints must be outside campus enforcement."
    for ⟨_, selected⟩ in localChecked.results do
      for ⟨_, cell⟩ in selected.cells do
        for ⟨arc, path⟩ in cell.paths do
          ensure (arc.source == "client" && arc.target == "east" && path.trace == ["ingress", "egress"])
            "Every stored campus must path must be the real direct native bypass trace."
  let some packed := checked.queries.results[0]? | throw (IO.userError "The bypass application witness is absent.")
  ensure (packed.2.witness.all (fun reference => decide (reference ≠ (⟨.left, "pep"⟩ : PublicRef))) &&
      packed.2.witness.any (fun reference => decide (reference = (⟨.right, "pep"⟩ : PublicRef))))
    "The concrete public must path must skip campus enforcement while retaining provider enforcement."

def run : IO Unit := do
  let fixture ← F.build
  let rawChecked ← load (Deployment.certifyJson (← IO.FS.readFile FederatedNativeFixture.file))
  checkPairs rawChecked.1 rawChecked.2
  compatibilityRejections fixture.input
  missingMustRejection fixture.input
  intermediateRejection fixture.input
  parserRejection
  genuineBypass
  IO.println "Federated deployment: four public queries, nine native revision pairs, and genuine bypass rejection."

end NetlibTest.FederatedDeployment
