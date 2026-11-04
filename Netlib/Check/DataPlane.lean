import Netlib.Model.DataPlane
import Netlib.Check.Verification

/-!
# Composed data-plane checks

Each query uses one fixed packet header and one named request.
Every endpoint pair has a checked path or cut.
The report carries a proof for each result and for the final status.
-/

namespace Netlib.DataPlane

open Certificate Compliance Verification

namespace Query

def gatewaysFor (c : Config) (q : Query) : List String :=
  (q.gateways.map c.select).getD []

def networkAt (c : Config) (q : Query) (header : Packet.Header) : Network String :=
  c.model header (c.requestFor q.request)

def network (c : Config) (q : Query) : Network String :=
  q.networkAt c (c.trafficFor q.traffic)

/-- A query states a property for each selected endpoint pair. -/
def PairMeaningAt (c : Config) (q : Query) (header : Packet.Header) (source target : String) : Prop :=
  match q.kind with
  | .reach => (q.networkAt c header).Reachable source target
  | .isolate => ¬(q.networkAt c header).Reachable source target
  | .mediated => ¬(q.networkAt c header).Bypass (fun node => node ∈ q.gatewaysFor c) source target

def PairMeaning (c : Config) (q : Query) (source target : String) : Prop :=
  q.PairMeaningAt c (c.trafficFor q.traffic) source target

def MeaningAt (c : Config) (q : Query) (header : Packet.Header) : Prop :=
  ∀ source ∈ c.select q.source, ∀ target ∈ c.select q.target,
    q.PairMeaningAt c header source target

def Meaning (c : Config) (q : Query) : Prop :=
  ∀ source ∈ c.select q.source, ∀ target ∈ c.select q.target, q.PairMeaning c source target

end Query

namespace Check

structure Checked (meaning : Prop) where
  value : Bool
  evidence : List String
  correct : value = true ↔ meaning

private def allChecked {α : Type u} (meaning : α → Prop)
    (check : (item : α) → Except String (Checked (meaning item))) :
    (items : List α) → Except String (Checked (∀ item ∈ items, meaning item))
  | [] => .ok ⟨true, [], by simp⟩
  | item :: items => do
    let head ← check item
    let tail ← allChecked meaning check items
    return ⟨head.value && tail.value, head.evidence ++ tail.evidence, by
      simp only [Bool.and_eq_true, head.correct, tail.correct, List.forall_mem_cons]⟩

private def pair (c : Config) (q : Query) (header : Packet.Header) (source target : String) :
    Except String (Checked (q.PairMeaningAt c header source target)) := do
  let request := c.requestFor q.request
  let edge := c.edge header request
  match kind : q.kind with
  | .reach =>
    let result ← decideReach c.ids edge source target
    return ⟨result.value, [s!"{source} -> {target}: {result.describe}"], by
      simp only [Query.PairMeaningAt, kind]
      change result.value = true ↔ (c.model header request).Reachable source target
      rw [← c.finiteNetwork_eq_model header request]
      exact result.correct⟩
  | .isolate =>
    let result ← decideReach c.ids edge source target
    have correct : result.value = true ↔ (q.networkAt c header).Reachable source target := by
      change result.value = true ↔ (c.model header request).Reachable source target
      rw [← c.finiteNetwork_eq_model header request]
      exact result.correct
    return ⟨!result.value, [s!"{source} -> {target}: {result.describe}"], by
      simp only [Query.PairMeaningAt, kind, ← correct]
      cases result.value <;> simp⟩
  | .mediated =>
    let gateways := q.gatewaysFor c
    if endpoint : (gateways.contains source || gateways.contains target) = true then
      have member : source ∈ gateways ∨ target ∈ gateways := by simpa using endpoint
      return ⟨true, [s!"{source} -> {target}: A gateway is an endpoint."], by
        simp only [Query.PairMeaningAt, kind]
        constructor
        · intro _ bypass
          rcases member with hs | ht
          · exact bypass.1 hs
          · exact bypass.2.1 ht
        · intro _; trivial⟩
    else
      let result ← decideReach c.ids (bypassEdge edge gateways) source target
      return ⟨!result.value, [s!"{source} -> {target}: bypass {result.describe}"], by
        have correct := mediation_pair_if_correct c.ids gateways edge source target result
        simp only [Query.PairMeaningAt, kind]
        change (!result.value) = true ↔
          ¬(c.model header request).Bypass (fun node => node ∈ gateways) source target
        rw [← c.finiteNetwork_eq_model header request]
        simpa only [ite_eq_right endpoint] using correct⟩

/-- A result has a proof for every selected source and target. -/
def evaluateAt (c : Config) (q : Query) (header : Packet.Header) :
    Except String (Checked (q.MeaningAt c header)) :=
  allChecked (fun source => ∀ target ∈ c.select q.target, q.PairMeaningAt c header source target)
    (fun source => allChecked (q.PairMeaningAt c header source) (pair c q header source)
      (c.select q.target)) (c.select q.source)

def evaluate (c : Config) (q : Query) : Except String (Checked (q.Meaning c)) :=
  evaluateAt c q (c.trafficFor q.traffic)

structure Report (c : Config) where
  results : List ((q : Query) × Checked (q.Meaning c))
  covered : results.map Sigma.fst = c.requirements

namespace Report

def compliant (report : Report c) : Bool := report.results.all (fun result => result.2.value)

/-- A passing report means that every original query holds in the composed model. -/
theorem compliant_iff (report : Report c) :
    report.compliant = true ↔ ∀ query ∈ c.requirements, query.Meaning c := by
  simp only [compliant, List.all_eq_true]
  constructor
  · intro passed query member
    rw [← report.covered] at member
    obtain ⟨result, resultMember, same⟩ := List.mem_map.mp member
    subst query
    exact result.2.correct.mp (passed result resultMember)
  · intro all result member
    exact result.2.correct.mpr (all result.1 (by rw [← report.covered]; exact List.mem_map.mpr ⟨result, member, rfl⟩))

end Report

private def evaluateQueries (c : Config) : (queries : List Query) →
    Except String {results : List ((q : Query) × Checked (q.Meaning c)) //
      results.map Sigma.fst = queries}
  | [] => .ok ⟨[], rfl⟩
  | query :: queries => do
    let head ← evaluate c query
    let tail ← evaluateQueries c queries
    return ⟨⟨query, head⟩ :: tail.val, by simp only [List.map_cons, tail.property]⟩

/-- Validate the input before any query can produce a report. -/
def check (c : Config) : Except String (Report c) := do
  c.validate
  let checked ← evaluateQueries c c.requirements
  return ⟨checked.val, checked.property⟩

def kindName : Kind → String
  | .reach => "reach"
  | .isolate => "isolate"
  | .mediated => "mediated"

def render (report : Report c) : String := Id.run do
  let mut lines := [if report.compliant then "COMPLIANT" else "NONCOMPLIANT"]
  for result in report.results do
    let query := result.1
    let finding := result.2
    let pairs := (c.select query.source).length * (c.select query.target).length
    lines := lines ++ [s!"{if finding.value then "PASS" else "FAIL"} {query.id}: " ++
      s!"{kindName query.kind} {query.source.render} -> {query.target.render}; " ++
      s!"traffic={query.traffic}; request={query.request}; pairs={pairs}"]
    lines := lines ++ finding.evidence.map ("  " ++ ·)
  return String.intercalate "\n" lines

def renderJson (report : Report c) : Lean.Json :=
  Lean.Json.mkObj [
    ("schema", Lean.toJson (1 : Nat)),
    ("compliant", Lean.toJson report.compliant),
    ("semantics", Lean.toJson "Physical links, longest-prefix routes, ordered ACLs, and supplied request policies."),
    ("requirements", Lean.toJson (report.results.map fun result =>
      let query := result.1
      Lean.Json.mkObj [
        ("id", Lean.toJson query.id), ("kind", Lean.toJson (kindName query.kind)),
        ("source", Lean.toJson query.source.render), ("target", Lean.toJson query.target.render),
        ("traffic", Lean.toJson query.traffic), ("request", Lean.toJson query.request),
        ("passed", Lean.toJson result.2.value),
        ("pairs", Lean.toJson ((c.select query.source).length * (c.select query.target).length)),
        ("evidence", Lean.toJson result.2.evidence)]))]

end Check
end Netlib.DataPlane
