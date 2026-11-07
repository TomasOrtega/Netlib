import Netlib.Check.FederatedCompatibility
import Netlib.Check.DomainContractValidation
import Netlib.Network.FiniteDecision

/-!
# Queries checked against public graph bounds

Safety uses the upper graph. Availability uses the must graph, whose local
arcs carry native paths. The global checker does not inspect private routes.
-/

namespace Netlib.Federation.Queries

structure AtRole (left right : Contract) (reference : PublicRef) (role : Role) where
  node : PublicNode
  found : (contracts left right reference.side).node? reference.node = some node
  roleEq : node.role = role

theorem AtRole.known (value : AtRole left right reference role) :
    reference.node ∈ (contracts left right reference.side).ids :=
  Compatibility.nodeFound_known _ _ value.node value.found

private def checkRole (left right : Contract) (reference : PublicRef) (role : Role) :
    Except String (AtRole left right reference role) := do
  match found : (contracts left right reference.side).node? reference.node with
  | none => throw s!"Unknown public node {repr reference}."
  | some node =>
    if matched : node.role = role then return ⟨node, found, matched⟩
    else throw s!"Public node {repr reference} does not have role {repr role}."

private def verify (property : Prop) [Decidable property] (message : String) : Except String (PLift property) :=
  if checked : property then .ok ⟨checked⟩ else .error message

private def checkGateways (left right : Contract) : (gateways : List PublicRef) →
    Except String (PLift (∀ reference ∈ gateways, Nonempty (AtRole left right reference .enforcement)))
  | [] => .ok ⟨by simp⟩
  | reference :: rest => do
    let checked ← checkRole left right reference .enforcement
    let later ← checkGateways left right rest
    return ⟨by
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact ⟨checked⟩
      · exact later.down selected member⟩

structure Validated (left right : Contract) (query : Query) where
  source : AtRole left right query.source .endpoint
  target : AtRole left right query.target .endpoint
  nonempty : query.kind = .mediated → query.gateways ≠ []
  gateways : ∀ reference ∈ query.gateways, Nonempty (AtRole left right reference .enforcement)
  other : query.kind ≠ .mediated → query.gateways = []

def validate (left right : Contract) (query : Query) : Except String (Validated left right query) := do
  let source ← checkRole left right query.source .endpoint
  let target ← checkRole left right query.target .endpoint
  let gateways ← checkGateways left right query.gateways
  if kind : query.kind = .mediated then
    let nonempty ← verify (query.gateways ≠ []) s!"Query {query.id} has no enforcement node."
    return ⟨source, target, fun _ => nonempty.down, gateways.down, fun other => False.elim (other kind)⟩
  else
    let empty ← verify (query.gateways = []) s!"Only a mediated query can name enforcement nodes: {query.id}."
    return ⟨source, target, fun same => False.elim (kind same), gateways.down, fun _ => empty.down⟩

def Meaning (left right : Contract) (first second : Case) (intent : Intent) (query : Query) : Prop :=
  match query.kind with
  | .reach => (publicModel left right first second intent.borders true).Reachable query.source query.target
  | .isolate => ¬(publicModel left right first second intent.borders false).Reachable query.source query.target
  | .mediated => ¬(publicModel left right first second intent.borders false).Bypass
      (fun node => node ∈ query.gateways) query.source query.target

def WitnessValid (left right : Contract) (first second : Case) (intent : Intent) (query : Query)
    (witness : List PublicRef) : Bool :=
  match query.kind with
  | .reach => Certificate.validPath (references left right)
      (publicEdge first second intent.borders · · true) query.source query.target witness
  | .isolate => Certificate.validCut (references left right)
      (publicEdge first second intent.borders · · false) query.source query.target witness
  | .mediated => Certificate.validCut (references left right)
      (FiniteDecision.bypassEdge (publicEdge first second intent.borders · · false) query.gateways)
      query.source query.target witness

theorem witness_sound (left right : Contract) (first second : Case) (intent : Intent) (query : Query)
    (witness : List PublicRef) (valid : WitnessValid left right first second intent query witness = true) :
    Meaning left right first second intent query := by
  cases kind : query.kind with
  | reach =>
    simpa only [Meaning, kind, publicModel] using Certificate.validPath_sound _ _ _ _ _ (by simpa only [WitnessValid, kind] using valid)
  | isolate =>
    simpa only [Meaning, kind, publicModel] using Certificate.validCut_sound _ _ _ _ _ (by simpa only [WitnessValid, kind] using valid)
  | mediated =>
    have blocked := Certificate.validCut_sound (references left right)
      (FiniteDecision.bypassEdge (publicEdge first second intent.borders · · false) query.gateways)
      query.source query.target witness (by simpa only [WitnessValid, kind] using valid)
    rw [FiniteDecision.bypass_network_eq] at blocked
    simp only [Meaning, kind]
    intro bypass
    exact blocked bypass.2.2

private def evaluate (left right : Contract) (first second : Case) (intent : Intent) (query : Query) :
    Except String { witness : List PublicRef // WitnessValid left right first second intent query witness = true } := do
  let nodes := references left right
  match kind : query.kind with
  | .reach =>
    let result ← FiniteDecision.decideReach nodes (publicEdge first second intent.borders · · true)
      query.source query.target
    match result with
    | .reachable trace valid => return ⟨trace, by simpa only [WitnessValid, kind] using valid⟩
    | .isolated region _ => throw s!"Query {query.id}: no must path; cut {repr region}."
  | .isolate =>
    let result ← FiniteDecision.decideReach nodes (publicEdge first second intent.borders · · false)
      query.source query.target
    match result with
    | .reachable trace _ => throw s!"Query {query.id}: an upper path violates isolation: {repr trace}."
    | .isolated region valid => return ⟨region, by simpa only [WitnessValid, kind] using valid⟩
  | .mediated =>
    let edge := fun source target => publicEdge first second intent.borders source target false
    let result ← FiniteDecision.decideReach nodes (FiniteDecision.bypassEdge edge query.gateways)
      query.source query.target
    match result with
    | .reachable trace _ => throw s!"Query {query.id}: an upper path bypasses enforcement: {repr trace}."
    | .isolated region valid => return ⟨region, by simpa only [WitnessValid, kind] using valid⟩

structure Result (left right : Contract) (intent : Intent) (query : Query) where
  first : Case
  second : Case
  firstFound : left.case? query.caseID = some first
  secondFound : right.case? query.caseID = some second
  agreement : Compatibility.Matches first second
  validated : Validated left right query
  witness : List PublicRef
  witnessValid : WitnessValid left right first second intent query witness = true
  correct : Meaning left right first second intent query

private def checkQuery (left right : Contract) (intent : Intent)
    (compatible : Compatibility.Compatible left right intent) (query : Query) :
    Except String (Result left right intent query) := do
  match firstFound : left.case? query.caseID, secondFound : right.case? query.caseID with
  | some first, some second =>
    let validated ← validate left right query
    let result ← evaluate left right first second intent query
    return ⟨first, second, firstFound, secondFound,
      compatible.matchingCase query.caseID first second firstFound secondFound, validated, result.val, result.property, witness_sound left right first second intent query result.val result.property⟩
  | _, _ => throw s!"Query {query.id} selects an unknown public case: {query.caseID}."

structure Checked (left right : Contract) (intent : Intent) where
  results : List ((query : Query) × Result left right intent query)
  covered : results.map Sigma.fst = intent.queries

private def checkQueries (left right : Contract) (intent : Intent)
    (compatible : Compatibility.Compatible left right intent) : (queries : List Query) →
    Except String { values : List ((query : Query) × Result left right intent query) //
      values.map Sigma.fst = queries }
  | [] => .ok ⟨[], rfl⟩
  | query :: rest => do
    let result ← checkQuery left right intent compatible query
    let later ← checkQueries left right intent compatible rest
    return ⟨⟨query, result⟩ :: later.val, by simp only [List.map_cons, later.property]⟩

private def contractRows (contract : Contract) : Nat :=
  1 + contract.nodes.length + contract.cases.foldl (fun count selected =>
    count + 1 + selected.upper.length + selected.must.length) 0

def workEstimate (left right : Contract) (intent : Intent) : Nat :=
  let rows := 1 + contractRows left + contractRows right +
    intent.borders.foldl (fun count border => count + 1 + border.cases.length) 0 +
    intent.queries.foldl (fun count query => count + 1 + query.gateways.length) 0
  rows * rows + intent.queries.length * ((references left right).length + 1) ^ 4 * rows

def check (left right : Contract) (intent : Intent) (compatible : Compatibility.Compatible left right intent)
    (budget : Nat) : Except String (Checked left right intent) := do
  let _ ← left.check
  let _ ← right.check
  let _ ← verify (intent.queries ≠ []) "The federation intent has no query."
  let _ ← verify ((intent.queries.map (·.id)).Nodup) "Federation query identities must be unique."
  let _ ← verify (intent.queries.all (fun query => !query.id.isEmpty) = true) "A federation query identity is empty."
  let _ ← verify (workEstimate left right intent ≤ budget) "Public graph checks exceed the supplied work budget."
  let results ← checkQueries left right intent compatible intent.queries
  return ⟨results.val, results.property⟩

end Netlib.Federation.Queries
