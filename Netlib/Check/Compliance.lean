import Netlib.Policy.Language
import Netlib.Network.Certificate

namespace Netlib.Compliance

open Certificate

/-- Every search answer carries evidence checked against the queried graph. -/
inductive Decision (nodes : List String) (edge : String → String → Bool)
    (source target : String) where
  | reachable (trace : List String) (valid : validPath nodes edge source target trace = true)
  | isolated (region : List String) (valid : validCut nodes edge source target region = true)

namespace Decision

def value : Decision nodes edge source target → Bool
  | .reachable _ _ => true
  | .isolated _ _ => false

def describe : Decision nodes edge source target → String
  | .reachable trace _ => "path " ++ String.intercalate " -> " trace
  | .isolated region _ => "closed cut {" ++ String.intercalate ", " region ++ "}"

theorem correct (result : Decision nodes edge source target) :
    result.value = true ↔ Network.Reachable (finiteNetwork nodes edge) source target := by
  cases result with
  | reachable trace valid => exact ⟨fun _ => validPath_sound _ _ _ _ _ valid, fun _ => rfl⟩
  | isolated region valid =>
    constructor
    · intro h; cases h
    · intro h; exact False.elim (validCut_sound _ _ _ _ _ valid h)

end Decision

private def discover (nodes : List String) (edge : String → String → Bool)
    (source : String) : List (String × List String) := Id.run do
  let mut known := [(source, [source])]
  for _ in List.range nodes.length do
    let snapshot := known
    for (a, path) in snapshot do
      for b in nodes do
        if edge a b && !(known.any (fun entry => entry.1 == b)) then
          known := known ++ [(b, path ++ [b])]
  return known

def decideReach (nodes : List String) (edge : String → String → Bool)
    (source target : String) : Except String (Decision nodes edge source target) := do
  let known := discover nodes edge source
  match known.find? (fun entry => entry.1 == target) with
  | some (_, trace) =>
    if valid : validPath nodes edge source target trace = true then
      return .reachable trace valid
    else throw "internal error: path certificate rejected"
  | none =>
    let region := known.map Prod.fst
    if valid : validCut nodes edge source target region = true then
      return .isolated region valid
    else throw "internal error: cut certificate rejected (search incomplete)"

structure Finding where
  observation : Observation
  value : Bool
  pairs : Nat
  evidence : List String
  deriving Repr

private def checkedSelect (c : Config) (s : Selector) : Except String (List String) := do
  let nodes := c.select s
  if nodes.isEmpty then throw s!"selector denotes no devices: {s.render}"
  return nodes

private def observePair (c : Config) (observation : Observation)
    (gateways : List String) (traffic source target : String) : Except String (Bool × String) := do
  match observation with
  | .reach _ _ _ _ =>
    let result ← decideReach c.ids (c.edge traffic) source target
    return (result.value, s!"{source} -> {target}: {result.describe}")
  | .mediated _ _ _ _ =>
    if gateways.contains source || gateways.contains target then
      return (true, s!"{source} -> {target}: endpoint belongs to gateway group")
    else
      let bypass := fun a b => c.edge traffic a b &&
        !gateways.contains a && !gateways.contains b
      let result ← decideReach c.ids bypass source target
      return (!result.value, s!"{source} -> {target}: bypass {result.describe}")

def observe (c : Config) (observation : Observation) : Except String Finding := do
  let (s, t, traffic) := match observation with
    | .reach s t traffic _ => (s, t, traffic)
    | .mediated s t _ traffic => (s, t, traffic)
  let sources ← checkedSelect c s
  let targets ← checkedSelect c t
  let gateways ← match observation with
    | .mediated _ _ g _ => checkedSelect c g
    | _ => pure []
  let pairs := sources.flatMap (fun source => targets.map (source, ·))
  let results ← pairs.mapM (fun (source, target) =>
    observePair c observation gateways traffic source target)
  let values := results.map Prod.fst
  let value := match observation with
    | .reach _ _ _ false => values.any id
    | _ => values.all id
  return ⟨observation, value, pairs.length, results.map Prod.snd⟩

structure Report where
  findings : List Finding
  results : List (Requirement × Bool)
  deriving Repr

def Report.compliant (report : Report) : Bool := report.results.all Prod.snd

def check (c : Config) (requirements : List Requirement) : Except String Report := do
  let c ← c.validate
  let atoms := (requirements.flatMap (fun r => r.formula.atoms)).eraseDups
  let findings ← atoms.mapM (observe c)
  let valuation := fun atom => ((findings.find? (·.observation == atom)).map (·.value)).getD false
  return ⟨findings, requirements.map (fun r => (r, r.formula.eval valuation))⟩

end Netlib.Compliance
