import Netlib.Check.DataPlane
import Netlib.Packet.Partition

namespace Netlib.DataPlane

open Packet

namespace Config

/-- Every stored rule and route contributes to the complete packet partition. -/
def trafficPartition (c : Config) (selection : Match) : Partition :=
  Partition.ofRulesAndRoutes (c.links.map (·.rules)) (c.routes.map (·.entries)) [selection]

private theorem partition_routes (c : Config) (selection : Match) (node : String)
    (entry : Routing.Entry String) (member : entry ∈ c.tables node) :
    entry.destination ∈ (c.trafficPartition selection).destinations := by
  cases found : c.routes.find? (·.node == node) with
  | none => simp [tables, found] at member
  | some table =>
    have tableMember := List.mem_of_find?_eq_some found
    apply Partition.route_included _ _ [selection] table.entries
      (List.mem_map.mpr ⟨table, tableMember, rfl⟩) entry
    simpa [tables, found] using member

private theorem partition_rules (c : Config) (selection : Match) (source target : String)
    (rule : Rule) (member : rule ∈ c.policies source target) :
    rule.test ∈ (c.trafficPartition selection).tests := by
  cases found : c.links.find? (fun link => link.source == source && link.target == target) with
  | none => simp [policies, found] at member
  | some link =>
    have linkMember := List.mem_of_find?_eq_some found
    apply Partition.rule_included _ _ [selection] link.rules
      (List.mem_map.mpr ⟨link, linkMember, rfl⟩) rule
    simpa [policies, found] using member

theorem trafficPartition_selected (c : Config) (selection : Match) :
    selection ∈ (c.trafficPartition selection).tests := by
  simp [trafficPartition, Partition.ofRulesAndRoutes]

theorem model_representative (c : Config) (selection : Match) (header : Header)
    (request : ZeroTrust.Request String String String) :
    c.model ((c.trafficPartition selection).representative header) request = c.model header request := by
  unfold model packetModel
  rw [(c.trafficPartition selection).packetNetwork_eq c.tables c.policies
    (partition_routes c selection) (partition_rules c selection) header]

end Config

namespace Query

def TrafficMeaning (c : Config) (q : Query) (selection : Match) : Prop :=
  ∀ header, selection.accepts header = true → q.MeaningAt c header

theorem meaningAt_representative (c : Config) (q : Query) (selection : Match) (header : Header) :
    q.MeaningAt c ((c.trafficPartition selection).representative header) ↔ q.MeaningAt c header := by
  simp only [MeaningAt, PairMeaningAt, networkAt, c.model_representative selection header]

theorem trafficMeaning_iff (c : Config) (q : Query) (selection : Match) :
    (∀ header ∈ (c.trafficPartition selection).representatives,
      selection.accepts header = true → q.MeaningAt c header) ↔ q.TrafficMeaning c selection := by
  constructor
  · intro checked header selected
    apply (meaningAt_representative c q selection header).mp
    apply checked _ ((c.trafficPartition selection).representative_mem header)
    rw [(c.trafficPartition selection).match_stable selection
      (c.trafficPartition_selected selection) header]
    exact selected
  · intro checked header _ selected
    exact checked header selected

end Query

namespace Check

private def trafficCells (c : Config) (q : Query) :
    (headers : List Header) → Except String (Checked (∀ header ∈ headers, q.MeaningAt c header))
  | [] => .ok ⟨true, [], by simp⟩
  | header :: headers => do
    let head ← evaluateAt c q header
    let tail ← trafficCells c q headers
    return ⟨head.value && tail.value,
      [s!"Packet {repr header}"] ++ head.evidence ++ tail.evidence, by
      simp only [Bool.and_eq_true, head.correct, tail.correct, List.forall_mem_cons]⟩

/-- A complete selected traffic class has a proof for every packet and endpoint pair. -/
def checkTraffic (c : Config) (q : Query) (selection : Match) (budget : Nat := 100000) :
    Except String (Checked (q.TrafficMeaning c selection)) := do
  c.validate
  if !c.requirements.contains q then throw "The traffic query is not in the validated configuration."
  let partition := c.trafficPartition selection
  if partition.cellCount > budget then
    throw s!"Traffic partition needs {partition.cellCount} cells; budget is {budget}."
  let headers := partition.representatives.filter (selection.accepts ·)
  if headers.isEmpty then throw "The traffic selection contains no packet."
  let checked ← trafficCells c q headers
  return ⟨checked.value, checked.evidence, by
    rw [checked.correct, ← q.trafficMeaning_iff c selection]
    simp only [headers, List.mem_filter]
    exact ⟨fun all header member selected => all header ⟨member, selected⟩,
      fun all header member => all header member.1 member.2⟩⟩

end Check
end Netlib.DataPlane
