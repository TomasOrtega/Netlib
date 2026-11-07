import Netlib.Model.FederatedJson

namespace Netlib.Federation.InFlight.JointPartition

open Packet

def revisions (input : Input) : List Revision := input.left.versions ++ input.right.versions

private def policies (input : Input) : List ACL :=
  (revisions input).flatMap fun revision => revision.snapshot.compile.links.map (·.rules)

private def routes (input : Input) : List (List (Routing.Entry String)) :=
  (revisions input).flatMap fun revision => revision.snapshot.compile.routes.map (·.entries)

/-- One classification covers every native revision on both sides. -/
def partition (input : Input) (selected : Case) : Partition :=
  Partition.ofRulesAndRoutes (policies input) (routes input) [selected.selector]

def fullCount (input : Input) (selected : Case) : Nat := (partition input selected).cellCount

theorem selector_included (input : Input) (selected : Case) :
    selected.selector ∈ (partition input selected).tests := by
  simp [partition, Partition.ofRulesAndRoutes]

theorem routes_included (input : Input) (selected : Case) (revision : Revision)
    (member : revision ∈ revisions input) (node : String) (entry : Routing.Entry String)
    (present : entry ∈ revision.snapshot.compile.tables node) :
    entry.destination ∈ (partition input selected).destinations := by
  cases found : revision.snapshot.compile.routes.find? (·.node == node) with
  | none => simp [DataPlane.Config.tables, found] at present
  | some table =>
    have tableMember := List.mem_of_find?_eq_some found
    exact Partition.route_included (policies input) (routes input) [selected.selector]
      table.entries (by
        exact List.mem_flatMap.mpr ⟨revision, member,
          List.mem_map.mpr ⟨table, tableMember, rfl⟩⟩) entry (by
        simpa [DataPlane.Config.tables, found] using present)

theorem rules_included (input : Input) (selected : Case) (revision : Revision)
    (member : revision ∈ revisions input) (source target : String) (rule : Rule)
    (present : rule ∈ revision.snapshot.compile.policies source target) :
    rule.test ∈ (partition input selected).tests := by
  cases found : revision.snapshot.compile.links.find?
      (fun link => link.source == source && link.target == target) with
  | none => simp [DataPlane.Config.policies, found] at present
  | some link =>
    have linkMember := List.mem_of_find?_eq_some found
    exact Partition.rule_included (policies input) (routes input) [selected.selector]
      link.rules (by
        exact List.mem_flatMap.mpr ⟨revision, member,
          List.mem_map.mpr ⟨link, linkMember, rfl⟩⟩) rule (by
        simpa [DataPlane.Config.policies, found] using present)

theorem compiledEdge_representative (input : Input) (selected : Case) (revision : Revision)
    (member : revision ∈ revisions input) (header : Header)
    (request : ZeroTrust.Request String String String) (source target : String) :
    revision.snapshot.compile.edge ((partition input selected).representative header) request source target =
      revision.snapshot.compile.edge header request source target := by
  unfold DataPlane.Config.edge
  rw [(partition input selected).nextHop_stable _
    (routes_included input selected revision member source) header,
    (partition input selected).acl_allows_stable _
      (rules_included input selected revision member source target) header]

theorem nativeEdge_representative (input : Input) (selected : Case) (revision : Revision)
    (member : revision ∈ revisions input) (header : Header)
    (request : ZeroTrust.Request String String String) (source target : String) :
    revision.snapshot.nativeEdge ((partition input selected).representative header) request source target =
      revision.snapshot.nativeEdge header request source target := by
  rw [← revision.snapshot.edge_correct, ← revision.snapshot.edge_correct]
  exact compiledEdge_representative input selected revision member header request source target

theorem compiledModel_representative (input : Input) (selected : Case) (revision : Revision)
    (member : revision ∈ revisions input) (header : Header)
    (request : ZeroTrust.Request String String String) :
    revision.snapshot.compile.model ((partition input selected).representative header) request =
      revision.snapshot.compile.model header request := by
  unfold DataPlane.Config.model DataPlane.Config.packetModel
  rw [(partition input selected).packetNetwork_eq _ _
    (routes_included input selected revision member)
    (rules_included input selected revision member) header]

theorem nativeModel_representative (input : Input) (selected : Case) (revision : Revision)
    (member : revision ∈ revisions input) (header : Header)
    (request : ZeroTrust.Request String String String) :
    revision.snapshot.nativeModel ((partition input selected).representative header) request =
      revision.snapshot.nativeModel header request := by
  exact (revision.snapshot.model_correct _ _).symm.trans
    ((compiledModel_representative input selected revision member header request).trans
      (revision.snapshot.model_correct header request))

def sourcePoints (input : Input) (selected : Case) : List Address :=
  (Interval.points 4294967296 (partition input selected).sourceBoundaries).filter
    (optionalMatch Prefix.contains selected.selector.source)

def destinationPoints (input : Input) (selected : Case) : List Address :=
  (Interval.points 4294967296 (partition input selected).destinationBoundaries).filter
    (optionalMatch Prefix.contains selected.selector.destination)

def protocolPoints (input : Input) (selected : Case) : List Protocol :=
  (Interval.points 256 (partition input selected).protocolBoundaries).filter
    (optionalMatch (fun expected actual => decide (expected = actual)) selected.selector.protocol)

def sourcePortPoints (input : Input) (selected : Case) : List Port :=
  (Interval.points 65536 (partition input selected).sourcePortBoundaries).filter
    (optionalMatch PortRange.contains selected.selector.sourcePorts)

def destinationPortPoints (input : Input) (selected : Case) : List Port :=
  (Interval.points 65536 (partition input selected).destinationPortBoundaries).filter
    (optionalMatch PortRange.contains selected.selector.destinationPorts)

private def product (sources destinations : List Address) (protocols : List Protocol)
    (sourcePorts destinationPorts : List Port) : List Header :=
  sources.flatMap fun source =>
  destinations.flatMap fun destination =>
  protocols.flatMap fun protocol =>
  sourcePorts.flatMap fun sourcePort =>
  destinationPorts.map fun destinationPort => ⟨source, destination, protocol, sourcePort, destinationPort⟩

/-- Filter each field before constructing the Cartesian product. -/
def selectedHeaders (input : Input) (selected : Case) : List Header :=
  product (sourcePoints input selected) (destinationPoints input selected)
    (protocolPoints input selected) (sourcePortPoints input selected) (destinationPortPoints input selected)

def selectedCount (input : Input) (selected : Case) : Nat :=
  (sourcePoints input selected).length * (destinationPoints input selected).length *
    (protocolPoints input selected).length * (sourcePortPoints input selected).length *
    (destinationPortPoints input selected).length

private theorem product_mem (sources destinations : List Address) (protocols : List Protocol)
    (sourcePorts destinationPorts : List Port) (header : Header) :
    header ∈ product sources destinations protocols sourcePorts destinationPorts ↔
      header.source ∈ sources ∧ header.destination ∈ destinations ∧ header.protocol ∈ protocols ∧
        header.sourcePort ∈ sourcePorts ∧ header.destinationPort ∈ destinationPorts := by
  simp only [product, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨source, sourceMember, destination, destinationMember, protocol, protocolMember,
      sourcePort, sourcePortMember, destinationPort, destinationPortMember, same⟩
    subst header
    exact ⟨sourceMember, destinationMember, protocolMember, sourcePortMember, destinationPortMember⟩
  · rintro ⟨sourceMember, destinationMember, protocolMember, sourcePortMember, destinationPortMember⟩
    exact ⟨header.source, sourceMember, header.destination, destinationMember, header.protocol,
      protocolMember, header.sourcePort, sourcePortMember, header.destinationPort, destinationPortMember, rfl⟩

theorem selectedHeaders_mem_iff (input : Input) (selected : Case) (header : Header) :
    header ∈ selectedHeaders input selected ↔
      header ∈ (partition input selected).representatives ∧ selected.selector.accepts header = true := by
  change header ∈ product _ _ _ _ _ ↔ header ∈ product _ _ _ _ _ ∧ _
  simp only [product_mem, sourcePoints, destinationPoints, protocolPoints,
    sourcePortPoints, destinationPortPoints, List.mem_filter, Match.accepts, Bool.and_eq_true, and_assoc]
  constructor
  · rintro ⟨sourceMember, sourceAccepted, destinationMember, destinationAccepted,
      protocolMember, protocolAccepted, sourcePortMember, sourcePortAccepted,
      destinationPortMember, destinationPortAccepted⟩
    exact ⟨sourceMember, destinationMember, protocolMember, sourcePortMember, destinationPortMember,
      sourceAccepted, destinationAccepted, protocolAccepted, sourcePortAccepted, destinationPortAccepted⟩
  · rintro ⟨sourceMember, destinationMember, protocolMember, sourcePortMember, destinationPortMember,
      sourceAccepted, destinationAccepted, protocolAccepted, sourcePortAccepted, destinationPortAccepted⟩
    exact ⟨sourceMember, sourceAccepted, destinationMember, destinationAccepted,
      protocolMember, protocolAccepted, sourcePortMember, sourcePortAccepted,
      destinationPortMember, destinationPortAccepted⟩

theorem selectedHeaders_accepted (input : Input) (selected : Case) (header : Header)
    (member : header ∈ selectedHeaders input selected) : selected.selector.accepts header = true :=
  ((selectedHeaders_mem_iff input selected header).mp member).2

theorem selected_representative_mem (input : Input) (selected : Case) (header : Header)
    (accepted : selected.selector.accepts header = true) :
    (partition input selected).representative header ∈ selectedHeaders input selected := by
  apply (selectedHeaders_mem_iff input selected _).mpr
  refine ⟨(partition input selected).representative_mem header, ?_⟩
  rw [(partition input selected).match_stable selected.selector (selector_included input selected) header]
  exact accepted

private theorem length_flatMap_constant (values : List α) (f : α → List β) (size : Nat)
    (same : ∀ value ∈ values, (f value).length = size) :
    (values.flatMap f).length = values.length * size := by
  induction values with
  | nil => simp
  | cons value values ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [same value (by simp), ih (fun next member => same next (List.mem_cons_of_mem _ member))]
    simp [Nat.add_mul, Nat.add_comm]

theorem selectedHeaders_length (input : Input) (selected : Case) :
    (selectedHeaders input selected).length = selectedCount input selected := by
  have counted : (selectedHeaders input selected).length =
      (sourcePoints input selected).length * ((destinationPoints input selected).length *
      ((protocolPoints input selected).length * ((sourcePortPoints input selected).length *
      (destinationPortPoints input selected).length))) := by
    apply length_flatMap_constant
    intro _ _
    apply length_flatMap_constant
    intro _ _
    apply length_flatMap_constant
    intro _ _
    apply length_flatMap_constant
    intro _ _
    exact List.length_map _
  simpa only [selectedCount, Nat.mul_assoc] using counted

theorem forall_selected_iff (input : Input) (selected : Case) (meaning : Header → Prop)
    (stable : ∀ header, meaning ((partition input selected).representative header) ↔ meaning header) :
    (∀ header ∈ selectedHeaders input selected, meaning header) ↔
      ∀ header, selected.selector.accepts header = true → meaning header := by
  constructor
  · intro checked header accepted
    exact (stable header).mp (checked _ (selected_representative_mem input selected header accepted))
  · intro checked header member
    exact checked header (selectedHeaders_accepted input selected header member)

end Netlib.Federation.InFlight.JointPartition
