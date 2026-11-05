import Netlib.Packet.Interval
import Netlib.Routing.Basic

namespace Netlib.Packet

namespace Prefix

def width (block : Prefix) : Nat := 2 ^ (32 - block.length.val)

def lower (block : Prefix) : Nat := block.address.val / block.width * block.width

def boundaries (block : Prefix) : List Nat := [block.lower, block.lower + block.width]

theorem contains_iff_interval (block : Prefix) (address : Address) :
    block.contains address = true ↔
      block.lower ≤ address.val ∧ address.val < block.lower + block.width := by
  have positive : 0 < block.width := Nat.two_pow_pos _
  simp only [contains, decide_eq_true_eq]
  change (address.val / block.width = block.address.val / block.width) ↔ _
  rw [Nat.div_eq_iff positive]
  simp only [lower, width] at *
  omega

end Prefix

namespace PortRange

def boundaries (range : PortRange) : List Nat := [range.first.val, range.last.val + 1]

end PortRange

/-- The predicates that can change a forwarding decision. -/
structure Partition where
  tests : List Match := []
  destinations : List Prefix := []
  deriving Repr

namespace Partition

/-- Collect every rule and route that can affect the selected graph. -/
def ofRulesAndRoutes (policies : List ACL) (routes : List (List (Routing.Entry Node)))
    (extraTests : List Match := []) : Partition where
  tests := policies.flatten.map (·.test) ++ extraTests
  destinations := routes.flatten.map (·.destination)

theorem rule_included (policies : List ACL) (routes : List (List (Routing.Entry Node)))
    (extraTests : List Match) (rules : ACL) (policyMember : rules ∈ policies)
    (rule : Rule) (ruleMember : rule ∈ rules) :
    rule.test ∈ (ofRulesAndRoutes policies routes extraTests).tests := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨rule, List.mem_flatten.mpr ⟨rules, policyMember, ruleMember⟩, rfl⟩

theorem route_included (policies : List ACL) (routes : List (List (Routing.Entry Node)))
    (extraTests : List Match) (entries : List (Routing.Entry Node)) (tableMember : entries ∈ routes)
    (entry : Routing.Entry Node) (entryMember : entry ∈ entries) :
    entry.destination ∈ (ofRulesAndRoutes policies routes extraTests).destinations :=
  List.mem_map.mpr ⟨entry, List.mem_flatten.mpr ⟨entries, tableMember, entryMember⟩, rfl⟩

private def prefixCuts (selection : Option Prefix) : List Nat :=
  selection.toList.flatMap Prefix.boundaries

private def portCuts (selection : Option PortRange) : List Nat :=
  selection.toList.flatMap PortRange.boundaries

private def protocolCuts (selection : Option Protocol) : List Nat :=
  selection.toList.flatMap (fun protocol => [protocol.val, protocol.val + 1])

def sourceBoundaries (partition : Partition) : List Nat :=
  partition.tests.flatMap (fun test => prefixCuts test.source)

def destinationBoundaries (partition : Partition) : List Nat :=
  partition.tests.flatMap (fun test => prefixCuts test.destination) ++
    partition.destinations.flatMap Prefix.boundaries

def protocolBoundaries (partition : Partition) : List Nat :=
  partition.tests.flatMap (fun test => protocolCuts test.protocol)

def sourcePortBoundaries (partition : Partition) : List Nat :=
  partition.tests.flatMap (fun test => portCuts test.sourcePorts)

def destinationPortBoundaries (partition : Partition) : List Nat :=
  partition.tests.flatMap (fun test => portCuts test.destinationPorts)

def representative (partition : Partition) (header : Header) : Header where
  source := Interval.representative partition.sourceBoundaries header.source
  destination := Interval.representative partition.destinationBoundaries header.destination
  protocol := Interval.representative partition.protocolBoundaries header.protocol
  sourcePort := Interval.representative partition.sourcePortBoundaries header.sourcePort
  destinationPort := Interval.representative partition.destinationPortBoundaries header.destinationPort

/-- One header per Cartesian cell. No field is exhaustively enumerated. -/
def representatives (partition : Partition) : List Header :=
  (Interval.points 4294967296 partition.sourceBoundaries).flatMap fun source =>
  (Interval.points 4294967296 partition.destinationBoundaries).flatMap fun destination =>
  (Interval.points 256 partition.protocolBoundaries).flatMap fun protocol =>
  (Interval.points 65536 partition.sourcePortBoundaries).flatMap fun sourcePort =>
  (Interval.points 65536 partition.destinationPortBoundaries).map fun destinationPort =>
    ⟨source, destination, protocol, sourcePort, destinationPort⟩

/-- The Cartesian product can be large even when each field has few cells. -/
def cellCount (partition : Partition) : Nat :=
  (Interval.points 4294967296 partition.sourceBoundaries).length *
  (Interval.points 4294967296 partition.destinationBoundaries).length *
  (Interval.points 256 partition.protocolBoundaries).length *
  (Interval.points 65536 partition.sourcePortBoundaries).length *
  (Interval.points 65536 partition.destinationPortBoundaries).length

private theorem length_flatMap_constant (values : List α) (f : α → List β) (size : Nat)
    (same : ∀ value ∈ values, (f value).length = size) :
    (values.flatMap f).length = values.length * size := by
  induction values with
  | nil => simp
  | cons value values ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [same value (by simp), ih (fun next member => same next (List.mem_cons_of_mem _ member))]
    simp [Nat.add_mul, Nat.add_comm]

theorem representatives_length (partition : Partition) :
    partition.representatives.length = partition.cellCount := by
  have counted : partition.representatives.length =
      (Interval.points 4294967296 partition.sourceBoundaries).length *
      ((Interval.points 4294967296 partition.destinationBoundaries).length *
      ((Interval.points 256 partition.protocolBoundaries).length *
      ((Interval.points 65536 partition.sourcePortBoundaries).length *
      (Interval.points 65536 partition.destinationPortBoundaries).length))) := by
    apply length_flatMap_constant
    intro _ _
    apply length_flatMap_constant
    intro _ _
    apply length_flatMap_constant
    intro _ _
    apply length_flatMap_constant
    intro _ _
    exact List.length_map _
  simpa only [cellCount, Nat.mul_assoc] using counted

theorem representative_mem (partition : Partition) (header : Header) :
    partition.representative header ∈ partition.representatives := by
  simp only [representatives]
  apply List.mem_flatMap.mpr
  refine ⟨_, Interval.representative_mem_points _ header.source, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨_, Interval.representative_mem_points _ header.destination, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨_, Interval.representative_mem_points _ header.protocol, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨_, Interval.representative_mem_points _ header.sourcePort, ?_⟩
  apply List.mem_map.mpr
  exact ⟨_, Interval.representative_mem_points _ header.destinationPort, rfl⟩

private theorem prefix_stable (cuts : List Nat) (block : Prefix) (address : Address)
    (included : ∀ boundary ∈ block.boundaries, boundary ∈ cuts) :
    block.contains (Interval.representative cuts address) = block.contains address := by
  apply Bool.eq_iff_iff.mpr
  rw [Prefix.contains_iff_interval, Prefix.contains_iff_interval]
  exact and_congr
    (Interval.representative_le_iff _ _ _ (included _ (by simp [Prefix.boundaries])))
    (Interval.representative_lt_iff _ _ _ (included _ (by simp [Prefix.boundaries])))

private theorem port_stable (cuts : List Nat) (range : PortRange) (port : Port)
    (included : ∀ boundary ∈ range.boundaries, boundary ∈ cuts) :
    range.contains (Interval.representative cuts port) = range.contains port := by
  apply Bool.eq_iff_iff.mpr
  simp only [PortRange.contains_iff, Fin.le_def]
  have lower := Interval.representative_le_iff cuts port range.first.val
    (included _ (by simp [PortRange.boundaries]))
  have upper := Interval.representative_lt_iff cuts port (range.last.val + 1)
    (included _ (by simp [PortRange.boundaries]))
  omega

private theorem protocol_stable (cuts : List Nat) (protocol value : Protocol)
    (lower : protocol.val ∈ cuts) (upper : protocol.val + 1 ∈ cuts) :
    decide (protocol = Interval.representative cuts value) = decide (protocol = value) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Fin.ext_iff]
  have left := Interval.representative_le_iff cuts value protocol.val lower
  have right := Interval.representative_lt_iff cuts value (protocol.val + 1) upper
  omega

theorem match_stable (partition : Partition) (test : Match) (member : test ∈ partition.tests)
    (header : Header) :
    test.accepts (partition.representative header) = test.accepts header := by
  have source : optionalMatch Prefix.contains test.source
      (partition.representative header).source =
      optionalMatch Prefix.contains test.source header.source := by
    cases selected : test.source with
    | none => rfl
    | some block =>
      apply prefix_stable
      intro boundary present
      exact List.mem_flatMap.mpr ⟨test, member, by simp [prefixCuts, selected, present]⟩
  have destination : optionalMatch Prefix.contains test.destination
      (partition.representative header).destination =
      optionalMatch Prefix.contains test.destination header.destination := by
    cases selected : test.destination with
    | none => rfl
    | some block =>
      apply prefix_stable
      intro boundary present
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨test, member, by simp [prefixCuts, selected, present]⟩
  have protocol : optionalMatch (fun expected actual => decide (expected = actual)) test.protocol
      (partition.representative header).protocol =
      optionalMatch (fun expected actual => decide (expected = actual)) test.protocol header.protocol := by
    cases selected : test.protocol with
    | none => rfl
    | some protocol =>
      apply protocol_stable
      all_goals exact List.mem_flatMap.mpr ⟨test, member, by simp [protocolCuts, selected]⟩
  have sourcePort : optionalMatch PortRange.contains test.sourcePorts
      (partition.representative header).sourcePort =
      optionalMatch PortRange.contains test.sourcePorts header.sourcePort := by
    cases selected : test.sourcePorts with
    | none => rfl
    | some range =>
      apply port_stable
      intro boundary present
      exact List.mem_flatMap.mpr ⟨test, member, by simp [portCuts, selected, present]⟩
  have destinationPort : optionalMatch PortRange.contains test.destinationPorts
      (partition.representative header).destinationPort =
      optionalMatch PortRange.contains test.destinationPorts header.destinationPort := by
    cases selected : test.destinationPorts with
    | none => rfl
    | some range =>
      apply port_stable
      intro boundary present
      exact List.mem_flatMap.mpr ⟨test, member, by simp [portCuts, selected, present]⟩
  simp only [Match.accepts, source, destination, protocol, sourcePort, destinationPort]

theorem destination_stable (partition : Partition) (block : Prefix)
    (member : block ∈ partition.destinations) (header : Header) :
    block.contains (partition.representative header).destination =
      block.contains header.destination := by
  apply prefix_stable
  intro boundary present
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨block, member, present⟩

theorem acl_lookup_stable (partition : Partition) (rules : ACL)
    (included : ∀ rule ∈ rules, rule.test ∈ partition.tests) (header : Header) :
    rules.lookup (partition.representative header) = rules.lookup header := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
    simp only [ACL.lookup, partition.match_stable rule.test (included rule (by simp)) header]
    rw [ih (fun next member => included next (List.mem_cons_of_mem _ member))]

theorem acl_allows_stable (partition : Partition) (rules : ACL)
    (included : ∀ rule ∈ rules, rule.test ∈ partition.tests) (header : Header) :
    rules.allows (partition.representative header) = rules.allows header := by
  unfold ACL.allows ACL.evaluate
  rw [partition.acl_lookup_stable rules included header]

theorem route_lookup_stable (partition : Partition) (entries : List (Routing.Entry Node))
    (included : ∀ entry ∈ entries, entry.destination ∈ partition.destinations) (header : Header) :
    Routing.lookup entries (partition.representative header).destination =
      Routing.lookup entries header.destination := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [Routing.lookup,
      partition.destination_stable entry.destination (included entry (by simp)) header]
    rw [ih (fun next member => included next (List.mem_cons_of_mem _ member))]

theorem nextHop_stable (partition : Partition) (entries : List (Routing.Entry Node))
    (included : ∀ entry ∈ entries, entry.destination ∈ partition.destinations) (header : Header) :
    Routing.nextHop entries (partition.representative header).destination =
      Routing.nextHop entries header.destination := by
  simp only [Routing.nextHop, partition.route_lookup_stable entries included header]

theorem packetNetwork_eq (partition : Partition) (tables : Node → List (Routing.Entry Node))
    (policies : Node → Node → ACL)
    (routesIncluded : ∀ node entry, entry ∈ tables node → entry.destination ∈ partition.destinations)
    (rulesIncluded : ∀ source target rule, rule ∈ policies source target → rule.test ∈ partition.tests)
    (header : Header) :
    Routing.packetNetwork tables policies (partition.representative header) =
      Routing.packetNetwork tables policies header := by
  change Network.mk _ = Network.mk _
  apply congrArg Network.mk
  funext source target
  apply propext
  change (Routing.nextHop (tables source) (partition.representative header).destination = some target ∧
    (policies source target).allows (partition.representative header) = true) ↔
      (Routing.nextHop (tables source) header.destination = some target ∧
        (policies source target).allows header = true)
  rw [partition.nextHop_stable _ (routesIncluded source) header,
    partition.acl_allows_stable _ (rulesIncluded source target) header]

/-- A finite check covers all headers when classification preserves its predicate. -/
def check (partition : Partition) (predicate : Header → Bool) : Bool :=
  partition.representatives.all predicate

/-- Count the product before enumeration. An exhausted budget gives no answer. -/
def checkBudget (partition : Partition) (predicate : Header → Bool) (budget : Nat) : Except String Bool :=
  if partition.cellCount ≤ budget then .ok (partition.check predicate)
  else .error "Packet partition exceeds its cell budget."

theorem checkBudget_within (partition : Partition) (predicate : Header → Bool) (budget : Nat)
    (value : Bool) (completed : partition.checkBudget predicate budget = .ok value) :
    partition.representatives.length ≤ budget := by
  rw [partition.representatives_length]
  unfold checkBudget at completed
  split at completed
  · assumption
  · cases completed

theorem check_iff (partition : Partition) (predicate : Header → Bool)
    (stable : ∀ header, predicate (partition.representative header) = predicate header) :
    partition.check predicate = true ↔ ∀ header, predicate header = true := by
  rw [check, List.all_eq_true]
  constructor
  · intro checked header
    rw [← stable header]
    exact checked _ (partition.representative_mem header)
  · intro checked header _
    exact checked header

theorem checkBudget_correct (partition : Partition) (predicate : Header → Bool) (budget : Nat)
    (stable : ∀ header, predicate (partition.representative header) = predicate header)
    (value : Bool) (completed : partition.checkBudget predicate budget = .ok value) :
    value = true ↔ ∀ header, predicate header = true := by
  unfold checkBudget at completed
  split at completed
  · cases completed
    exact partition.check_iff predicate stable
  · cases completed

/-- Any graph property transfers from the finite cells to the complete header space. -/
theorem forall_selected_iff (partition : Partition) (tables : Node → List (Routing.Entry Node))
    (policies : Node → Node → ACL)
    (routesIncluded : ∀ node entry, entry ∈ tables node → entry.destination ∈ partition.destinations)
    (rulesIncluded : ∀ source target rule, rule ∈ policies source target → rule.test ∈ partition.tests)
    (selection : Match) (selected : selection ∈ partition.tests) (property : Network Node → Prop) :
    (∀ header ∈ partition.representatives, selection.accepts header = true →
      property (Routing.packetNetwork tables policies header)) ↔
    ∀ header, selection.accepts header = true → property (Routing.packetNetwork tables policies header) := by
  constructor
  · intro checked header accepted
    rw [← partition.packetNetwork_eq tables policies routesIncluded rulesIncluded header]
    apply checked _ (partition.representative_mem header)
    rw [partition.match_stable selection selected header]
    exact accepted
  · intro checked header _ accepted
    exact checked header accepted

/-- Decide policy strengthening over every IPv4 header. -/
def checkACLRefines (stronger weaker : ACL) : Bool :=
  let partition := ofRulesAndRoutes [stronger, weaker] ([] : List (List (Routing.Entry Unit)))
  partition.check fun header => decide (stronger.allows header = true → weaker.allows header = true)

def checkACLRefinesBudget (stronger weaker : ACL) (budget : Nat := 100000) : Except String Bool :=
  let partition := ofRulesAndRoutes [stronger, weaker] ([] : List (List (Routing.Entry Unit)))
  partition.checkBudget
    (fun header => decide (stronger.allows header = true → weaker.allows header = true)) budget

theorem checkACLRefines_iff (stronger weaker : ACL) :
    checkACLRefines stronger weaker = true ↔ stronger.Refines weaker := by
  let partition := ofRulesAndRoutes [stronger, weaker] ([] : List (List (Routing.Entry Unit)))
  have strongerStable (header : Header) :
      stronger.allows (partition.representative header) = stronger.allows header :=
    partition.acl_allows_stable stronger
      (fun rule member => rule_included _ _ [] stronger (by simp) rule member) header
  have weakerStable (header : Header) :
      weaker.allows (partition.representative header) = weaker.allows header :=
    partition.acl_allows_stable weaker
      (fun rule member => rule_included _ _ [] weaker (by simp) rule member) header
  have result := partition.check_iff
    (fun header => decide (stronger.allows header = true → weaker.allows header = true))
    (fun header => by rw [strongerStable header, weakerStable header])
  exact result.trans (by simp only [decide_eq_true_eq, ACL.Refines])

theorem checkACLRefinesBudget_correct (stronger weaker : ACL) (budget : Nat) (value : Bool)
    (completed : checkACLRefinesBudget stronger weaker budget = .ok value) :
    value = true ↔ stronger.Refines weaker := by
  unfold checkACLRefinesBudget checkBudget at completed
  dsimp only at completed
  split at completed
  · cases completed
    exact checkACLRefines_iff stronger weaker
  · cases completed

/-- Return a concrete packet when a policy permits traffic outside its contract. -/
def aclCounterexample (stronger weaker : ACL) : Option Header :=
  let partition := ofRulesAndRoutes [stronger, weaker] ([] : List (List (Routing.Entry Unit)))
  partition.representatives.find? fun header => stronger.allows header && !weaker.allows header

theorem aclCounterexample_sound (stronger weaker : ACL) (header : Header)
    (found : aclCounterexample stronger weaker = some header) :
    stronger.allows header = true ∧ weaker.allows header = false := by
  have selected := List.find?_some found
  simpa using selected

theorem aclCounterexample_none_iff (stronger weaker : ACL) :
    aclCounterexample stronger weaker = none ↔ stronger.Refines weaker := by
  rw [← checkACLRefines_iff]
  simp only [aclCounterexample, checkACLRefines, check, List.find?_eq_none, List.all_eq_true]
  constructor
  · intro none header member
    have := none header member
    cases left : stronger.allows header <;> cases right : weaker.allows header <;> simp_all
  · intro checked header member
    have := checked header member
    cases left : stronger.allows header <;> cases right : weaker.allows header <;> simp_all

end Partition
end Netlib.Packet
