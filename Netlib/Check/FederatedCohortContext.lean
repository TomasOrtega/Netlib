import Netlib.Check.FederatedCohortComponents
import Netlib.Check.FederatedCohortControl

/-!
# Closed admission of finite packet groups

Native checking runs for an empty group as well. Capacity rows cover exactly
the all-revision node inventory; the initial FIFO state must fit those rows.
-/

namespace Netlib.Federation.Cohort

structure Limits where
  classes : Nat
  states : Nat
  edges : Nat
  work : Nat
  deriving Repr

structure Profile where
  packets : List InFlight.Profile
  capacities : List Capacity
  limits : Limits
  deriving Repr

structure Local (input : Input) where
  profile : InFlight.Profile
  certificate : InFlight.Certified input profile

def makeContext (locals : List (Local input))
    (capacities : Vector Nat (InFlight.Control.nodes input).length) : Context input locals.length :=
  ⟨Vector.ofFn (fun index => (locals.get index).certificate.context), capacities⟩

@[simp] theorem makeContext_packet (locals : List (Local input))
    (capacities : Vector Nat (InFlight.Control.nodes input).length) (index : Fin locals.length) :
    ((makeContext locals capacities).packets.get index) = (locals.get index).certificate.context := by
  simp [makeContext, Vector.get, Fin.cast]

def capacityValue (rows : List Capacity) (node : InFlight.Node) : Nat :=
  ((rows.find? (fun row => decide (row.node = node))).map (·.slots)).getD 0

def capacityVector (input : Input) (rows : List Capacity) : Vector Nat (InFlight.Control.nodes input).length :=
  Vector.ofFn fun index => capacityValue rows (nodeAt input index)

def capacityCheck (input : Input) (rows : List Capacity) : Bool :=
  decide (rows.map (·.node)).Nodup &&
  rows.all (fun row => decide (row.node ∈ InFlight.Control.nodes input)) &&
  (List.finRange (InFlight.Control.nodes input).length).all (fun index =>
    rows.any (fun row => decide (row.node = nodeAt input index ∧
      row.slots = (capacityVector input rows).get index)))

structure CapacityFacts (input : Input) (rows : List Capacity) : Prop where
  unique : (rows.map (·.node)).Nodup
  known : ∀ row ∈ rows, row.node ∈ InFlight.Control.nodes input
  source : ∀ index, ∃ row ∈ rows, row.node = nodeAt input index ∧
    row.slots = (capacityVector input rows).get index

theorem capacityCheck_sound (input : Input) (rows : List Capacity)
    (checked : capacityCheck input rows = true) : CapacityFacts input rows := by
  have facts : ((rows.map (·.node)).Nodup ∧ ∀ row ∈ rows, row.node ∈ InFlight.Control.nodes input) ∧
      ∀ index ∈ List.finRange (InFlight.Control.nodes input).length,
        ∃ row ∈ rows, row.node = nodeAt input index ∧ row.slots = (capacityVector input rows).get index := by
    simpa only [capacityCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] using checked
  exact ⟨facts.1.1, facts.1.2, fun index => facts.2 index (List.mem_finRange index)⟩

def rawWork (input : Input) (profile : Profile) : Nat :=
  (1 + profile.capacities.length + profile.packets.length +
    (profile.packets.map (InFlight.rawRows input)).sum) ^ 2

def localWork (locals : List (Local input)) : Nat :=
  (locals.map (fun value => value.certificate.totalWork)).sum

private def buildLocals (input : Input) : (profiles : List InFlight.Profile) →
    Except String { values : List (Local input) // values.map (·.profile) = profiles }
  | [] => return ⟨[], rfl⟩
  | profile :: rest => do
    let certificate ← InFlight.certify input profile
    let tail ← buildLocals input rest
    return ⟨⟨profile, certificate⟩ :: tail.val, by simp only [List.map_cons, tail.property]⟩

structure Prepared (input : Input) (profile : Profile) where
  deployment : Deployment.Checked input
  locals : List (Local input)
  profilesEq : locals.map (·.profile) = profile.packets
  capacityFacts : CapacityFacts input profile.capacities
  unique : (makeContext locals (capacityVector input profile.capacities)).Unique
  initialGood : Control.good (makeContext locals (capacityVector input profile.capacities))
    (initialKey (makeContext locals (capacityVector input profile.capacities))) = true
  rawWithin : rawWork input profile ≤ profile.limits.work
  totalWork : Nat
  totalWorkEq : totalWork = Deployment.workEstimate input + rawWork input profile + localWork locals
  workWithin : totalWork ≤ profile.limits.work

abbrev Prepared.size (value : Prepared input profile) : Nat := value.locals.length

def Prepared.context (value : Prepared input profile) : Context input value.size :=
  makeContext value.locals (capacityVector input profile.capacities)

def Prepared.family (value : Prepared input profile) : Family value.context where
  component index :=
    ⟨(value.locals.get index).profile, (value.locals.get index).certificate,
      (makeContext_packet value.locals _ index).symm⟩

def prepare (input : Input) (profile : Profile) : Except String (Prepared input profile) := do
  if rawWithin : rawWork input profile ≤ profile.limits.work then
    let base := Deployment.workEstimate input
    if base + rawWork input profile + (profile.packets.map (·.work)).sum > profile.limits.work then
      throw "The complete native and packet admission estimate exceeds the cohort budget."
    if capacityChecked : capacityCheck input profile.capacities = true then
      if !(profile.packets.map (·.packetID)).Nodup then
        throw "The cohort contains a repeated packet ID."
      let deployment ← Deployment.certify input
      let locals ← buildLocals input profile.packets
      let context := makeContext locals.val (capacityVector input profile.capacities)
      if unique : (context.packets.toList.map (fun packet => packet.profile.packetID)).Nodup then
        if initialGood : Control.good context (initialKey context) = true then
          let total := base + rawWork input profile + localWork locals.val
          if workWithin : total ≤ profile.limits.work then
            return ⟨deployment, locals.val, locals.property, capacityCheck_sound input profile.capacities capacityChecked,
              unique, initialGood, rawWithin, total, rfl, workWithin⟩
          else throw "The actual native and packet admission estimate exceeds the cohort budget."
        else throw "The initial cohort exceeds buffer capacity or has invalid queue membership."
      else throw "The checked packet contexts repeat a packet ID."
    else throw "Capacity rows must cover each native node exactly once."
  else throw "The raw cohort input estimate exceeds the work budget."

end Netlib.Federation.Cohort
