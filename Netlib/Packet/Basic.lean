import Std

/-!
# Packet fields

A header has addresses, a protocol number, and port numbers.
A match selects headers by these fields.
-/

namespace Netlib.Packet

/-- An address has 32 bits. -/
abbrev Address := Fin 4294967296

/-- A port number has 16 bits. -/
abbrev Port := Fin 65536

/-- A protocol number has 8 bits. -/
abbrev Protocol := Fin 256

namespace Address

/-- Reject numbers that do not fit in 32 bits. -/
def ofNat? (value : Nat) : Option Address :=
  if fits : value < 4294967296 then some ⟨value, fits⟩ else none

theorem ofNat?_some_iff (value : Nat) (address : Address) :
    ofNat? value = some address ↔ address.val = value := by
  unfold ofNat?
  split
  next fits => simp only [Option.some.injEq]; exact ⟨fun h => by cases h; rfl, Fin.ext ∘ Eq.symm⟩
  next tooLarge =>
    constructor
    · intro impossible; cases impossible
    · intro equal; have := address.isLt; omega

end Address

namespace Port

/-- Reject numbers that do not fit in 16 bits. -/
def ofNat? (value : Nat) : Option Port :=
  if fits : value < 65536 then some ⟨value, fits⟩ else none

end Port

namespace Protocol

/-- Reject numbers that do not fit in 8 bits. -/
def ofNat? (value : Nat) : Option Protocol :=
  if fits : value < 256 then some ⟨value, fits⟩ else none


def icmp : Protocol := 1
def tcp : Protocol := 6
def udp : Protocol := 17

end Protocol

/-- A header contains the packet fields used by a policy. -/
structure Header where
  source : Address
  destination : Address
  protocol : Protocol
  sourcePort : Port
  destinationPort : Port
  deriving Repr, BEq, DecidableEq

/-- An address prefix selects addresses with the same first bits. -/
structure Prefix where
  address : Address
  length : Fin 33
  deriving Repr, BEq, DecidableEq

namespace Prefix

/-- Division discards the bits outside the address prefix. -/
def contains (block : Prefix) (address : Address) : Bool :=
  decide (address.val / 2 ^ (32 - block.length.val) =
    block.address.val / 2 ^ (32 - block.length.val))

@[simp] theorem contains_address (block : Prefix) : block.contains block.address = true := by
  simp [contains]


/-- A zero-length prefix accepts every address. -/
theorem contains_zero (base address : Address) :
    (⟨base, 0⟩ : Prefix).contains address = true := by
  have size : 2 ^ (32 : Nat) = 4294967296 := by decide
  simp [contains, size, Nat.div_eq_of_lt address.isLt, Nat.div_eq_of_lt base.isLt]

/-- A full-length prefix selects one address. -/
theorem contains_full (base address : Address) :
    (⟨base, 32⟩ : Prefix).contains address = true ↔ address = base := by
  change decide (address.val / 1 = base.val / 1) = true ↔ address = base
  simp [Fin.ext_iff]

/-- A shorter prefix can contain a longer prefix. -/
def Refines (child parent : Prefix) : Prop :=
  ∀ address, child.contains address = true → parent.contains address = true

theorem refines_refl (block : Prefix) : block.Refines block := fun _ => id

theorem Refines.trans {a b c : Prefix} (ab : a.Refines b) (bc : b.Refines c) :
    a.Refines c := fun address member => bc address (ab address member)

/-- Disjoint prefixes cannot select the same address. -/
def Disjoint (left right : Prefix) : Prop :=
  ∀ address, left.contains address = true → right.contains address = false

theorem Disjoint.symm {left right : Prefix} (disjoint : left.Disjoint right) :
    right.Disjoint left := by
  intro address member
  cases leftMember : left.contains address with
  | false => rfl
  | true => have := disjoint address leftMember; simp_all

theorem disjoint_of_refines {child parent other : Prefix} (inside : child.Refines parent)
    (apart : parent.Disjoint other) : child.Disjoint other :=
  fun address member => apart address (inside address member)

end Prefix

/-- A range selects port numbers between its two bounds. -/
structure PortRange where
  first : Port
  last : Port
  deriving Repr, BEq, DecidableEq

namespace PortRange

def contains (range : PortRange) (port : Port) : Bool :=
  decide (range.first ≤ port ∧ port ≤ range.last)

@[simp] theorem contains_iff (range : PortRange) (port : Port) :
    range.contains port = true ↔ range.first ≤ port ∧ port ≤ range.last := by
  simp [contains]

def single (port : Port) : PortRange := ⟨port, port⟩

@[simp] theorem contains_single (selected port : Port) :
    (single selected).contains port = true ↔ port = selected := by
  simp only [contains_iff, single]
  exact ⟨fun ⟨left, right⟩ => Fin.le_antisymm right left,
    fun equal => by subst port; exact ⟨Fin.le_refl selected, Fin.le_refl selected⟩⟩

theorem contains_false_of_reversed (range : PortRange) (reversed : range.last < range.first)
    (port : Port) : range.contains port = false := by
  cases member : range.contains port with
  | false => rfl
  | true =>
    obtain ⟨lower, upper⟩ := (contains_iff _ _).mp member
    simp only [Fin.le_def] at lower upper
    simp only [Fin.lt_def] at reversed
    omega


/-- This range accepts every port number. -/
def all : PortRange := ⟨0, 65535⟩

@[simp] theorem contains_all (port : Port) : all.contains port = true := by
  simp only [contains_iff, all, Fin.le_def]
  have := port.isLt
  simp only [Fin.val_zero]
  constructor <;> omega

end PortRange

/-- An absent field accepts every value for that field. -/
def optionalMatch (test : α → β → Bool) (selected : Option α) (value : β) : Bool :=
  match selected with
  | none => true
  | some selection => test selection value

@[simp] theorem optionalMatch_none (test : α → β → Bool) (value : β) :
    optionalMatch test none value = true := rfl

@[simp] theorem optionalMatch_some (test : α → β → Bool) (selection : α) (value : β) :
    optionalMatch test (some selection) value = test selection value := rfl

/-- A match selects a set of packet headers. -/
structure Match where
  source : Option Prefix := none
  destination : Option Prefix := none
  protocol : Option Protocol := none
  sourcePorts : Option PortRange := none
  destinationPorts : Option PortRange := none
  deriving Repr, BEq, DecidableEq

namespace Match

def accepts (test : Match) (header : Header) : Bool :=
  optionalMatch Prefix.contains test.source header.source &&
  optionalMatch Prefix.contains test.destination header.destination &&
  optionalMatch (fun expected actual => decide (expected = actual)) test.protocol header.protocol &&
  optionalMatch PortRange.contains test.sourcePorts header.sourcePort &&
  optionalMatch PortRange.contains test.destinationPorts header.destinationPort

/-- Each selected field must accept the header. -/
def Holds (test : Match) (header : Header) : Prop :=
  (∀ block, test.source = some block → block.contains header.source = true) ∧
  (∀ block, test.destination = some block → block.contains header.destination = true) ∧
  (∀ protocol, test.protocol = some protocol → protocol = header.protocol) ∧
  (∀ range, test.sourcePorts = some range → range.contains header.sourcePort = true) ∧
  (∀ range, test.destinationPorts = some range → range.contains header.destinationPort = true)

private theorem optionalMatch_iff (test : α → β → Bool) (selected : Option α) (value : β) :
    optionalMatch test selected value = true ↔
      ∀ selection, selected = some selection → test selection value = true := by
  cases selected <;> simp [optionalMatch]

theorem accepts_iff (test : Match) (header : Header) :
    test.accepts header = true ↔ test.Holds header := by
  simp only [accepts, Bool.and_eq_true, optionalMatch_iff, decide_eq_true_eq, Holds, and_assoc]

@[simp] theorem any_accepts (header : Header) : ({} : Match).accepts header = true := rfl

/-- A stronger match accepts no extra headers. -/
def Refines (stronger weaker : Match) : Prop :=
  ∀ header, stronger.accepts header = true → weaker.accepts header = true

theorem refines_refl (test : Match) : test.Refines test := fun _ => id

theorem Refines.trans {a b c : Match} (ab : a.Refines b) (bc : b.Refines c) :
    a.Refines c := fun header member => bc header (ab header member)

theorem refines_any (test : Match) : test.Refines {} := by
  intro header _
  exact any_accepts header

end Match
end Netlib.Packet
