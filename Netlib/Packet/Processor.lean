import Netlib.Packet.Rewrite
import Netlib.Packet.ACL

namespace Netlib.Packet

universe u v

/-- A dropped packet can still leave an updated store. -/
structure Processor (State : Type u) where
  run : State → Header → State × Option Header

namespace Processor

def stateless (process : Header → Option Header) : Processor State :=
  ⟨fun state header => (state, process header)⟩

def identity : Processor State := stateless some

def drop : Processor State := stateless (fun _ => none)

def guard (test : Header → Bool) : Processor State :=
  stateless (fun header => if test header then some header else none)

def rewrite (change : Rewrite) : Processor State := stateless (some ∘ change.apply)

def acl (rules : ACL) : Processor State := guard rules.allows

/-- A drop skips later stages and retains all updates from completed stages. -/
def seq (first second : Processor State) : Processor State where
  run state header :=
    let result := first.run state header
    match result.2 with
    | none => (result.1, none)
    | some packet => second.run result.1 packet

def liftLeft (processor : Processor Left) : Processor (Left × Right) where
  run state header :=
    let result := processor.run state.1 header
    ((result.1, state.2), result.2)

def liftRight (processor : Processor Right) : Processor (Left × Right) where
  run state header :=
    let result := processor.run state.2 header
    ((state.1, result.1), result.2)

def Preserves (processor : Processor State) (property : State → Prop) : Prop :=
  ∀ state header, property state → property (processor.run state header).1

@[simp] theorem stateless_state (process : Header → Option Header) (state : State) (header : Header) :
    ((stateless process).run state header).1 = state := rfl

@[simp] theorem identity_run (state : State) (header : Header) :
    (identity : Processor State).run state header = (state, some header) := rfl

@[simp] theorem drop_run (state : State) (header : Header) :
    (drop : Processor State).run state header = (state, none) := rfl

@[simp] theorem liftLeft_right (processor : Processor Left) (state : Left × Right) (header : Header) :
    ((liftLeft processor).run state header).1.2 = state.2 := rfl

@[simp] theorem liftRight_left (processor : Processor Right) (state : Left × Right) (header : Header) :
    ((liftRight processor).run state header).1.1 = state.1 := rfl

@[simp] theorem identity_seq (processor : Processor State) : identity.seq processor = processor := by
  cases processor
  rfl

@[simp] theorem seq_identity (processor : Processor State) : processor.seq identity = processor := by
  change Processor.mk _ = Processor.mk _
  apply congrArg Processor.mk
  funext state header
  cases result : processor.run state header with
  | mk next output => cases output <;> rfl

@[simp] theorem drop_seq (processor : Processor State) : drop.seq processor = drop := rfl

theorem seq_drop_run (processor : Processor State) (state : State) (header : Header) :
    (processor.seq drop).run state header = ((processor.run state header).1, none) := by
  cases result : processor.run state header with
  | mk next output => cases output <;> simp only [seq, result, drop, stateless]

theorem seq_assoc (first second third : Processor State) :
    (first.seq second).seq third = first.seq (second.seq third) := by
  change Processor.mk _ = Processor.mk _
  apply congrArg Processor.mk
  funext state header
  simp only [seq]
  cases firstRun : first.run state header with
  | mk middle firstOutput =>
    cases firstOutput with
    | none => rfl
    | some packet =>
      cases secondRun : second.run middle packet with
      | mk next secondOutput => cases secondOutput <;> rfl

theorem seq_run_some_iff (first second : Processor State) (initial final : State)
    (input output : Header) :
    (first.seq second).run initial input = (final, some output) ↔
      ∃ middle packet, first.run initial input = (middle, some packet) ∧
        second.run middle packet = (final, some output) := by
  cases firstRun : first.run initial input with
  | mk middle firstOutput =>
    cases firstOutput <;> simp [seq, firstRun]
    constructor
    · intro finished
      exact ⟨_, _, ⟨rfl, rfl⟩, finished⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, finished⟩
      exact finished

theorem seq_run_none_iff (first second : Processor State) (initial final : State) (input : Header) :
    (first.seq second).run initial input = (final, none) ↔
      first.run initial input = (final, none) ∨
      ∃ middle packet, first.run initial input = (middle, some packet) ∧
        second.run middle packet = (final, none) := by
  cases firstRun : first.run initial input with
  | mk middle firstOutput =>
    cases firstOutput <;> simp [seq, firstRun]
    constructor
    · intro finished
      exact ⟨_, _, ⟨rfl, rfl⟩, finished⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, finished⟩
      exact finished

theorem seq_output_some_iff (first second : Processor State) (initial : State) (input output : Header) :
    ((first.seq second).run initial input).2 = some output ↔
      ∃ middle packet, first.run initial input = (middle, some packet) ∧
        (second.run middle packet).2 = some output := by
  cases firstRun : first.run initial input with
  | mk middle firstOutput =>
    cases firstOutput <;> simp [seq, firstRun]
    constructor
    · intro finished
      exact ⟨_, _, ⟨rfl, rfl⟩, finished⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, finished⟩
      exact finished

theorem seq_drop_first (first second : Processor State) (initial updated : State) (header : Header)
    (dropped : first.run initial header = (updated, none)) :
    (first.seq second).run initial header = (updated, none) := by
  simp [seq, dropped]

theorem stateless_seq (first second : Header → Option Header) :
    (stateless first : Processor State).seq (stateless second) =
      stateless (fun header => (first header).bind second) := by
  change Processor.mk _ = Processor.mk _
  apply congrArg Processor.mk
  funext state header
  cases output : first header <;> simp [stateless, output]

theorem stateless_preserves (process : Header → Option Header) (property : State → Prop) :
    (stateless process).Preserves property := fun _ _ invariant => invariant

theorem identity_preserves (property : State → Prop) : (identity : Processor State).Preserves property :=
  stateless_preserves _ _

theorem drop_preserves (property : State → Prop) : (drop : Processor State).Preserves property :=
  stateless_preserves _ _

theorem guard_preserves (test : Header → Bool) (property : State → Prop) :
    (guard test).Preserves property := stateless_preserves _ _

theorem rewrite_preserves (change : Rewrite) (property : State → Prop) :
    (rewrite change).Preserves property := stateless_preserves _ _

theorem acl_preserves (rules : ACL) (property : State → Prop) :
    (acl rules).Preserves property := stateless_preserves _ _

namespace Preserves

theorem seq {first second : Processor State} {property : State → Prop}
    (firstSafe : first.Preserves property) (secondSafe : second.Preserves property) :
    (first.seq second).Preserves property := by
  intro state header initial
  have nextSafe := firstSafe state header initial
  cases firstRun : first.run state header with
  | mk middle output =>
    have middleSafe : property middle := by simpa only [firstRun] using nextSafe
    cases output with
    | none => simpa only [Processor.seq, firstRun] using middleSafe
    | some packet => simpa only [Processor.seq, firstRun] using secondSafe middle packet middleSafe

theorem liftLeft {processor : Processor Left} {property : Left → Prop}
    (safe : processor.Preserves property) (other : Right → Prop) :
    (processor.liftLeft).Preserves (fun state => property state.1 ∧ other state.2) := by
  intro state header initial
  exact ⟨safe state.1 header initial.1, initial.2⟩

theorem liftRight {processor : Processor Right} {property : Right → Prop}
    (safe : processor.Preserves property) (other : Left → Prop) :
    (processor.liftRight).Preserves (fun state => other state.1 ∧ property state.2) := by
  intro state header initial
  exact ⟨initial.1, safe state.2 header initial.2⟩

end Preserves
end Processor
end Netlib.Packet
