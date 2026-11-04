import Netlib.Packet.Processor
import Netlib.Protocol.Transition

/-!
# Shared packet-processing state

Each observed output belongs to one call in the ordered execution.
Dropped packets can still change the state used by later calls.
-/

namespace Netlib.Packet.Processor

universe u v
variable {Store : Type u} {Kind : Type v}

structure Observation (Kind : Type v) where
  kind : Kind
  packet : Header
  output : Option Header
  deriving Repr, DecidableEq

def Observation.input (event : Observation Kind) : Kind × Header := (event.kind, event.packet)

def transition (programs : Kind → Processor Store) :
    Protocol.Transition Store (Observation Kind) where
  step before event after := (programs event.kind).run before event.packet = (after, event.output)

def execute (programs : Kind → Processor Store) (initial : Store) :
    List (Kind × Header) → Store × List (Observation Kind)
  | [] => (initial, [])
  | (kind, packet) :: inputs =>
    let result := (programs kind).run initial packet
    let rest := execute programs result.1 inputs
    (rest.1, ⟨kind, packet, result.2⟩ :: rest.2)

theorem execute_covered (programs : Kind → Processor Store) (initial : Store)
    (inputs : List (Kind × Header)) :
    (execute programs initial inputs).2.map Observation.input = inputs := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input inputs ih =>
    rcases input with ⟨kind, packet⟩
    simp only [execute, List.map_cons, Observation.input, ih]

theorem execute_trace (programs : Kind → Processor Store) (initial : Store)
    (inputs : List (Kind × Header)) :
    (transition programs).Trace initial (execute programs initial inputs).2
      (execute programs initial inputs).1 := by
  induction inputs generalizing initial with
  | nil => exact .nil initial
  | cons input inputs ih =>
    rcases input with ⟨kind, packet⟩
    exact .cons rfl (ih ((programs kind).run initial packet).1)

theorem trace_eq_execute (programs : Kind → Processor Store)
    {before after : Store} {events : List (Observation Kind)}
    (execution : (transition programs).Trace before events after) :
    execute programs before (events.map Observation.input) = (after, events) := by
  induction execution with
  | nil => rfl
  | @cons before middle after event events edge _ ih =>
    change (programs event.kind).run before event.packet = (middle, event.output) at edge
    cases event
    simp only [List.map_cons, Observation.input, execute, edge, ih]

theorem transition_preserves (programs : Kind → Processor Store) (property : Store → Prop)
    (preserved : ∀ kind, (programs kind).Preserves property) :
    (transition programs).Invariant property := by
  intro before event after safe edge
  have result := preserved event.kind before event.packet safe
  change (programs event.kind).run before event.packet = (after, event.output) at edge
  simpa only [edge] using result

theorem execute_preserves (programs : Kind → Processor Store) (property : Store → Prop)
    (preserved : ∀ kind, (programs kind).Preserves property) (initial : Store)
    (safe : property initial) (inputs : List (Kind × Header)) :
    property (execute programs initial inputs).1 :=
  (transition_preserves programs property preserved).trace safe (execute_trace programs initial inputs)

end Netlib.Packet.Processor
