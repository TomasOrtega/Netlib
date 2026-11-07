import Netlib.Check.TCPHandshakeRecovery

/-!
# Startup phases required by retained outputs

The inventory keeps a phase floor for each actual occurrence.
It does not identify occurrences by their packet bytes.
-/

namespace Netlib.Check.TCPHandshakeRecovery

def phaseLevel : Phase active passive → Nat
  | .idle => 0
  | .opened _ => 1
  | .answered _ => 2
  | .acknowledged .. => 3
  | .complete .. => 4

def Kind.phaseFloor : Kind → Nat
  | .syn => 1
  | .synAck | .synReplyAck => 2
  | .finalAck => 3

def Availability (state : State active passive) : Prop :=
  ∀ output ∈ state.emissions, output.kind.phaseFloor ≤ phaseLevel state.phase

theorem Availability.initial : Availability (State.initial : State active passive) := by
  intro output member
  cases member

theorem Availability.reframe (prior : Availability before)
    (phase : phaseLevel before.phase ≤ phaseLevel after.phase) (emissions : after.emissions = before.emissions) :
    Availability after := by
  intro output member
  rw [emissions] at member
  exact Nat.le_trans (prior output member) phase

theorem Availability.withTimer (prior : Availability state) (actor : Side) (timer : T.State) (valid : timer.Valid) :
    Availability (state.withTimer actor timer valid) := by
  cases actor <;> exact prior

theorem Availability.publish (prior : Availability state) (output : Emission)
    (floor : output.kind.phaseFloor ≤ phaseLevel state.phase) : Availability (publish state output).state := by
  intro selected member
  rcases List.mem_append.mp member with old | fresh
  · exact prior selected old
  · exact List.mem_singleton.mp fresh ▸ floor

theorem Availability.retainReceipt (prior : Availability effect.state) (receipt : Receipt) :
    Availability (retainReceipt effect receipt).state := prior

theorem Availability.source (prior : Availability state) (found : state.source index = some output) :
    output.kind.phaseFloor ≤ phaseLevel state.phase :=
  prior output (List.mem_of_find?_eq_some found)

end Netlib.Check.TCPHandshakeRecovery
