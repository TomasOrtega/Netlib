import Netlib.Check.TCPHandshakeRecoveryFacts

/-!
# Reachable startup recovery state

Both timers keep the source of their original control.
Accepted empty ACKs retain the actual window markers and local operations.
Each timer template joins an actual emission in the same trace.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : Handshake.Local}
variable {state startState final : State active passive} {actual : Step active passive}
variable {events : List Event} {steps : List (Step active passive)}

structure Invariant (state : State active passive) : Prop where
  history : History state
  phase : PhaseInvariant state

theorem Invariant.initial : Invariant (State.initial (active := active) (passive := passive)) :=
  ⟨History.initial, PhaseInvariant.initial⟩

theorem Invariant.step (prior : Invariant actual.before) : Invariant actual.result.state :=
  ⟨History.step actual prior.history, actual.phase_invariant prior.phase⟩

theorem Trace.invariant (trace : Trace startState events steps final) (prior : Invariant startState) : Invariant final := by
  induction trace with
  | done => exact prior
  | next actual tail ih => exact ih prior.step

theorem Reachable.invariant (value : Reachable state) : Invariant state :=
  value.trace.invariant Invariant.initial

theorem Reachable.phase_timers (value : Reachable state) : PhaseTimers state := value.invariant.phase.1

theorem Reachable.predata_frames (value : Reachable state) : PreDataFrames state := value.invariant.phase.2.1

theorem Reachable.template_sources (value : Reachable state) : TemplateSources state := value.invariant.phase.2.2

private theorem index_unique {outputs : List Emission} {left right : Emission}
    (ordered : outputs.Pairwise (fun a b : Emission => a.index < b.index))
    (first : left ∈ outputs) (second : right ∈ outputs) (same : left.index = right.index) : left = right := by
  induction outputs with
  | nil => cases first
  | cons head tail ih =>
    obtain ⟨before, ordered⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp first with firstEq | firstTail
    · subst left
      rcases List.mem_cons.mp second with secondEq | secondTail
      · exact secondEq.symm
      · have newer := before right secondTail
        omega
    · rcases List.mem_cons.mp second with secondEq | secondTail
      · subst right
        have newer := before left firstTail
        omega
      · exact ih ordered firstTail secondTail

theorem History.source_of_member {output : Emission} (history : History state) (member : output ∈ state.emissions) :
    state.source output.index = some output := by
  cases found : state.source output.index with
  | none =>
    have absent := List.find?_eq_none.mp found output member
    exact False.elim (absent (beq_self_eq_true _))
  | some selected =>
    have retained := List.mem_of_find?_eq_some found
    have equal : selected.index = output.index := by simpa only [beq_iff_eq] using List.find?_some found
    have same := index_unique history.emissionOrder retained member equal
    subst selected
    rfl

structure TemplateOrigin (state : State active passive) (steps : List (Step active passive))
    (source : Nat) (actor : Side) (kind : Kind) (packet : H.Input) where
  output : Emission
  lookup : state.source source = some output
  index : output.index = source
  actorEq : output.actor = actor
  kindEq : output.kind = kind
  packetEq : output.packet = packet
  origin : EmissionOrigin steps output

theorem Reachable.template_origin (value : Reachable state) (template : Template state source actor kind packet) :
    Nonempty (TemplateOrigin state value.steps source actor kind packet) := by
  obtain ⟨output, member, index, actorEq, kindEq, packetEq⟩ := template
  obtain ⟨origin⟩ := value.trace.output_origin member
  have found := value.history.source_of_member member
  rw [index] at found
  exact ⟨⟨output, found, index, actorEq, kindEq, packetEq, origin⟩⟩

theorem TemplateOrigin.producer_fields (origin : TemplateOrigin state steps source actor kind packet) :
    origin.origin.actual.result.output = some origin.output ∧ origin.origin.actual.index = source :=
  ⟨origin.origin.recorded, origin.origin.index.symm.trans origin.index⟩

theorem Reachable.acknowledged (value : Reachable state)
    (current : state.phase = .acknowledged ready client) :
    TimerClosed state.activeTimer .syn ready.answered.opened.index ∧
      TimerPending state.passiveTimer .synAck ready.answered.index ∧
      PreDataClean ready.ready.seed client := by
  have timers := value.phase_timers
  have frame := value.predata_frames
  simp only [PhaseTimers, PreDataFrames, current] at timers frame
  exact ⟨timers.1, timers.2, frame⟩

theorem Reachable.complete (value : Reachable state) {certificate : O.Completed active passive}
    {client : PreData certificate.certificate.activeSeed} {server : PreData certificate.certificate.passiveSeed}
    (current : state.phase = .complete certificate client server) :
    TimerClosed state.activeTimer .syn certificate.input.times.opened ∧
      TimerClosed state.passiveTimer .synAck certificate.input.times.synReceived ∧
      PreDataClean certificate.certificate.activeSeed client ∧
      PreDataClean certificate.certificate.passiveSeed server := by
  have timers := value.phase_timers
  have frames := value.predata_frames
  simp only [PhaseTimers, PreDataFrames, current] at timers frames
  exact ⟨timers.1, timers.2, frames⟩

theorem Reachable.complete_sources (value : Reachable state) {certificate : O.Completed active passive}
    {client : PreData certificate.certificate.activeSeed} {server : PreData certificate.certificate.passiveSeed}
    (current : state.phase = .complete certificate client server) :
    Nonempty (TemplateOrigin state value.steps certificate.input.times.opened .active .syn certificate.certificate.activePending.output) ∧
      Nonempty (TemplateOrigin state value.steps certificate.input.times.synReceived .passive .synAck certificate.certificate.passivePending.output) := by
  have sources := value.template_sources
  simp only [TemplateSources, current] at sources
  exact ⟨value.template_origin sources.1, value.template_origin sources.2⟩

end Netlib.Check.TCPHandshakeRecovery
