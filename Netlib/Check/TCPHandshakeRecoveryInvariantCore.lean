import Netlib.Check.TCPHandshakeRecovery

/-!
# Current startup phase and endpoint frames

Each timer names its original control occurrence.
An empty ACK can change the window markers without changing the byte state.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

def WindowFrame (before after : Endpoint.State) : Prop :=
  ∃ window sequence acknowledgment,
    after = { before with sendWindow := window, sendWL1 := sequence, sendWL2 := acknowledgment }

theorem WindowFrame.refl (state : Endpoint.State) : WindowFrame state state :=
  ⟨state.sendWindow, state.sendWL1, state.sendWL2, rfl⟩

theorem WindowFrame.trans (first : WindowFrame before middle) (second : WindowFrame middle after) : WindowFrame before after := by
  obtain ⟨window, sequence, acknowledgment, rfl⟩ := first
  obtain ⟨nextWindow, nextSequence, nextAcknowledgment, rfl⟩ := second
  exact ⟨nextWindow, nextSequence, nextAcknowledgment, rfl⟩

theorem WindowFrame.windowState (state : Endpoint.State) (segment : Segment) :
    WindowFrame state (Endpoint.windowState state state segment) := by
  unfold Endpoint.windowState
  split
  · exact ⟨segment.window.val, segment.sequence, segment.acknowledgment, rfl⟩
  · exact .refl state

theorem WindowFrame.core (frame : WindowFrame before after) : after.core = before.core := by
  obtain ⟨_, _, _, rfl⟩ := frame
  rfl

theorem WindowFrame.pending (frame : WindowFrame before after) : after.pending = before.pending := by
  obtain ⟨_, _, _, rfl⟩ := frame
  rfl

theorem WindowFrame.store (frame : WindowFrame before after) : after.receiveStore = before.receiveStore := by
  obtain ⟨_, _, _, rfl⟩ := frame
  rfl

theorem WindowFrame.recovery (frame : WindowFrame before after) : after.recovery = before.recovery := by
  obtain ⟨_, _, _, rfl⟩ := frame
  rfl

theorem WindowFrame.reaction (frame : WindowFrame before after) : after.ackReaction = before.ackReaction := by
  obtain ⟨_, _, _, rfl⟩ := frame
  rfl

def PreDataClean (seed : Endpoint.State) (current : PreData seed) : Prop :=
  WindowFrame seed current.current ∧ seed.recovery = none ∧ seed.ackReaction = none ∧
    seed.receiveStore = ReceiveStore.initial ∧ seed.pending = [] ∧ seed.core.sent = [] ∧ seed.core.received = []

theorem PreDataClean.active (pending : H.SynSent) (packet : H.Input) (ready : H.ActiveEstablished pending packet) :
    PreDataClean ready.seed (PreData.initial ready.seed ready.valid) := by
  refine ⟨.refl _, ?_⟩
  rw [ready.derived]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PreDataClean.passive (pending : H.SynReceived) (packet : H.Input) (ready : H.PassiveEstablished pending packet) :
    PreDataClean ready.seed (PreData.initial ready.seed ready.valid) := by
  refine ⟨.refl _, ?_⟩
  rw [ready.derived]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def TimerPending (timer : T.State) (kind : T.Kind) (source : Nat) : Prop :=
  ∃ flight, timer.status = .pending flight ∧ flight.kind = kind ∧ flight.source = source

def TimerClosed (timer : T.State) (kind : T.Kind) (source : Nat) : Prop :=
  ∃ flight ackAt, timer.status = .acknowledged flight ackAt ∧ flight.kind = kind ∧ flight.source = source

def PhaseTimers (state : State active passive) : Prop :=
  match state.phase with
  | .idle => state.activeTimer.status = .idle ∧ state.passiveTimer.status = .idle
  | .opened value => TimerPending state.activeTimer .syn value.index ∧ state.passiveTimer.status = .idle
  | .answered value => TimerPending state.activeTimer .syn value.opened.index ∧ TimerPending state.passiveTimer .synAck value.index
  | .acknowledged value _ => TimerClosed state.activeTimer .syn value.answered.opened.index ∧ TimerPending state.passiveTimer .synAck value.answered.index
  | .complete value _ _ => TimerClosed state.activeTimer .syn value.input.times.opened ∧ TimerClosed state.passiveTimer .synAck value.input.times.synReceived

def PreDataFrames (state : State active passive) : Prop :=
  match state.phase with
  | .idle | .opened _ | .answered _ => True
  | .acknowledged value client => PreDataClean value.ready.seed client
  | .complete value client server => PreDataClean value.certificate.activeSeed client ∧ PreDataClean value.certificate.passiveSeed server

def Template (state : State active passive) (source : Nat) (actor : Side) (kind : Kind) (packet : H.Input) : Prop :=
  ∃ output ∈ state.emissions, output.index = source ∧ output.actor = actor ∧ output.kind = kind ∧ output.packet = packet

def TemplateSources (state : State active passive) : Prop :=
  match state.phase with
  | .idle => True
  | .opened value => Template state value.index .active .syn value.pending.output
  | .answered value => Template state value.opened.index .active .syn value.opened.pending.output ∧
      Template state value.index .passive .synAck value.pending.output
  | .acknowledged value _ => Template state value.answered.opened.index .active .syn value.answered.opened.pending.output ∧
      Template state value.answered.index .passive .synAck value.answered.pending.output
  | .complete value _ _ => Template state value.input.times.opened .active .syn value.certificate.activePending.output ∧
      Template state value.input.times.synReceived .passive .synAck value.certificate.passivePending.output

def PhaseInvariant (state : State active passive) : Prop := PhaseTimers state ∧ PreDataFrames state ∧ TemplateSources state

theorem PreDataClean.fields (clean : PreDataClean seed current) :
    current.current.recovery = none ∧ current.current.ackReaction = none ∧
      current.current.receiveStore = ReceiveStore.initial ∧ current.current.pending = [] ∧
      current.current.core.sent = [] ∧ current.current.core.received = [] ∧ current.current.core = seed.core :=
  ⟨clean.1.recovery.trans clean.2.1, clean.1.reaction.trans clean.2.2.1,
    clean.1.store.trans clean.2.2.2.1, clean.1.pending.trans clean.2.2.2.2.1,
    (congrArg EstablishedReceive.State.sent clean.1.core).trans clean.2.2.2.2.2.1,
    (congrArg EstablishedReceive.State.received clean.1.core).trans clean.2.2.2.2.2.2, clean.1.core⟩

theorem Template.retain (template : Template state source actor kind packet) (retained : state.emissions <+: next.emissions) :
    Template next source actor kind packet := by
  obtain ⟨output, member, fields⟩ := template
  exact ⟨output, retained.subset member, fields⟩

theorem PhaseInvariant.last (invariant : PhaseInvariant state) : PhaseInvariant { state with last := some index } := invariant

theorem PhaseInvariant.initial : PhaseInvariant (State.initial (active := active) (passive := passive)) :=
  ⟨⟨rfl, rfl⟩, trivial, trivial⟩

theorem TimerPending.advance (pending : TimerPending before kind source)
    (computed : HandshakeTimer.advance before now = .ok after) : TimerPending after kind source := by
  obtain ⟨_, rfl⟩ := HandshakeTimer.advance_eq computed
  exact pending

theorem TimerClosed.advance (closed : TimerClosed before kind source)
    (computed : HandshakeTimer.advance before now = .ok after) : TimerClosed after kind source := by
  obtain ⟨_, rfl⟩ := HandshakeTimer.advance_eq computed
  exact closed

theorem TimerPending.arm (computed : HandshakeTimer.arm before kind source = .ok after) : TimerPending after kind source := by
  obtain ⟨_, rfl⟩ := HandshakeTimer.arm_eq computed
  exact ⟨_, rfl, rfl, rfl⟩

theorem TimerPending.expire (pending : TimerPending before kind source)
    (computed : HandshakeTimer.expire before generation = .ok after) : TimerPending after kind source := by
  obtain ⟨flight, status, kindEq, sourceEq⟩ := pending
  obtain ⟨selected, same, _, _, rfl⟩ := HandshakeTimer.expire_eq computed
  have equal : selected = flight := HandshakeTimer.Status.pending.inj (same.symm.trans status)
  subst selected
  exact ⟨_, rfl, kindEq, sourceEq⟩

theorem TimerClosed.acknowledge (pending : TimerPending before kind source)
    (computed : HandshakeTimer.acknowledge before = .ok after) : TimerClosed after kind source := by
  obtain ⟨flight, status, kindEq, sourceEq⟩ := pending
  obtain ⟨selected, same, rfl⟩ := HandshakeTimer.acknowledge_eq computed
  have equal : selected = flight := HandshakeTimer.Status.pending.inj (same.symm.trans status)
  subst selected
  exact ⟨_, _, rfl, kindEq, sourceEq⟩

end Netlib.Check.TCPHandshakeRecovery
