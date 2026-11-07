import Netlib.Check.CampusTCPRecoveryStartupCurrentSources
import Netlib.Check.CampusTCPRecoveryEventFacts

/-!
# The actual campus recovery OPEN

The source is the occurrence emitted by this same checked operation.
Its event stamp remains separate from its campus output position.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupOpened

open Protocol.TCP CampusTCPModel

namespace J
export CampusTCPStartupJobs (Source)
end J
namespace S
export CampusTCPRecoveryStartupCurrentSources (ProducedAt)
end S

variable {input : Input} {before : State input} {effect : Effect input}

structure OpenedAt (actual : Step input) (remote : Handshake.Socket) (policy : Bool) where
  control : C.Step input.active input.passive
  recorded : actual.result.recovery = some control
  beforeInitial : control.before = .initial
  event : control.event = .activeOpen remote policy
  opened : TCPHandshake.Opened input.active
  phase : control.result.state.phase = .opened opened
  remoteEq : opened.remote = remote
  policyEq : opened.policy = policy
  index : opened.index = control.index
  emitted : control.result.output = some ⟨control.index, .active, .syn, opened.pending.output, .open⟩
  produced : actual.result.output = some (.recovery control ⟨control.index, .active, .syn, opened.pending.output, .open⟩ emitted)
  after : actual.result.state.connection = .recovering control.result.state

variable {actual : Step input} {remote : Handshake.Socket} {policy : Bool}

def OpenedAt.source (value : OpenedAt actual remote policy) : J.Source input :=
  ⟨value.control, ⟨value.control.index, .active, .syn, value.opened.pending.output, .open⟩, value.emitted⟩

theorem OpenedAt.source_header (value : OpenedAt actual remote policy) :
    value.source.occurrence.packet.packet.header = Handshake.outbound input.active remote := by
  have fields := Handshake.activeOpen_fields _ _ _ _ value.opened.computed
  change value.opened.pending.output.packet.header = _
  rw [value.opened.pending.output_fields.1, fields.1, fields.2.1, value.remoteEq]

theorem OpenedAt.source_at (value : OpenedAt actual remote policy) (report : Report input events)
    (member : actual ∈ report.steps) : Nonempty (S.ProducedAt report value.source) :=
  ⟨⟨actual, member, value.produced⟩⟩

private structure OpenFields (before : State input) (effect : Effect input) (remote : Handshake.Socket) (policy : Bool) where
  control : C.Step input.active input.passive
  recorded : effect.recovery = some control
  beforeInitial : control.before = .initial
  event : control.event = .activeOpen remote policy
  opened : TCPHandshake.Opened input.active
  phase : control.result.state.phase = .opened opened
  remoteEq : opened.remote = remote
  policyEq : opened.policy = policy
  index : opened.index = control.index
  emitted : control.result.output = some ⟨control.index, .active, .syn, opened.pending.output, .open⟩
  produced : effect.output = some (.recovery control ⟨control.index, .active, .syn, opened.pending.output, .open⟩ emitted)
  after : effect.state.connection = .recovering control.result.state

private theorem open_fields (connected : before.connection = .startup .idle pending)
    (computed : openRecovering input before remote policy = .ok effect) : Nonempty (OpenFields before effect remote policy) := by
  unfold openRecovering at computed
  dsimp only at computed
  split at computed
  · cases computed
  · simp only [connected, runRecovery] at computed
    split at computed
    · cases computed
    · rename_i result evaluated
      obtain ⟨opened, _, phase, remoteEq, policyEq, index, emitted⟩ := TCPHandshakeRecovery.evaluate_opened evaluated
      split at computed
      · rename_i absent
        rw [emitted] at absent
        cases absent
      · rename_i emission present
        have same := Option.some.inj (present.symm.trans emitted)
        subst emission
        simp only [pure, Except.pure, Except.ok.injEq] at computed
        subst effect
        exact ⟨⟨⟨.initial, before.time, .activeOpen remote policy, result, evaluated⟩,
          rfl, rfl, rfl, opened, phase, remoteEq, policyEq, index, emitted, rfl, rfl⟩⟩

theorem Step.opened (actual : Step input) (connected : actual.before.connection = .startup .idle pending)
    (event : actual.event = .openRecovering remote policy) : Nonempty (OpenedAt actual remote policy) := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  rw [event] at computed
  obtain ⟨fields⟩ := open_fields connected computed
  exact ⟨⟨fields.control, by simpa only [result] using fields.recorded, fields.beforeInitial, fields.event,
    fields.opened, fields.phase, fields.remoteEq, fields.policyEq, fields.index, fields.emitted,
    by simpa only [result] using fields.produced, by simpa only [result] using fields.after⟩⟩

end Netlib.Check.CampusTCPRecoveryStartupOpened
