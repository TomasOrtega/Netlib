import Netlib.Check.CampusTCPStartupJobDrain
import Netlib.Check.CampusTCPRecoveryReceipts

/-!
# Queue frames after both startup timers close

Actual clocks and obsolete timeouts add no jobs.
A completed startup receipt can generate only an ACK response.
-/

namespace Netlib.Check.CampusTCPStartupJobDrainComplete

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace C
export TCPHandshakeRecovery (State Step Reachable PhaseTimers PreData)
end C

structure QueueFrame (before after : State input) : Prop where
  work : after.work = before.work
  custody : after.custody = before.custody

variable {input : Input}

theorem QueueFrame.inventory (frame : QueueFrame before after) : inventory after = inventory before :=
  inventory_same (congrArg Theory.PacketCustody.State.pending frame.custody)
    (congrArg Theory.Outstanding.State.pending frame.work)

theorem QueueFrame.selected (frame : QueueFrame before after) (key : Key) : CampusTCPStartupJobs.selected after key = CampusTCPStartupJobs.selected before key := by
  rw [CampusTCPStartupJobs.selected, CampusTCPStartupJobs.selected, frame.inventory]

theorem QueueFrame.potential (frame : QueueFrame before after) : CampusTCPStartupJobs.potential after = CampusTCPStartupJobs.potential before := by
  rw [CampusTCPStartupJobs.potential, CampusTCPStartupJobs.potential, frame.inventory]

private def QuietRecovery (before : State input) (effect : Effect input) : Prop :=
  effect.state.work = before.work ∧ effect.output = none ∧ effect.service = none

private theorem recovery_clock (computed : runRecovery input before (.advanceClock actor millis) = .ok effect) :
    QuietRecovery before effect := by
  cases connection : before.connection with
  | startup stage pending | application complete endpoints =>
    simp only [runRecovery, connection, pure, Except.pure, Except.ok.injEq] at computed
    subst effect
    exact ⟨rfl, rfl, rfl⟩
  | recovering current =>
    simp only [runRecovery, connection] at computed
    split at computed
    · cases computed
    · rename_i result evaluated
      have quiet := TCPHandshakeRecovery.evaluate_clock_no_output evaluated
      split at computed
      · simp only [pure, Except.pure, Except.ok.injEq] at computed
        subst effect
        exact ⟨rfl, rfl, rfl⟩
      · rename_i emission emitted
        rw [quiet] at emitted
        cases emitted

private theorem recovery_timeout
    (connection : before.connection = .recovering current) (reachable : C.Reachable current)
    (phase : current.phase = .complete complete client server)
    (computed : runRecovery input before (.timeout actor generation policy) = .ok effect) :
    QuietRecovery before effect := by
  simp only [runRecovery, connection] at computed
  split at computed
  · cases computed
  · rename_i result evaluated
    have quiet := TCPHandshakeRecovery.evaluate_complete_timeout_no_output reachable.phase_timers phase evaluated
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst effect
      exact ⟨rfl, rfl, rfl⟩
    · rename_i emission emitted
      rw [quiet] at emitted
      cases emitted

private theorem queue_frame (actual : Step input)
    (quiet : ∀ effect, processCore input actual.before actual.event = .ok effect → QuietRecovery actual.before effect)
    (unchanged : prepareCustody actual.before actual.event = .ok actual.before.custody) :
    QueueFrame actual.before actual.result.state ∧ actual.result.output = none := by
  obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
  have frames := quiet effect computed
  have same : custody = actual.before.custody := Except.ok.inj (prepared.symm.trans unchanged)
  rw [final, same]
  exact ⟨⟨frames.1, by simp only [finishCustody, frames.2.1, frames.2.2]⟩, frames.2.1⟩

theorem Step.clock_frame (actual : Step input) (event : actual.event = .startupClock actor millis) :
    QueueFrame actual.before actual.result.state ∧ actual.result.output = none := by
  apply queue_frame actual
  · intro effect computed
    rw [event] at computed
    exact recovery_clock computed
  · simp only [prepareCustody, event]
    rfl

theorem Step.complete_timeout_frame (actual : Step input)
    (connection : actual.before.connection = .recovering current) (reachable : C.Reachable current)
    (phase : current.phase = .complete complete client server)
    (event : actual.event = .startupTimeout actor generation policy) :
    QueueFrame actual.before actual.result.state ∧ actual.result.output = none := by
  apply queue_frame actual
  · intro effect computed
    rw [event] at computed
    exact recovery_timeout connection reachable phase computed
  · simp only [prepareCustody, event]
    rfl

theorem Step.complete_response (actual : Step input)
    (connection : actual.before.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (event : actual.event = .deliver index bytes policy)
    (control : C.Step input.active input.passive) (output : TCPHandshakeRecovery.Emission)
    (present : control.result.output = some output)
    (recorded : actual.result.output = some (.recovery control output present)) :
    ∃ receipt, control.result.receipt = some receipt ∧
      ((receipt.source.kind = .syn ∧ output.kind = .synReplyAck) ∨
        (receipt.source.kind = .synAck ∧ output.kind = .finalAck)) := by
  have recovered := CampusTCPRecoveryReceipts.Step.recovery_output_recorded actual control output present recorded
  obtain ⟨delivery⟩ := CampusTCPRecoveryReceipts.Step.recovery_delivery actual recovered event
  have before : control.before = current := by
    exact Connection.recovering.inj (delivery.beforeEq.symm.trans connection)
  have computed := control.computed
  rw [delivery.controlEvent] at computed
  have phaseBefore : control.before.phase = .complete complete client server :=
    (congrArg TCPHandshakeRecovery.State.phase before).trans phase
  exact TCPHandshakeRecovery.evaluate_complete_response phaseBefore computed present

end Netlib.Check.CampusTCPStartupJobDrainComplete
