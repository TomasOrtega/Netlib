import Netlib.Check.CampusTCPTwoProgressPhaseBase
import Netlib.Check.CampusTCPTwoProgressAckOutput
import Netlib.Check.CampusTCPTwoProgressPaths

/-!
# Actual ACK output from the joint phase

The current receiver queue supplies the response credit.
The same output extends the actual monitor and source history.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseAckSend

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane Allowed observe nextDemand)
end M
namespace S
export CampusTCPTwoProgressSender (Stage)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace F
export CampusTCPTwoProgressMonitorFacts
  (allowed_iff serves_operation phase_beq_false phase_beq observe_action observe_ack)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage} {lane : M.Lane} {actual : Step input}
variable {timeouts : Nat} {live : CampusTCPTwoProgressState.Live initial current sent timeouts received}

def ingressLane (lane : M.Lane) (index packetID : Nat) : M.Lane :=
  ⟨.ackIngress, { lane.refs with ackOutput := some index, ackIngressPacket := some packetID }⟩

private theorem ack_allowed (mode : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (lowerSent : monitor.lower.phase ≠ .needSend) (upperSent : monitor.upper.phase ≠ .needSend)
    (selected : monitor.ack = some lane) (pending : lane.phase = .needAck) :
    M.Allowed (config initial native quantum allowance) current.report.final monitor (.emitAck sender.other true) := by
  have demand : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.single (.operation (.emitAck sender.other true))) := by
    rcases mode with mode | mode
    all_goals simp only [M.nextDemand, mode, (F.phase_beq_false _ _).mpr lowerSent,
      (F.phase_beq_false _ _).mpr upperSent, Bool.false_eq_true, ite_false, selected,
      CampusTCPTwoProgressMonitor.laneDemand, CampusTCPGapProgressMonitor.nextAction,
      CampusTCPTwoProgressMonitor.Lane.toGap, pending, CampusTCPGapProgressMonitor.packetAt,
      bind, Option.bind, pure, Option.map_some]
    all_goals rfl
  apply (F.allowed_iff _ _ _ _).mpr
  refine ⟨?_, .inl ⟨_, demand, (F.serves_operation _ _).mpr rfl⟩, rfl⟩
  rcases mode with mode | mode <;> rw [mode] <;> decide

private theorem core_cast_book (core : Core initial native quantum allowance current before sent received)
    (same : before = after) : (same ▸ core).losses.book = core.losses.book := by cases same; rfl

private theorem history_cast_book
    (history : CampusTCPTwoProgressLossHistory.History initial (config initial native quantum allowance) current before)
    (same : before = after) : (same ▸ history).book = history.book := by cases same; rfl

private theorem gateway_frame (value : CampusTCPTwoProgressAckOutput.Acked live actual) :
    beforeService input value.move.after.report.final gateway = beforeService input current.report.final gateway := by
  rw [value.move.final, ← value.facts.beforeEq]
  exact CampusTCPRoundLocal.step_service_nonservice actual (by rw [value.facts.event]; trivial) gateway

private theorem sender_steps (value : CampusTCPTwoProgressAckOutput.Acked live actual) :
    applicationSteps value.move.after.endpoints sender = applicationSteps current.endpoints sender := by
  have connected : Connection.application complete value.move.after.endpoints = .application complete value.facts.after := by
    rw [← value.move.after.connection, value.move.final]
    exact value.facts.connection
  have endpoints : value.move.after.endpoints = value.facts.after := eq_of_heq (Connection.application.inj connected).2
  rw [endpoints]
  have twice : sender.other.other = sender := by cases sender <;> rfl
  simpa only [twice] using value.facts.peerSteps

private theorem recovery_same (value : CampusTCPTwoProgressAckOutput.Acked live actual) :
    value.next.senderFlight.recovery = live.senderFlight.recovery := by
  have runtime := value.next.senderFlight.runtime.symm.trans
    ((congrArg (fun state : Endpoint.State => state.recovery) value.peer).trans live.senderFlight.runtime)
  exact Option.some.inj runtime

private theorem duplicate_same (value : CampusTCPTwoProgressAckOutput.Acked live actual) :
    value.next.senderFlight.recovery.duplicateAcks = live.senderFlight.recovery.duplicateAcks :=
  congrArg Recovery.State.duplicateAcks (recovery_same value)

structure AckSent (core : Core initial native quantum allowance current monitor sent received) (lane : M.Lane) (actual : Step input) where
  value : CampusTCPTwoProgressAckOutput.Acked core.live actual
  pending : core.live.receiverFacts.reaction.work.pending ≠ []
  allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event
  packetID : Nat
  custody : value.move.after.report.final.custody.pendingID (Transit.ingressAt current.report.final.outputs.length) = some packetID
  observed : M.observe (config initial native quantum allowance) monitor actual =
    { monitor with ack := some (ingressLane lane current.report.final.outputs.length packetID) }
  next : Core initial native quantum allowance value.move.after
    (M.observe (config initial native quantum allowance) monitor actual) sent received
  book : next.losses.book = core.losses.book
  path : CampusTCPTwoProgressPaths.AckIngress initial value.move.after (received.bytes lower upper).length
    (ingressLane lane current.report.final.outputs.length packetID)

theorem ack_at (core : Core initial native quantum allowance current monitor sent received)
    (mode : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (lowerSent : monitor.lower.phase ≠ .needSend) (upperSent : monitor.upper.phase ≠ .needSend)
    (selected : monitor.ack = some lane) (phase : lane.phase = .needAck)
    (pending : core.live.receiverFacts.reaction.work.pending ≠ []) :
    ∃ actual, Nonempty (AckSent core lane actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressAckOutput.ack_at core.live core.senderWindow pending
  have allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event := by
    rw [value.facts.event]
    exact ack_allowed mode lowerSent upperSent selected phase
  obtain ⟨packetID, custody⟩ := CampusTCPRoundMonitorFacts.output_pending actual value.facts.produced value.facts.output
  rw [value.facts.beforeEq] at custody
  have observed : M.observe (config initial native quantum allowance) monitor actual =
      { monitor with ack := some (ingressLane lane current.report.final.outputs.length packetID) } := by
    rw [F.observe_action _ _ _ value.move.supported value.move.passed
      (by rw [value.move.beforeEq]; exact allowed) (.emitAck sender.other true) value.facts.event,
      F.observe_ack _ _ _ lane mode lowerSent upperSent selected]
    have actor : value.facts.produced.actor = sender.other := by rw [value.facts.production]; rfl
    have self : (sender.other == sender.other) = true := by cases sender <;> rfl
    simp only [CampusTCPTwoProgressMonitor.observeAck, CampusTCPTwoProgressMonitor.ackLane,
      phase, CampusTCPGapProgressMonitor.observeOutput, value.facts.output, actor, config,
      ite_false, ite_true, self, value.move.beforeEq, custody,
      CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap, F.phase_beq,
      reduceCtorEq, decide_false, Bool.false_eq_true, ingressLane]
  let joint : CampusTCPTwoProgressState.Live initial value.move.after sent monitor.retries received :=
    { value.next with
      gatewayState := core.live.gatewayState.reframe (gateway_frame value)
      gatewayWindow := core.live.gatewayWindow }
  let healthy : Core initial native quantum allowance value.move.after
      { monitor with ack := some (ingressLane lane current.report.final.outputs.length packetID) } sent received := {
    live := joint, senderWindow := value.reserve
    originals := core.originals.retain_steps value.move.retained
    originalTimes := core.originalTimes
    writer := core.writer.same (sender_steps value)
    losses := observed ▸ core.losses.append value.move
      (by rw [CampusTCPTwoProgressLossHistory.isDrop, value.facts.event])
      (by rw [CampusTCPTwoProgressLossHistory.isTimeout, value.facts.event])
      (by rw [observed]) (by rw [observed])
    lossBound := core.lossBound, retired := core.retired, gatewayAck := core.gatewayAck
    peerSettled := core.peerSettled, peerWindow := core.peerWindow
    covered := core.covered
    duplicates := duplicate_same value ▸ core.duplicates
    emptyDuplicate := fun empty => duplicate_same value ▸ core.emptyDuplicate empty
    deadline := recovery_same value ▸ core.deadline
    estimatorBeforeRetire := by
      rw [recovery_same value]
      exact core.estimatorBeforeRetire
    rtoBeforeRetire := by
      rw [recovery_same value]
      exact core.rtoBeforeRetire
    rtoPending := by
      rw [recovery_same value]
      exact core.rtoPending }
  have book : (observed.symm ▸ healthy).losses.book = core.losses.book := by
    rw [core_cast_book]
    exact history_cast_book _ observed
  have path : CampusTCPTwoProgressPaths.AckIngress initial value.move.after (received.bytes lower upper).length
      (ingressLane lane current.report.final.outputs.length packetID) := {
    output := {
      index := current.report.final.outputs.length, produced := value.facts.produced
      stored := by rw [value.move.final]; exact value.facts.source
      actor := by rw [value.facts.production]; rfl
      application := by rw [value.facts.production]; trivial
      fields := value.fields }
    packetID, custody := by
      change value.move.after.report.final.custody.pendingID (Transit.ingressAt current.report.final.outputs.length) = some packetID
      rw [value.move.final]
      exact custody
    phase := rfl, outputRef := rfl, packetRef := rfl }
  exact ⟨actual, ⟨⟨value, pending, allowed, packetID, by rw [value.move.final]; exact custody,
    observed, observed.symm ▸ healthy, book, path⟩⟩⟩

theorem AckSent.ack_state {core : Core initial native quantum allowance current monitor sent received}
    (record : AckSent core lane actual) :
    record.value.facts.localStep.result.state.ackReaction = some
      (AckReaction.outputState core.live.receiverFacts.reaction (endpoint current.endpoints sender.other).now
        (endpoint current.endpoints sender.other).core.receiveNext (endpoint current.endpoints sender.other).core.capacity
        (endpoint current.endpoints sender.other).core.window (endpoint current.endpoints sender.other).effectiveMSS) := by
  have state := record.value.facts.origin.ack_state
  rw [record.value.facts.localBefore, core.live.receiverFacts.ackRuntime, Option.map_some] at state
  exact state

end Netlib.Check.CampusTCPTwoProgressPhaseAckSend
