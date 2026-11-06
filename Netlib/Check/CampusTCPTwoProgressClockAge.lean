import Netlib.Check.CampusTCPTwoProgressClock
import Netlib.Protocol.TCP.ApplicationTrace
import Netlib.Protocol.TCP.RecoveryEnabled

namespace Netlib.Check.CampusTCPTwoProgressClockAge

open Protocol.TCP

private theorem window_now (before after : Endpoint.State) (segment : Segment) :
    (Endpoint.windowState before after segment).now = after.now := by
  unfold Endpoint.windowState
  split <;> rfl

private theorem receive_recovery_now (state : Endpoint.State) (segment : Segment) (count : Nat)
    (after : Option Recovery.State) (computed : Endpoint.receiveRecovery state segment count = .ok after) :
    (after.map (·.now)).getD 0 = state.now := by
  unfold Endpoint.receiveRecovery at computed
  cases runtime : state.recovery with
  | none => simp only [runtime, Except.ok.injEq] at computed; cases computed; simp [Endpoint.State.now, runtime]
  | some recovery =>
    simp only [runtime] at computed
    cases acknowledged : Recovery.acknowledge recovery count with
    | error reason => simp [acknowledged, bind, Except.bind] at computed
    | ok received =>
      have clock : received.now = recovery.now := by
        rw [(Recovery.acknowledge_fields _ _ _ acknowledged).2]
        exact Recovery.acknowledgeState_now _ _
      simp only [acknowledged, bind, Except.bind] at computed
      split at computed
      · cases duplicate : Recovery.duplicate received with
        | error reason => simp only [duplicate, Functor.map, Except.map] at computed; cases computed
        | ok updated =>
          simp only [duplicate, Functor.map, Except.map, Except.ok.injEq] at computed
          cases computed
          rw [(Recovery.duplicate_fields _ _ duplicate).1]
          simpa only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some] using clock
      · simp only [pure, Except.pure, Except.ok.injEq] at computed
        cases computed
        simpa only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some] using clock

private theorem header_now (state : Endpoint.State) (header : ReceiveReassembly.HeaderEffect) (after : Endpoint.State)
    (computed : Endpoint.applyHeader state header = .ok after) : after.now = state.now := by
  unfold Endpoint.applyHeader at computed
  split at computed
  · cases computed
  · cases runtime : state.recovery with
    | none =>
      simp only [runtime] at computed
      cases computed
      rw [window_now]
      simp [Endpoint.State.now, runtime]
    | some recovery =>
      simp only [runtime] at computed
      cases received : Recovery.acknowledgeAt recovery header.acknowledged header.run.metadata.receivedAt with
      | error reason => simp only [received, Except.map] at computed; cases computed
      | ok updated =>
        simp only [received, Except.map] at computed
        cases computed
        rw [window_now]
        simpa only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some] using Recovery.acknowledgeAt_now _ _ _ _ received

private theorem runs_now (state : Endpoint.State) (runs : List ReceiveReassembly.Run) (processed : Endpoint.ReceiveProcessed)
    (computed : Endpoint.processRuns state runs = .ok processed) : processed.received.now = state.now := by
  induction runs generalizing state processed with
  | nil => simp only [Endpoint.processRuns, Except.ok.injEq] at computed; cases computed; rfl
  | cons head tail ih =>
    cases prepared : ReceiveReassembly.applyRun state.core head with
    | error reason => simp only [Endpoint.processRuns, prepared] at computed; cases computed
    | ok header =>
      cases applied : Endpoint.applyHeader state header with
      | error reason => simp only [Endpoint.processRuns, prepared, applied] at computed; cases computed
      | ok after =>
        cases continued : Endpoint.processRuns after tail with
        | error reason => simp only [Endpoint.processRuns, prepared, applied, continued] at computed; cases computed
        | ok next =>
          simp only [Endpoint.processRuns, prepared, applied, continued, Except.ok.injEq] at computed
          cases computed
          exact (ih after next continued).trans (header_now state header after applied)

private theorem stopped_now (state : Endpoint.State) (reason : EstablishedReceive.Block)
    (ack : Option EstablishedReceive.AckRequest) : (Endpoint.receiveStopped state reason ack).state.now = state.now := by
  cases reason with
  | unsupported => rfl
  | reject reason =>
    dsimp only [Endpoint.receiveStopped]
    split
    · rw [Endpoint.ackBlocked_state]
    · rfl

private theorem in_order_now (state : Endpoint.State) (packet : EstablishedReceive.Input) :
    (Endpoint.receiveInOrder state packet).state.now = state.now := by
  unfold Endpoint.receiveInOrder
  dsimp only
  repeat' first
    | (solve | rfl)
    | (solve | rw [Endpoint.recoveryBlocked_state])
    | (solve | rw [Endpoint.ackBlocked_state])
    | (solve | exact receive_recovery_now state packet.packet.segment _ _ (by assumption))
    | split

private theorem failed_now (state : Endpoint.State) (id : Nat) (failure : Endpoint.ReceiveFailure) :
    (Endpoint.receiveFailed state id failure).result.state.now = state.now := by
  unfold Endpoint.receiveFailed
  split
  · cases failure with
    | header failed => exact stopped_now state _ _
    | recovery failed => rw [Endpoint.recoveryBlocked_state]
  · rfl

private theorem raw_now (state : Endpoint.State) (packet : EstablishedReceive.Input) :
    (Endpoint.receiveRaw state packet).result.state.now = state.now := by
  unfold Endpoint.receiveRaw
  dsimp only
  repeat' first
    | (solve | rfl)
    | (solve | rw [Endpoint.recoveryBlocked_state])
    | (solve | rw [Endpoint.ackBlocked_state])
    | (solve | exact stopped_now state _ _)
    | (solve | exact in_order_now state packet)
    | (solve | exact failed_now state _ _)
    | (solve | exact runs_now state _ _ (by assumption))
    | split

theorem receive_now (state : Endpoint.State) (packet : EstablishedReceive.Input) :
    (Endpoint.receive state packet).state.now = state.now := by
  unfold Endpoint.receive Endpoint.receiveEffect
  dsimp only
  split
  · exact raw_now state packet
  · rfl

private theorem send_state_now (state : Endpoint.State) (count : Nat) :
    (Endpoint.sendState state count).now = state.now := by
  cases runtime : state.recovery <;>
    simp only [Endpoint.sendState, Endpoint.outputState, Endpoint.State.now, runtime,
      Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, Recovery.sent]

private theorem send_now (state : Endpoint.State) (count : Nat) (policy : Bool) :
    (Endpoint.send state count policy).state.now = state.now := by
  unfold Endpoint.send
  repeat' first
    | (solve | rfl)
    | (solve | exact send_state_now state count)
    | (solve | rw [Endpoint.recoveryBlocked_state])
    | (solve | rw [Endpoint.ackBlocked_state])
    | split

private theorem pure_ack_now (state : Endpoint.State) (policy dueOnly : Bool) :
    (Endpoint.pureAck state policy dueOnly).state.now = state.now := by
  unfold Endpoint.pureAck
  repeat' first | (solve | rfl) | (solve | rw [Endpoint.ackBlocked_state]) | split

private theorem timeout_now (state : Endpoint.State) (policy : Bool) :
    (Endpoint.timeout state policy).state.now = state.now := by
  unfold Endpoint.timeout
  dsimp only
  repeat' first
    | (solve | rfl)
    | (solve | rw [Endpoint.recoveryBlocked_state])
    | (solve | rw [Endpoint.ackBlocked_state])
    | (solve |
        have clock := Recovery.timeout_clock _ _ _ (by assumption)
        simp_all only [Endpoint.State.now, Option.map_some, Option.getD_some])
    | split

private theorem enable_recovery_now (state : Endpoint.State) : (Endpoint.enableRecovery state).state.now ≤ state.now := by
  unfold Endpoint.enableRecovery
  repeat' first
    | (solve | exact Nat.le_refl _)
    | (solve | rw [Endpoint.recoveryBlocked_state])
    | (solve | exact Nat.zero_le _)
    | split

private theorem advance_now_le (state : Endpoint.State) (millis : Nat) :
    (Endpoint.advanceClock state millis).state.now ≤ max state.now millis := by
  unfold Endpoint.advanceClock
  repeat' first
    | (solve | exact Nat.le_max_left _ _)
    | (solve | rw [Endpoint.recoveryBlocked_state]; exact Nat.le_max_left _ _)
    | (solve | rw [Endpoint.ackBlocked_state]; exact Nat.le_max_left _ _)
    | (solve |
        have changed := (Recovery.advance_fields _ _ _ (by assumption)).2
        rw [changed]
        exact Nat.le_max_right _ _)
    | split

theorem advance_now_of_accepted (state : Endpoint.State) (millis : Nat)
    (accepted : (Endpoint.advanceClock state millis).decision = .accepted .advanceClock) :
    (Endpoint.advanceClock state millis).state.now = millis := by
  unfold Endpoint.advanceClock at accepted
  repeat' first
    | (solve | cases accepted)
    | (solve | unfold Endpoint.recoveryBlocked at accepted; split at accepted <;> cases accepted)
    | (solve | unfold Endpoint.ackBlocked at accepted; split at accepted <;> cases accepted)
    | (solve |
        have changed := (Recovery.advance_fields _ _ _ (by assumption)).2
        simp_all [Endpoint.advanceClock, Endpoint.State.now])
    | split at accepted

def ClockBound (quantum : Nat) (step : ApplicationTrace.Step) : Prop :=
  ∀ millis, step.event = .advanceClock millis → millis ≤ step.before.now + quantum

def isClock : ApplicationTrace.Event → Bool
  | .advanceClock _ => true
  | _ => false

def clockCount (steps : List ApplicationTrace.Step) : Nat := steps.countP (fun step => isClock step.event)

theorem Step.nonclock_now_le (step : ApplicationTrace.Step) (nonclock : isClock step.event = false) :
    step.result.state.now ≤ step.before.now := by
  rw [step.computed]
  cases event : step.event with
  | receive packet => rw [ApplicationTrace.evaluate, receive_now]; exact Nat.le_refl _
  | send count policy => rw [ApplicationTrace.evaluate, send_now]; exact Nat.le_refl _
  | emitAck policy => rw [ApplicationTrace.evaluate, Endpoint.emitAck, pure_ack_now]; exact Nat.le_refl _
  | dispatchAck policy => rw [ApplicationTrace.evaluate, Endpoint.dispatchAck, pure_ack_now]; exact Nat.le_refl _
  | timeout policy => rw [ApplicationTrace.evaluate, timeout_now]; exact Nat.le_refl _
  | enableRecovery => exact enable_recovery_now _
  | advanceClock millis => rw [event] at nonclock; cases nonclock
  | write bytes =>
    change (Endpoint.write step.before bytes).state.now ≤ step.before.now
    unfold Endpoint.write
    repeat' first | (solve | exact Nat.le_refl _) | split
  | read count =>
    change (Endpoint.read step.before count).state.now ≤ step.before.now
    unfold Endpoint.read
    repeat' first | (solve | exact Nat.le_refl _) | split
  | enableAck =>
    change (Endpoint.enableAck step.before).state.now ≤ step.before.now
    unfold Endpoint.enableAck
    repeat' first
      | (solve | exact Nat.le_refl _)
      | (solve | rw [Endpoint.recoveryBlocked_state])
      | (solve | rw [Endpoint.ackBlocked_state])
      | split

theorem Step.now_le (step : ApplicationTrace.Step) (bounded : ClockBound quantum step) :
    step.result.state.now ≤ step.before.now + if isClock step.event then quantum else 0 := by
  cases event : step.event with
  | advanceClock millis =>
    rw [step.computed, event]
    exact Nat.le_trans (advance_now_le _ _) (Nat.max_le.mpr ⟨Nat.le_add_right _ _, bounded millis event⟩)
  | _ =>
    have nonclock : isClock step.event = false := by rw [event]; rfl
    simpa only [isClock, Bool.false_eq_true, ite_false, Nat.add_zero] using Step.nonclock_now_le step nonclock

theorem Step.now_le_quantum (step : ApplicationTrace.Step) (bounded : ClockBound quantum step) :
    step.result.state.now ≤ step.before.now + quantum := by
  have upper := Step.now_le step bounded
  cases selected : isClock step.event <;> simp only [selected, Bool.false_eq_true, ite_false, ite_true] at upper <;> omega

theorem Step.clock_now (step : ApplicationTrace.Step) (event : step.event = .advanceClock millis)
    (accepted : step.result.decision = .accepted .advanceClock) : step.result.state.now = millis := by
  have actual : (Endpoint.advanceClock step.before millis).decision = .accepted .advanceClock := by
    simpa only [step.computed, event, ApplicationTrace.evaluate] using accepted
  rw [step.computed, event]
  exact advance_now_of_accepted step.before millis actual

theorem Chain.now_le_clocks (chain : ApplicationTrace.Chain initial steps final)
    (bounded : ∀ step ∈ steps, ClockBound quantum step) :
    final.now ≤ initial.now + clockCount steps * quantum := by
  induction chain with
  | nil state => simp only [clockCount, List.countP_nil, Nat.zero_mul, Nat.add_zero, Nat.le_refl]
  | @cons steps final head tail ih =>
    have localBound := Step.now_le head (bounded head (by simp))
    have rest := ih (fun step member => bounded step (List.mem_cons_of_mem _ member))
    simp only [clockCount, List.countP_cons, Nat.add_mul] at *
    cases clock : isClock head.event <;> simp only [clock, Bool.false_eq_true, ite_false, ite_true, Nat.zero_mul, Nat.one_mul] at * <;> omega

theorem Chain.now_le_length (chain : ApplicationTrace.Chain initial steps final)
    (bounded : ∀ step ∈ steps, ClockBound quantum step) : final.now ≤ initial.now + steps.length * quantum := by
  exact Nat.le_trans (Chain.now_le_clocks chain bounded)
    (Nat.add_le_add_left (Nat.mul_le_mul_right quantum (List.countP_le_length)) _)

theorem Chain.age_le_clocks (chain : ApplicationTrace.Chain initial steps final)
    (bounded : ∀ step ∈ steps, ClockBound quantum step) (sentAt : Nat) (earlier : initial.now ≤ sentAt) :
    final.now - sentAt ≤ clockCount steps * quantum := by
  have upper := Chain.now_le_clocks chain bounded
  omega

theorem Chain.age_le_length (chain : ApplicationTrace.Chain initial steps final)
    (bounded : ∀ step ∈ steps, ClockBound quantum step) (sentAt : Nat) (earlier : initial.now ≤ sentAt) :
    final.now - sentAt ≤ steps.length * quantum := by
  have upper := Chain.now_le_length chain bounded
  omega

theorem clocked_local_bound {input : CampusTCPModel.Input}
    {complete : TCPHandshake.Completed input.active input.passive}
    {initial current : CampusTCPRound.Cut input complete} {cfg : CampusTCPTwoProgressMonitor.Config}
    {monitor : CampusTCPTwoProgressMonitor.Monitor} {actor : CampusTCPModel.Actor} {millis : Nat}
    {actual : CampusTCPModel.Step input}
    (clocked : CampusTCPTwoProgressClock.Clocked initial current cfg monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed cfg current.report.final monitor (.advanceClock actor millis)) :
    ClockBound cfg.quantum clocked.base.value.operation := by
  intro selected event
  have same : millis = selected := ApplicationTrace.Event.advanceClock.inj (clocked.base.value.localEvent.symm.trans event)
  subst selected
  rw [clocked.base.value.localBefore]
  obtain ⟨_, _, _, upper, _⟩ := CampusTCPGapProgressClock.clock_allowed_fields cfg.toConfig current actor millis
    (CampusTCPTwoProgressClock.allowed_guard cfg current monitor actor millis allowed)
  exact upper

theorem clocked_actor_le {input : CampusTCPModel.Input}
    {complete : TCPHandshake.Completed input.active input.passive}
    {initial current : CampusTCPRound.Cut input complete} {cfg : CampusTCPTwoProgressMonitor.Config}
    {monitor : CampusTCPTwoProgressMonitor.Monitor} {actor : CampusTCPModel.Actor} {millis : Nat}
    {actual : CampusTCPModel.Step input}
    (clocked : CampusTCPTwoProgressClock.Clocked initial current cfg monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed cfg current.report.final monitor (.advanceClock actor millis))
    (receiver : CampusTCPModel.Actor) :
    (CampusTCPEnabled.endpoint clocked.move.after.endpoints receiver).now ≤
      (CampusTCPEnabled.endpoint current.endpoints receiver).now + cfg.quantum := by
  by_cases selected : receiver = actor
  · subst receiver
    have afterNow : (CampusTCPEnabled.endpoint clocked.move.after.endpoints actor).now = millis := by
      change (CampusTCPEnabled.endpoint clocked.base.move.after.endpoints actor).now = millis
      rw [clocked.base.endpoints]
      exact clocked.base.value.selectedNow
    rw [afterNow]
    obtain ⟨_, _, _, upper, _⟩ := CampusTCPGapProgressClock.clock_allowed_fields cfg.toConfig current actor millis
      (CampusTCPTwoProgressClock.allowed_guard cfg current monitor actor millis allowed)
    exact upper
  · have other : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [CampusTCPModel.Actor.other]
    rw [other, clocked.peer]
    exact Nat.le_add_right _ _

end Netlib.Check.CampusTCPTwoProgressClockAge
