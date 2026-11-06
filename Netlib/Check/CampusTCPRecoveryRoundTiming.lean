import Netlib.Check.CampusTCPRecoveryRoundClock
import Netlib.Check.CampusTCPRecoveryRoundProgress
import Netlib.Check.CampusTCPRecoveryRoundBookkeeping
import Netlib.Theory.BoundedProgress

/-!
# Actual time bounds for a recovery attempt

An admitted clock slot adds at most one quantum to client time.
Packet and local operations retain the endpoint clock.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundTiming

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRecoveryRoundEvidence
open CampusTCPRecoveryRoundPhaseBase (config)

namespace M
export CampusTCPRecoveryRoundMonitor (Monitor Allowed)
end M

variable {input : Input} {events : List Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}
  {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
  {current : Cut input complete} {monitor : M.Monitor}

theorem Clocked.client_now_le (clocked : Clocked initial native quantum current monitor actor millis actual)
    (allowed : M.Allowed (config initial native quantum) current.report.final monitor actual.event) :
    (endpoint clocked.move.after.endpoints .client).now ≤ (endpoint current.endpoints .client).now + quantum := by
  have guard := (CampusTCPRecoveryRoundMonitorFacts.allowed_iff _ _ _ _).mp allowed |>.2
  rw [clocked.event] at guard
  obtain ⟨_, _, _, upper, _⟩ := clock_allowed_fields current actor millis guard
  cases actor with
  | client =>
    rw [clocked.endpoints, clocked.value.selectedNow]
    exact upper
  | server =>
    have same : endpoint clocked.move.after.endpoints .client = endpoint current.endpoints .client := clocked.peer
    rw [same]
    omega

private def runtimeNow (runtime : Option Recovery.State) : Nat := (runtime.map (·.now)).getD 0

private theorem windowState_now (before after : Endpoint.State) (segment : Segment) :
    (Endpoint.windowState before after segment).now = after.now := by
  unfold Endpoint.windowState
  split <;> rfl

private theorem receiveRecovery_now (state : Endpoint.State) (segment : Segment) (count : Nat)
    (after : Option Recovery.State) (accepted : Endpoint.receiveRecovery state segment count = .ok after) :
    runtimeNow after = state.now := by
  unfold Endpoint.receiveRecovery at accepted
  cases stored : state.recovery with
  | none =>
    simp only [stored] at accepted
    cases accepted
    simp only [runtimeNow, Endpoint.State.now, stored, Option.map_none, Option.getD_none]
  | some recovery =>
    simp only [stored] at accepted
    cases updated : Recovery.acknowledge recovery count with
    | error reason => simp only [updated, bind, Except.bind] at accepted; cases accepted
    | ok received =>
      have same : received.now = recovery.now := by
        rw [(Recovery.acknowledge_fields _ _ _ updated).2]
        unfold Recovery.acknowledgeState
        split <;> rfl
      simp only [updated, bind, Except.bind] at accepted
      split at accepted
      · cases duplicate : Recovery.duplicate received with
        | error reason => simp only [duplicate, Functor.map, Except.map] at accepted; cases accepted
        | ok repeated =>
          simp only [duplicate, Functor.map, Except.map] at accepted
          cases accepted
          have changed := (Recovery.duplicate_fields _ _ duplicate).1
          simp only [runtimeNow, Endpoint.State.now, stored, Option.map_some, Option.getD_some, changed, same]
      · cases accepted
        simpa only [runtimeNow, Endpoint.State.now, stored, Option.map_some, Option.getD_some] using same

private theorem receiveInOrder_now (state : Endpoint.State) (packet : EstablishedReceive.Input) :
    (Endpoint.receiveInOrder state packet).state.now = state.now := by
  unfold Endpoint.receiveInOrder
  repeat' first
    | rfl
    | (solve | rw [Endpoint.recoveryBlocked_state])
    | (solve | rw [Endpoint.ackBlocked_state])
    | (solve | change runtimeNow _ = state.now; exact receiveRecovery_now _ _ _ _ (by assumption))
    | split
  all_goals dsimp only
  repeat' first
    | rfl
    | (solve | rw [Endpoint.recoveryBlocked_state])
    | (solve | rw [Endpoint.ackBlocked_state])
    | (solve | change runtimeNow _ = state.now; exact receiveRecovery_now _ _ _ _ (by assumption))
    | split

private theorem applyHeader_now (state : Endpoint.State) (header : ReceiveReassembly.HeaderEffect)
    (after : Endpoint.State) (accepted : Endpoint.applyHeader state header = .ok after) : after.now = state.now := by
  unfold Endpoint.applyHeader at accepted
  split at accepted
  · cases accepted
  · cases stored : state.recovery with
    | none =>
      simp only [stored] at accepted
      cases accepted
      rw [windowState_now]
      simp only [Endpoint.State.now, stored, Option.map_none, Option.getD_none]
    | some recovery =>
      simp only [stored] at accepted
      cases updated : Recovery.acknowledgeAt recovery header.acknowledged header.run.metadata.receivedAt with
      | error reason => simp only [updated, Except.map] at accepted; cases accepted
      | ok received =>
        simp only [updated, Except.map] at accepted
        cases accepted
        rw [windowState_now]
        simpa only [Endpoint.State.now, stored, Option.map_some, Option.getD_some] using
          Recovery.acknowledgeAt_now _ _ _ _ updated

private theorem processRuns_now (state : Endpoint.State) (runs : List ReceiveReassembly.Run)
    (after : Endpoint.ReceiveProcessed) (accepted : Endpoint.processRuns state runs = .ok after) :
    after.received.now = state.now := by
  induction runs generalizing state after with
  | nil => cases accepted; rfl
  | cons run rest ih =>
    cases applied : ReceiveReassembly.applyRun state.core run with
    | error reason => simp only [Endpoint.processRuns, applied] at accepted; cases accepted
    | ok header =>
      cases updated : Endpoint.applyHeader state header with
      | error reason => simp only [Endpoint.processRuns, applied, updated] at accepted; cases accepted
      | ok received =>
        cases following : Endpoint.processRuns received rest with
        | error reason => simp only [Endpoint.processRuns, applied, updated, following] at accepted; cases accepted
        | ok last =>
          simp only [Endpoint.processRuns, applied, updated, following] at accepted
          cases accepted
          exact (ih _ _ following).trans (applyHeader_now _ _ _ updated)

private theorem receiveStopped_now (state : Endpoint.State) (reason : EstablishedReceive.Block)
    (ack : Option EstablishedReceive.AckRequest) : (Endpoint.receiveStopped state reason ack).state.now = state.now := by
  unfold Endpoint.receiveStopped
  repeat' first | rfl | (solve | rw [Endpoint.ackBlocked_state]) | split

private theorem receiveFailed_now (state : Endpoint.State) (receipt : Nat) (failure : Endpoint.ReceiveFailure) :
    (Endpoint.receiveFailed state receipt failure).result.state.now = state.now := by
  unfold Endpoint.receiveFailed
  split
  · cases failure with
    | header value => exact receiveStopped_now _ _ _
    | recovery value => exact congrArg Endpoint.State.now (Endpoint.recoveryBlocked_state _ _)
  · rfl

theorem receive_now (state : Endpoint.State) (packet : EstablishedReceive.Input) :
    (Endpoint.receive state packet).state.now = state.now := by
  have raw : (Endpoint.receiveRaw state packet).result.state.now = state.now := by
    unfold Endpoint.receiveRaw
    repeat' first
      | rfl
      | (solve | rw [Endpoint.recoveryBlocked_state])
      | (solve | rw [Endpoint.ackBlocked_state])
      | (solve | exact receiveStopped_now _ _ _)
      | (solve | exact receiveInOrder_now _ _)
      | (solve | exact receiveFailed_now _ _ _)
      | (solve | exact processRuns_now _ _ _ (by assumption))
      | split
    all_goals dsimp only
    repeat' first
      | rfl
      | (solve | exact processRuns_now _ _ _ (by assumption))
      | split
  unfold Endpoint.receive Endpoint.receiveEffect
  dsimp only
  split
  · exact raw
  · rfl

private theorem sendState_now (state : Endpoint.State) (count : Nat) : (Endpoint.sendState state count).now = state.now := by
  cases stored : state.recovery <;> simp only [Endpoint.sendState, Endpoint.State.now, stored,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some, Recovery.sent]

private theorem timeout_now (state : Endpoint.State) (policy : Bool) :
    (Endpoint.timeout state policy).state.now = state.now := by
  unfold Endpoint.timeout
  repeat' first
    | rfl
    | (solve | rw [Endpoint.recoveryBlocked_state])
    | (solve | rw [Endpoint.ackBlocked_state])
    | (solve
        | have same := Recovery.timeout_clock _ _ _ (by assumption)
          simp_all only [Endpoint.State.now, Option.map_some, Option.getD_some])
    | split

private theorem pureAck_now (state : Endpoint.State) (policy dueOnly : Bool) :
    (Endpoint.pureAck state policy dueOnly).state.now = state.now := by
  unfold Endpoint.pureAck
  repeat' first | rfl | (solve | rw [Endpoint.ackBlocked_state]) | split

theorem evaluate_now (state : Endpoint.State) (event : T.Event)
    (notClock : ∀ millis, event ≠ .advanceClock millis) : (ApplicationTrace.evaluate state event).state.now = state.now := by
  cases event with
  | write bytes =>
    change (Endpoint.write state bytes).state.now = state.now
    unfold Endpoint.write
    repeat' first | rfl | split
  | send count policy =>
    change (Endpoint.send state count policy).state.now = state.now
    unfold Endpoint.send
    repeat' first
      | rfl
      | (solve | rw [Endpoint.recoveryBlocked_state])
      | (solve | rw [Endpoint.ackBlocked_state])
      | (solve | exact sendState_now _ _)
      | split
  | read count =>
    change (Endpoint.read state count).state.now = state.now
    unfold Endpoint.read
    repeat' first | rfl | split
  | emitAck policy => exact pureAck_now _ _ _
  | receive packet => exact receive_now _ _
  | enableRecovery =>
    change (Endpoint.enableRecovery state).state.now = state.now
    cases stored : state.recovery with
    | none =>
      unfold Endpoint.enableRecovery
      repeat' first
        | (solve | simp only [Endpoint.State.now, stored, Option.map_none, Option.map_some,
            Option.getD_none, Option.getD_some, Recovery.initial])
        | rfl
        | (solve | rw [Endpoint.recoveryBlocked_state])
        | split
    | some recovery =>
      simp only [Endpoint.enableRecovery, stored, Option.isSome_some, Bool.true_or, ite_true]
      split
      · rfl
      · rw [Endpoint.recoveryBlocked_state]
  | advanceClock millis => exact False.elim (notClock millis rfl)
  | timeout policy => exact timeout_now _ _
  | enableAck =>
    change (Endpoint.enableAck state).state.now = state.now
    unfold Endpoint.enableAck
    repeat' first
      | rfl
      | (solve | rw [Endpoint.recoveryBlocked_state])
      | (solve | rw [Endpoint.ackBlocked_state])
      | split
  | dispatchAck policy => exact pureAck_now _ _ _

def clientNow (state : State input) : Nat :=
  match state.connection with
  | .application _ endpoints => (endpoint endpoints .client).now
  | _ => 0

theorem clientNow_application (state : State input) (connection : state.connection = .application complete endpoints) :
    clientNow state = (endpoint endpoints .client).now := by simp only [clientNow, connection]

private theorem application_client_now (before : State input) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (notClock : ∀ millis, event ≠ .advanceClock millis) : clientNow effect.state = clientNow before := by
  have recorded := CampusTCPRoundLocal.application_recorded before complete endpoints connection actor event effect computed earlier
  obtain ⟨after, connected, selected, peer, _, _, _, _, _⟩ :=
    CampusTCPEnabled.application_frame before complete endpoints connection actor event effect _ computed recorded
  rw [clientNow_application _ connected, clientNow_application _ connection]
  cases actor with
  | client =>
    rw [selected]
    exact evaluate_now _ _ notClock
  | server => exact congrArg Endpoint.State.now peer

private theorem delivery_client_now (before : State input) (connection : before.connection = .application complete endpoints)
    (earlier : ApplicationsBefore endpoints before.time) (index : Nat) (bytes : List UInt8) (policy : Bool)
    (effect : Effect input) (computed : processCore input before (.deliver index bytes policy) = .ok effect) :
    clientNow effect.state = clientNow before := by
  simp only [processCore] at computed
  repeat' first
    | (solve
        | cases computed
          first
            | rename_i applied after accepted
              exact application_client_now before connection _ _ after accepted (earlier _)
                (by intro millis same; cases same)
            | rename_i applied after accepted
              simp only [connection, Except.ok.injEq] at accepted
              cases accepted
              rfl)
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        startup, connection, unsupported] at computed)

theorem Step.action_client_now (actual : Step input) (before : actual.before = current.report.final)
    (action : CampusTCPRoundMonitor.Action) (event : actual.event = action.event) :
    clientNow actual.result.state = clientNow current.report.final := by
  obtain ⟨effect, custody, core, final⟩ := actual.processed
  rw [event, before] at core
  have earlier := CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection
  have allEarlier : ApplicationsBefore current.endpoints current.report.final.time := by
    intro actor
    cases actor
    · exact earlier.1
    · exact earlier.2
  rw [final]
  change clientNow effect.state = _
  cases action with
  | send actor count policy =>
    exact application_client_now _ current.connection actor (.send count policy) effect core (allEarlier _)
      (by intro millis same; cases same)
  | assign index ingress =>
    have unchanged := CampusTCPRoundClock.Step.connection_frame actual (event ▸ .assign index ingress)
    have same : effect.state.connection = current.report.final.connection := by simpa only [final, before] using unchanged
    unfold clientNow
    rw [same]
  | serve id =>
    have unchanged := CampusTCPRoundClock.Step.connection_frame actual (event ▸ .serve id none)
    have same : effect.state.connection = current.report.final.connection := by simpa only [final, before] using unchanged
    unfold clientNow
    rw [same]
  | deliver index bytes policy => exact delivery_client_now _ current.connection allEarlier _ _ _ effect core
  | emitAck actor policy =>
    exact application_client_now _ current.connection actor (.emitAck policy) effect core (allEarlier _)
      (by intro millis same; cases same)
  | read actor count =>
    exact application_client_now _ current.connection actor (.read count) effect core (allEarlier _)
      (by intro millis same; cases same)

theorem Step.timeout_client_now (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .timeout .client true) : clientNow actual.result.state = clientNow current.report.final := by
  obtain ⟨effect, custody, core, final⟩ := actual.processed
  rw [event, before] at core
  have earlier := CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection
  rw [final]
  exact application_client_now _ current.connection .client (.timeout true) effect core earlier.1
    (by intro millis same; cases same)

theorem Step.drop_client_now (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .dropPacket packet) : clientNow actual.result.state = clientNow current.report.final := by
  obtain ⟨effect, custody, core, final⟩ := actual.processed
  rw [event, before] at core
  cases core
  rw [final]
  rfl

private theorem clock_client_now_le (actual : Step input) (evidence : Evidence initial native quantum current monitor)
    (before : actual.before = current.report.final) (event : actual.event = .advanceClock actor millis)
    (allowed : M.Allowed (config initial native quantum) current.report.final monitor actual.event) :
    clientNow actual.result.state ≤ clientNow current.report.final + quantum := by
  have guard := (CampusTCPRecoveryRoundMonitorFacts.allowed_iff _ _ _ _).mp allowed |>.2
  rw [event] at guard
  obtain ⟨clocked⟩ := CampusTCPRecoveryRoundEvidence.Step.clock actual evidence actor millis before event guard
  rw [← clocked.move.final, clientNow_application _ clocked.move.after.connection,
    clientNow_application _ current.connection]
  exact Clocked.client_now_le clocked allowed

theorem Step.client_now_le (actual : Step input) (evidence : Evidence initial native quantum current monitor)
    (before : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum) current.report.final monitor actual.event) :
    clientNow actual.result.state ≤ clientNow current.report.final + quantum := by
  obtain ⟨selected, _⟩ := (CampusTCPRecoveryRoundMonitorFacts.allowed_iff _ _ _ _).mp allowed
  rcases selected with ⟨demand, _pending, served⟩ | free
  · cases demand with
    | operation action =>
      rw [Step.action_client_now actual before action
        ((CampusTCPRecoveryRoundMonitorFacts.serves_operation _ _).mp served)]
      omega
    | resolution action packet =>
      rcases (CampusTCPRecoveryRoundMonitorFacts.serves_resolution _ _ _).mp served with event | event
      · rw [Step.action_client_now actual before action event]
        omega
      · rw [Step.drop_client_now actual before event]
        omega
    | tick millis =>
      exact clock_client_now_le actual evidence before
        ((CampusTCPRecoveryRoundMonitorFacts.serves_tick _ _).mp served) allowed
    | timeout =>
      rw [Step.timeout_client_now actual before ((CampusTCPRecoveryRoundMonitorFacts.serves_timeout _).mp served)]
      omega
  · obtain ⟨actor, millis, event, _⟩ := CampusTCPRecoveryRoundMonitorFacts.freeClock_event _ _ _ _ free
    exact clock_client_now_le actual evidence before event allowed

theorem time_growth (time : Nat → Nat) (quantum start count : Nat)
    (growth : ∀ slot, start ≤ slot → slot < start + count → time (slot + 1) ≤ time slot + quantum) :
    time (start + count) ≤ time start + quantum * count := by
  induction count with
  | zero => simp only [Nat.add_zero, Nat.mul_zero, Nat.le_refl]
  | succ count ih =>
    have previous := ih (fun slot begun within => growth slot begun (by omega))
    have next := growth (start + count) (by omega) (by omega)
    rw [Nat.mul_succ, ← Nat.add_assoc]
    omega

theorem prefix_time_growth (positive : 0 < quantum)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system)
    (invariant : CampusTCPRecoveryRoundProgress.Invariant initial native quantum (execution.state 0))
    (start count : Nat) (within : start + count ≤ execution.length) :
    clientNow (execution.state (start + count)).1 ≤ clientNow (execution.state start).1 + quantum * count := by
  apply time_growth (fun slot => clientNow (execution.state slot).1) quantum start count
  intro slot _ inside
  obtain ⟨current, final, _, ⟨evidence⟩⟩ := execution.invariant
    (adapter := CampusTCPRecoveryRoundProgress.adapter initial native quantum positive) invariant slot (by omega)
  obtain ⟨allowed, actual, before, selected, result, _⟩ := execution.checked slot (by omega)
  have admitted : M.Allowed (config initial native quantum) current.report.final (execution.state slot).2 actual.event := by
    rw [final, selected]
    exact allowed
  have growth := Step.client_now_le actual evidence (before.trans final.symm) admitted
  simpa only [result, final] using growth

theorem before_deadline_of_slots (quantum service slots retries lastAt now : Nat)
    (bounded : slots ≤ 7 * service) (timely : quantum * (7 * service) < 1000)
    (growth : now ≤ lastAt + quantum * slots) : now < lastAt + 2 ^ retries * 1000 := by
  have elapsed := Nat.mul_le_mul_left quantum bounded
  have positive : 0 < 2 ^ retries := Nat.pow_pos (by decide)
  omega

theorem flight_not_due_of_slots (flight : CampusTCPRecoveryRoundSender.Flight initial sentAt state retries)
    (bounded : slots ≤ 7 * service) (timely : quantum * (7 * service) < 1000)
    (growth : state.now ≤ flight.entry.lastAt + quantum * slots) :
    ¬flight.entry.lastAt + flight.recovery.rto ≤ flight.recovery.now := by
  have now : state.now = flight.recovery.now := by
    simp only [Endpoint.State.now, flight.runtime, Option.map_some, Option.getD_some]
  rw [now] at growth
  have early := before_deadline_of_slots quantum service slots retries flight.entry.lastAt flight.recovery.now
    bounded timely growth
  rw [flight.rto]
  omega

def pathRank (baseDrops : Nat) (monitor : M.Monitor) : Nat :=
  if baseDrops < monitor.drops.length then 0 else monitor.round.rank - 1

theorem pathRank_dataIngress (monitor : M.Monitor) (phase : monitor.round.phase = .dataIngress) :
    pathRank monitor.drops.length monitor = 7 := by
  simp only [pathRank, Nat.lt_irrefl, ite_false, CampusTCPRoundMonitor.Monitor.rank, phase,
    CampusTCPRoundMonitor.Phase.rank]

theorem pathRank_dropped (monitor : M.Monitor) (dropped : baseDrops < monitor.drops.length) :
    pathRank baseDrops monitor = 0 := by simp only [pathRank, dropped, ite_true]

theorem pathRank_needRead (monitor : M.Monitor) (phase : monitor.round.phase = .needRead) :
    pathRank baseDrops monitor = 0 := by
  unfold pathRank
  split
  · rfl
  · simp only [CampusTCPRoundMonitor.Monitor.rank, phase, CampusTCPRoundMonitor.Phase.rank, Nat.sub_self]

theorem pathRank_done (monitor : M.Monitor) (phase : monitor.round.phase = .done) : pathRank baseDrops monitor = 0 := by
  unfold pathRank
  split
  · rfl
  · simp only [CampusTCPRoundMonitor.Monitor.rank, phase, CampusTCPRoundMonitor.Phase.rank, Nat.zero_sub]

private theorem pathRank_le_of_rank_le (cfg : CampusTCPRecoveryRoundMonitor.Config)
    (before after : State input) (monitor next : M.Monitor)
    (waiting : monitor.waiting = false) (active : next.waiting = false)
    (retries : next.retries = monitor.retries) (drops : next.drops.length = monitor.drops.length)
    (rank : next.rank cfg after ≤ monitor.rank cfg before) : pathRank baseDrops next ≤ pathRank baseDrops monitor := by
  unfold pathRank
  rw [drops]
  by_cases dropped : baseDrops < monitor.drops.length
  · simp only [dropped, ite_true, Nat.le_refl]
  · simp only [dropped, ite_false]
    cases first : monitor.round.phase <;> cases last : next.round.phase
    all_goals
      simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, waiting, active, Bool.false_eq_true,
        ite_false, first, last, retries, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank] at rank
      simp only [CampusTCPRoundMonitor.Monitor.rank, first, last, CampusTCPRoundMonitor.Phase.rank]
      omega

private theorem pathRank_lt_of_rank_lt (cfg : CampusTCPRecoveryRoundMonitor.Config)
    (before after : State input) (monitor next : M.Monitor)
    (waiting : monitor.waiting = false) (active : next.waiting = false)
    (retries : next.retries = monitor.retries) (drops : next.drops.length = monitor.drops.length)
    (positive : 0 < pathRank baseDrops monitor) (rank : next.rank cfg after < monitor.rank cfg before) :
    pathRank baseDrops next < pathRank baseDrops monitor := by
  unfold pathRank at positive ⊢
  rw [drops]
  by_cases dropped : baseDrops < monitor.drops.length
  · simp only [dropped, ite_true] at positive
    omega
  · simp only [dropped, ite_false] at positive ⊢
    cases first : monitor.round.phase <;> cases last : next.round.phase
    all_goals
      simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, waiting, active, Bool.false_eq_true,
        ite_false, first, last, retries, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank] at rank
      simp only [CampusTCPRoundMonitor.Monitor.rank, first, CampusTCPRoundMonitor.Phase.rank] at positive
      simp only [CampusTCPRoundMonitor.Monitor.rank, first, last, CampusTCPRoundMonitor.Phase.rank]
      omega

private theorem rank_eq_of_pathRank_eq (cfg : CampusTCPRecoveryRoundMonitor.Config)
    (before after : State input) (monitor next : M.Monitor)
    (waiting : monitor.waiting = false) (active : next.waiting = false)
    (retries : next.retries = monitor.retries) (drops : next.drops.length = monitor.drops.length)
    (positive : 0 < pathRank baseDrops monitor) (rank : pathRank baseDrops next = pathRank baseDrops monitor) :
    next.rank cfg after = monitor.rank cfg before := by
  unfold pathRank at positive rank
  rw [drops] at rank
  by_cases dropped : baseDrops < monitor.drops.length
  · simp only [dropped, ite_true] at positive
    omega
  · simp only [dropped, ite_false] at positive rank
    cases first : monitor.round.phase <;> cases last : next.round.phase
    all_goals
      simp only [CampusTCPRoundMonitor.Monitor.rank, first, CampusTCPRoundMonitor.Phase.rank] at positive
      simp only [CampusTCPRoundMonitor.Monitor.rank, first, last, CampusTCPRoundMonitor.Phase.rank] at rank
      simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, waiting, active, Bool.false_eq_true,
        ite_false, first, last, retries, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank]
      all_goals omega

private theorem retries_eq_drops (evidence : Evidence initial native quantum current monitor)
    (active : monitor.waiting = false) : monitor.retries = monitor.drops.length := by
  cases evidence with
  | needSend record => rw [record.monitorEq]; rfl
  | dataIngress record => exact record.retryCount.trans record.dropCount.symm
  | dataTicket record => exact record.retryCount.trans record.dropCount.symm
  | dataLink record => exact record.retryCount.trans record.dropCount.symm
  | needAck record => exact record.retryCount.trans record.dropCount.symm
  | ackIngress record => exact record.retryCount.trans record.dropCount.symm
  | ackTicket record => exact record.retryCount.trans record.dropCount.symm
  | ackLink record => exact record.retryCount.trans record.dropCount.symm
  | needRead record => exact record.retryCount.trans record.dropCount.symm
  | done record => exact record.retryCount.trans record.dropCount.symm
  | waiting record => rw [record.waiting] at active; cases active

private theorem waiting_drops (evidence : Evidence initial native quantum current monitor)
    (waiting : monitor.waiting = true) : monitor.drops.length = monitor.retries + 1 := by
  cases evidence with
  | needSend record => rw [record.monitorEq] at waiting; cases waiting
  | dataIngress record => rw [record.waiting] at waiting; cases waiting
  | dataTicket record => rw [record.waiting] at waiting; cases waiting
  | dataLink record => rw [record.waiting] at waiting; cases waiting
  | needAck record => rw [record.waiting] at waiting; cases waiting
  | ackIngress record => rw [record.waiting] at waiting; cases waiting
  | ackTicket record => rw [record.waiting] at waiting; cases waiting
  | ackLink record => rw [record.waiting] at waiting; cases waiting
  | needRead record => rw [record.waiting] at waiting; cases waiting
  | done record => rw [record.waiting] at waiting; cases waiting
  | waiting record => rw [record.dropCount, record.retryCount]

private theorem next_active (old : Evidence initial native quantum current monitor)
    (new : Evidence initial native quantum after next) (active : monitor.waiting = false)
    (drops : next.drops.length = monitor.drops.length) (retries : monitor.retries ≤ next.retries) : next.waiting = false := by
  by_cases result : next.waiting = false
  · exact result
  · have waiting : next.waiting = true := by cases selected : next.waiting <;> simp_all
    have first := retries_eq_drops old active
    have last := waiting_drops new waiting
    omega

private theorem pathRank_positive_main (cfg : CampusTCPRecoveryRoundMonitor.Config) (state : State input)
    (monitor : M.Monitor) (active : monitor.waiting = false) (positive : 0 < pathRank baseDrops monitor) :
    0 < monitor.rank cfg state := by
  unfold pathRank at positive
  split at positive
  · omega
  · cases phase : monitor.round.phase
    all_goals
      simp only [CampusTCPRoundMonitor.Monitor.rank, phase, CampusTCPRoundMonitor.Phase.rank] at positive
      simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, active, Bool.false_eq_true, ite_false,
        phase, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank]
      omega

private theorem edge_counts (invariant : CampusTCPRecoveryRoundProgress.Invariant initial native quantum before)
    (positive : 0 < quantum)
    (edge : (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system.step before event after) :
    before.2.drops.length ≤ after.2.drops.length ∧ before.2.retries ≤ after.2.retries := by
  have next := (CampusTCPRecoveryRoundProgress.transition invariant positive edge).invariant
  obtain ⟨oldCut, oldFinal, _, ⟨old⟩⟩ := invariant
  obtain ⟨newCut, newFinal, _, ⟨new⟩⟩ := next
  have first := CampusTCPRecoveryRoundBookkeeping.Evidence.drop_count old
  have last := CampusTCPRecoveryRoundBookkeeping.Evidence.drop_count new
  rw [oldFinal] at first
  rw [newFinal] at last
  obtain ⟨_, actual, beforeEq, _, afterEq, observed⟩ := edge
  have changed := CampusTCPCustodyFacts.Step.drop_count actual
  rw [beforeEq, afterEq] at changed
  have retried := CampusTCPRecoveryRoundBookkeeping.observe_retry_mono (config initial native quantum) before.2 actual
  rw [observed] at retried
  exact ⟨by omega, retried⟩

def PathInvariant (initial : Initial report complete request) (native : NativeEnv initial) (quantum baseDrops : Nat)
    (state : State input × M.Monitor) : Prop :=
  CampusTCPRecoveryRoundProgress.Invariant initial native quantum state ∧ baseDrops ≤ state.2.drops.length ∧
    (state.2.drops.length = baseDrops → state.2.waiting = false)

private theorem path_preserve (invariant : PathInvariant initial native quantum baseDrops before)
    (positive : 0 < quantum)
    (edge : (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system.step before event after) :
    PathInvariant initial native quantum baseDrops after := by
  have next := (CampusTCPRecoveryRoundProgress.transition invariant.1 positive edge).invariant
  have counts := edge_counts invariant.1 positive edge
  refine ⟨next, Nat.le_trans invariant.2.1 counts.1, ?_⟩
  intro selected
  have first : before.2.drops.length = baseDrops := by have lower := invariant.2.1; omega
  obtain ⟨_, _, _, ⟨old⟩⟩ := invariant.1
  obtain ⟨_, _, _, ⟨new⟩⟩ := next
  exact next_active old new (invariant.2.2 first) (by omega) counts.2

private theorem path_active (invariant : PathInvariant initial native quantum baseDrops state)
    (positive : 0 < pathRank baseDrops state.2) : state.2.waiting = false := by
  apply invariant.2.2
  have lower := invariant.2.1
  unfold pathRank at positive
  split at positive <;> omega

private theorem path_rank_le (invariant : PathInvariant initial native quantum baseDrops before)
    (positive : 0 < quantum)
    (edge : (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system.step before event after) :
    pathRank baseDrops after.2 ≤ pathRank baseDrops before.2 := by
  have next := path_preserve invariant positive edge
  have counts := edge_counts invariant.1 positive edge
  by_cases dropped : baseDrops < before.2.drops.length
  · rw [pathRank_dropped before.2 dropped, pathRank_dropped after.2 (by omega)]
    exact Nat.le_refl _
  · by_cases resolved : baseDrops < after.2.drops.length
    · rw [pathRank_dropped after.2 resolved]
      omega
    · have first : before.2.drops.length = baseDrops := by have lower := invariant.2.1; omega
      have last : after.2.drops.length = baseDrops := by have lower := next.2.1; omega
      obtain ⟨_, _, _, ⟨old⟩⟩ := invariant.1
      obtain ⟨_, _, _, ⟨new⟩⟩ := next.1
      have oldCount := retries_eq_drops old (invariant.2.2 first)
      have newCount := retries_eq_drops new (next.2.2 last)
      apply pathRank_le_of_rank_le (config initial native quantum) before.1 after.1 before.2 after.2
        (invariant.2.2 first) (next.2.2 last) (by omega) (by omega)
      exact (CampusTCPRecoveryRoundProgress.transition invariant.1 positive edge).nonincrease

private theorem path_rank_lt (invariant : PathInvariant initial native quantum baseDrops before)
    (positive : 0 < quantum)
    (edge : (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system.step before event after)
    (begun : 0 < pathRank baseDrops before.2)
    (rank : after.2.rank (config initial native quantum) after.1 < before.2.rank (config initial native quantum) before.1) :
    pathRank baseDrops after.2 < pathRank baseDrops before.2 := by
  have next := path_preserve invariant positive edge
  by_cases resolved : baseDrops < after.2.drops.length
  · rw [pathRank_dropped after.2 resolved]
    exact begun
  · have counts := edge_counts invariant.1 positive edge
    have first : before.2.drops.length = baseDrops := by
      have lower := invariant.2.1
      have upper := next.2.1
      omega
    have last : after.2.drops.length = baseDrops := by have lower := next.2.1; omega
    obtain ⟨_, _, _, ⟨old⟩⟩ := invariant.1
    obtain ⟨_, _, _, ⟨new⟩⟩ := next.1
    have oldCount := retries_eq_drops old (invariant.2.2 first)
    have newCount := retries_eq_drops new (next.2.2 last)
    exact pathRank_lt_of_rank_lt (config initial native quantum) before.1 after.1 before.2 after.2
      (invariant.2.2 first) (next.2.2 last) (by omega) (by omega) begun rank

private theorem path_rank_same (invariant : PathInvariant initial native quantum baseDrops before)
    (positive : 0 < quantum)
    (edge : (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system.step before event after)
    (begun : 0 < pathRank baseDrops before.2) (rank : pathRank baseDrops after.2 = pathRank baseDrops before.2) :
    after.2.rank (config initial native quantum) after.1 = before.2.rank (config initial native quantum) before.1 := by
  have next := path_preserve invariant positive edge
  have oldActive := path_active invariant begun
  have newActive := path_active next (by omega)
  obtain ⟨_, _, _, ⟨old⟩⟩ := invariant.1
  obtain ⟨_, _, _, ⟨new⟩⟩ := next.1
  have first := retries_eq_drops old oldActive
  have last := retries_eq_drops new newActive
  have oldDrops : before.2.drops.length = baseDrops := by
    have lower := invariant.2.1
    unfold pathRank at begun
    split at begun <;> omega
  have newDrops : after.2.drops.length = baseDrops := by
    have lower := next.2.1
    have positiveNext : 0 < pathRank baseDrops after.2 := by omega
    unfold pathRank at positiveNext
    split at positiveNext <;> omega
  exact rank_eq_of_pathRank_eq (config initial native quantum) before.1 after.1 before.2 after.2 oldActive newActive
    (by omega) (by omega) begun rank

def pathAdapter (initial : Initial report complete request) (native : NativeEnv initial) (quantum baseDrops : Nat)
    (positive : 0 < quantum) : Theory.BoundedProgress.Adapter (State input × M.Monitor) Event CampusTCPRecoveryRoundMonitor.Demand where
  system := (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system
  invariant := PathInvariant initial native quantum baseDrops
  pending state demand := 0 < pathRank baseDrops state.2 ∧
    (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).pending state demand
  enabled := (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).enabled
  serves := (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).serves
  rank state := pathRank baseDrops state.2
  complete state := pathRank baseDrops state.2 = 0
  preserve := by intro _ _ _ invariant edge; exact path_preserve invariant positive edge
  nonincrease := by intro _ _ _ invariant edge; exact path_rank_le invariant positive edge
  demand := by
    intro state invariant begun
    have mainPositive := pathRank_positive_main (config initial native quantum) state.1 state.2 (path_active invariant begun) begun
    obtain ⟨demand, pending⟩ := (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).demand invariant.1 mainPositive
    exact ⟨demand, begun, pending⟩
  pending_enabled := by
    intro _ _ invariant pending
    exact (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).pending_enabled invariant.1 pending.2
  persistent := by
    intro before event after demand invariant edge same pending
    refine ⟨by omega, ?_⟩
    exact (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).persistent invariant.1 edge
      (path_rank_same invariant positive edge pending.1 same) pending.2
  advance := by
    intro before event after demand invariant edge pending enabled served
    apply path_rank_lt invariant positive edge pending.1
    exact (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).advance invariant.1 edge pending.2 enabled served
  finished := by intro _ _ zero; exact zero

theorem path_service (positive : 0 < quantum)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system)
    (service : execution.ServiceFrom (adapter := CampusTCPRecoveryRoundProgress.adapter initial native quantum positive) bound first) :
    execution.ServiceFrom (adapter := pathAdapter initial native quantum baseDrops positive) bound first := by
  intro start begun within demand pending persistent
  exact service start begun within demand pending.2 (fun offset inside => (persistent offset inside).2)

theorem path_resolves_by (positive : 0 < quantum)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system)
    (invariant : CampusTCPRecoveryRoundProgress.Invariant initial native quantum (execution.state 0))
    (active : (execution.state 0).2.waiting = false) (phase : (execution.state 0).2.round.phase = .dataIngress)
    (service : execution.ServiceBound (adapter := CampusTCPRecoveryRoundProgress.adapter initial native quantum positive) bound)
    (within : 7 * bound ≤ execution.length) :
    pathRank (execution.state 0).2.drops.length (execution.state (7 * bound)).2 = 0 := by
  have localInvariant : PathInvariant initial native quantum (execution.state 0).2.drops.length (execution.state 0) :=
    ⟨invariant, Nat.le_refl _, fun _ => active⟩
  have initialRank := pathRank_dataIngress (execution.state 0).2 phase
  have resolved := execution.zero_by (adapter := pathAdapter initial native quantum (execution.state 0).2.drops.length positive)
    localInvariant (path_service positive execution service) 0 (Nat.zero_le _) (by simpa only [pathAdapter, initialRank, Nat.zero_add] using within)
  simpa only [pathAdapter, initialRank, Nat.zero_add] using resolved

theorem sent_lastAt_now (sent : CampusTCPRecoveryRoundSend.Sent initial native current quantum actual) :
    sent.flight.entry.lastAt = (endpoint sent.move.after.endpoints .client).now := by
  have same := Step.action_client_now actual sent.move.beforeEq (.send .client request.bytes.length true) sent.event
  rw [← sent.move.final, clientNow_application _ sent.move.after.connection,
    clientNow_application _ current.connection] at same
  exact (sent.flight.firstTime rfl).trans same.symm

theorem retry_lastAt_now (retry : CampusTCPRecoveryRoundRetry.Retry live native quantum monitor actual) :
    retry.next.sender.entry.lastAt = (endpoint retry.move.after.endpoints .client).now := by
  have connected : Connection.application complete retry.move.after.endpoints = .application complete retry.facts.after := by
    rw [← retry.move.after.connection, retry.move.final]
    exact retry.facts.connection
  have endpoints : retry.move.after.endpoints = retry.facts.after := eq_of_heq (Connection.application.inj connected).2
  have runtime : (endpoint retry.move.after.endpoints .client).recovery =
      some (Recovery.timeoutState live.sender.recovery live.sender.entry []) :=
    (congrArg (fun ends => (endpoint ends .client).recovery) endpoints).trans retry.facts.runtime
  have recovery : retry.next.sender.recovery = Recovery.timeoutState live.sender.recovery live.sender.entry [] :=
    Option.some.inj (retry.next.sender.runtime.symm.trans runtime)
  have source := retry.next.sender.source
  rw [recovery] at source
  have entry : retry.next.sender.entry = { live.sender.entry with lastAt := live.sender.recovery.now, retried := true } := by
    simpa only [Recovery.timeoutState, List.cons.injEq, and_true] using source.symm
  have now : (endpoint retry.move.after.endpoints .client).now = live.sender.recovery.now := by
    simp only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some, Recovery.timeoutState]
  exact (congrArg Recovery.Outstanding.lastAt entry).trans now.symm

theorem path_before_initial_deadline (positive : 0 < quantum)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system)
    (invariant : CampusTCPRecoveryRoundProgress.Invariant initial native quantum (execution.state 0))
    (flight : CampusTCPRecoveryRoundSender.Flight initial sentAt state retries)
    (started : clientNow (execution.state 0).1 = flight.entry.lastAt)
    (timely : quantum * (7 * service) < 1000) (slot : Nat) (bounded : slot ≤ 7 * service)
    (within : slot ≤ execution.length) :
    clientNow (execution.state slot).1 < flight.entry.lastAt + flight.recovery.rto := by
  have growth := prefix_time_growth positive execution invariant 0 slot (by simpa only [Nat.zero_add] using within)
  simp only [Nat.zero_add, started] at growth
  rw [flight.rto]
  exact before_deadline_of_slots quantum service slot retries flight.entry.lastAt _ bounded timely growth

private theorem output_phase (monitor : CampusTCPRoundMonitor.Monitor) (actual : Step input) (actor : Actor) (phase) :
    (CampusTCPRoundMonitor.observeOutput monitor actual actor phase).phase = phase ∨
      (CampusTCPRoundMonitor.observeOutput monitor actual actor phase).phase = .invalid := by
  unfold CampusTCPRoundMonitor.observeOutput
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split
  all_goals dsimp only
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split

private theorem assignment_phase (monitor : CampusTCPRoundMonitor.Monitor) (actual : Step input) (actor : Actor) (phase) :
    (CampusTCPRoundMonitor.observeAssignment monitor actual actor phase).phase = phase ∨
      (CampusTCPRoundMonitor.observeAssignment monitor actual actor phase).phase = .invalid := by
  unfold CampusTCPRoundMonitor.observeAssignment
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split

private theorem service_phase (monitor : CampusTCPRoundMonitor.Monitor) (actual : Step input) (actor : Actor) (phase) :
    (CampusTCPRoundMonitor.observeService monitor actual actor phase).phase = phase ∨
      (CampusTCPRoundMonitor.observeService monitor actual actor phase).phase = .invalid := by
  unfold CampusTCPRoundMonitor.observeService
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split
  all_goals dsimp only
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split

private theorem receipt_phase (monitor : CampusTCPRoundMonitor.Monitor) (actual : Step input) (actor : Actor) (phase) :
    (CampusTCPRoundMonitor.observeReceipt monitor actual actor phase).phase = phase ∨
      (CampusTCPRoundMonitor.observeReceipt monitor actual actor phase).phase = .invalid := by
  unfold CampusTCPRoundMonitor.observeReceipt
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split

private theorem low_phase_false (monitor : CampusTCPRoundMonitor.Monitor) (phase : CampusTCPRoundMonitor.Phase)
    (low : monitor.rank ≤ 1) (large : 1 < phase.rank) (choice : monitor.phase = phase ∨ monitor.phase = .invalid) : False := by
  rcases choice with selected | invalid
  · simp only [CampusTCPRoundMonitor.Monitor.rank, selected] at low
    omega
  · simp only [CampusTCPRoundMonitor.Monitor.rank, invalid, CampusTCPRoundMonitor.Phase.rank] at low
    omega

private theorem ack_receipt (monitor : CampusTCPRoundMonitor.Monitor) (actual : Step input)
    (low : (CampusTCPRoundMonitor.observeReceipt monitor actual .client .needRead).rank ≤ 1) :
    ∃ receipt, actual.result.receipt = some receipt ∧ receipt.actor = .client := by
  unfold CampusTCPRoundMonitor.observeReceipt at low
  cases present : actual.result.receipt with
  | none => simp only [present, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Monitor.invalid,
      CampusTCPRoundMonitor.Phase.rank] at low; omega
  | some receipt =>
    cases applied : actual.result.application with
    | none => simp only [present, applied, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Monitor.invalid,
        CampusTCPRoundMonitor.Phase.rank] at low; omega
    | some pair =>
      obtain ⟨actor, operation⟩ := pair
      simp only [present, applied] at low
      split at low
      · rename_i matching
        have same := matching
        simp only [Bool.and_eq_true] at same
        have actorEq : receipt.actor = .client := by
          cases selected : receipt.actor with
          | client => rfl
          | server =>
            have mismatch : (Actor.server == Actor.client) = false := by decide
            have bad : false = true := by simpa only [selected, mismatch] using same.1
            cases bad
        exact ⟨receipt, rfl, actorEq⟩
      · simp only [CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Monitor.invalid,
          CampusTCPRoundMonitor.Phase.rank] at low
        omega

private theorem advance_low_receipt (cfg : CampusTCPRoundMonitor.Config) (monitor : CampusTCPRoundMonitor.Monitor)
    (actual : Step input) (begun : 1 < monitor.rank) (low : (CampusTCPRoundMonitor.advance cfg monitor actual).rank ≤ 1) :
    ∃ receipt, actual.result.receipt = some receipt ∧ receipt.actor = .client := by
  cases phase : monitor.phase
  all_goals simp only [CampusTCPRoundMonitor.advance, phase] at low
  case needSend => exact False.elim (low_phase_false _ .dataIngress low (by decide) (output_phase _ _ _ _))
  case dataIngress => exact False.elim (low_phase_false _ .dataTicket low (by decide) (assignment_phase _ _ _ _))
  case dataTicket => exact False.elim (low_phase_false _ .dataLink low (by decide) (service_phase _ _ _ _))
  case dataLink => exact False.elim (low_phase_false _ .needAck low (by decide) (receipt_phase _ _ _ _))
  case needAck => exact False.elim (low_phase_false _ .ackIngress low (by decide) (output_phase _ _ _ _))
  case ackIngress => exact False.elim (low_phase_false _ .ackTicket low (by decide) (assignment_phase _ _ _ _))
  case ackTicket => exact False.elim (low_phase_false _ .ackLink low (by decide) (service_phase _ _ _ _))
  case ackLink => exact ack_receipt _ _ low
  case needRead => simp only [CampusTCPRoundMonitor.Monitor.rank, phase, CampusTCPRoundMonitor.Phase.rank] at begun; omega
  case done => simp only [CampusTCPRoundMonitor.Monitor.rank, phase, CampusTCPRoundMonitor.Phase.rank] at begun; omega
  case invalid => simp only [CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Monitor.invalid,
      CampusTCPRoundMonitor.Phase.rank] at low; omega

private theorem primary_resolution_receipt (evidence : Evidence initial native quantum current monitor)
    (positive : 0 < quantum) (actual : Step input) (before : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum) current.report.final monitor actual.event)
    (active : monitor.waiting = false) (begun : 0 < pathRank baseDrops monitor)
    (action : CampusTCPRoundMonitor.Action)
    (pending : CampusTCPRoundMonitor.nextAction (config initial native quantum).toConfig current.report.final monitor.round = some action)
    (event : actual.event = action.event)
    (resolved : pathRank baseDrops (CampusTCPRecoveryRoundMonitor.observe (config initial native quantum) monitor actual) = 0) :
    ∃ receipt, actual.result.receipt = some receipt ∧ receipt.actor = .client := by
  obtain ⟨checked⟩ := CampusTCPRecoveryRoundProgress.checked_step evidence positive actual before allowed
  have selected : CampusTCPRoundMonitor.nextAction (config initial native quantum).toConfig actual.before monitor.round = some action := by
    rw [before]; exact pending
  have observed := CampusTCPRecoveryRoundMonitorFacts.observe_action (config initial native quantum) monitor actual active
    checked.move.supported checked.move.passed action selected event
  have notDropped : ¬baseDrops < monitor.drops.length := by
    intro dropped
    rw [pathRank_dropped _ dropped] at begun
    omega
  have large : 1 < monitor.round.rank := by
    simp only [pathRank, notDropped, ite_false] at begun
    omega
  have low : (CampusTCPRoundMonitor.advance (config initial native quantum).toConfig monitor.round actual).rank ≤ 1 := by
    rw [observed] at resolved
    simp only [pathRank, notDropped, ite_false] at resolved
    omega
  exact advance_low_receipt _ _ _ large low

def Resolution (cfg : CampusTCPRecoveryRoundMonitor.Config) (state : State input) (monitor : M.Monitor) (actual : Step input) : Prop :=
  (∃ action packet, CampusTCPRecoveryRoundMonitor.nextDemand cfg state monitor = some (.resolution action packet) ∧
    actual.event = .dropPacket packet) ∨ ∃ receipt, actual.result.receipt = some receipt ∧ receipt.actor = .client

theorem Step.path_resolution (evidence : Evidence initial native quantum current monitor)
    (positive : 0 < quantum) (actual : Step input) (before : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum) current.report.final monitor actual.event)
    (active : monitor.waiting = false) (begun : 0 < pathRank baseDrops monitor)
    (resolved : pathRank baseDrops (CampusTCPRecoveryRoundMonitor.observe (config initial native quantum) monitor actual) = 0) :
    Resolution (config initial native quantum) current.report.final monitor actual := by
  obtain ⟨selected, _⟩ := (CampusTCPRecoveryRoundMonitorFacts.allowed_iff _ _ _ _).mp allowed
  rcases selected with ⟨demand, pending, served⟩ | free
  · obtain ⟨action, next, shape⟩ := CampusTCPRecoveryRoundMonitorFacts.nextDemand_action_exists _ _ _ active demand pending
    rcases shape with event | ⟨packet, event⟩
    · subst demand
      exact .inr (primary_resolution_receipt evidence positive actual before allowed active begun action next
        ((CampusTCPRecoveryRoundMonitorFacts.serves_operation _ _).mp served) resolved)
    · subst demand
      rcases (CampusTCPRecoveryRoundMonitorFacts.serves_resolution _ _ _).mp served with event | event
      · exact .inr (primary_resolution_receipt evidence positive actual before allowed active begun action next event resolved)
      · exact .inl ⟨action, packet, pending, event⟩
  · obtain ⟨actor, millis, event, _⟩ := CampusTCPRecoveryRoundMonitorFacts.freeClock_event _ _ _ _ free
    obtain ⟨checked⟩ := CampusTCPRecoveryRoundProgress.checked_step evidence positive actual before allowed
    rw [CampusTCPRecoveryRoundMonitorFacts.observe_clock _ _ _ checked.move.supported checked.move.passed actor millis event] at resolved
    omega

private theorem first_zero (rank : Nat → Nat) (positive : 0 < rank 0) (zero : rank count = 0) :
    ∃ slot, slot < count ∧ 0 < rank slot ∧ rank (slot + 1) = 0 := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases previous : rank count = 0
    · obtain ⟨slot, inside, begun, result⟩ := ih previous
      exact ⟨slot, by omega, begun, result⟩
    · exact ⟨count, by omega, by omega, zero⟩

theorem path_resolution_by (positive : 0 < quantum)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system)
    (invariant : CampusTCPRecoveryRoundProgress.Invariant initial native quantum (execution.state 0))
    (active : (execution.state 0).2.waiting = false) (phase : (execution.state 0).2.round.phase = .dataIngress)
    (service : execution.ServiceBound (adapter := CampusTCPRecoveryRoundProgress.adapter initial native quantum positive) bound)
    (within : 7 * bound ≤ execution.length) :
    ∃ slot, slot < 7 * bound ∧ ∃ actual : Step input,
      actual.before = (execution.state slot).1 ∧ actual.event = execution.action slot ∧
      actual.result.state = (execution.state (slot + 1)).1 ∧
      Resolution (config initial native quantum) (execution.state slot).1 (execution.state slot).2 actual ∧
      ∀ offset, offset ≤ slot → 0 < pathRank (execution.state 0).2.drops.length (execution.state offset).2 := by
  let base := (execution.state 0).2.drops.length
  have localInvariant : PathInvariant initial native quantum base (execution.state 0) :=
    ⟨invariant, Nat.le_refl _, fun _ => active⟩
  have initialRank : pathRank base (execution.state 0).2 = 7 := pathRank_dataIngress _ phase
  obtain ⟨slot, inside, begun, last⟩ := first_zero (fun slot => pathRank base (execution.state slot).2)
    (by rw [initialRank]; decide) (path_resolves_by positive execution invariant active phase service within)
  have localAt := execution.invariant (adapter := pathAdapter initial native quantum base positive) localInvariant slot (by omega)
  obtain ⟨current, final, _, ⟨evidence⟩⟩ := localAt.1
  obtain ⟨allowed, actual, before, event, result, observed⟩ := execution.checked slot (by omega)
  have allowedHere : M.Allowed (config initial native quantum) current.report.final (execution.state slot).2 actual.event := by
    rw [final, event]; exact allowed
  have resolved : pathRank base (CampusTCPRecoveryRoundMonitor.observe (config initial native quantum) (execution.state slot).2 actual) = 0 := by
    rw [observed]
    exact last
  have resolution := Step.path_resolution evidence positive actual (before.trans final.symm) allowedHere
    (path_active localAt begun) begun resolved
  refine ⟨slot, inside, actual, before, event, result, by simpa only [final] using resolution, ?_⟩
  intro offset earlier
  have order := execution.rank_mono (adapter := pathAdapter initial native quantum base positive)
    localInvariant earlier (show slot ≤ execution.length by omega)
  change pathRank base (execution.state slot).2 ≤ pathRank base (execution.state offset).2 at order
  change 0 < pathRank base (execution.state offset).2
  omega

private theorem active_no_timeout (cfg : CampusTCPRecoveryRoundMonitor.Config) (state : State input) (monitor : M.Monitor)
    (active : monitor.waiting = false) : ¬M.Allowed cfg state monitor (.timeout .client true) := by
  intro allowed
  obtain ⟨selected, _⟩ := (CampusTCPRecoveryRoundMonitorFacts.allowed_iff _ _ _ _).mp allowed
  rcases selected with ⟨demand, pending, served⟩ | free
  · obtain ⟨action, _, shape⟩ := CampusTCPRecoveryRoundMonitorFacts.nextDemand_action_exists _ _ _ active demand pending
    rcases shape with same | ⟨packet, same⟩
    · subst demand
      have event := (CampusTCPRecoveryRoundMonitorFacts.serves_operation _ _).mp served
      cases action <;> cases event
    · subst demand
      rcases (CampusTCPRecoveryRoundMonitorFacts.serves_resolution _ _ _).mp served with event | event
      · cases action <;> cases event
      · cases event
  · obtain ⟨actor, millis, event, _⟩ := CampusTCPRecoveryRoundMonitorFacts.freeClock_event _ _ _ _ free
    cases event

structure TimedResolution (initial : Initial report complete request) (native : NativeEnv initial) (quantum bound due : Nat)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPRecoveryRoundMonitor.guardedSystem input (config initial native quantum))) where
  slot : Nat
  within : slot < 7 * bound
  actual : Step input
  before : actual.before = (execution.state slot).1
  event : actual.event = execution.action slot
  result : actual.result.state = (execution.state (slot + 1)).1
  resolution : Resolution (config initial native quantum) (execution.state slot).1 (execution.state slot).2 actual
  early : ∀ offset, offset ≤ slot + 1 → clientNow (execution.state offset).1 < due
  noTimeout : ∀ offset, offset ≤ slot → execution.action offset ≠ .timeout .client true

private theorem timed_resolution (positive : 0 < quantum)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system)
    (invariant : CampusTCPRecoveryRoundProgress.Invariant initial native quantum (execution.state 0))
    (active : (execution.state 0).2.waiting = false) (phase : (execution.state 0).2.round.phase = .dataIngress)
    (service : execution.ServiceBound (adapter := CampusTCPRecoveryRoundProgress.adapter initial native quantum positive) bound)
    (within : 7 * bound ≤ execution.length)
    (flight : CampusTCPRecoveryRoundSender.Flight initial sentAt state retries)
    (started : clientNow (execution.state 0).1 = flight.entry.lastAt) (timely : quantum * (7 * bound) < 1000) :
    Nonempty (TimedResolution initial native quantum bound (flight.entry.lastAt + flight.recovery.rto) execution) := by
  obtain ⟨slot, inside, actual, before, event, result, resolution, previous⟩ :=
    path_resolution_by positive execution invariant active phase service within
  refine ⟨⟨slot, inside, actual, before, event, result, resolution, ?_, ?_⟩⟩
  · intro offset selected
    exact path_before_initial_deadline positive execution invariant flight started timely offset (by omega) (by omega)
  · intro offset selected timeout
    have localInvariant : PathInvariant initial native quantum (execution.state 0).2.drops.length (execution.state 0) :=
      ⟨invariant, Nat.le_refl _, fun _ => active⟩
    have localAt := execution.invariant (adapter := pathAdapter initial native quantum (execution.state 0).2.drops.length positive)
      localInvariant offset (by omega)
    have oldActive := path_active localAt (previous offset selected)
    obtain ⟨allowed, _⟩ := execution.checked offset (by omega)
    rw [timeout] at allowed
    exact active_no_timeout _ _ _ oldActive allowed

theorem sent_path_timed (sent : CampusTCPRecoveryRoundSend.Sent initial native current quantum actual)
    (positive : 0 < quantum)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system)
    (invariant : CampusTCPRecoveryRoundProgress.Invariant initial native quantum (execution.state 0))
    (start : execution.state 0 = (sent.move.after.report.final,
      CampusTCPRecoveryRoundMonitor.observe (config initial native quantum) CampusTCPRecoveryRoundMonitor.Monitor.initial actual))
    (service : execution.ServiceBound (adapter := CampusTCPRecoveryRoundProgress.adapter initial native quantum positive) bound)
    (within : 7 * bound ≤ execution.length) (timely : quantum * (7 * bound) < 1000) :
    sent.flight.recovery.deadline = some (sent.flight.entry.lastAt + sent.flight.recovery.rto) ∧
    Nonempty (TimedResolution initial native quantum bound (sent.flight.entry.lastAt + sent.flight.recovery.rto) execution) := by
  have active : (execution.state 0).2.waiting = false := by rw [start, sent.observed]
  have phase : (execution.state 0).2.round.phase = .dataIngress := by rw [start, sent.observed]
  have started : clientNow (execution.state 0).1 = sent.flight.entry.lastAt := by
    rw [start, clientNow_application _ sent.move.after.connection]
    exact (sent_lastAt_now sent).symm
  exact ⟨sent.flight.deadline, timed_resolution positive execution invariant active phase service within sent.flight started timely⟩

theorem retry_path_timed (retry : CampusTCPRecoveryRoundRetry.Retry live native quantum monitor actual)
    (positive : 0 < quantum)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPRecoveryRoundProgress.adapter initial native quantum positive).system)
    (invariant : CampusTCPRecoveryRoundProgress.Invariant initial native quantum (execution.state 0))
    (start : execution.state 0 = (retry.move.after.report.final,
      CampusTCPRecoveryRoundMonitor.observe (config initial native quantum) monitor actual))
    (service : execution.ServiceBound (adapter := CampusTCPRecoveryRoundProgress.adapter initial native quantum positive) bound)
    (within : 7 * bound ≤ execution.length) (timely : quantum * (7 * bound) < 1000) :
    retry.next.sender.recovery.deadline = some (retry.next.sender.entry.lastAt + retry.next.sender.recovery.rto) ∧
    Nonempty (TimedResolution initial native quantum bound
      (retry.next.sender.entry.lastAt + retry.next.sender.recovery.rto) execution) := by
  have active : (execution.state 0).2.waiting = false := by rw [start, retry.observed]
  have phase : (execution.state 0).2.round.phase = .dataIngress := by rw [start, retry.observed]
  have started : clientNow (execution.state 0).1 = retry.next.sender.entry.lastAt := by
    rw [start, clientNow_application _ retry.move.after.connection]
    exact (retry_lastAt_now retry).symm
  exact ⟨retry.next.sender.deadline,
    timed_resolution positive execution invariant active phase service within retry.next.sender started timely⟩

end Netlib.Check.CampusTCPRecoveryRoundTiming
