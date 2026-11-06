import Netlib.Check.CampusTCPGapProgressProgress
import Netlib.Check.CampusTCPGapProgressBookkeeping
import Netlib.Check.CampusTCPGapProgressContextClock
import Netlib.Check.CampusTCPGapProgressRetry
import Netlib.Check.CampusTCPRecoveryRoundTiming

namespace Netlib.Check.CampusTCPGapProgressTiming

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressSetup (config)
open CampusTCPGapProgressWire (Geometry)
open CampusTCPGapProgressEvidence
open CampusTCPGapProgressOrigins (SourceHistory)

namespace M
export CampusTCPGapProgressMonitor (Monitor Allowed)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper} {native : NativeEnv cut initial.gateway.seed.entry}
  {quantum allowance : Nat} {monitor : M.Monitor}

def endpointNow (state : State input) (actor : Actor) : Nat :=
  match state.connection with
  | .application _ endpoints => (endpoint endpoints actor).now
  | _ => 0

theorem endpointNow_application (state : State input) (connection : state.connection = .application complete endpoints) (actor : Actor) :
    endpointNow state actor = (endpoint endpoints actor).now := by simp only [endpointNow, connection]

private theorem application_now (before : State input) (connection : before.connection = .application complete endpoints)
    (actor selected : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (notClock : ∀ millis, event ≠ .advanceClock millis) : endpointNow effect.state selected = endpointNow before selected := by
  have recorded := CampusTCPRoundLocal.application_recorded before complete endpoints connection actor event effect computed earlier
  obtain ⟨after, connected, changed, peer, _, _, _, _, _⟩ :=
    CampusTCPEnabled.application_frame before complete endpoints connection actor event effect _ computed recorded
  rw [endpointNow_application _ connected, endpointNow_application _ connection]
  by_cases same : selected = actor
  · rw [same, changed]
    exact CampusTCPRecoveryRoundTiming.evaluate_now _ _ notClock
  · have other : selected = actor.other := by cases selected <;> cases actor <;> simp_all [Actor.other]
    rw [other]
    exact congrArg Endpoint.State.now peer

private theorem delivery_now (before : State input) (connection : before.connection = .application complete endpoints)
    (earlier : ApplicationsBefore endpoints before.time) (actor : Actor) (index : Nat) (bytes : List UInt8) (policy : Bool)
    (effect : Effect input) (computed : processCore input before (.deliver index bytes policy) = .ok effect) :
    endpointNow effect.state actor = endpointNow before actor := by
  simp only [processCore] at computed
  repeat' first
    | (solve
        | cases computed
          first
            | rename_i applied after accepted
              exact application_now before connection _ actor _ after accepted (earlier _)
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

theorem Step.action_now (actual : Step input) (before : actual.before = current.report.final)
    (actor : Actor) (action : CampusTCPRoundMonitor.Action) (event : actual.event = action.event) :
    endpointNow actual.result.state actor = endpointNow current.report.final actor := by
  obtain ⟨effect, custody, core, final⟩ := actual.processed
  rw [event, before] at core
  have earlier := CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection
  have allEarlier : ApplicationsBefore current.endpoints current.report.final.time := by
    intro selected
    cases selected
    · exact earlier.1
    · exact earlier.2
  rw [final]
  change endpointNow effect.state actor = _
  cases action with
  | send selected count policy =>
    exact application_now _ current.connection selected actor (.send count policy) effect core (allEarlier _)
      (by intro millis same; cases same)
  | assign index ingress =>
    have unchanged := CampusTCPRoundClock.Step.connection_frame actual (event ▸ .assign index ingress)
    have same : effect.state.connection = current.report.final.connection := by simpa only [final, before] using unchanged
    unfold endpointNow
    rw [same]
  | serve id =>
    have unchanged := CampusTCPRoundClock.Step.connection_frame actual (event ▸ .serve id none)
    have same : effect.state.connection = current.report.final.connection := by simpa only [final, before] using unchanged
    unfold endpointNow
    rw [same]
  | deliver index bytes policy => exact delivery_now _ current.connection allEarlier actor _ _ _ effect core
  | emitAck selected policy =>
    exact application_now _ current.connection selected actor (.emitAck policy) effect core (allEarlier _)
      (by intro millis same; cases same)
  | read selected count =>
    exact application_now _ current.connection selected actor (.read count) effect core (allEarlier _)
      (by intro millis same; cases same)

theorem Step.timeout_now (actual : Step input) (before : actual.before = current.report.final)
    (actor selected : Actor) (event : actual.event = .timeout selected true) :
    endpointNow actual.result.state actor = endpointNow current.report.final actor := by
  obtain ⟨effect, custody, core, final⟩ := actual.processed
  rw [event, before] at core
  have earlier := CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection
  have allEarlier : ApplicationsBefore current.endpoints current.report.final.time := by
    intro selected
    cases selected
    · exact earlier.1
    · exact earlier.2
  rw [final]
  exact application_now _ current.connection selected actor (.timeout true) effect core (allEarlier _)
    (by intro millis same; cases same)

theorem Step.drop_now (actual : Step input) (before : actual.before = current.report.final) (actor : Actor)
    (event : actual.event = .dropPacket packet) : endpointNow actual.result.state actor = endpointNow current.report.final actor := by
  obtain ⟨effect, custody, core, final⟩ := actual.processed
  rw [event, before] at core
  cases core
  rw [final]
  rfl

theorem Clocked.now_le (clocked : Clocked initial native quantum allowance current monitor actor millis actual)
    (selected : Actor) (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    (endpoint clocked.move.after.endpoints selected).now ≤ (endpoint current.endpoints selected).now + quantum := by
  have guard := (CampusTCPGapProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed |>.2
  rw [clocked.event] at guard
  obtain ⟨_, _, _, upper, _⟩ := CampusTCPGapProgressClock.clock_allowed_fields _ current actor millis guard
  by_cases same : selected = actor
  · rw [same, clocked.endpoints, clocked.value.selectedNow]
    exact upper
  · have peer : selected = actor.other := by cases selected <;> cases actor <;> simp_all [Actor.other]
    rw [peer, clocked.peer]
    omega

private theorem clock_now_le (actual : Step input) (evidence : Evidence initial native allowance current monitor)
    (before : actual.before = current.report.final) (event : actual.event = .advanceClock actor millis)
    (selected : Actor) (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    endpointNow actual.result.state selected ≤ endpointNow current.report.final selected + quantum := by
  have guard := (CampusTCPGapProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed |>.2
  rw [event] at guard
  obtain ⟨clocked⟩ := CampusTCPGapProgressEvidence.Step.clock actual evidence quantum actor millis before event guard
  rw [← clocked.move.final, endpointNow_application _ clocked.move.after.connection,
    endpointNow_application _ current.connection]
  exact Clocked.now_le clocked selected allowed

theorem Step.now_le (actual : Step input) (evidence : Evidence initial native allowance current monitor)
    (before : actual.before = current.report.final) (actor : Actor)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    endpointNow actual.result.state actor ≤ endpointNow current.report.final actor + quantum := by
  obtain ⟨selected, _⟩ := (CampusTCPGapProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
  rcases selected with ⟨demand, _pending, served⟩ | free
  · cases demand with
    | operation action =>
      rw [Step.action_now actual before actor action ((CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp served)]
      omega
    | resolution action packet =>
      rcases (CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _).mp served with event | event
      · rw [Step.action_now actual before actor action event]
        omega
      · rw [Step.drop_now actual before actor event]
        omega
    | tick selected millis =>
      exact clock_now_le actual evidence before ((CampusTCPGapProgressMonitorFacts.serves_tick _ _ _).mp served) actor allowed
    | timeout selected =>
      rw [Step.timeout_now actual before actor selected ((CampusTCPGapProgressMonitorFacts.serves_timeout _ _).mp served)]
      omega
  · obtain ⟨selected, millis, event, _⟩ := CampusTCPGapProgressMonitorFacts.freeClock_event _ _ _ _ free
    exact clock_now_le actual evidence before event actor allowed

abbrev time_growth := CampusTCPRecoveryRoundTiming.time_growth

theorem before_deadline_of_slots (quantum path service slots start now due : Nat)
    (bounded : slots ≤ path * service) (timely : quantum * (path * service) < due - start)
    (growth : now ≤ start + quantum * slots) : now < due := by
  have elapsed := Nat.mul_le_mul_left quantum bounded
  omega

theorem initial_remaining (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance : Nat) :
    (config initial native quantum allowance).initialRemaining =
      initial.flight.head.lastAt + initial.flight.recovery.rto - endpointNow cut.report.final sender := by
  simp only [config, endpointNow_application _ cut.connection, Endpoint.State.now,
    initial.flight.runtime, Option.map_some, Option.getD_some]

variable {live : CampusTCPGapProgressState.Live initial current retries released} {actual : Step input}

theorem retry_lastAt_now (retry : CampusTCPGapProgressRetry.Retry live actual) :
    retry.next.senderFlight.head.lastAt = (endpoint retry.move.after.endpoints sender).now := by
  have runtime : (endpoint retry.move.after.endpoints sender).recovery =
      some (Recovery.timeoutState live.senderFlight.recovery live.senderFlight.head [initial.flight.tail]) := by
    rw [retry.endpointsEq]
    exact retry.facts.runtime
  have recovery : retry.next.senderFlight.recovery =
      Recovery.timeoutState live.senderFlight.recovery live.senderFlight.head [initial.flight.tail] :=
    Option.some.inj (retry.next.senderFlight.runtime.symm.trans runtime)
  have source := retry.next.senderFlight.source
  rw [recovery] at source
  change { live.senderFlight.head with lastAt := live.senderFlight.recovery.now, retried := true } :: [initial.flight.tail] =
    retry.next.senderFlight.head :: [initial.flight.tail] at source
  have entry := (List.cons.inj source).1.symm
  have now : (endpoint retry.move.after.endpoints sender).now = live.senderFlight.recovery.now := by
    simp only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some, Recovery.timeoutState]
  exact (congrArg Recovery.Outstanding.lastAt entry).trans now.symm

def pathRank (baseDrops : Nat) (monitor : M.Monitor) : Nat :=
  if baseDrops < monitor.drops.length then 0 else monitor.phase.rank - 1

theorem pathRank_dataIngress (monitor : M.Monitor) (phase : monitor.phase = .dataIngress) :
    pathRank monitor.drops.length monitor = 7 := by
  simp only [pathRank, Nat.lt_irrefl, ite_false, phase,
    CampusTCPRoundMonitor.Phase.rank]

theorem pathRank_dropped (monitor : M.Monitor) (dropped : baseDrops < monitor.drops.length) :
    pathRank baseDrops monitor = 0 := by simp only [pathRank, dropped, ite_true]

theorem pathRank_needRead (monitor : M.Monitor) (phase : monitor.phase = .needRead) :
    pathRank baseDrops monitor = 0 := by
  unfold pathRank
  split
  · rfl
  · simp only [phase, CampusTCPRoundMonitor.Phase.rank, Nat.sub_self]

theorem pathRank_done (monitor : M.Monitor) (phase : monitor.phase = .done) : pathRank baseDrops monitor = 0 := by
  unfold pathRank
  split
  · rfl
  · simp only [phase, CampusTCPRoundMonitor.Phase.rank, Nat.zero_sub]

private theorem pathRank_le_of_rank_le (cfg : CampusTCPGapProgressMonitor.Config)
    (before after : State input) (monitor next : M.Monitor)
    (waiting : monitor.waiting = false) (active : next.waiting = false)
    (retries : next.retries = monitor.retries) (drops : next.drops.length = monitor.drops.length)
    (rank : next.rank cfg after ≤ monitor.rank cfg before) : pathRank baseDrops next ≤ pathRank baseDrops monitor := by
  unfold pathRank
  rw [drops]
  by_cases dropped : baseDrops < monitor.drops.length
  · simp only [dropped, ite_true, Nat.le_refl]
  · simp only [dropped, ite_false]
    cases first : monitor.phase <;> cases last : next.phase
    all_goals
      simp only [CampusTCPGapProgressMonitor.Monitor.rank, waiting, active, Bool.false_eq_true,
        ite_false, first, last, retries, CampusTCPRoundMonitor.Phase.rank] at rank
      simp only [CampusTCPRoundMonitor.Phase.rank]
      omega

private theorem pathRank_lt_of_rank_lt (cfg : CampusTCPGapProgressMonitor.Config)
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
    cases first : monitor.phase <;> cases last : next.phase
    all_goals
      simp only [CampusTCPGapProgressMonitor.Monitor.rank, waiting, active, Bool.false_eq_true,
        ite_false, first, last, retries, CampusTCPRoundMonitor.Phase.rank] at rank
      simp only [first, CampusTCPRoundMonitor.Phase.rank] at positive
      simp only [CampusTCPRoundMonitor.Phase.rank]
      omega

private theorem rank_eq_of_pathRank_eq (cfg : CampusTCPGapProgressMonitor.Config)
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
    cases first : monitor.phase <;> cases last : next.phase
    all_goals
      simp only [first, CampusTCPRoundMonitor.Phase.rank] at positive
      simp only [first, last, CampusTCPRoundMonitor.Phase.rank] at rank
      simp only [CampusTCPGapProgressMonitor.Monitor.rank, waiting, active, Bool.false_eq_true,
        ite_false, first, last, retries, CampusTCPRoundMonitor.Phase.rank]
      all_goals omega

private theorem retries_eq_drops (evidence : Evidence initial native allowance current monitor)
    (active : monitor.waiting = false) : monitor.retries = monitor.drops.length := by
  cases evidence with
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

private theorem waiting_drops (evidence : Evidence initial native allowance current monitor)
    (waiting : monitor.waiting = true) : monitor.drops.length = monitor.retries + 1 := by
  cases evidence with
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

private theorem next_active (old : Evidence initial native allowance current monitor)
    (new : Evidence initial native allowance after next) (active : monitor.waiting = false)
    (drops : next.drops.length = monitor.drops.length) (retries : monitor.retries ≤ next.retries) : next.waiting = false := by
  by_cases result : next.waiting = false
  · exact result
  · have waiting : next.waiting = true := by cases selected : next.waiting <;> simp_all
    have first := retries_eq_drops old active
    have last := waiting_drops new waiting
    omega

private theorem pathRank_positive_main (cfg : CampusTCPGapProgressMonitor.Config) (state : State input)
    (monitor : M.Monitor) (active : monitor.waiting = false) (positive : 0 < pathRank baseDrops monitor) :
    0 < monitor.rank cfg state := by
  unfold pathRank at positive
  split at positive
  · omega
  · cases phase : monitor.phase
    all_goals
      simp only [phase, CampusTCPRoundMonitor.Phase.rank] at positive
      simp only [CampusTCPGapProgressMonitor.Monitor.rank, active, Bool.false_eq_true, ite_false,
        phase, CampusTCPRoundMonitor.Phase.rank]
      omega

private theorem edge_counts (invariant : CampusTCPGapProgressProgress.Invariant initial native allowance before)
    (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (edge : (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system.step before event after) :
    before.2.drops.length ≤ after.2.drops.length ∧ before.2.retries ≤ after.2.retries := by
  have next := (CampusTCPGapProgressProgress.transition wire invariant positive budget edge).invariant
  obtain ⟨oldCut, oldFinal, _, ⟨old⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence invariant
  obtain ⟨newCut, newFinal, _, ⟨new⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence next
  have first := CampusTCPGapProgressBookkeeping.Evidence.drop_count old
  have last := CampusTCPGapProgressBookkeeping.Evidence.drop_count new
  rw [oldFinal] at first
  rw [newFinal] at last
  obtain ⟨_, actual, beforeEq, _, afterEq, observed⟩ := edge
  have changed := CampusTCPCustodyFacts.Step.drop_count actual
  rw [beforeEq, afterEq] at changed
  have retried := CampusTCPGapProgressBookkeeping.observe_retry_mono (config initial native quantum allowance) before.2 actual
  rw [observed] at retried
  exact ⟨by omega, retried⟩

def PathInvariant (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry) (allowance baseDrops : Nat)
    (state : State input × M.Monitor) : Prop :=
  CampusTCPGapProgressProgress.Invariant initial native allowance state ∧ baseDrops ≤ state.2.drops.length ∧
    (state.2.drops.length = baseDrops → state.2.waiting = false)

private theorem path_preserve (invariant : PathInvariant initial native allowance baseDrops before)
    (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (edge : (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system.step before event after) :
    PathInvariant initial native allowance baseDrops after := by
  have next := (CampusTCPGapProgressProgress.transition wire invariant.1 positive budget edge).invariant
  have counts := edge_counts invariant.1 wire positive budget edge
  refine ⟨next, Nat.le_trans invariant.2.1 counts.1, ?_⟩
  intro selected
  have first : before.2.drops.length = baseDrops := by have lower := invariant.2.1; omega
  obtain ⟨_, _, _, ⟨old⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence invariant.1
  obtain ⟨_, _, _, ⟨new⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence next
  exact next_active old new (invariant.2.2 first) (by omega) counts.2

private theorem path_active (invariant : PathInvariant initial native allowance baseDrops state)
    (positive : 0 < pathRank baseDrops state.2) : state.2.waiting = false := by
  apply invariant.2.2
  have lower := invariant.2.1
  unfold pathRank at positive
  split at positive <;> omega

private theorem path_rank_le (invariant : PathInvariant initial native allowance baseDrops before)
    (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (edge : (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system.step before event after) :
    pathRank baseDrops after.2 ≤ pathRank baseDrops before.2 := by
  have next := path_preserve invariant wire positive budget edge
  have counts := edge_counts invariant.1 wire positive budget edge
  by_cases dropped : baseDrops < before.2.drops.length
  · rw [pathRank_dropped before.2 dropped, pathRank_dropped after.2 (by omega)]
    exact Nat.le_refl _
  · by_cases resolved : baseDrops < after.2.drops.length
    · rw [pathRank_dropped after.2 resolved]
      omega
    · have first : before.2.drops.length = baseDrops := by have lower := invariant.2.1; omega
      have last : after.2.drops.length = baseDrops := by have lower := next.2.1; omega
      obtain ⟨_, _, _, ⟨old⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence invariant.1
      obtain ⟨_, _, _, ⟨new⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence next.1
      have oldCount := retries_eq_drops old (invariant.2.2 first)
      have newCount := retries_eq_drops new (next.2.2 last)
      apply pathRank_le_of_rank_le (config initial native quantum allowance) before.1 after.1 before.2 after.2
        (invariant.2.2 first) (next.2.2 last) (by omega) (by omega)
      exact (CampusTCPGapProgressProgress.transition wire invariant.1 positive budget edge).nonincrease

private theorem path_rank_lt (invariant : PathInvariant initial native allowance baseDrops before)
    (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (edge : (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system.step before event after)
    (begun : 0 < pathRank baseDrops before.2)
    (rank : after.2.rank (config initial native quantum allowance) after.1 < before.2.rank (config initial native quantum allowance) before.1) :
    pathRank baseDrops after.2 < pathRank baseDrops before.2 := by
  have next := path_preserve invariant wire positive budget edge
  by_cases resolved : baseDrops < after.2.drops.length
  · rw [pathRank_dropped after.2 resolved]
    exact begun
  · have counts := edge_counts invariant.1 wire positive budget edge
    have first : before.2.drops.length = baseDrops := by
      have lower := invariant.2.1
      have upper := next.2.1
      omega
    have last : after.2.drops.length = baseDrops := by have lower := next.2.1; omega
    obtain ⟨_, _, _, ⟨old⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence invariant.1
    obtain ⟨_, _, _, ⟨new⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence next.1
    have oldCount := retries_eq_drops old (invariant.2.2 first)
    have newCount := retries_eq_drops new (next.2.2 last)
    exact pathRank_lt_of_rank_lt (config initial native quantum allowance) before.1 after.1 before.2 after.2
      (invariant.2.2 first) (next.2.2 last) (by omega) (by omega) begun rank

private theorem path_rank_same (invariant : PathInvariant initial native allowance baseDrops before)
    (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (edge : (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system.step before event after)
    (begun : 0 < pathRank baseDrops before.2) (rank : pathRank baseDrops after.2 = pathRank baseDrops before.2) :
    after.2.rank (config initial native quantum allowance) after.1 = before.2.rank (config initial native quantum allowance) before.1 := by
  have next := path_preserve invariant wire positive budget edge
  have oldActive := path_active invariant begun
  have newActive := path_active next (by omega)
  obtain ⟨_, _, _, ⟨old⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence invariant.1
  obtain ⟨_, _, _, ⟨new⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence next.1
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
  exact rank_eq_of_pathRank_eq (config initial native quantum allowance) before.1 after.1 before.2 after.2 oldActive newActive
    (by omega) (by omega) begun rank

def pathAdapter (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance baseDrops : Nat)
    (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2) : Theory.BoundedProgress.Adapter (State input × M.Monitor) Event CampusTCPGapProgressMonitor.Demand where
  system := (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system
  invariant := PathInvariant initial native allowance baseDrops
  pending state demand := 0 < pathRank baseDrops state.2 ∧
    (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).pending state demand
  enabled := (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).enabled
  serves := (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).serves
  rank state := pathRank baseDrops state.2
  complete state := pathRank baseDrops state.2 = 0
  preserve := by intro _ _ _ invariant edge; exact path_preserve invariant wire positive budget edge
  nonincrease := by intro _ _ _ invariant edge; exact path_rank_le invariant wire positive budget edge
  demand := by
    intro state invariant begun
    have mainPositive := pathRank_positive_main (config initial native quantum allowance) state.1 state.2 (path_active invariant begun) begun
    obtain ⟨demand, pending⟩ := (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).demand invariant.1 mainPositive
    exact ⟨demand, begun, pending⟩
  pending_enabled := by
    intro _ _ invariant pending
    exact (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).pending_enabled invariant.1 pending.2
  persistent := by
    intro before event after demand invariant edge same pending
    refine ⟨by omega, ?_⟩
    exact (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).persistent invariant.1 edge
      (path_rank_same invariant wire positive budget edge pending.1 same) pending.2
  advance := by
    intro before event after demand invariant edge pending enabled served
    apply path_rank_lt invariant wire positive budget edge pending.1
    exact (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).advance invariant.1 edge pending.2 enabled served
  finished := by intro _ _ zero; exact zero

theorem path_service (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system)
    (service : execution.ServiceFrom (adapter := CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget) bound first) :
    execution.ServiceFrom (adapter := pathAdapter initial native quantum allowance baseDrops wire positive budget) bound first := by
  intro start begun within demand pending persistent
  exact service start begun within demand pending.2 (fun offset inside => (persistent offset inside).2)


theorem pathRank_dataLink (monitor : M.Monitor) (phase : monitor.phase = .dataLink) :
    pathRank monitor.drops.length monitor = 5 := by
  simp only [pathRank, Nat.lt_irrefl, ite_false, phase, CampusTCPRoundMonitor.Phase.rank]

theorem prefix_time_growth (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system)
    (invariant : CampusTCPGapProgressProgress.Invariant initial native allowance (execution.state 0))
    (actor : Actor) (start count : Nat) (within : start + count ≤ execution.length) :
    endpointNow (execution.state (start + count)).1 actor ≤ endpointNow (execution.state start).1 actor + quantum * count := by
  apply time_growth (fun slot => endpointNow (execution.state slot).1 actor) quantum start count
  intro slot _ inside
  have atSlot := execution.invariant
    (adapter := CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget) invariant slot (by omega)
  obtain ⟨current, final, _, ⟨evidence⟩⟩ := CampusTCPGapProgressProgress.invariant_evidence atSlot
  obtain ⟨allowed, actual, before, selected, result, _⟩ := execution.checked slot (by omega)
  have admitted : M.Allowed (config initial native quantum allowance) current.report.final (execution.state slot).2 actual.event := by
    rw [final, selected]
    exact allowed
  have growth := Step.now_le actual evidence (before.trans final.symm) actor admitted
  simpa only [result, final] using growth

theorem path_resolves_by (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system)
    (invariant : CampusTCPGapProgressProgress.Invariant initial native allowance (execution.state 0))
    (active : (execution.state 0).2.waiting = false)
    (service : execution.ServiceBound (adapter := CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget) bound)
    (within : pathRank (execution.state 0).2.drops.length (execution.state 0).2 * bound ≤ execution.length) :
    pathRank (execution.state 0).2.drops.length
      (execution.state (pathRank (execution.state 0).2.drops.length (execution.state 0).2 * bound)).2 = 0 := by
  have localInvariant : PathInvariant initial native allowance (execution.state 0).2.drops.length (execution.state 0) :=
    ⟨invariant, Nat.le_refl _, fun _ => active⟩
  have resolved := execution.zero_by
    (adapter := pathAdapter initial native quantum allowance (execution.state 0).2.drops.length wire positive budget)
    localInvariant (path_service wire positive budget execution service) 0 (Nat.zero_le _)
    (by simpa only [pathAdapter, Nat.zero_add] using within)
  simpa only [pathAdapter, Nat.zero_add] using resolved

private theorem output_phase (cfg : CampusTCPGapProgressMonitor.Config) (monitor : M.Monitor)
    (actual : Step input) (data : Bool) (phase) :
    (CampusTCPGapProgressMonitor.observeOutput cfg monitor actual data phase).phase = phase ∨
      (CampusTCPGapProgressMonitor.observeOutput cfg monitor actual data phase).phase = .invalid := by
  unfold CampusTCPGapProgressMonitor.observeOutput
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split | (dsimp only; split)

private theorem assignment_phase (monitor : M.Monitor) (actual : Step input) (data : Bool) (phase) :
    (CampusTCPGapProgressMonitor.observeAssignment monitor actual data phase).phase = phase ∨
      (CampusTCPGapProgressMonitor.observeAssignment monitor actual data phase).phase = .invalid := by
  unfold CampusTCPGapProgressMonitor.observeAssignment
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split | (dsimp only; split)

private theorem service_phase (monitor : M.Monitor) (actual : Step input) (data : Bool) (phase) :
    (CampusTCPGapProgressMonitor.observeService monitor actual data phase).phase = phase ∨
      (CampusTCPGapProgressMonitor.observeService monitor actual data phase).phase = .invalid := by
  unfold CampusTCPGapProgressMonitor.observeService
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split | (dsimp only; split)

private theorem receipt_phase (cfg : CampusTCPGapProgressMonitor.Config) (monitor : M.Monitor)
    (actual : Step input) (data : Bool) (phase) :
    (CampusTCPGapProgressMonitor.observeReceipt cfg monitor actual data phase).phase = phase ∨
      (CampusTCPGapProgressMonitor.observeReceipt cfg monitor actual data phase).phase = .invalid := by
  unfold CampusTCPGapProgressMonitor.observeReceipt
  repeat' first | (solve | exact .inl rfl) | (solve | exact .inr rfl) | split | (dsimp only; split)

private theorem low_phase_false (monitor : M.Monitor) (phase : CampusTCPRoundMonitor.Phase)
    (low : monitor.phase.rank ≤ 1) (large : 1 < phase.rank) (choice : monitor.phase = phase ∨ monitor.phase = .invalid) : False := by
  rcases choice with selected | invalid
  · rw [selected] at low
    omega
  · simp only [invalid, CampusTCPRoundMonitor.Phase.rank] at low
    omega

private theorem actor_eq {left right : Actor} (same : (left == right) = true) : left = right := by
  cases left <;> cases right <;> first | rfl | cases same

private theorem ack_receipt (cfg : CampusTCPGapProgressMonitor.Config) (monitor : M.Monitor) (actual : Step input)
    (low : (CampusTCPGapProgressMonitor.observeReceipt cfg monitor actual false .needRead).phase.rank ≤ 1) :
    ∃ receipt, actual.result.receipt = some receipt ∧ receipt.actor = cfg.sender := by
  unfold CampusTCPGapProgressMonitor.observeReceipt at low
  cases present : actual.result.receipt with
  | none => simp only [present, CampusTCPGapProgressMonitor.Monitor.invalid, CampusTCPRoundMonitor.Phase.rank] at low; omega
  | some receipt =>
    cases applied : actual.result.application with
    | none => simp only [present, applied, CampusTCPGapProgressMonitor.Monitor.invalid,
        CampusTCPRoundMonitor.Phase.rank] at low; omega
    | some pair =>
      obtain ⟨actor, operation⟩ := pair
      simp only [present, applied, Bool.false_eq_true, ite_false] at low
      split at low
      · rename_i matching
        exact ⟨receipt, rfl, actor_eq (Bool.and_eq_true_iff.mp matching).1⟩
      · simp only [CampusTCPGapProgressMonitor.Monitor.invalid, CampusTCPRoundMonitor.Phase.rank] at low
        omega

private theorem advance_low_receipt (cfg : CampusTCPGapProgressMonitor.Config) (monitor : M.Monitor)
    (actual : Step input) (begun : 1 < monitor.phase.rank)
    (low : (CampusTCPGapProgressMonitor.advance cfg monitor actual).phase.rank ≤ 1) :
    ∃ receipt, actual.result.receipt = some receipt ∧ receipt.actor = cfg.sender := by
  cases phase : monitor.phase
  all_goals simp only [CampusTCPGapProgressMonitor.advance, phase] at low
  case needSend => simp only [CampusTCPGapProgressMonitor.Monitor.invalid, CampusTCPRoundMonitor.Phase.rank] at low; omega
  case dataIngress => exact False.elim (low_phase_false _ .dataTicket low (by decide) (assignment_phase _ _ _ _))
  case dataTicket => exact False.elim (low_phase_false _ .dataLink low (by decide) (service_phase _ _ _ _))
  case dataLink => exact False.elim (low_phase_false _ .needAck low (by decide) (receipt_phase _ _ _ _ _))
  case needAck => exact False.elim (low_phase_false _ .ackIngress low (by decide) (output_phase _ _ _ _ _))
  case ackIngress => exact False.elim (low_phase_false _ .ackTicket low (by decide) (assignment_phase _ _ _ _))
  case ackTicket => exact False.elim (low_phase_false _ .ackLink low (by decide) (service_phase _ _ _ _))
  case ackLink => exact ack_receipt _ _ _ low
  case needRead => simp only [phase, CampusTCPRoundMonitor.Phase.rank] at begun; omega
  case done => simp only [phase, CampusTCPRoundMonitor.Phase.rank] at begun; omega
  case invalid => simp only [CampusTCPGapProgressMonitor.Monitor.invalid, CampusTCPRoundMonitor.Phase.rank] at low; omega

private theorem advance_drops (cfg : CampusTCPGapProgressMonitor.Config) (monitor : M.Monitor) (actual : Step input) :
    (CampusTCPGapProgressMonitor.advance cfg monitor actual).drops = monitor.drops := by
  unfold CampusTCPGapProgressMonitor.advance CampusTCPGapProgressMonitor.observeAssignment
    CampusTCPGapProgressMonitor.observeService CampusTCPGapProgressMonitor.observeReceipt
    CampusTCPGapProgressMonitor.observeOutput
  repeat' first | (solve | rfl) | (solve | dsimp only; rfl) | split | (dsimp only; split)

private theorem primary_resolution_receipt (wire : Geometry initial) (evidence : Evidence initial native allowance current monitor)
    (sources : SourceHistory initial current monitor) (positive : 0 < quantum) (budget : allowance ≤ 2) (actual : Step input) (before : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (active : monitor.waiting = false) (begun : 0 < pathRank baseDrops monitor)
    (action : CampusTCPRoundMonitor.Action)
    (pending : CampusTCPGapProgressMonitor.nextAction (config initial native quantum allowance) current.report.final monitor = some action)
    (event : actual.event = action.event)
    (resolved : pathRank baseDrops (CampusTCPGapProgressMonitor.observe (config initial native quantum allowance) monitor actual) = 0) :
    ∃ receipt, actual.result.receipt = some receipt ∧ receipt.actor = sender := by
  obtain ⟨checked⟩ := CampusTCPGapProgressProgress.checked_step wire evidence sources positive budget actual before allowed
  have selected : CampusTCPGapProgressMonitor.nextAction (config initial native quantum allowance) actual.before monitor = some action := by
    rw [before]
    exact pending
  have observed := CampusTCPGapProgressMonitorFacts.observe_action (config initial native quantum allowance) monitor actual active
    checked.move.supported checked.move.passed action selected event
  have notDropped : ¬baseDrops < monitor.drops.length := by
    intro dropped
    rw [pathRank_dropped _ dropped] at begun
    omega
  have large : 1 < monitor.phase.rank := by
    simp only [pathRank, notDropped, ite_false] at begun
    omega
  have low : (CampusTCPGapProgressMonitor.advance (config initial native quantum allowance) monitor actual).phase.rank ≤ 1 := by
    rw [observed] at resolved
    simp only [pathRank, advance_drops, notDropped, ite_false] at resolved
    omega
  exact advance_low_receipt _ _ _ large low

def Resolution (cfg : CampusTCPGapProgressMonitor.Config) (state : State input) (monitor : M.Monitor) (actual : Step input) : Prop :=
  (∃ action packet, CampusTCPGapProgressMonitor.nextDemand cfg state monitor = some (.resolution action packet) ∧
    actual.event = .dropPacket packet) ∨ ∃ receipt, actual.result.receipt = some receipt ∧ receipt.actor = cfg.sender

theorem Step.path_resolution (wire : Geometry initial) (evidence : Evidence initial native allowance current monitor)
    (sources : SourceHistory initial current monitor) (positive : 0 < quantum) (budget : allowance ≤ 2) (actual : Step input) (before : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (active : monitor.waiting = false) (begun : 0 < pathRank baseDrops monitor)
    (resolved : pathRank baseDrops (CampusTCPGapProgressMonitor.observe (config initial native quantum allowance) monitor actual) = 0) :
    Resolution (config initial native quantum allowance) current.report.final monitor actual := by
  obtain ⟨selected, _⟩ := (CampusTCPGapProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
  rcases selected with ⟨demand, pending, served⟩ | free
  · obtain ⟨action, next, shape⟩ := CampusTCPGapProgressMonitorFacts.nextDemand_action_exists _ _ _ active demand pending
    rcases shape with event | ⟨packet, event⟩
    · subst demand
      exact .inr (primary_resolution_receipt wire evidence sources positive budget actual before allowed active begun action next
        ((CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp served) resolved)
    · subst demand
      rcases (CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _).mp served with event | event
      · exact .inr (primary_resolution_receipt wire evidence sources positive budget actual before allowed active begun action next event resolved)
      · exact .inl ⟨action, packet, pending, event⟩
  · obtain ⟨actor, millis, event, _⟩ := CampusTCPGapProgressMonitorFacts.freeClock_event _ _ _ _ free
    obtain ⟨checked⟩ := CampusTCPGapProgressProgress.checked_step wire evidence sources positive budget actual before allowed
    rw [CampusTCPGapProgressMonitorFacts.observe_clock _ _ _ checked.move.supported checked.move.passed actor millis event] at resolved
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

theorem path_resolution_by (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system)
    (invariant : CampusTCPGapProgressProgress.Invariant initial native allowance (execution.state 0))
    (active : (execution.state 0).2.waiting = false)
    (started : pathRank (execution.state 0).2.drops.length (execution.state 0).2 = path)
    (nonzero : 0 < path)
    (service : execution.ServiceBound (adapter := CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget) bound)
    (within : path * bound ≤ execution.length) :
    ∃ slot, slot < path * bound ∧ ∃ actual : Step input,
      actual.before = (execution.state slot).1 ∧ actual.event = execution.action slot ∧
      actual.result.state = (execution.state (slot + 1)).1 ∧
      Resolution (config initial native quantum allowance) (execution.state slot).1 (execution.state slot).2 actual ∧
      ∀ offset, offset ≤ slot → 0 < pathRank (execution.state 0).2.drops.length (execution.state offset).2 := by
  let base := (execution.state 0).2.drops.length
  have localInvariant : PathInvariant initial native allowance base (execution.state 0) :=
    ⟨invariant, Nat.le_refl _, fun _ => active⟩
  obtain ⟨slot, inside, begun, last⟩ := first_zero (fun slot => pathRank base (execution.state slot).2)
    (by rw [started]; exact nonzero) (by
      have resolved := path_resolves_by wire positive budget execution invariant active service (by rw [started]; exact within)
      simpa only [started] using resolved)
  have localAt := execution.invariant
    (adapter := pathAdapter initial native quantum allowance base wire positive budget) localInvariant slot (by omega)
  obtain ⟨current, final, _, sources, ⟨evidence⟩⟩ := CampusTCPGapProgressProgress.invariant_sources localAt.1
  obtain ⟨allowed, actual, before, event, result, observed⟩ := execution.checked slot (by omega)
  have allowedHere : M.Allowed (config initial native quantum allowance) current.report.final (execution.state slot).2 actual.event := by
    rw [final, event]
    exact allowed
  have resolved : pathRank base (CampusTCPGapProgressMonitor.observe (config initial native quantum allowance) (execution.state slot).2 actual) = 0 := by
    rw [observed]
    exact last
  have resolution := Step.path_resolution wire evidence sources positive budget actual (before.trans final.symm) allowedHere
    (path_active localAt begun) begun resolved
  refine ⟨slot, inside, actual, before, event, result, by simpa only [final] using resolution, ?_⟩
  intro offset earlier
  have order := execution.rank_mono
    (adapter := pathAdapter initial native quantum allowance base wire positive budget)
    localInvariant earlier (show slot ≤ execution.length by omega)
  change pathRank base (execution.state slot).2 ≤ pathRank base (execution.state offset).2 at order
  change 0 < pathRank base (execution.state offset).2
  omega

private theorem active_no_timeout (cfg : CampusTCPGapProgressMonitor.Config) (state : State input) (monitor : M.Monitor)
    (active : monitor.waiting = false) : ¬M.Allowed cfg state monitor (.timeout cfg.sender true) := by
  intro allowed
  obtain ⟨selected, _⟩ := (CampusTCPGapProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
  rcases selected with ⟨demand, pending, served⟩ | free
  · obtain ⟨action, _, shape⟩ := CampusTCPGapProgressMonitorFacts.nextDemand_action_exists _ _ _ active demand pending
    rcases shape with same | ⟨packet, same⟩
    · subst demand
      have event := (CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp served
      cases action <;> cases event
    · subst demand
      rcases (CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _).mp served with event | event
      · cases action <;> cases event
      · cases event
  · obtain ⟨actor, millis, event, _⟩ := CampusTCPGapProgressMonitorFacts.freeClock_event _ _ _ _ free
    cases event

structure TimedResolution (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance path bound due : Nat)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPGapProgressMonitor.guardedSystem input (config initial native quantum allowance))) where
  slot : Nat
  within : slot < path * bound
  actual : Step input
  before : actual.before = (execution.state slot).1
  event : actual.event = execution.action slot
  result : actual.result.state = (execution.state (slot + 1)).1
  resolution : Resolution (config initial native quantum allowance) (execution.state slot).1 (execution.state slot).2 actual
  early : ∀ offset, offset ≤ slot + 1 → endpointNow (execution.state offset).1 sender < due
  noTimeout : ∀ offset, offset ≤ slot → execution.action offset ≠ .timeout sender true

private theorem timed_resolution (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system)
    (invariant : CampusTCPGapProgressProgress.Invariant initial native allowance (execution.state 0))
    (active : (execution.state 0).2.waiting = false)
    (started : pathRank (execution.state 0).2.drops.length (execution.state 0).2 = path) (nonzero : 0 < path)
    (service : execution.ServiceBound (adapter := CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget) bound)
    (within : path * bound ≤ execution.length)
    (timely : quantum * (path * bound) < due - endpointNow (execution.state 0).1 sender) :
    Nonempty (TimedResolution initial native quantum allowance path bound due execution) := by
  obtain ⟨slot, inside, actual, before, event, result, resolution, previous⟩ :=
    path_resolution_by wire positive budget execution invariant active started nonzero service within
  refine ⟨⟨slot, inside, actual, before, event, result, resolution, ?_, ?_⟩⟩
  · intro offset selected
    have growth := prefix_time_growth wire positive budget execution invariant sender 0 offset (by omega)
    simp only [Nat.zero_add] at growth
    exact before_deadline_of_slots quantum path bound offset _ _ due (by omega) timely growth
  · intro offset selected timeout
    have localInvariant : PathInvariant initial native allowance (execution.state 0).2.drops.length (execution.state 0) :=
      ⟨invariant, Nat.le_refl _, fun _ => active⟩
    have localAt := execution.invariant
      (adapter := pathAdapter initial native quantum allowance (execution.state 0).2.drops.length wire positive budget)
      localInvariant offset (by omega)
    have oldActive := path_active localAt (previous offset selected)
    obtain ⟨allowed, _⟩ := execution.checked offset (by omega)
    rw [timeout] at allowed
    exact active_no_timeout _ _ _ oldActive allowed

theorem initial_path_timed (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system)
    (invariant : CampusTCPGapProgressProgress.Invariant initial native allowance (execution.state 0))
    (start : execution.state 0 = (cut.report.final, CampusTCPGapProgressSetup.initialMonitor initial))
    (service : execution.ServiceBound (adapter := CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget) bound)
    (within : 5 * bound ≤ execution.length)
    (timely : quantum * (5 * bound) < (config initial native quantum allowance).initialRemaining) :
    initial.flight.recovery.deadline = some (initial.flight.head.lastAt + initial.flight.recovery.rto) ∧
    Nonempty (TimedResolution initial native quantum allowance 5 bound
      (initial.flight.head.lastAt + initial.flight.recovery.rto) execution) := by
  have active : (execution.state 0).2.waiting = false := by rw [start]; rfl
  have phase : (execution.state 0).2.phase = .dataLink := by rw [start]; rfl
  refine ⟨initial.flight.deadline, timed_resolution wire positive budget execution invariant active
    (pathRank_dataLink _ phase) (by decide) service within ?_⟩
  rw [start, ← initial_remaining initial native quantum allowance]
  exact timely

theorem retry_path_timed (retry : CampusTCPGapProgressRetry.Retry live actual) (wire : Geometry initial)
    (positive : 0 < quantum) (budget : allowance ≤ 2) (waiting : monitor.waiting = true)
    (execution : Theory.BoundedProgress.Prefix (CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget).system)
    (invariant : CampusTCPGapProgressProgress.Invariant initial native allowance (execution.state 0))
    (start : execution.state 0 = (retry.move.after.report.final,
      CampusTCPGapProgressMonitor.observe (config initial native quantum allowance) monitor actual))
    (service : execution.ServiceBound (adapter := CampusTCPGapProgressProgress.adapter initial native quantum allowance wire positive budget) bound)
    (within : 7 * bound ≤ execution.length)
    (timely : quantum * (7 * bound) < retry.next.senderFlight.recovery.rto) :
    retry.next.senderFlight.recovery.deadline = some (retry.next.senderFlight.head.lastAt + retry.next.senderFlight.recovery.rto) ∧
    Nonempty (TimedResolution initial native quantum allowance 7 bound
      (retry.next.senderFlight.head.lastAt + retry.next.senderFlight.recovery.rto) execution) := by
  have active : (execution.state 0).2.waiting = false := by rw [start, retry.observe native quantum allowance monitor waiting]
  have phase : (execution.state 0).2.phase = .dataIngress := by rw [start, retry.observe native quantum allowance monitor waiting]
  have started : endpointNow (execution.state 0).1 sender = retry.next.senderFlight.head.lastAt := by
    rw [start, endpointNow_application _ retry.move.after.connection]
    exact (retry_lastAt_now retry).symm
  refine ⟨retry.next.senderFlight.deadline, timed_resolution wire positive budget execution invariant active
    (pathRank_dataIngress _ phase) (by decide) service within ?_⟩
  simpa only [started, Nat.add_sub_cancel_left] using timely

end Netlib.Check.CampusTCPGapProgressTiming
