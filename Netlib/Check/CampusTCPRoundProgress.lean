import Netlib.Check.CampusTCPRoundPhaseBase
import Netlib.Check.CampusTCPRoundServiceBound
import Netlib.Check.CampusTCPRoundPhaseForward
import Netlib.Check.CampusTCPRoundPhaseReverse

/-!
# Evidence across scheduled TCP round operations

Clock slots retain the actual packet-operation anchors.
Completion retains the actual read and sender retirement.
-/

namespace Netlib.Check.CampusTCPRoundProgress

open CampusTCPModel CampusTCPEnabled CampusTCPRound CampusTCPRoundStart CampusTCPRoundPhaseBase
open CampusTCPRoundMonitor

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}
variable {current : Cut input complete} {monitor : Monitor}

def Invariant (initial : Initial report complete request) (native : NativeEnv initial)
    (state : State input × Monitor) : Prop :=
  ∃ current : Cut input complete, current.report.final = state.1 ∧ Nonempty (Evidence initial native current state.2)

structure SelectedStep (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (monitor : Monitor) where
  action : Action
  selected : nextAction (config initial native) current.report.final monitor = some action
  actual : Step input
  move : Move current actual
  event : actual.event = action.event
  evidence : Nonempty (Evidence initial native move.after (observe (config initial native) monitor actual))
  decreases : (observe (config initial native) monitor actual).rank + 1 = monitor.rank

private theorem package_step {prior : Cut input complete} {priorMonitor : Monitor} {previous next : Phase}
    {action : Action} (anchor : Anchor initial native prior priorMonitor previous (some action))
    (placement : Current prior priorMonitor current monitor) (hop : Hop prior priorMonitor)
    (before : hop.before = current) (event : hop.actual.event = action.event)
    (evidence : Nonempty (Evidence initial native hop.post (hop.monitor (config initial native))))
    (phase : (hop.monitor (config initial native)).phase = next) (rank : next.rank + 1 = previous.rank) :
    Nonempty (SelectedStep initial native current monitor) := by
  subst current
  refine ⟨⟨action, placement.next _ anchor.next, hop.actual, hop.move, event, ?_, ?_⟩⟩
  · simpa only [placement.monitorEq, Hop.monitor, Hop.post] using evidence
  · have oldPhase : monitor.phase = previous := by rw [placement.monitorEq]; exact anchor.phaseEq
    have nextPhase : (observe (config initial native) monitor hop.actual).phase = next := by
      rw [placement.monitorEq]
      exact phase
    simpa only [Monitor.rank, oldPhase, nextPhase] using rank

theorem selected_step (evidence : Evidence initial native current monitor) (positive : 0 < monitor.rank) :
    Nonempty (SelectedStep initial native current monitor) := by
  cases evidence with
  | started record placement =>
    obtain ⟨next, before⟩ := CampusTCPRoundPhaseForward.send_at initial native current placement.placement
    exact package_step record.anchor placement next.hop before next.event
      ⟨.sent next (Current.refl _ _)⟩ next.anchor.phaseEq (by decide)
  | sent record placement =>
    obtain ⟨next, before⟩ := CampusTCPRoundPhaseForward.assign_at record current placement.placement
    exact package_step record.anchor placement next.hop before next.facts.event
      ⟨.assigned record next (Current.refl _ _)⟩ next.anchor.phaseEq (by decide)
  | assigned sent record placement =>
    obtain ⟨next, before⟩ := CampusTCPRoundPhaseForward.serve_data_at record current placement.placement
    exact package_step record.anchor placement next.hop before next.facts.event
      ⟨.dataServed sent record next (Current.refl _ _)⟩ next.anchor.phaseEq (by decide)
  | dataServed sent assigned record placement =>
    obtain ⟨next, before⟩ := CampusTCPRoundPhaseForward.release_data_at record current placement.placement
    have event : next.hop.actual.event = .deliver record.index record.emission.bytes true := by
      rw [← next.actual]
      exact next.delivery.event
    exact package_step record.anchor placement next.hop before event
      ⟨.released sent assigned record next (Current.refl _ _)⟩ next.anchor.phaseEq (by decide)
  | released sent assigned service record placement =>
    obtain ⟨next, before⟩ := CampusTCPRoundPhaseForward.emit_ack_at record current placement.placement
    exact package_step record.anchor placement next.hop before next.facts.event
      ⟨.acked sent assigned service record next (Current.refl _ _)⟩ next.anchor.phaseEq (by decide)
  | acked sent assigned service released record placement =>
    obtain ⟨next, before⟩ := CampusTCPRoundPhaseReverse.assign_ack_at record current placement.placement
    exact package_step record.anchor placement next.hop before next.facts.event
      ⟨.ackAssigned sent assigned service released record next (Current.refl _ _)⟩ next.anchor.phaseEq (by decide)
  | ackAssigned sent assigned service released ack record placement =>
    obtain ⟨next, before⟩ := CampusTCPRoundPhaseReverse.serve_ack_at record current placement.placement
    exact package_step record.anchor placement next.hop before next.facts.event
      ⟨.ackServed sent assigned service released ack record next (Current.refl _ _)⟩ next.anchor.phaseEq (by decide)
  | ackServed sent assigned service released ack assignedAck record placement =>
    obtain ⟨next, before⟩ := CampusTCPRoundPhaseReverse.deliver_ack_at record current placement.placement
    have event : next.hop.actual.event = .deliver record.index record.emission.bytes true := by
      rw [← next.actual]
      exact next.delivery.event
    exact package_step record.anchor placement next.hop before event
      ⟨.retired sent assigned service released ack assignedAck record next (Current.refl _ _)⟩ next.anchor.phaseEq (by decide)
  | retired sent assigned service released ack assignedAck ackService record placement =>
    obtain ⟨next, before⟩ := CampusTCPRoundPhaseReverse.read_at record current placement.placement
    exact package_step record.anchor placement next.hop before next.event
      ⟨.read sent assigned service released ack assignedAck ackService record next (Current.refl _ _)⟩ next.anchor.phaseEq (by decide)
  | read sent assigned service released ack assignedAck ackService retired record placement =>
    simp only [Monitor.rank, placement.monitorEq, record.anchor.phaseEq, Phase.rank, Nat.lt_irrefl] at positive

theorem pending_positive (evidence : Evidence initial native current monitor)
    (pending : nextAction (config initial native) current.report.final monitor = some action) : 0 < monitor.rank := by
  cases evidence <;> rename_i record placement
  all_goals first
    | (simp only [Monitor.rank, placement.monitorEq, record.anchor.phaseEq, Phase.rank]; decide)
    | have missing := placement.next _ record.anchor.next
      rw [missing] at pending
      cases pending

theorem advance (evidence : Evidence initial native current monitor) (actual : Step input)
    (before : actual.before = current.report.final)
    (selected : nextEvent (config initial native) current.report.final monitor = some actual.event) :
    ∃ move : Move current actual,
      Nonempty (Evidence initial native move.after (observe (config initial native) monitor actual)) ∧
      (observe (config initial native) monitor actual).rank + 1 = monitor.rank := by
  obtain ⟨action, pending, event⟩ := nextEvent_action _ _ _ _ selected
  obtain ⟨chosen⟩ := selected_step evidence (pending_positive evidence pending)
  have actionEq : action = chosen.action := Option.some.inj (pending.symm.trans chosen.selected)
  have eventEq : actual.event = chosen.actual.event := event.trans (actionEq ▸ chosen.event.symm)
  have actualEq : actual = chosen.actual :=
    CampusTCPRoundPhaseBase.Step.eq_of_before_event actual chosen.actual
      (before.trans chosen.move.beforeEq.symm) eventEq
  subst actual
  exact ⟨chosen.move, chosen.evidence, chosen.decreases⟩

theorem clock_event (current : Cut input complete) (event : Event)
    (selected : sameClock current.report.final event = true) :
    ∃ actor, event = .advanceClock actor (endpoint current.endpoints actor).now := by
  cases event <;> simp only [sameClock, current.connection, Bool.false_eq_true] at selected
  all_goals try contradiction
  rename_i actor now
  have pair : (endpoint current.endpoints actor).recovery.isSome = true ∧
      (now == (endpoint current.endpoints actor).now) = true := by
    simpa only [Bool.and_eq_true] using selected
  have time : now = (endpoint current.endpoints actor).now := by simpa only [beq_iff_eq] using pair.2
  exact ⟨actor, by rw [time]⟩

theorem clock (evidence : Evidence initial native current monitor) (actual : Step input)
    (before : actual.before = current.report.final) (actor : Actor)
    (event : actual.event = .advanceClock actor (endpoint current.endpoints actor).now) :
    ∃ move : Move current actual,
      Nonempty (Evidence initial native move.after (observe (config initial native) monitor actual)) := by
  have guards := evidence.guards
  cases evidence <;> rename_i record placement
  all_goals
    obtain ⟨move, next⟩ := placement.clock (config initial native) actual before actor event guards
    refine ⟨move, ?_⟩
    first
    | exact ⟨.started record next⟩
    | exact ⟨.sent record next⟩
    | exact ⟨.assigned _ record next⟩
    | exact ⟨.dataServed _ _ record next⟩
    | exact ⟨.released _ _ _ record next⟩
    | exact ⟨.acked _ _ _ _ record next⟩
    | exact ⟨.ackAssigned _ _ _ _ _ record next⟩
    | exact ⟨.ackServed _ _ _ _ _ _ record next⟩
    | exact ⟨.retired _ _ _ _ _ _ _ record next⟩
    | exact ⟨.read _ _ _ _ _ _ _ _ record next⟩

theorem clock_pending (evidence : Evidence initial native current monitor) (actual : Step input)
    (before : actual.before = current.report.final) (actor : Actor)
    (event : actual.event = .advanceClock actor (endpoint current.endpoints actor).now) :
    nextAction (config initial native) actual.result.state (observe (config initial native) monitor actual) =
      nextAction (config initial native) current.report.final monitor := by
  obtain ⟨move, placement⟩ := (At.refl current).clock actual before actor event evidence.guards
  have selected : sameClock actual.before actual.event = true := by
    simp only [sameClock, before, event, current.connection, (evidence.guards actor).runtime,
      beq_self_eq_true, Bool.and_self]
  rw [observe_clock _ _ _ move.supported move.passed selected, ← move.final]
  exact Frame.nextAction placement.frame _ _

theorem transition (evidence : Evidence initial native current monitor) (actual : Step input)
    (before : actual.before = current.report.final)
    (allowed : Allowed (config initial native) current.report.final monitor actual.event) :
    ∃ move : Move current actual,
      Nonempty (Evidence initial native move.after (observe (config initial native) monitor actual)) ∧
      ((observe (config initial native) monitor actual).rank + 1 = monitor.rank ∨
        (observe (config initial native) monitor actual).rank = monitor.rank) := by
  rcases allowed with selected | selected
  · obtain ⟨move, next, decrease⟩ := advance evidence actual before selected
    exact ⟨move, next, .inl decrease⟩
  · obtain ⟨actor, event⟩ := clock_event current actual.event selected
    obtain ⟨move, next⟩ := clock evidence actual before actor event
    have clock : sameClock actual.before actual.event = true := before ▸ selected
    exact ⟨move, next, .inr (congrArg Monitor.rank (observe_clock _ _ _ move.supported move.passed clock))⟩

structure Completion (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (monitor : Monitor) where
  sent : CampusTCPRoundPhaseBase.Sent initial native
  assigned : CampusTCPRoundPhaseBase.Assigned sent
  service : CampusTCPRoundPhaseBase.DataServed assigned
  released : CampusTCPRoundPhaseBase.Released service
  ack : CampusTCPRoundPhaseBase.Acked released
  assignedAck : CampusTCPRoundPhaseBase.AckAssigned ack
  ackService : CampusTCPRoundPhaseBase.AckServed assignedAck
  retired : CampusTCPRoundPhaseBase.Retired ackService
  read : CampusTCPRoundPhaseBase.Read retired
  placement : Current read.hop.post (read.hop.monitor (config initial native)) current monitor

def Completed (initial : Initial report complete request) (native : NativeEnv initial)
    (state : State input × Monitor) : Prop :=
  ∃ current : Cut input complete, current.report.final = state.1 ∧ Nonempty (Completion initial native current state.2)

theorem initial_invariant (initial : Initial report complete request) (native : NativeEnv initial) :
    Invariant initial native (initial.state, Monitor.initial) :=
  ⟨Cut.ofPrepared initial.start, rfl, initial_evidence initial native⟩

theorem finished (evidence : Evidence initial native current monitor) (zero : monitor.rank = 0) :
    Nonempty (Completion initial native current monitor) := by
  cases evidence <;> rename_i record placement
  all_goals first
    | exact ⟨⟨_, _, _, _, _, _, _, _, record, placement⟩⟩
    | have positive : monitor.rank ≠ 0 := by
        simp only [Monitor.rank, placement.monitorEq, record.anchor.phaseEq, Phase.rank]
        decide
      exact False.elim (positive zero)

theorem Completion.read_member (done : Completion initial native current monitor) :
    done.read.hop.actual ∈ current.report.steps :=
  done.placement.placement.member done.read.hop.move.member

theorem Completion.read_bytes (done : Completion initial native current monitor) :
    done.read.hop.actual.result.read = request.bytes := done.read.returned

theorem Completion.read_event (done : Completion initial native current monitor) :
    done.read.hop.actual.event = .read .server request.bytes.length := done.read.event

theorem Completion.retirement (done : Completion initial native current monitor) :
    (endpoint current.endpoints .client).core.sent = [] ∧
      ∃ recovery, (endpoint current.endpoints .client).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 := by
  have sender := (done.placement.placement.frame.endpointEq .client).trans done.read.sender
  rw [sender]
  exact ⟨done.retired.delivery.sentEmpty, done.retired.delivery.nextRecovery, done.retired.delivery.runtime,
    done.retired.delivery.outstanding, done.retired.delivery.deadline, done.retired.delivery.timeoutCount⟩

variable {first last : State input × Monitor} {event : Event}

theorem edge_progress (prior : Invariant initial native first)
    (edge : (guardedSystem input (config initial native)).step first event last) :
    Invariant initial native last ∧ last.2.rank ≤ first.2.rank := by
  obtain ⟨current, same, ⟨evidence⟩⟩ := prior
  obtain ⟨allowed, actual, before, eventEq, after, observed⟩ := edge
  have old : actual.before = current.report.final := before.trans same.symm
  have permitted : Allowed (config initial native) current.report.final first.2 actual.event := by
    rw [same, eventEq]
    exact allowed
  obtain ⟨move, next, rank⟩ := transition evidence actual old permitted
  refine ⟨⟨move.after, move.final.trans after, ?_⟩, ?_⟩
  · simpa only [observed] using next
  · rcases rank with less | equal
    · rw [observed] at less
      omega
    · rw [observed] at equal
      omega

theorem enabled (evidence : Evidence initial native current monitor)
    (pending : nextAction (config initial native) current.report.final monitor = some demand) :
    ∃ actual : Step input, actual.before = current.report.final ∧ actual.event = demand.event ∧ actual.result.supported = true := by
  obtain ⟨chosen⟩ := selected_step evidence (pending_positive evidence pending)
  have same : chosen.action = demand := Option.some.inj (chosen.selected.symm.trans pending)
  exact ⟨chosen.actual, chosen.move.beforeEq, chosen.event.trans (congrArg Action.event same), chosen.move.supported⟩

theorem pending_persistent (prior : Invariant initial native first)
    (edge : (guardedSystem input (config initial native)).step first event last)
    (sameRank : last.2.rank = first.2.rank)
    (pending : nextAction (config initial native) first.1 first.2 = some demand) :
    nextAction (config initial native) last.1 last.2 = some demand := by
  obtain ⟨current, same, ⟨evidence⟩⟩ := prior
  obtain ⟨allowed, actual, before, eventEq, after, observed⟩ := edge
  have old : actual.before = current.report.final := before.trans same.symm
  rcases allowed with selected | selected
  · have selectedAt : nextEvent (config initial native) current.report.final first.2 = some actual.event := by
      rw [same, eventEq]
      exact selected
    obtain ⟨_, _, less⟩ := advance evidence actual old selectedAt
    rw [observed] at less
    omega
  · have clock : sameClock current.report.final actual.event = true := by rw [same, eventEq]; exact selected
    obtain ⟨actor, clockEq⟩ := clock_event current actual.event clock
    have fixed := clock_pending evidence actual old actor clockEq
    rw [after, observed, same] at fixed
    exact fixed.trans pending

theorem selected_decreases (prior : Invariant initial native first)
    (edge : (guardedSystem input (config initial native)).step first event last)
    (pending : nextAction (config initial native) first.1 first.2 = some demand)
    (served : actionOf event = some demand) : last.2.rank < first.2.rank := by
  obtain ⟨current, same, ⟨evidence⟩⟩ := prior
  obtain ⟨_, actual, before, eventEq, _, observed⟩ := edge
  have old : actual.before = current.report.final := before.trans same.symm
  have eventAction : event = demand.event := CampusTCPRoundServiceBound.action_event event demand served
  have selected : nextEvent (config initial native) current.report.final first.2 = some actual.event := by
    rw [same, eventEq, eventAction]
    simp only [nextEvent, pending, Option.map_some]
  obtain ⟨_, _, less⟩ := advance evidence actual old selected
  rw [observed] at less
  omega

def adapter (initial : Initial report complete request) (native : NativeEnv initial) :
    Theory.BoundedProgress.Adapter (State input × Monitor) Event Action where
  system := guardedSystem input (config initial native)
  invariant := Invariant initial native
  pending state demand := nextAction (config initial native) state.1 state.2 = some demand
  enabled state demand := ∃ actual : Step input,
    actual.before = state.1 ∧ actual.event = demand.event ∧ actual.result.supported = true
  serves demand event := actionOf event = some demand
  rank state := state.2.rank
  complete := Completed initial native
  preserve := by intro before event after prior edge; exact (edge_progress prior edge).1
  nonincrease := by intro before event after prior edge; exact (edge_progress prior edge).2
  demand := by
    intro state prior positive
    obtain ⟨current, same, ⟨evidence⟩⟩ := prior
    obtain ⟨action, pending⟩ := evidence.pending positive
    exact ⟨action, by simpa only [same] using pending⟩
  pending_enabled := by
    intro state demand prior pending
    obtain ⟨current, same, ⟨evidence⟩⟩ := prior
    have selected : nextAction (config initial native) current.report.final state.2 = some demand := by
      simpa only [same] using pending
    obtain ⟨actual, before, event, supported⟩ := enabled evidence selected
    exact ⟨actual, before.trans same, event, supported⟩
  persistent := by
    intro before event after demand prior edge same pending
    exact pending_persistent prior edge same pending
  advance := by
    intro before event after demand prior edge pending _enabled served
    exact selected_decreases prior edge pending served
  finished := by
    intro state prior zero
    obtain ⟨current, same, ⟨evidence⟩⟩ := prior
    exact ⟨current, same, finished evidence zero⟩

end Netlib.Check.CampusTCPRoundProgress
