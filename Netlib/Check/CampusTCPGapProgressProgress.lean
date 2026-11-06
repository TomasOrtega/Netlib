import Netlib.Check.CampusTCPGapProgressDemand
import Netlib.Check.CampusTCPGapProgressPhaseLoss
import Netlib.Check.CampusTCPGapProgressRank
import Netlib.Check.CampusTCPGapProgressSelected
import Netlib.Check.CampusTCPGapProgressClockRank
import Netlib.Check.CampusTCPGapProgressOrigins

/-!
# Concrete progress after an actual held-gap cut

Each state witness retains the actual current report.
Completion retains the actual read and retired sender range.
-/

namespace Netlib.Check.CampusTCPGapProgressProgress

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressWire (Geometry)
open CampusTCPGapProgressSetup (config)
open CampusTCPRound (Cut)
open CampusTCPGapProgressEvidence
open CampusTCPGapProgressMonitor
open CampusTCPGapProgressOrigins (SourceHistory LowerSource)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
variable {initial : GapInitial cut sender lower upper} {native : NativeEnv cut initial.gateway.seed.entry}
variable {quantum allowance : Nat} {monitor : Monitor} {demand : Demand}

def SuffixPassed (initial current : Cut input complete) : Prop :=
  ∃ extra, current.report.steps = initial.report.steps ++ extra ∧
    ∀ actual ∈ extra, actual.result.passed = true

theorem SuffixPassed.append (passed : SuffixPassed cut current)
    (move : CampusTCPRoundPhaseBase.Move current actual) : SuffixPassed cut move.after := by
  obtain ⟨extra, history, accepted⟩ := passed
  refine ⟨extra ++ [actual], ?_, ?_⟩
  · rw [move.history, history, List.append_assoc]
  · intro step member
    rcases List.mem_append.mp member with old | fresh
    · exact accepted step old
    · exact List.mem_singleton.mp fresh ▸ move.passed

def Invariant (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry) (allowance : Nat)
    (state : State input × Monitor) : Prop :=
  ∃ current : Cut input complete, current.report.final = state.1 ∧ SuffixPassed cut current ∧
    SourceHistory initial current state.2 ∧ Nonempty (Evidence initial native allowance current state.2)

def Completed (initial : GapInitial cut sender lower upper) (_native : NativeEnv cut initial.gateway.seed.entry) (allowance : Nat)
    (state : State input × Monitor) : Prop :=
  ∃ current : Cut input complete, current.report.final = state.1 ∧ SuffixPassed cut current ∧
    SourceHistory initial current state.2 ∧ ∃ retries, Nonempty (Done initial allowance current state.2 retries)

theorem invariant_evidence (invariant : Invariant initial native allowance state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ SuffixPassed cut current ∧
      Nonempty (Evidence initial native allowance current state.2) := by
  obtain ⟨current, final, passed, _, evidence⟩ := invariant
  exact ⟨current, final, passed, evidence⟩

theorem invariant_sources (invariant : Invariant initial native allowance state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ SuffixPassed cut current ∧
      SourceHistory initial current state.2 ∧ Nonempty (Evidence initial native allowance current state.2) := invariant

theorem completed_done (completed : Completed initial native allowance state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ SuffixPassed cut current ∧
      ∃ retries, Nonempty (Done initial allowance current state.2 retries) := by
  obtain ⟨current, final, passed, _, done⟩ := completed
  exact ⟨current, final, passed, done⟩

theorem completed_sources (completed : Completed initial native allowance state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ SuffixPassed cut current ∧
      SourceHistory initial current state.2 ∧ ∃ retries, Nonempty (Done initial allowance current state.2 retries) := completed

theorem initial_invariant (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (allowance : Nat)
    (receiver : CampusTCPGapProgressReceiver.Geometry initial) (wire : Geometry initial) :
    Invariant initial native allowance (cut.report.final, CampusTCPGapProgressSetup.initialMonitor initial) :=
  ⟨cut, rfl, ⟨[], by simp, by simp⟩, SourceHistory.ofInitial initial, ⟨initial_evidence initial native allowance receiver wire⟩⟩

theorem pending_positive (evidence : Evidence initial native allowance current monitor)
    (pending : nextDemand (config initial native quantum allowance)
      current.report.final monitor = some demand) :
    0 < monitor.rank (config initial native quantum allowance) current.report.final := by
  by_cases positive : 0 < monitor.rank (config initial native quantum allowance) current.report.final
  · exact positive
  · have zero : monitor.rank (config initial native quantum allowance) current.report.final = 0 := by omega
    obtain ⟨retries, ⟨done⟩⟩ := evidence.done_of_rank_zero quantum zero
    rw [done.demand native quantum] at pending
    cases pending

theorem finished (invariant : Invariant initial native allowance state)
    (zero : state.2.rank (config initial native quantum allowance) state.1 = 0) :
    Completed initial native allowance state := by
  obtain ⟨current, final, passed, sources, ⟨evidence⟩⟩ := invariant
  rw [← final] at zero
  exact ⟨current, final, passed, sources, evidence.done_of_rank_zero quantum zero⟩

theorem selected_step (wire : Geometry initial) (evidence : Evidence initial native allowance current monitor) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (pending : nextDemand (config initial native quantum allowance)
      current.report.final monitor = some demand) :
    Nonempty (CampusTCPGapProgressSelected.Selected initial native quantum allowance current monitor demand) := by
  by_cases active : monitor.waiting = false
  · exact CampusTCPGapProgressSelected.ordinary_selected wire evidence active pending
  · cases evidence with
    | dataIngress record => exact False.elim (active record.waiting)
    | dataTicket record => exact False.elim (active record.waiting)
    | dataLink record => exact False.elim (active record.waiting)
    | needAck record => exact False.elim (active record.waiting)
    | ackIngress record => exact False.elim (active record.waiting)
    | ackTicket record => exact False.elim (active record.waiting)
    | ackLink record => exact False.elim (active record.waiting)
    | needRead record => exact False.elim (active record.waiting)
    | done record => exact False.elim (active record.waiting)
    | waiting record =>
      by_cases early : record.live.senderFlight.recovery.now < record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto
      · have offered := record.tick_demand native quantum early
        have same := Option.some.inj (pending.symm.trans offered)
        subst demand
        obtain ⟨actual, ⟨ticked⟩⟩ := record.tick_at native quantum positive early
        refine ⟨⟨actual, ticked.clocked.move, ticked.clocked.event, ?_, ?_⟩⟩
        · rw [ticked.clocked.observed]
          exact ⟨ticked.clocked.evidence⟩
        · rw [ticked.clocked.observed]
          exact ticked.decreases
      · have due : record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto ≤ record.live.senderFlight.recovery.now := by omega
        have offered := record.timeout_demand native quantum due
        have same := Option.some.inj (pending.symm.trans offered)
        subst demand
        obtain ⟨actual, move, event, ⟨next⟩⟩ := CampusTCPGapProgressRetry.Waiting.retry_at wire native quantum record budget due
        refine ⟨⟨actual, move, event, ⟨.dataIngress next⟩, ?_⟩⟩
        apply rank_timeout (config initial native quantum allowance) positive
          current.report.final move.after.report.final monitor _ record.waiting record.live.senderFlight.recovery
          (record.recovery native quantum) record.live.senderFlight.deadline due next.waiting next.phaseEq _
        rw [next.retryCount, record.retryCount]

theorem canonical_advance (wire : Geometry initial) (evidence : Evidence initial native allowance current monitor) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (actual : Step input) (before : actual.before = current.report.final)
    (pending : nextDemand (config initial native quantum allowance)
      current.report.final monitor = some demand) (event : actual.event = demand.event) :
    ∃ move : CampusTCPRoundPhaseBase.Move current actual,
      Nonempty (Evidence initial native allowance move.after
        (observe (config initial native quantum allowance) monitor actual)) ∧
      (observe (config initial native quantum allowance) monitor actual).rank
        (config initial native quantum allowance) move.after.report.final <
        monitor.rank (config initial native quantum allowance) current.report.final := by
  obtain ⟨selected⟩ := selected_step wire evidence positive budget pending
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event selected.actual actual
    (selected.move.beforeEq.trans before.symm) (selected.event.trans event.symm)
  cases same
  exact ⟨selected.move, selected.evidence, selected.decreases⟩

private theorem move_arrays (move : CampusTCPRoundPhaseBase.Move current actual) :
    current.report.final.outputs <+: move.after.report.final.outputs ∧
      current.report.final.services <+: move.after.report.final.services ∧
      current.report.final.receipts <+: move.after.report.final.receipts := by
  refine ⟨?_, ?_, ?_⟩
  · rw [move.final, CampusTCPOrigins.output_history, move.beforeEq]
    exact List.prefix_append _ _
  · rw [move.final, CampusTCPOrigins.service_history, move.beforeEq]
    exact List.prefix_append _ _
  · rw [move.final, CampusTCPRecoveryRoundOrigins.Step.receipts, move.beforeEq]
    exact List.prefix_append _ _

private theorem advance_output (cfg : CampusTCPGapProgressMonitor.Config) (monitor : Monitor) (actual : Step input) :
    (advance cfg monitor actual).refs.dataOutput = monitor.refs.dataOutput := by
  cases phase : monitor.phase <;>
    simp only [advance, phase, observeAssignment, observeService, observeReceipt, observeOutput, Monitor.invalid, Bool.false_eq_true, ite_false, ite_true]
  all_goals repeat' first | (solve | rfl) | (solve | simp_all) | split

private theorem advance_service (cfg : CampusTCPGapProgressMonitor.Config) (monitor : Monitor) (actual : Step input)
    (notTicket : monitor.phase ≠ .dataTicket) :
    (advance cfg monitor actual).refs.dataService = monitor.refs.dataService := by
  cases phase : monitor.phase
  all_goals first
    | exact False.elim (notTicket phase)
    | simp only [advance, phase, observeAssignment, observeService, observeReceipt, observeOutput, Monitor.invalid, Bool.false_eq_true, ite_false, ite_true]
  all_goals repeat' first | (solve | rfl) | (solve | simp_all) | split

private theorem advance_first (cfg : CampusTCPGapProgressMonitor.Config) (monitor : Monitor) (actual : Step input)
    (notData : monitor.phase ≠ .dataLink) :
    (advance cfg monitor actual).firstDataReceipt = monitor.firstDataReceipt := by
  cases phase : monitor.phase
  all_goals first
    | exact False.elim (notData phase)
    | simp only [advance, phase, observeAssignment, observeService, observeReceipt, observeOutput, Monitor.invalid, Bool.false_eq_true, ite_false, ite_true]
  all_goals repeat' first | (solve | rfl) | (solve | simp_all) | split

private theorem source_quiet (history : SourceHistory initial current monitor)
    (move : CampusTCPRoundPhaseBase.Move current actual)
    (observed : observe (config initial native quantum allowance) monitor actual =
      advance (config initial native quantum allowance) monitor actual)
    (notTicket : monitor.phase ≠ .dataTicket) (notData : monitor.phase ≠ .dataLink) :
    SourceHistory initial move.after (observe (config initial native quantum allowance) monitor actual) := by
  obtain ⟨outputs, services, receipts⟩ := move_arrays move
  apply history.retain outputs services receipts
  · rw [observed]; exact advance_output _ _ _
  · rw [observed]; exact advance_service _ _ _ notTicket
  · rw [observed]; exact advance_first _ _ _ notData

private theorem source_invalid (history : SourceHistory initial current monitor)
    (move : CampusTCPRoundPhaseBase.Move current actual) : SourceHistory initial move.after monitor.invalid := by
  obtain ⟨outputs, services, receipts⟩ := move_arrays move
  exact history.retain outputs services receipts rfl rfl rfl

private theorem source_service (history : SourceHistory initial current monitor)
    (record : DataTicket initial native allowance current monitor retries released)
    (move : CampusTCPRoundPhaseBase.Move current actual) (event : actual.event = .serve record.ticket.id none)
    (observed : observe (config initial native quantum allowance) monitor actual =
      advance (config initial native quantum allowance) monitor actual) :
    SourceHistory initial move.after (observe (config initial native quantum allowance) monitor actual) := by
  rw [observed, advance, record.phaseEq]
  unfold observeService
  cases recorded : actual.result.service with
  | none => simpa only [recorded] using source_invalid history move
  | some served =>
    cases emitted : served.evidence.output with
    | none => simpa only [recorded, emitted] using source_invalid history move
    | some emission =>
      cases pending : actual.result.state.custody.pendingID (Transit.linkAt actual.before.services.length) with
      | none => simpa only [recorded, emitted, pending] using source_invalid history move
      | some id =>
        simp only [emitted, pending, ite_true]
        obtain ⟨completed, _, ticket, _⟩ := CampusTCPRoundService.Step.serve_frame actual record.ticket.id none event served recorded
        have valid : actual.before.work.Valid := by rw [move.beforeEq]; exact CampusTCPOrigins.Report.work_valid current.report
        have member : record.ticket ∈ actual.before.work.pending := by rw [move.beforeEq]; exact record.pending
        have same : served.ticket = record.ticket := ticket.trans (completed.item_eq valid record.ticket member rfl)
        have source : Nonempty (LowerSource initial served.ticket.value.produced) := by
          rw [same, record.produced]
          exact history.output_source record.outputRef record.output.stored
        obtain ⟨outputs, _, receipts⟩ := move_arrays move
        refine history.update_service (index := actual.before.services.length)
          (updated := { monitor with phase := .dataLink, refs := { monitor.refs with
            dataService := some actual.before.services.length, dataLinkPacket := some id } })
          served ?_ source outputs receipts rfl rfl rfl
        rw [move.final, CampusTCPOrigins.service_history, recorded, Option.toList_some]
        simp

private theorem source_receipt (history : SourceHistory initial current monitor)
    (record : DataLink initial allowance current monitor retries released)
    (move : CampusTCPRoundPhaseBase.Move current actual)
    (event : actual.event = .deliver record.index record.emission.bytes true)
    (observed : observe (config initial native quantum allowance) monitor actual =
      advance (config initial native quantum allowance) monitor actual) :
    SourceHistory initial move.after (observe (config initial native quantum allowance) monitor actual) := by
  rw [observed, advance, record.phaseEq]
  unfold observeReceipt
  cases recorded : actual.result.receipt with
  | none => simpa only [recorded] using source_invalid history move
  | some receipt =>
    cases application : actual.result.application with
    | none => simpa only [recorded, application] using source_invalid history move
    | some pair =>
      obtain ⟨receiver, operation⟩ := pair
      by_cases actors : (receipt.actor == (config initial native quantum allowance).sender.other &&
          receiver == (config initial native quantum allowance).sender.other) = true
      · simp only [ite_true, actors]
        obtain ⟨outputs, services, receipts⟩ := move_arrays move
        cases first : monitor.firstDataReceipt with
        | some previous =>
          apply history.retain outputs services receipts
          · rfl
          · rfl
          · exact first.symm
        | none =>
          have stored := (CampusTCPFacts.deliver_origin actual record.index record.emission.bytes true event receipt recorded).2.2
          rw [move.beforeEq] at stored
          have same : receipt.served = record.served := Option.some.inj (stored.symm.trans record.stored)
          have source : Nonempty (LowerSource initial receipt.served.ticket.value.produced) := by
            rw [same]
            exact history.service_source record.serviceRef record.stored
          refine history.update_first (index := actual.before.receipts.length)
            (updated := { monitor with
              phase := .needAck
              refs := { monitor.refs with
                dataReceipt := some actual.before.receipts.length, dataReceiveStamp := some operation.stamp }
              firstDataReceipt := some actual.before.receipts.length })
            receipt ?_ source outputs services rfl rfl rfl
          rw [move.final, CampusTCPRecoveryRoundOrigins.Step.receipts, recorded, Option.toList_some]
          simp
      · simpa only [ite_true, actors, Bool.false_eq_true, ite_false] using source_invalid history move

private theorem source_ordinary (history : SourceHistory initial current monitor)
    (evidence : Evidence initial native allowance current monitor) (move : CampusTCPRoundPhaseBase.Move current actual)
    (active : monitor.waiting = false) (action : CampusTCPRoundMonitor.Action)
    (next : nextAction (config initial native quantum allowance) current.report.final monitor = some action)
    (event : actual.event = action.event) :
    SourceHistory initial move.after (observe (config initial native quantum allowance) monitor actual) := by
  have selected : nextAction (config initial native quantum allowance) actual.before monitor = some action := by
    rw [move.beforeEq]; exact next
  have observed := CampusTCPGapProgressMonitorFacts.observe_action _ _ _ active move.supported move.passed action selected event
  cases evidence with
  | dataTicket record =>
    have same := Option.some.inj (next.symm.trans (record.next_action quantum))
    exact source_service history record move (event.trans (congrArg CampusTCPRoundMonitor.Action.event same)) observed
  | dataLink record =>
    have same := Option.some.inj (next.symm.trans (record.next_action native quantum))
    exact source_receipt history record move (event.trans (congrArg CampusTCPRoundMonitor.Action.event same)) observed
  | waiting record => rw [record.waiting] at active; cases active
  | dataIngress record => exact source_quiet history move observed (by rw [record.phaseEq]; decide) (by rw [record.phaseEq]; decide)
  | needAck record => exact source_quiet history move observed (by rw [record.phaseEq]; decide) (by rw [record.phaseEq]; decide)
  | ackIngress record => exact source_quiet history move observed (by rw [record.phaseEq]; decide) (by rw [record.phaseEq]; decide)
  | ackTicket record => exact source_quiet history move observed (by rw [record.phaseEq]; decide) (by rw [record.phaseEq]; decide)
  | ackLink record => exact source_quiet history move observed (by rw [record.phaseEq]; decide) (by rw [record.phaseEq]; decide)
  | needRead record => exact source_quiet history move observed (by rw [record.phaseEq]; decide) (by rw [record.phaseEq]; decide)
  | done record => exact source_quiet history move observed (by rw [record.phaseEq]; decide) (by rw [record.phaseEq]; decide)

private theorem source_canonical (wire : Geometry initial) (history : SourceHistory initial current monitor)
    (evidence : Evidence initial native allowance current monitor) (budget : allowance ≤ 2)
    (move : CampusTCPRoundPhaseBase.Move current actual)
    (pending : nextDemand (config initial native quantum allowance) current.report.final monitor = some demand)
    (event : actual.event = demand.event) :
    SourceHistory initial move.after (observe (config initial native quantum allowance) monitor actual) := by
  by_cases active : monitor.waiting = false
  · obtain ⟨action, next, choice⟩ := CampusTCPGapProgressMonitorFacts.nextDemand_action_exists _ _ _ active demand pending
    have selected : actual.event = action.event := by
      rcases choice with rfl | ⟨packet, rfl⟩ <;> exact event
    exact source_ordinary history evidence move active action next selected
  · cases evidence with
    | dataIngress record => exact False.elim (active record.waiting)
    | dataTicket record => exact False.elim (active record.waiting)
    | dataLink record => exact False.elim (active record.waiting)
    | needAck record => exact False.elim (active record.waiting)
    | ackIngress record => exact False.elim (active record.waiting)
    | ackTicket record => exact False.elim (active record.waiting)
    | ackLink record => exact False.elim (active record.waiting)
    | needRead record => exact False.elim (active record.waiting)
    | done record => exact False.elim (active record.waiting)
    | waiting record =>
      by_cases early : record.live.senderFlight.recovery.now < record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto
      · have same := Option.some.inj (pending.symm.trans (record.tick_demand native quantum early))
        have clockEvent : actual.event = .advanceClock sender (record.tickTarget quantum) :=
          event.trans (congrArg Demand.event same)
        have observed := CampusTCPGapProgressMonitorFacts.observe_clock
          (config initial native quantum allowance) monitor actual move.supported move.passed _ _ clockEvent
        obtain ⟨outputs, services, receipts⟩ := move_arrays move
        apply history.retain outputs services receipts
        all_goals rw [observed]
      · have due : record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto ≤ record.live.senderFlight.recovery.now := by omega
        have same := Option.some.inj (pending.symm.trans (record.timeout_demand native quantum due))
        have timeoutEvent : actual.event = .timeout sender true := event.trans (congrArg Demand.event same)
        obtain ⟨value⟩ := CampusTCPGapProgressRetry.Step.retry actual wire record.live (record.credit budget) due move.beforeEq timeoutEvent
        have source : Nonempty (LowerSource initial value.facts.produced) := ⟨.retry {
          prior := current, actual, move := value.move, retained := record.live.anchor.retained
          retries := _, flight := record.live.senderFlight, operation := value.facts.localStep
          recorded := value.facts.application, localBefore := value.facts.localBefore, localEvent := value.facts.localEvent
          packet := value.facts.packet, origin := value.facts.origin, production := value.facts.production
          output := value.facts.output, encoded := value.encoded }⟩
        have observed := value.observe native quantum allowance monitor record.waiting
        obtain ⟨_, services, receipts⟩ := move_arrays value.move
        have next : SourceHistory initial value.move.after (observe (config initial native quantum allowance) monitor actual) := by
          refine history.update_output (index := actual.before.outputs.length)
            (updated := observe (config initial native quantum allowance) monitor actual)
            value.facts.produced value.source source services receipts ?_ ?_ ?_
          all_goals rw [observed]
        exact next.reframe (value.move.final.trans move.final.symm)

private theorem source_drop {id : Nat} {action : CampusTCPRoundMonitor.Action} (history : SourceHistory initial current monitor)
    (move : CampusTCPRoundPhaseBase.Move current actual)
    (pending : nextDemand (config initial native quantum allowance) current.report.final monitor = some (.resolution action id))
    (event : actual.event = .dropPacket id) :
    SourceHistory initial move.after (observe (config initial native quantum allowance) monitor actual) := by
  have selected : nextDemand (config initial native quantum allowance) actual.before monitor = some (.resolution action id) := by
    rw [move.beforeEq]; exact pending
  have observed := CampusTCPGapProgressMonitorFacts.observe_drop _ _ _ move.supported move.passed action selected event
  obtain ⟨outputs, services, receipts⟩ := move_arrays move
  apply history.retain outputs services receipts
  all_goals rw [observed]

structure CheckedStep (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (actual : Step input) where
  move : CampusTCPRoundPhaseBase.Move current actual
  evidence : Nonempty (Evidence initial native allowance move.after
    (observe (config initial native quantum allowance) monitor actual))
  sources : SourceHistory initial move.after (observe (config initial native quantum allowance) monitor actual)
  nonincrease : (observe (config initial native quantum allowance) monitor actual).rank
      (config initial native quantum allowance) move.after.report.final ≤
    monitor.rank (config initial native quantum allowance) current.report.final
  persistent : ∀ demand,
    (observe (config initial native quantum allowance) monitor actual).rank
        (config initial native quantum allowance) move.after.report.final =
      monitor.rank (config initial native quantum allowance) current.report.final →
    nextDemand (config initial native quantum allowance) current.report.final monitor = some demand →
    nextDemand (config initial native quantum allowance) move.after.report.final
      (observe (config initial native quantum allowance) monitor actual) = some demand
  advances : ∀ demand,
    nextDemand (config initial native quantum allowance) current.report.final monitor = some demand →
    serves demand actual.event = true →
    (observe (config initial native quantum allowance) monitor actual).rank
        (config initial native quantum allowance) move.after.report.final <
      monitor.rank (config initial native quantum allowance) current.report.final

private def strict_step (move : CampusTCPRoundPhaseBase.Move current actual)
    (evidence : Nonempty (Evidence initial native allowance move.after
      (observe (config initial native quantum allowance) monitor actual)))
    (sources : SourceHistory initial move.after (observe (config initial native quantum allowance) monitor actual))
    (decreases : (observe (config initial native quantum allowance) monitor actual).rank
        (config initial native quantum allowance) move.after.report.final <
      monitor.rank (config initial native quantum allowance) current.report.final) :
    CheckedStep initial native quantum allowance current monitor actual :=
  ⟨move, evidence, sources, Nat.le_of_lt decreases, by intro demand equal _; omega, by intro _ _ _; exact decreases⟩

private def clock_step (clocked : Clocked initial native quantum allowance current monitor actor millis actual)
    (history : SourceHistory initial current monitor) (positive : 0 < quantum)
    (allowed : Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    CheckedStep initial native quantum allowance current monitor actual where
  move := clocked.move
  evidence := by rw [clocked.observed]; exact ⟨clocked.evidence⟩
  sources := by rw [clocked.observed]; exact history.clock clocked.placement
  nonincrease := by rw [clocked.observed]; exact clocked.rank_le
  persistent := by
    intro demand equal pending
    rw [clocked.observed] at equal ⊢
    exact clocked.pending_persistent positive allowed equal pending
  advances := by
    intro demand pending served
    rw [clocked.observed]
    exact clocked.serves_decreases positive pending served

theorem checked_step (wire : Geometry initial) (evidence : Evidence initial native allowance current monitor)
    (history : SourceHistory initial current monitor) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    Nonempty (CheckedStep initial native quantum allowance current monitor actual) := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    have guarded := (CampusTCPGapProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed |>.2
    have clockAllowed : clockAllowed (config initial native quantum allowance)
        current.report.final (.advanceClock actor millis) = true := by simpa only [event] using guarded
    obtain ⟨clocked⟩ := CampusTCPGapProgressEvidence.Step.clock actual evidence quantum actor millis before event clockAllowed
    exact ⟨clock_step clocked history positive allowed⟩
  · obtain ⟨choice, _⟩ := (CampusTCPGapProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
    rcases choice with ⟨demand, pending, served⟩ | free
    · cases demand with
      | operation action =>
        have event := (CampusTCPGapProgressMonitorFacts.serves_operation action actual.event).mp served
        obtain ⟨move, next, decreases⟩ := canonical_advance wire evidence positive budget actual before pending event
        exact ⟨strict_step move next (source_canonical wire history evidence budget move pending event) decreases⟩
      | resolution action id =>
        rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action id actual.event).mp served with event | event
        · obtain ⟨move, next, decreases⟩ := canonical_advance wire evidence positive budget actual before pending event
          exact ⟨strict_step move next (source_canonical wire history evidence budget move pending event) decreases⟩
        · obtain ⟨dropped⟩ := evidence.drop_selected budget pending
          have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event dropped.actual actual
            (dropped.move.beforeEq.trans before.symm) (dropped.event.trans event.symm)
          cases same
          exact ⟨strict_step dropped.move dropped.evidence (source_drop history dropped.move pending dropped.event) dropped.decreases⟩
      | tick actor target =>
        have event := (CampusTCPGapProgressMonitorFacts.serves_tick actor target actual.event).mp served
        exact False.elim (clock ⟨actor, target, event⟩)
      | timeout actor =>
        have event := (CampusTCPGapProgressMonitorFacts.serves_timeout actor actual.event).mp served
        obtain ⟨move, next, decreases⟩ := canonical_advance wire evidence positive budget actual before pending event
        exact ⟨strict_step move next (source_canonical wire history evidence budget move pending event) decreases⟩
    · obtain ⟨actor, millis, event, _⟩ := CampusTCPGapProgressMonitorFacts.freeClock_event _ _ _ _ free
      exact False.elim (clock ⟨actor, millis, event⟩)

structure EdgeFacts (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance : Nat)
    (before after : State input × Monitor) (event : Event) : Prop where
  invariant : Invariant initial native allowance after
  nonincrease : after.2.rank (config initial native quantum allowance) after.1 ≤
    before.2.rank (config initial native quantum allowance) before.1
  persistent : ∀ demand,
    after.2.rank (config initial native quantum allowance) after.1 =
      before.2.rank (config initial native quantum allowance) before.1 →
    nextDemand (config initial native quantum allowance) before.1 before.2 = some demand →
    nextDemand (config initial native quantum allowance) after.1 after.2 = some demand
  advances : ∀ demand,
    nextDemand (config initial native quantum allowance) before.1 before.2 = some demand →
    serves demand event = true →
    after.2.rank (config initial native quantum allowance) after.1 <
      before.2.rank (config initial native quantum allowance) before.1

theorem transition (wire : Geometry initial) (invariant : Invariant initial native allowance beforeState) (positive : 0 < quantum) (budget : allowance ≤ 2)
    (edge : (guardedSystem input (config initial native quantum allowance)).step
      beforeState event afterState) : EdgeFacts initial native quantum allowance beforeState afterState event := by
  obtain ⟨current, final, passed, sources, ⟨evidence⟩⟩ := invariant
  obtain ⟨allowed, actual, before, selected, after, observed⟩ := edge
  have atCurrent : actual.before = current.report.final := before.trans final.symm
  have allowedHere : Allowed (config initial native quantum allowance)
      current.report.final beforeState.2 actual.event := by rw [final, selected]; exact allowed
  obtain ⟨checked⟩ := checked_step wire evidence sources positive budget actual atCurrent allowedHere
  have newFinal : checked.move.after.report.final = afterState.1 := checked.move.final.trans after
  refine ⟨⟨checked.move.after, newFinal, passed.append checked.move, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa only [observed] using checked.sources
  · simpa only [observed] using checked.evidence
  · simpa only [newFinal, observed, final] using checked.nonincrease
  · intro demand equal pending
    have equalHere : (observe (config initial native quantum allowance) beforeState.2 actual).rank
        (config initial native quantum allowance) checked.move.after.report.final =
      beforeState.2.rank (config initial native quantum allowance) current.report.final := by
      simpa only [newFinal, observed, final] using equal
    have pendingHere : nextDemand (config initial native quantum allowance)
        current.report.final beforeState.2 = some demand := by simpa only [final] using pending
    simpa only [newFinal, observed] using checked.persistent demand equalHere pendingHere
  · intro demand pending served
    have pendingHere : nextDemand (config initial native quantum allowance)
        current.report.final beforeState.2 = some demand := by simpa only [final] using pending
    have servedHere : serves demand actual.event = true := by simpa only [selected] using served
    simpa only [newFinal, observed, final] using checked.advances demand pendingHere servedHere

def adapter (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
    (quantum allowance : Nat) (wire : Geometry initial) (positive : 0 < quantum) (budget : allowance ≤ 2) : Theory.BoundedProgress.Adapter (State input × Monitor) Event Demand where
  system := guardedSystem input (config initial native quantum allowance)
  invariant := Invariant initial native allowance
  pending state demand := nextDemand (config initial native quantum allowance) state.1 state.2 = some demand
  enabled state demand := ∃ actual : Step input, actual.before = state.1 ∧ actual.event = demand.event ∧
    actual.result.supported = true
  serves demand event := serves demand event = true
  rank state := state.2.rank (config initial native quantum allowance) state.1
  complete := Completed initial native allowance
  preserve := by
    intro before event after invariant edge
    exact (transition wire invariant positive budget edge).invariant
  nonincrease := by
    intro before event after invariant edge
    exact (transition wire invariant positive budget edge).nonincrease
  demand := by
    intro state invariant begun
    obtain ⟨current, final, _, _, ⟨evidence⟩⟩ := invariant
    have positiveHere : 0 < state.2.rank (config initial native quantum allowance) current.report.final := by
      simpa only [final] using begun
    simpa only [final] using evidence.pending_positive quantum positiveHere
  pending_enabled := by
    intro state demand invariant pending
    obtain ⟨current, final, _, _, ⟨evidence⟩⟩ := invariant
    have pendingHere : nextDemand (config initial native quantum allowance)
        current.report.final state.2 = some demand := by simpa only [final] using pending
    obtain ⟨selected⟩ := selected_step wire evidence positive budget pendingHere
    exact ⟨selected.actual, selected.move.beforeEq.trans final, selected.event, selected.move.supported⟩
  persistent := by
    intro before event after demand invariant edge equal pending
    exact (transition wire invariant positive budget edge).persistent demand equal pending
  advance := by
    intro before event after demand invariant edge pending _ served
    exact (transition wire invariant positive budget edge).advances demand pending served
  finished := by
    intro state invariant zero
    exact finished invariant zero

end Netlib.Check.CampusTCPGapProgressProgress
