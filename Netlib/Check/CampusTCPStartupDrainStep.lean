import Netlib.Check.CampusTCPStartupDrainSelection
import Netlib.Check.CampusTCPStartupJobDrainDelivery
import Netlib.Check.CampusTCPStartupJobDrainService

/-!
# Actual queue progress after startup completes

Unsupported service retains the queues. A supported demanded job reduces the rank.
Equal rank preserves the current protected demand.
-/

namespace Netlib.Check.CampusTCPStartupDrainStep

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs CampusTCPStartupJobDrain

namespace Q
export CampusTCPStartupJobDrainComplete (QueueFrame)
end Q

variable {input : Input}

theorem Step.assignment_strict (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (packets : ∀ item ∈ report.final.custody.pending, item.value.payload.isRecovery = true)
    (event : actual.event = .assign index ingress) : potential actual.result.state < potential actual.before := by
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [before]
    exact CampusTCPCustodyFacts.Report.history report
  obtain ⟨id, resolved, selected, computed, predicate, _⟩ :=
    CampusTCPCustodyFacts.Step.assign actual index ingress event history
  obtain ⟨produced, payload⟩ := CampusTCPCustodyFacts.ingress_stage _ _ predicate
  have recovery : produced.isRecovery = true := by
    have pending : resolved.item ∈ report.final.custody.pending := by rw [← before]; exact resolved.member
    have current := packets resolved.item pending
    simpa only [payload, Transit.isRecovery] using current
  have source : actual.before.outputs[index]? = some produced := by
    have sourced := CampusTCPCustodyFacts.Report.sources report resolved.item
      (List.mem_append_right _ (by rw [← before]; exact resolved.member))
    rw [payload] at sourced
    simpa only [CampusTCPCustodyFacts.Sourced, before] using sourced
  obtain ⟨custody, prepared, frame⟩ := CampusTCPRoundAssignment.Step.assign_frame actual index ingress event produced source
  have custodyEq : custody = resolved.state := by
    simp only [prepareCustody, selected, computed, Except.mapError, bind, Except.bind,
      pure, Except.pure, Except.ok.injEq] at prepared
    exact prepared.symm
  have work : actual.result.state.work = Theory.Outstanding.enqueue actual.before.work
      (CampusTCPRoundAssignment.ticketValue actual.before index ingress produced) := by rw [frame]
  have custodyAfter : actual.result.state.custody = resolved.state := by rw [frame, custodyEq]
  have removed := resolved_weight (input := input) resolved
  have oldWeight : packetWeight resolved.item = sourceWeight .ingress produced := by rw [packetWeight, payload]
  have newWeight : ticketWeight (CampusTCPRoundAssignment.ticket actual.before index ingress produced) =
      sourceWeight .ticket produced := rfl
  have gap : sourceWeight .ingress produced = sourceWeight .ticket produced + 1 := by
    cases production : produced with
    | startup step output present | application actor step output present =>
      simp only [production, Produced.isRecovery, Bool.false_eq_true] at recovery
    | recovery control occurrence present => cases kind : occurrence.kind <;> simp only [sourceWeight, kind, stageWeight]
  rw [oldWeight] at removed
  rw [potential_rows, potential_rows, work, custodyAfter]
  change (resolved.state.pending.map packetWeight).sum +
    ((actual.before.work.pending ++ [CampusTCPRoundAssignment.ticket actual.before index ingress produced]).map ticketWeight).sum < _
  rw [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, newWeight]
  omega

private theorem service_frame (actual : Step input) (event : actual.event = .serve ticketID observed)
    (absent : actual.result.service = none) : Q.QueueFrame actual.before actual.result.state := by
  obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
  have noService : effect.service = none := by simpa only [final] using absent
  have custodyEq : custody = actual.before.custody := by
    simpa only [event, prepareCustody, pure, Except.pure, Except.ok.injEq] using prepared.symm
  rw [event] at computed
  simp only [processCore] at computed
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; cases noService)
    | (solve |
      cases computed
      rw [final, custodyEq]
      exact ⟨rfl, rfl⟩)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.service_cases (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (tickets : ∀ item ∈ report.final.work.pending, item.value.produced.isRecovery = true)
    (event : actual.event = .serve ticketID observed) :
    potential actual.result.state < potential actual.before ∨
      (actual.result.supported = false ∧ Q.QueueFrame actual.before actual.result.state) := by
  cases recorded : actual.result.service with
  | some served =>
    obtain ⟨completed, _, selected, _, _, _⟩ := CampusTCPFacts.serve_origin actual ticketID observed event served recorded
    have member : served.ticket ∈ report.final.work.pending := by rw [← before, selected]; exact completed.member
    exact Or.inl (CampusTCPStartupJobDrainService.Step.service_strict actual served recorded
      (tickets served.ticket member))
  | none =>
    right
    refine ⟨?_, service_frame actual event recorded⟩
    obtain ⟨effect, custody, computed, final⟩ := actual.processed
    have absent : effect.service = none := by simpa only [final] using recorded
    rw [event] at computed
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed)
      | (solve | cases computed; cases absent)
      | (solve | cases computed; rw [final]; rfl)
      | (split at computed)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.service_nonincrease (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (tickets : ∀ item ∈ report.final.work.pending, item.value.produced.isRecovery = true)
    (event : actual.event = .serve ticketID observed) : potential actual.result.state ≤ potential actual.before := by
  rcases Step.service_cases actual report before tickets event with strict | ⟨unsupported, frame⟩
  · exact Nat.le_of_lt strict
  · exact Nat.le_of_eq frame.potential

theorem Step.service_strict (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (tickets : ∀ item ∈ report.final.work.pending, item.value.produced.isRecovery = true)
    (event : actual.event = .serve ticketID observed) (supported : actual.result.supported = true) :
    potential actual.result.state < potential actual.before := by
  rcases Step.service_cases actual report before tickets event with strict | ⟨unsupported, frame⟩
  · exact strict
  · rw [supported] at unsupported
    cases unsupported


theorem Step.job_nonincrease (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (connection : report.final.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (packets : ∀ item ∈ report.final.custody.pending, item.value.payload.isRecovery = true)
    (tickets : ∀ item ∈ report.final.work.pending, item.value.produced.isRecovery = true)
    (job : Job input) (event : actual.event = CampusTCPStartupSelection.Job.event config job) :
    potential actual.result.state ≤ potential actual.before := by
  cases job with
  | ingress item index source payload => exact Nat.le_of_lt (Step.assignment_strict actual report before packets event)
  | ticket item source production => exact Step.service_nonincrease actual report before tickets event
  | link item index served emission emitted source production payload =>
    exact Nat.le_of_lt (CampusTCPStartupJobDrainDelivery.Step.complete_delivery_strict actual report before connection phase packets event)

theorem Step.job_strict (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (connection : report.final.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (packets : ∀ item ∈ report.final.custody.pending, item.value.payload.isRecovery = true)
    (tickets : ∀ item ∈ report.final.work.pending, item.value.produced.isRecovery = true)
    (job : Job input) (event : actual.event = CampusTCPStartupSelection.Job.event config job)
    (supported : actual.result.supported = true) : potential actual.result.state < potential actual.before := by
  cases job with
  | ingress item index source payload => exact Step.assignment_strict actual report before packets event
  | ticket item source production => exact Step.service_strict actual report before tickets event supported
  | link item index served emission emitted source production payload =>
    exact CampusTCPStartupJobDrainDelivery.Step.complete_delivery_strict actual report before connection phase packets event

private theorem finish_frame (actual : Step input) (event : actual.event = .finishStartup) :
    Q.QueueFrame actual.before actual.result.state := by
  obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
  have custodyEq : custody = actual.before.custody := by
    simpa only [event, prepareCustody, pure, Except.pure, Except.ok.injEq] using prepared.symm
  rw [event] at computed
  simp only [processCore, finishStartup] at computed
  repeat' first
    | (solve | cases computed; rw [final, custodyEq]; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.allowed_nonincrease (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (connection : report.final.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (packets : ∀ item ∈ report.final.custody.pending, item.value.payload.isRecovery = true)
    (tickets : ∀ item ∈ report.final.work.pending, item.value.produced.isRecovery = true)
    (allowed : CampusTCPStartupSelection.allowed config actual.before held actual.event = true) :
    potential actual.result.state ≤ potential actual.before := by
  cases event : actual.event with
  | startupClock actor millis =>
    exact Nat.le_of_eq (CampusTCPStartupJobDrainComplete.Step.clock_frame actual event).1.potential
  | startupTimeout actor generation policy =>
    have connected : actual.before.connection = .recovering current := by rw [before]; exact connection
    have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connection
    exact Nat.le_of_eq (CampusTCPStartupJobDrainComplete.Step.complete_timeout_frame actual connected reachable phase event).1.potential
  | dropPacket id =>
    apply Nat.le_of_lt (CampusTCPStartupJobDrain.Step.drop_strict actual id event ?_)
    intro item member selected
    exact packets item (by rw [← before]; exact member)
  | finishStartup => exact Nat.le_of_eq (finish_frame actual event).potential
  | _ =>
    have jobAllowed : CampusTCPStartupSelection.jobAllowed config actual.before actual.event = true := by
      simpa only [event, CampusTCPStartupSelection.allowed] using allowed
    obtain ⟨job, member, selected⟩ := List.any_eq_true.mp jobAllowed
    have selectedEvent : actual.event = CampusTCPStartupSelection.Job.event config job := (of_decide_eq_true selected).symm
    exact Step.job_nonincrease actual report before connection phase packets tickets job selectedEvent

theorem Step.equal_frame (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (connection : report.final.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (packets : ∀ item ∈ report.final.custody.pending, item.value.payload.isRecovery = true)
    (tickets : ∀ item ∈ report.final.work.pending, item.value.produced.isRecovery = true)
    (allowed : CampusTCPStartupSelection.allowed config actual.before held actual.event = true)
    (equal : potential actual.result.state = potential actual.before) :
    Q.QueueFrame actual.before actual.result.state := by
  cases event : actual.event with
  | startupClock actor millis => exact (CampusTCPStartupJobDrainComplete.Step.clock_frame actual event).1
  | startupTimeout actor generation policy =>
    have connected : actual.before.connection = .recovering current := by rw [before]; exact connection
    have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connection
    exact (CampusTCPStartupJobDrainComplete.Step.complete_timeout_frame actual connected reachable phase event).1
  | dropPacket id =>
    have strict := CampusTCPStartupJobDrain.Step.drop_strict actual id event (fun item member selected =>
      packets item (by rw [← before]; exact member))
    omega
  | finishStartup => exact finish_frame actual event
  | _ =>
    have jobAllowed : CampusTCPStartupSelection.jobAllowed config actual.before actual.event = true := by
      simpa only [event, CampusTCPStartupSelection.allowed] using allowed
    obtain ⟨job, member, selected⟩ := List.any_eq_true.mp jobAllowed
    have selectedEvent : actual.event = CampusTCPStartupSelection.Job.event config job := (of_decide_eq_true selected).symm
    cases job with
    | ingress item index source payload =>
      have strict := Step.assignment_strict actual report before packets selectedEvent
      omega
    | ticket item source production =>
      rcases Step.service_cases actual report before tickets selectedEvent with strict | ⟨unsupported, frame⟩
      · omega
      · exact frame
    | link item index served emission emitted source production payload =>
      have strict := CampusTCPStartupJobDrainDelivery.Step.complete_delivery_strict actual report before connection phase packets selectedEvent
      omega


private theorem stage_rank {state : State input} {current : C.State input.active input.passive} (connection : CampusTCPRecoveryStartupOrigins.stage state.connection = .recovering current) :
    CampusTCPStartupSelection.phaseRank state = TCPHandshakeRecovery.phaseLevel current.phase := by
  cases selected : state.connection with
  | startup value pending | application value endpoints =>
    simp only [selected, CampusTCPRecoveryStartupOrigins.stage, reduceCtorEq] at connection
  | recovering value =>
    simp only [selected, CampusTCPRecoveryStartupOrigins.stage,
      CampusTCPRecoveryStartupOrigins.Stage.recovering.injEq] at connection
    subst value
    cases phase : current.phase <;> simp only [CampusTCPStartupSelection.phaseRank, selected, phase, TCPHandshakeRecovery.phaseLevel]

theorem Step.complete_phaseRank (actual : Step input)
    (connection : actual.before.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (notFinish : actual.event ≠ .finishStartup) : CampusTCPStartupSelection.phaseRank actual.result.state = 4 := by
  cases CampusTCPRecoveryStartupOrigins.Step.linked actual with
  | quiet ordinary recovery same =>
    rw [stage_rank (same.trans (by rw [connection]; rfl)), phase]
    rfl
  | ordinary selected ordinary recovery prior after stamp pending supported =>
    simp only [connection, CampusTCPRecoveryStartupOrigins.stage, reduceCtorEq] at prior
  | recovery selected recorded ordinary prior after stamp =>
    rcases prior with prior | ⟨prior, seeded⟩
    · have beforeEq : current = selected.before := by
        simpa only [connection, CampusTCPRecoveryStartupOrigins.stage,
          CampusTCPRecoveryStartupOrigins.Stage.recovering.injEq] using prior
      have lower := TCPHandshakeRecovery.evaluate_phase_level selected.computed
      rw [← beforeEq, phase] at lower
      change 4 ≤ TCPHandshakeRecovery.phaseLevel selected.result.state.phase at lower
      have upper : TCPHandshakeRecovery.phaseLevel selected.result.state.phase ≤ 4 := by
        cases selected.result.state.phase <;> simp only [TCPHandshakeRecovery.phaseLevel] <;> omega
      rw [stage_rank after]
      omega
    · simp only [connection, CampusTCPRecoveryStartupOrigins.stage, reduceCtorEq] at prior
  | drain archive ordinary recovery event prior after retained stamp => exact False.elim (notFinish event)

theorem Step.positive_not_finish (actual : Step input)
    (complete : CampusTCPStartupSelection.phaseRank actual.before = 4)
    (positive : 0 < potential actual.before)
    (allowed : CampusTCPStartupSelection.allowed config actual.before held actual.event = true) :
    actual.event ≠ .finishStartup := by
  intro event
  have selected : CampusTCPStartupSelection.demand config actual.before held = some .finishStartup := by
    simpa only [event, CampusTCPStartupSelection.allowed, decide_eq_true_eq] using allowed
  obtain ⟨job, member, demand⟩ := CampusTCPStartupDrainSelection.positive_demand (config := config) (held := held) complete positive
  have impossible := demand.symm.trans selected
  cases job <;> cases impossible

theorem Step.equal_pending (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (connection : report.final.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (packets : ∀ item ∈ report.final.custody.pending, item.value.payload.isRecovery = true)
    (tickets : ∀ item ∈ report.final.work.pending, item.value.produced.isRecovery = true)
    (monitor : CampusTCPStartupMonitor.Monitor)
    (allowed : CampusTCPStartupSelection.allowed config actual.before monitor.protection actual.event = true)
    (positive : 0 < potential actual.before)
    (equal : potential actual.result.state = potential actual.before) :
    CampusTCPStartupSelection.demand config actual.result.state (CampusTCPStartupMonitor.advanceProtection config monitor actual) =
      CampusTCPStartupSelection.demand config actual.before monitor.protection := by
  have complete : CampusTCPStartupSelection.phaseRank actual.before = 4 := by
    simp only [CampusTCPStartupSelection.phaseRank, before, connection, phase]
  have frame := Step.equal_frame actual report before connection phase packets tickets allowed equal
  have connected : actual.before.connection = .recovering current := by rw [before]; exact connection
  have later := Step.complete_phaseRank actual connected phase (Step.positive_not_finish actual complete positive allowed)
  exact CampusTCPStartupDrainSelection.pending_frame actual monitor complete later frame


theorem Step.demand_strict (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (connection : report.final.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (packets : ∀ item ∈ report.final.custody.pending, item.value.payload.isRecovery = true)
    (tickets : ∀ item ∈ report.final.work.pending, item.value.produced.isRecovery = true)
    (positive : 0 < potential actual.before)
    (selected : CampusTCPStartupSelection.demand config actual.before held = some actual.event)
    (supported : actual.result.supported = true) : potential actual.result.state < potential actual.before := by
  have complete : CampusTCPStartupSelection.phaseRank actual.before = 4 := by
    simp only [CampusTCPStartupSelection.phaseRank, before, connection, phase]
  obtain ⟨job, member, demand⟩ := CampusTCPStartupDrainSelection.positive_demand (config := config) (held := held) complete positive
  have event : actual.event = CampusTCPStartupSelection.Job.event config job := Option.some.inj (selected.symm.trans demand)
  exact Step.job_strict actual report before connection phase packets tickets job event supported

theorem zero_guards (state : State input) (zero : potential state = 0) :
    state.work.pending.any (fun item => item.value.produced.isRecovery) = false ∧
      state.custody.pending.any (fun item => item.value.payload.isRecovery) = false := by
  obtain ⟨packets, tickets⟩ := inventory_empty_iff.mp (potential_zero_iff.mp zero)
  exact ⟨tickets, packets⟩

end Netlib.Check.CampusTCPStartupDrainStep
