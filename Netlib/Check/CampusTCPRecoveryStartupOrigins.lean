import Netlib.Check.CampusTCPModel
import Netlib.Check.TCPHandshakeRecoveryFacts

/-!
# Actual startup modes in the campus trace

Recovery records retain their checked steps and current states.
Drain changes modes only through the actual checked campus event.
Recovery indices remain campus event stamps, with gaps between recovery operations.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupOrigins

open Packet Protocol CampusTCPModel

namespace H
export TCPHandshake (Stage Step)
end H

inductive Stage (active passive : TCP.Handshake.Local) where
  | ordinary (value : H.Stage active passive)
  | recovering (current : C.State active passive)

def stage : Connection active passive → Stage active passive
  | .startup value _ => .ordinary value
  | .recovering current => .recovering current
  | .application complete _ => .ordinary (.complete complete)

@[simp] theorem stage_ofStage (value : H.Stage active passive) :
    stage (Connection.ofStage value) = .ordinary value := by cases value <;> rfl

inductive Linked (before : State input) (event : CampusTCPModel.Event) (effect : Effect input) : Prop where
  | quiet (ordinary : effect.startup = none) (recovery : effect.recovery = none)
      (same : stage effect.state.connection = stage before.connection)
  | ordinary (actual : H.Step input.active input.passive)
      (recorded : effect.startup = some actual) (recovery : effect.recovery = none)
      (prior : stage before.connection = .ordinary actual.before)
      (after : stage effect.state.connection = .ordinary actual.result.state)
      (stamp : actual.index = before.time) (pending : actual.before.exchangeComplete = false)
      (supported : effect.supported = actual.supported)
  | recovery (actual : C.Step input.active input.passive)
      (recorded : effect.recovery = some actual) (ordinary : effect.startup = none)
      (prior : stage before.connection = .recovering actual.before ∨
        (stage before.connection = .ordinary .idle ∧ actual.before = .initial))
      (after : stage effect.state.connection = .recovering actual.result.state)
      (stamp : actual.index = before.time)
  | drain (archive : RecoveryArchive input.active input.passive)
      (ordinary : effect.startup = none) (recovery : effect.recovery = none)
      (event : event = .finishStartup)
      (prior : before.connection = .recovering archive.current)
      (after : stage effect.state.connection = .ordinary (.complete archive.complete))
      (retained : effect.state.recoveryArchive = some archive)
      (stamp : archive.time = before.time)

private theorem startup_linked (before : State input) (event : TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : Linked before joint effect := by
  unfold startup at computed
  split at computed
  · cases computed; exact .quiet rfl rfl rfl
  · cases computed; exact .quiet rfl rfl rfl
  · rename_i pendingStage pending connected
    split at computed
    · cases computed
    · rename_i result evaluated
      split at computed
      all_goals
        simp only [pure, Except.pure, Except.ok.injEq] at computed
        subst effect
        refine Linked.ordinary ⟨pendingStage, before.time, event, result, evaluated⟩ rfl rfl ?_ ?_ rfl pending rfl
        · rw [connected]; rfl
        · simp only [publish, stage_ofStage]

private theorem application_linked (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) : Linked before joint effect := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; apply Linked.quiet <;> simp_all [publish, stage, unsupported])
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw] at computed)

private theorem recovery_record (before : State input) (event : C.Event) (effect : Effect input)
    (connected : before.connection = .recovering current)
    (computed : runRecovery input before event = .ok effect) :
    ∃ actual : C.Step input.active input.passive,
      effect.recovery = some actual ∧ effect.startup = none ∧ actual.before = current ∧
      stage effect.state.connection = .recovering actual.result.state ∧ actual.index = before.time := by
  simp only [runRecovery, connected] at computed
  split at computed
  · cases computed
  · rename_i result evaluated
    split at computed
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst effect
      exact ⟨⟨current, before.time, event, result, evaluated⟩, rfl, rfl, rfl, rfl, rfl⟩

private theorem recovery_linked (before : State input) (event : C.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) : Linked before joint effect := by
  cases connected : before.connection with
  | startup value pending =>
    simp only [runRecovery, connected, pure, Except.pure, Except.ok.injEq] at computed
    subst effect
    exact .quiet rfl rfl rfl
  | application complete endpoints =>
    simp only [runRecovery, connected, pure, Except.pure, Except.ok.injEq] at computed
    subst effect
    exact .quiet rfl rfl rfl
  | recovering current =>
    obtain ⟨actual, recorded, ordinary, prior, after, stamp⟩ := recovery_record before event effect connected computed
    refine .recovery actual recorded ordinary (Or.inl ?_) after stamp
    rw [connected, prior]
    rfl

private theorem open_linked (before : State input) (remote : TCP.Handshake.Socket) (policy : Bool)
    (effect : Effect input) (computed : openRecovering input before remote policy = .ok effect) :
    Linked before (.openRecovering remote policy) effect := by
  unfold openRecovering at computed
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; exact .quiet rfl rfl rfl)
    | (solve
        | obtain ⟨actual, recorded, ordinary, prior, after, stamp⟩ := recovery_record _ _ _ rfl computed
          refine .recovery actual recorded ordinary (Or.inr ?_) after stamp
          exact ⟨by simp_all [stage], prior⟩)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem finish_linked (before : State input) (effect : Effect input)
    (computed : finishStartup input before = .ok effect) : Linked before .finishStartup effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; exact .quiet rfl rfl rfl)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  all_goals
    rename_i connection current connected complete client server phase activeData activeHandoff passiveData passiveHandoff noPackets noWork noArchive
    cases computed
    exact Linked.drain ⟨before.time, current, complete, client, server, phase,
      activeData, activeHandoff, passiveData, passiveHandoff⟩ rfl rfl rfl connected rfl rfl rfl

private theorem enableRecovery_linked (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableRecovery input before actor = .ok effect) : Linked before joint effect := by
  exact application_linked _ _ _ _ computed

private theorem enableStartupRecovery_linked (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableStartupRecovery input before actor = .ok effect) : Linked before joint effect := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; exact .quiet rfl rfl rfl
  · exact application_linked _ _ _ _ computed

private theorem enableAck_linked (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) : Linked before joint effect := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_linked _ _ _ _ computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [throw, throwThe, MonadExceptOf.throw] at computed)

@[simp] private theorem stage_write (before : State input) (gateway) (resident) :
    stage (before.write gateway resident).connection = stage before.connection := by cases gateway <;> rfl

theorem Linked.of_fields {before : State input} {event : CampusTCPModel.Event} {effect : Effect input}
    (linked : Linked before event effect) {next : Effect input}
    (ordinary : next.startup = effect.startup) (recovery : next.recovery = effect.recovery)
    (connection : next.state.connection = effect.state.connection)
    (archive : next.state.recoveryArchive = effect.state.recoveryArchive)
    (supported : next.supported = effect.supported) : Linked before event next := by
  cases linked with
  | quiet oldH oldC same => exact .quiet (ordinary.trans oldH) (recovery.trans oldC) (by rw [connection]; exact same)
  | ordinary actual recorded oldC prior after stamp pending selected =>
    exact .ordinary actual (ordinary.trans recorded) (recovery.trans oldC) prior
      (by rw [connection]; exact after) stamp pending (supported.trans selected)
  | recovery actual recorded oldH prior after stamp =>
    exact .recovery actual (recovery.trans recorded) (ordinary.trans oldH) prior
      (by rw [connection]; exact after) stamp
  | drain saved oldH oldC event prior after retained stamp =>
    exact .drain saved (ordinary.trans oldH) (recovery.trans oldC) event prior
      (by rw [connection]; exact after) (archive.trans retained) stamp

private theorem process_linked (before : State input) (event : CampusTCPModel.Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) : Linked before event effect := by
  cases event with
  | «open» remote policy => exact startup_linked _ _ _ computed
  | openRecovering remote policy => exact open_linked _ _ _ _ computed
  | startupClock actor millis | startupTimeout actor generation policy => exact recovery_linked _ _ _ computed
  | finishStartup => exact finish_linked _ _ computed
  | write actor bytes | send actor bytes policy | read actor bytes | emitAck actor policy
  | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_linked _ _ _ _ computed
  | enableRecovery actor => exact enableRecovery_linked _ _ _ computed
  | enableStartupRecovery actor => exact enableStartupRecovery_linked _ _ _ computed
  | enableAck actor => exact enableAck_linked _ _ _ computed
  | copyPacket id | dropPacket id => cases computed; exact .quiet rfl rfl rfl
  | authentication index | install id | stage id | installGuard id | installAt gateway id
  | stageAt gateway id | installGuardAt gateway id | pause | stageCheckpoint | installCheckpoint ns
  | switchRoute actor gateway | fencePrimary | resume | assign index ingress | serve index observed =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress, transferControl] at computed
    repeat' first
      | (solve | cases computed; apply Linked.quiet <;> simp [stage_write, unsupported])
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
    all_goals
      rename_i inner applied
      cases computed
      first
        | (solve
            | have fresh : Linked before (.deliver index bytes policy) inner := startup_linked before _ inner applied
              exact Linked.of_fields fresh rfl rfl rfl rfl rfl)
        | (solve
            | have fresh : Linked before (.deliver index bytes policy) inner := application_linked before _ _ inner applied
              exact Linked.of_fields fresh rfl rfl rfl rfl rfl)
        | (solve
            | have fresh : Linked before (.deliver index bytes policy) inner := recovery_linked before _ inner applied
              exact Linked.of_fields fresh rfl rfl rfl rfl rfl)

theorem Step.linked (actual : CampusTCPModel.Step input) : Linked actual.before actual.event actual.result := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  have linked := process_linked actual.before actual.event effect computed
  cases linked with
  | quiet ordinary recovery same => exact .quiet (by simpa [result] using ordinary) (by simpa [result] using recovery) (by simpa [result] using same)
  | ordinary head recorded recovery prior after stamp pending supported =>
    exact .ordinary head (by simpa [result] using recorded) (by simpa [result] using recovery)
      prior (by simpa [result] using after) stamp pending (by simpa [result] using supported)
  | recovery head recorded ordinary prior after stamp =>
    exact .recovery head (by simpa [result] using recorded) (by simpa [result] using ordinary)
      prior (by simpa [result] using after) stamp
  | drain archive ordinary recovery event prior after retained stamp =>
    exact .drain archive (by simpa [result] using ordinary) (by simpa [result] using recovery)
      event prior (by simpa [result] using after) (by simpa [result] using retained) stamp

inductive Chain : Stage input.active input.passive → List (CampusTCPModel.Step input) →
    Stage input.active input.passive → Prop where
  | done (value) : Chain value [] value
  | next (actual : CampusTCPModel.Step input) (linked : Linked actual.before actual.event actual.result)
      (tail : Chain (stage actual.result.state.connection) rest final) :
      Chain (stage actual.before.connection) (actual :: rest) final

theorem Trace.startup_chain (trace : CampusTCPModel.Trace input initial events steps final remaining) :
    Chain (stage initial.connection) steps (stage final.connection) := by
  induction trace with
  | done => exact .done _
  | stop head _ _ => exact .next head (Step.linked head) (.done _)
  | next head _ _ ih => exact .next head (Step.linked head) ih

theorem Report.startup_chain (report : CampusTCPModel.Report input events) :
    Chain (.ordinary .idle) report.steps (stage report.final.connection) :=
  Trace.startup_chain report.trace


private theorem application_archive (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) :
    effect.state.recoveryArchive = before.recoveryArchive := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw] at computed)

private theorem startup_archive (before : State input) (event : TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) :
    effect.state.recoveryArchive = before.recoveryArchive := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_archive (before : State input) (event : C.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) :
    effect.state.recoveryArchive = before.recoveryArchive := by
  cases connected : before.connection with
  | startup value pending | application value pending =>
    simp only [runRecovery, connected, pure, Except.pure, Except.ok.injEq] at computed
    subst effect
    rfl
  | recovering current =>
    simp only [runRecovery, connected] at computed
    split at computed
    · cases computed
    · split at computed
      all_goals
        simp only [pure, Except.pure, Except.ok.injEq] at computed
        subst effect
        rfl

private theorem open_archive (before : State input) (remote : TCP.Handshake.Socket) (policy : Bool)
    (effect : Effect input) (computed : openRecovering input before remote policy = .ok effect) :
    effect.state.recoveryArchive = before.recoveryArchive := by
  unfold openRecovering at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (solve | exact recovery_archive { before with connection := .recovering .initial } _ effect computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem enableStartupRecovery_archive (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableStartupRecovery input before actor = .ok effect) :
    effect.state.recoveryArchive = before.recoveryArchive := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; rfl
  · exact application_archive _ _ _ _ computed

private theorem enableAck_archive (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) :
    effect.state.recoveryArchive = before.recoveryArchive := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_archive _ _ _ _ computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

inductive ArchiveChange (before : State input) (effect : Effect input) : Prop where
  | frame (same : effect.state.recoveryArchive = before.recoveryArchive)
  | drain (archive : RecoveryArchive input.active input.passive)
      (prior : before.connection = .recovering archive.current)
      (after : stage effect.state.connection = .ordinary (.complete archive.complete))
      (retained : effect.state.recoveryArchive = some archive)

private theorem finish_archive (before : State input) (effect : Effect input)
    (computed : finishStartup input before = .ok effect) : ArchiveChange before effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; exact .frame rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  all_goals
    rename_i connection current connected complete client server phase activeData activeHandoff passiveData passiveHandoff noPackets noWork noArchive
    cases computed
    exact .drain ⟨before.time, current, complete, client, server, phase,
      activeData, activeHandoff, passiveData, passiveHandoff⟩ connected rfl rfl

private theorem archive_write (state : State input) (gateway : Gateway) (resident : Local) :
    (state.write gateway resident).recoveryArchive = state.recoveryArchive := by cases gateway <;> rfl

private theorem process_archive (before : State input) (event : CampusTCPModel.Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) : ArchiveChange before effect := by
  cases event with
  | «open» remote policy => exact .frame (startup_archive _ _ _ computed)
  | openRecovering remote policy => exact .frame (open_archive _ _ _ _ computed)
  | startupClock actor millis | startupTimeout actor generation policy => exact .frame (recovery_archive _ _ _ computed)
  | finishStartup => exact finish_archive _ _ computed
  | write actor bytes | send actor bytes policy | read actor bytes | emitAck actor policy
  | advanceClock actor millis | timeout actor policy | dispatchAck actor policy | enableRecovery actor =>
    exact .frame (application_archive _ _ _ _ computed)
  | enableStartupRecovery actor => exact .frame (enableStartupRecovery_archive _ _ _ computed)
  | enableAck actor => exact .frame (enableAck_archive _ _ _ computed)
  | copyPacket id | dropPacket id => cases computed; exact .frame rfl
  | authentication index | install id | stage id | installGuard id | installAt gateway id
  | stageAt gateway id | installGuardAt gateway id | pause | stageCheckpoint | installCheckpoint ns
  | switchRoute actor gateway | fencePrimary | resume | assign index ingress | serve index observed =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress, transferControl] at computed
    repeat' first
      | (solve | cases computed; apply ArchiveChange.frame; simp only [archive_write, unsupported])
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
    all_goals
      rename_i inner applied
      cases computed
      apply ArchiveChange.frame
      first
        | exact startup_archive before _ inner applied
        | exact application_archive before _ _ inner applied
        | exact recovery_archive before _ inner applied

theorem Step.archive_change (actual : CampusTCPModel.Step input) : ArchiveChange actual.before actual.result := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  cases process_archive actual.before actual.event effect computed with
  | frame same => exact .frame (by simpa only [result] using same)
  | drain archive prior after retained =>
    exact .drain archive prior (by simpa only [result] using after) (by simpa only [result] using retained)


inductive RecoveryProjection {active passive : TCP.Handshake.Local} :
    Stage active passive → List (C.Step active passive) → Prop where
  | ordinary (value) : RecoveryProjection (.ordinary value) []
  | recovering (trace : TCPHandshakeRecovery.Trace .initial (records.map (·.event)) records current) :
      RecoveryProjection (.recovering current) records
  | drained (archive : RecoveryArchive active passive)
      (trace : TCPHandshakeRecovery.Trace .initial (records.map (·.event)) records archive.current) :
      RecoveryProjection (.ordinary (.complete archive.complete)) records

variable {input : Input} {records : List (C.Step input.active input.passive)}

private theorem RecoveryProjection.advance (linked : Linked before event effect)
    (projection : RecoveryProjection (stage before.connection) records) :
    RecoveryProjection (stage effect.state.connection) (records ++ effect.recovery.toList) := by
  cases linked with
  | quiet ordinary recovery same => simpa only [same, recovery, Option.toList_none, List.append_nil] using projection
  | ordinary actual recorded recovery prior after stamp pending supported =>
    rw [prior] at projection
    cases phase : actual.before <;> rw [phase] at projection
    all_goals first
      | (solve | rw [phase] at pending; cases pending)
      | (cases projection; simpa only [after, recovery, Option.toList_none, List.append_nil] using RecoveryProjection.ordinary actual.result.state)
  | recovery actual recorded ordinary prior after stamp =>
    rw [after, recorded]
    rcases prior with prior | ⟨prior, seeded⟩
    · rw [prior] at projection
      cases projection with
      | recovering trace =>
        apply RecoveryProjection.recovering
        simpa only [Option.toList_some, List.map_append, List.map_singleton] using trace.snoc (actual := actual)
    · rw [prior] at projection
      cases projection with
      | ordinary =>
        apply RecoveryProjection.recovering
        have trace : TCPHandshakeRecovery.Trace .initial [actual.event] [actual] actual.result.state := by
          rw [← seeded]
          exact .next actual (.done _)
        exact trace
  | drain archive ordinary recovery event prior after retained stamp =>
    have start : stage before.connection = .recovering archive.current := by rw [prior]; rfl
    rw [start] at projection
    cases projection with
    | recovering trace =>
      simpa only [after, recovery, Option.toList_none, List.append_nil] using RecoveryProjection.drained archive trace

theorem Chain.recovery_projection (chain : Chain first steps final)
    (projection : RecoveryProjection first records) :
    RecoveryProjection final (records ++ steps.filterMap (·.result.recovery)) := by
  induction chain generalizing records with
  | done => simpa only [List.filterMap_nil, List.append_nil] using projection
  | next actual linked tail ih =>
    have after := ih (RecoveryProjection.advance linked projection)
    cases present : actual.result.recovery <;>
      simpa only [List.filterMap_cons, present, Option.toList_none, Option.toList_some,
        List.append_nil, List.singleton_append, List.append_assoc] using after


structure RecoveryEvidence (state : State input) (records : List (C.Step input.active input.passive)) : Prop where
  projection : RecoveryProjection (stage state.connection) records
  archive : ∀ archive, state.recoveryArchive = some archive →
    stage state.connection = .ordinary (.complete archive.complete) ∧
      TCPHandshakeRecovery.Trace .initial (records.map (·.event)) records archive.current

private theorem RecoveryEvidence.advance (linked : Linked before event effect) (change : ArchiveChange before effect)
    (evidence : RecoveryEvidence before records) :
    RecoveryEvidence effect.state (records ++ effect.recovery.toList) := by
  refine ⟨RecoveryProjection.advance linked evidence.projection, ?_⟩
  intro archive present
  cases linked with
  | quiet ordinary recovery same =>
    cases change with
    | frame frame =>
      obtain ⟨before, trace⟩ := evidence.archive archive (frame.symm.trans present)
      exact ⟨same.trans before, by simpa only [recovery, Option.toList_none, List.append_nil] using trace⟩
    | drain selected prior after retained =>
      have start : stage before.connection = .recovering selected.current := by rw [prior]; rfl
      have impossible := after.symm.trans (same.trans start)
      cases impossible
  | ordinary actual recorded recovery prior after stamp pending supported =>
    cases change with
    | frame frame =>
      obtain ⟨before, trace⟩ := evidence.archive archive (frame.symm.trans present)
      have complete : actual.before = .complete archive.complete := Stage.ordinary.inj (prior.symm.trans before)
      rw [complete] at pending
      cases pending
    | drain selected before after retained =>
      rw [before] at prior
      cases prior
  | recovery actual recorded ordinary prior after stamp =>
    cases change with
    | frame frame =>
      obtain ⟨before, trace⟩ := evidence.archive archive (frame.symm.trans present)
      rcases prior with prior | ⟨prior, seeded⟩
      · rw [before] at prior; cases prior
      · have impossible := before.symm.trans prior; cases impossible
    | drain selected prior finish retained =>
      have impossible := after.symm.trans finish
      cases impossible
  | drain selected ordinary recovery event prior after retained stamp =>
    have same : selected = archive := Option.some.inj (retained.symm.trans present)
    subst selected
    have start : stage before.connection = .recovering archive.current := by rw [prior]; rfl
    have projection := evidence.projection
    rw [start] at projection
    cases projection with
    | recovering trace => exact ⟨after, by simpa only [recovery, Option.toList_none, List.append_nil] using trace⟩

theorem Trace.recovery_evidence (trace : CampusTCPModel.Trace input initial events steps final remaining)
    (evidence : RecoveryEvidence initial records) :
    RecoveryEvidence final (records ++ steps.filterMap (·.result.recovery)) := by
  induction trace generalizing records with
  | done => simpa only [List.filterMap_nil, List.append_nil] using evidence
  | stop head blocked tail =>
    have after := RecoveryEvidence.advance (Step.linked head) (Step.archive_change head) evidence
    cases present : head.result.recovery <;>
      simpa only [List.filterMap_cons, List.filterMap_nil, present, Option.toList_none, Option.toList_some] using after
  | next head supported tail ih =>
    have after := ih (RecoveryEvidence.advance (Step.linked head) (Step.archive_change head) evidence)
    cases present : head.result.recovery <;>
      simpa only [List.filterMap_cons, present, Option.toList_none, Option.toList_some,
        List.append_nil, List.singleton_append, List.append_assoc] using after

theorem Report.recovery_evidence (report : CampusTCPModel.Report input events) :
    RecoveryEvidence report.final (report.steps.filterMap (·.result.recovery)) := by
  have initial : RecoveryEvidence (input.initial) [] := ⟨.ordinary .idle, by intro archive present; cases present⟩
  simpa only [List.nil_append] using Trace.recovery_evidence report.trace initial

theorem Report.archive_trace (report : CampusTCPModel.Report input events)
    (present : report.final.recoveryArchive = some archive) :
    TCPHandshakeRecovery.Trace .initial ((report.steps.filterMap (·.result.recovery)).map (·.event))
      (report.steps.filterMap (·.result.recovery)) archive.current :=
  ((Report.recovery_evidence report).archive archive present).2

def Report.archiveReachable (report : CampusTCPModel.Report input events)
    (present : report.final.recoveryArchive = some archive) : TCPHandshakeRecovery.Reachable archive.current :=
  ⟨_, _, Report.archive_trace report present⟩

theorem Report.recovery_projection (report : CampusTCPModel.Report input events) :
    RecoveryProjection (stage report.final.connection) (report.steps.filterMap (·.result.recovery)) := by
  simpa only [List.nil_append] using Chain.recovery_projection (Report.startup_chain report) (RecoveryProjection.ordinary .idle)

theorem Report.recovery_trace (report : CampusTCPModel.Report input events)
    (connection : report.final.connection = .recovering current) :
    TCPHandshakeRecovery.Trace .initial ((report.steps.filterMap (·.result.recovery)).map (·.event))
      (report.steps.filterMap (·.result.recovery)) current := by
  have projection := Report.recovery_projection report
  rw [connection] at projection
  cases projection with
  | recovering trace => exact trace

def Report.recoveryReachable (report : CampusTCPModel.Report input events)
    (connection : report.final.connection = .recovering current) : TCPHandshakeRecovery.Reachable current :=
  ⟨_, _, Report.recovery_trace report connection⟩


theorem Step.recovery_stamp (actual : CampusTCPModel.Step input) (head : C.Step input.active input.passive)
    (recorded : actual.result.recovery = some head) : head.index = actual.before.time := by
  cases Step.linked actual with
  | quiet ordinary absent same | ordinary selected ordinary absent prior after stamp pending supported
  | drain archive ordinary absent event prior after retained stamp => rw [absent] at recorded; cases recorded
  | recovery selected present ordinary prior after stamp =>
    have same := Option.some.inj (present.symm.trans recorded)
    subst selected
    exact stamp

theorem Report.recovery_step_origin (report : CampusTCPModel.Report input events)
    (member : actual ∈ report.steps.filterMap (·.result.recovery)) :
    ∃ joint ∈ report.steps, joint.result.recovery = some actual ∧ actual.index = joint.before.time := by
  obtain ⟨joint, retained, recorded⟩ := List.mem_filterMap.mp member
  exact ⟨joint, retained, recorded, Step.recovery_stamp joint actual recorded⟩

end Netlib.Check.CampusTCPRecoveryStartupOrigins
