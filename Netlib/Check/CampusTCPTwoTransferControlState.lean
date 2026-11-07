import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoTransferControlObserve
import Netlib.Check.CampusTCPTwoTransferGuards
import Netlib.Check.CampusTCPTwoTransferHandoff

/-!
# Current planned-transfer control state

Capture permits pending primary work. Installation follows its actual drain.
The finished stage retains routing without freezing later standby transport.
-/

namespace Netlib.Check.CampusTCPTwoTransferControlState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

namespace W
export CampusTCPTwoTransferMonitor (Mode Monitor Control controlDemand drainTicket observe)
end W
namespace T
export CampusTCPTransferEnabled (Control)
end T
namespace G
export CampusTCPTwoTransferGuards (Ready)
end G

variable {input : Input} {state after : State input}
variable {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {kind : W.Control} {actual : Step input}

structure Source (state : State input) (paused : Bool) : Prop where
  paused : state.assignmentPaused = paused
  unsealed : state.primarySealed = false
  unfenced : state.primaryFenced = false
  client : state.owners.client = .primary
  server : state.owners.server = .primary
  empty : state.standby.transport = Checkpoint.Gateway.initial
  namespaceEq : state.standby.guard.source.ns = (input.deployment .standby).executionNS

structure Captured (state : State input) : Prop where
  drained : state.outstanding .primary = 0
  fresh : ∃ checkpoint, state.cache = some checkpoint ∧ Checkpoint.capture state.primary.history = .ok checkpoint.snapshot

def Consistent (state : State input) : Prop :=
  ∃ installed, state.installation = some installed ∧ state.primary.transport = installed.checkpoint.snapshot.source ∧
    state.standby.transport = installed.installed.state

structure Target (state : State input) (fenced : Bool) : Prop where
  paused : state.assignmentPaused = true
  sealed : state.primarySealed = true
  fenced : state.primaryFenced = fenced
  drained : state.outstanding .primary = 0
  consistent : Consistent state

structure Finished (state : State input) : Prop where
  unpaused : state.assignmentPaused = false
  sealed : state.primarySealed = true
  fenced : state.primaryFenced = true
  client : state.owners.client = .standby
  server : state.owners.server = .standby
  installed : state.installation.isSome = true

inductive Phase (state : State input) : W.Mode → Gateway → Prop where
  | armed (source : Source state false) : Phase state .armed .primary
  | capture (source : Source state true) : Phase state .capture .primary
  | install (source : Source state true) (captured : Captured state) : Phase state .install .primary
  | clientRoute (target : Target state false) (client : state.owners.client = .primary)
      (server : state.owners.server = .primary) : Phase state .clientRoute .standby
  | serverRoute (target : Target state false) (client : state.owners.client = .standby)
      (server : state.owners.server = .primary) : Phase state .serverRoute .standby
  | fence (target : Target state false) (client : state.owners.client = .standby)
      (server : state.owners.server = .standby) : Phase state .fence .standby
  | resume (target : Target state true) (client : state.owners.client = .standby)
      (server : state.owners.server = .standby) : Phase state .resume .standby
  | finished (routing : Finished state) : Phase state .finished .standby

theorem of_initial (routing : Routing current .primary) (empty : current.report.final.standby.transport = Checkpoint.Gateway.initial)
    (namespaceEq : current.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS) :
    Phase current.report.final .armed .primary :=
  .armed ⟨routing.unpaused, (routing.primary rfl).1, (routing.primary rfl).2,
    routing.owners .client, routing.owners .server, empty, namespaceEq⟩

theorem finished_routing (phase : Phase current.report.final .finished location) : Routing current .standby := by
  cases phase with
  | finished fields =>
    refine { owners := ?_, unpaused := fields.unpaused, primary := ?_, standby := ?_ }
    · intro actor
      cases actor
      · exact fields.client
      · exact fields.server
    · intro impossible
      cases impossible
    · intro _
      cases installed : current.report.final.installation with
      | none =>
        have present := fields.installed
        simp only [installed, Option.isSome_none, Bool.false_eq_true] at present
      | some value => exact ⟨value, rfl, fields.sealed, fields.fenced⟩

private theorem mode_beq (left right : W.Mode) : (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem capture_drainless (mode : monitor.mode = .capture) (drainless : W.drainTicket state monitor = none) :
    state.outstanding .primary = 0 := by
  have absent : state.work.pending.find? (fun item => decide (item.value.gateway = .primary)) = none := by
    cases found : state.work.pending.find? (fun item => decide (item.value.gateway = .primary)) with
    | none => rfl
    | some item =>
      simp only [W.drainTicket, mode, mode_beq, decide_true, ite_true, found, Option.map_some] at drainless
      cases drainless
  change (state.work.pending.filter (fun item => decide (item.value.gateway = .primary))).length = 0
  apply List.length_eq_zero_iff.mpr
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro item member
  obtain ⟨pending, primary⟩ := List.mem_filter.mp member
  exact (List.find?_eq_none.mp absent) item pending primary

private theorem route_ready (target : Target state fenced) (configured : input.configured .standby = true) :
    CampusTCPTransferEnabled.RouteReady state :=
  ⟨configured, target.paused, target.sealed, target.consistent⟩

theorem ready (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : Phase current.report.final monitor.mode location) (selected : W.controlDemand monitor = some kind)
    (_drainless : W.drainTicket current.report.final monitor = none) : G.Ready current.report.final kind := by
  have configured := checks.configured .standby
  generalize modeEq : monitor.mode = mode at phase
  cases phase with
  | armed source =>
    have same : kind = .pause := by
      simp only [W.controlDemand, modeEq] at selected
      split at selected
      · exact Option.some.inj selected.symm
      · cases selected
    subst kind
    exact ⟨configured, source.paused, source.unsealed, source.unfenced⟩
  | capture source =>
    have same : kind = .capture := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    exact ⟨configured, source.unsealed, source.unfenced, CampusTCPTwoTransferHandoff.capture_ready core.live.gatewayState⟩
  | install source captured =>
    have same : kind = .install := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    refine ⟨configured, source.paused, source.unsealed, source.unfenced, captured.drained, source.namespaceEq, source.empty, ?_⟩
    obtain ⟨checkpoint, stored, capture⟩ := captured.fresh
    have fields := Checkpoint.capture_source _ _ capture
    exact ⟨checkpoint, stored, fields.1.symm, fields.2.1.symm⟩
  | clientRoute target client server =>
    have same : kind = .clientRoute := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    exact route_ready target configured
  | serverRoute target client server =>
    have same : kind = .serverRoute := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    exact route_ready target configured
  | fence target client server =>
    have same : kind = .fence := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    have installed : current.report.final.installation.isSome = true := by
      obtain ⟨value, stored, _, _⟩ := target.consistent
      rw [stored]
      rfl
    exact ⟨configured, target.paused, target.sealed, installed, client, server, target.drained⟩
  | resume target client server =>
    have same : kind = .resume := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    exact ⟨configured, target.paused, target.fenced, client, server, target.consistent⟩
  | finished fields => simp only [W.controlDemand, modeEq] at selected; cases selected

def Stored (kind : W.Control) (actual : Step input) : Prop :=
  match kind with
  | .capture => ∃ checkpoint, actual.result.checkpoint = some checkpoint
  | .install => ∃ installation, actual.result.installation = some installation
  | _ => True

def afterLocation : W.Control → Gateway
  | .pause | .capture => .primary
  | _ => .standby

private theorem noninstall (kind : W.Control) (different : kind ≠ .install) :
    ∀ ns, kind.event cfg ≠ .installCheckpoint ns := by
  cases kind <;> simp only [CampusTCPTwoTransferMonitor.Control.event] <;> intro ns impossible
  all_goals first | (solve | cases impossible) | exact False.elim (different rfl)

private theorem source_after (value : T.Control current (kind.event cfg) actual) (source : Source current.report.final paused)
    (different : kind ≠ .install) (routes : ∀ actor gateway, kind.event cfg ≠ .switchRoute actor gateway)
    (fenced : kind ≠ .fence) (unpaused : kind ≠ .resume) :
    Source value.move.after.report.final (if kind = .pause then true else paused) := by
  have standby := value.frame.standby (noninstall kind different)
  rcases source with ⟨pausedEq, unsealedEq, unfencedEq, clientEq, serverEq, emptyEq, namespaceEq⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [value.frame.paused]
    cases kind <;> simp_all [CampusTCPTransferEnabled.pausedAfter, CampusTCPTwoTransferMonitor.Control.event]
  · rw [value.frame.sealed]
    cases kind <;> simp_all [CampusTCPTransferEnabled.sealedAfter, CampusTCPTwoTransferMonitor.Control.event]
  · rw [value.frame.fenced]
    cases kind <;> simp_all [CampusTCPTransferEnabled.fencedAfter, CampusTCPTwoTransferMonitor.Control.event]
  · rw [value.frame.owners]
    cases kind <;> simp_all [CampusTCPTransferEnabled.ownersAfter, CampusTCPTwoTransferMonitor.Control.event]
  · rw [value.frame.owners]
    cases kind <;> simp_all [CampusTCPTransferEnabled.ownersAfter, CampusTCPTwoTransferMonitor.Control.event]
  · rw [standby]
    exact emptyEq
  · rw [standby]
    exact namespaceEq

private theorem consistent_after (value : T.Control current (kind.event cfg) actual) (different : kind ≠ .install)
    (consistent : Consistent current.report.final) : Consistent value.move.after.report.final := by
  obtain ⟨installed, stored, source, target⟩ := consistent
  exact ⟨installed, (value.frame.installation (noninstall kind different)).trans stored,
    (congrArg Local.transport value.frame.primary).trans source,
    (congrArg Local.transport (value.frame.standby (noninstall kind different))).trans target⟩

private theorem target_after (value : T.Control current (kind.event cfg) actual) (target : Target current.report.final fenced)
    (different : kind ≠ .install) (pause : kind ≠ .pause) (resume : kind ≠ .resume) :
    Target value.move.after.report.final (if kind = .fence then true else fenced) := by
  have consistent := consistent_after value different target.consistent
  rcases target with ⟨pausedEq, sealedEq, fencedEq, drainedEq, oldConsistent⟩
  refine ⟨?_, ?_, ?_, ?_, consistent⟩
  · rw [value.frame.paused]
    cases kind <;> simp_all [CampusTCPTransferEnabled.pausedAfter, CampusTCPTwoTransferMonitor.Control.event]
  · rw [value.frame.sealed]
    cases kind <;> simp_all [CampusTCPTransferEnabled.sealedAfter, CampusTCPTwoTransferMonitor.Control.event]
  · rw [value.frame.fenced]
    cases kind <;> simp_all [CampusTCPTransferEnabled.fencedAfter, CampusTCPTwoTransferMonitor.Control.event]
  · simpa only [State.outstanding, value.frame.work] using drainedEq

theorem control_next (phase : Phase current.report.final monitor.mode location)
    (value : T.Control current (kind.event cfg) actual) (selected : W.controlDemand monitor = some kind)
    (drainless : W.drainTicket current.report.final monitor = none) (stored : Stored kind actual) :
    Phase value.move.after.report.final kind.after (afterLocation kind) := by
  generalize modeEq : monitor.mode = mode at phase
  cases phase with
  | armed source =>
    have same : kind = .pause := by
      simp only [W.controlDemand, modeEq] at selected
      split at selected
      · exact Option.some.inj selected.symm
      · cases selected
    subst kind
    exact .capture (source_after value source (by decide) (by intros; intro impossible; cases impossible) (by decide) (by decide))
  | capture source =>
    have same : kind = .capture := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    obtain ⟨checkpoint, present⟩ := stored
    have origin := CampusTCPTransferFacts.checkpoint_origin actual value.eventEq checkpoint present
    have capture := origin.1
    rw [value.move.beforeEq] at capture
    have cached := origin.2.2.2.2.2.1
    rw [← value.move.final] at cached
    refine .install (source_after value source (by decide) (by intros; intro impossible; cases impossible) (by decide) (by decide)) ⟨?_, ?_⟩
    · simpa only [State.outstanding, value.frame.work] using capture_drainless modeEq drainless
    · exact ⟨checkpoint, cached, by rw [value.frame.primary]; exact capture⟩
  | install source captured =>
    have same : kind = .install := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    obtain ⟨installed, present⟩ := stored
    have origin := CampusTCPTransferFacts.installation_origin actual _ value.eventEq installed present
    refine .clientRoute ⟨?_, value.frame.sealed, ?_, ?_, ?_⟩ ?_ ?_
    · exact value.frame.paused.trans source.paused
    · exact value.frame.fenced.trans source.unfenced
    · simpa only [State.outstanding, value.frame.work] using captured.drained
    · refine ⟨installed, by rw [value.move.final]; exact origin.stored, ?_, ?_⟩
      · rw [value.frame.primary, ← value.move.beforeEq]
        exact origin.cut
      · rw [value.move.final]
        exact origin.copied.trans installed.installed.copied.symm
    · rw [value.frame.owners]
      exact source.client
    · rw [value.frame.owners]
      exact source.server
  | clientRoute target client server =>
    have same : kind = .clientRoute := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    refine .serverRoute (target_after value target (by decide) (by decide) (by decide)) ?_ ?_
    · rw [value.frame.owners]
      rfl
    · rw [value.frame.owners]
      exact server
  | serverRoute target client server =>
    have same : kind = .serverRoute := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    refine .fence (target_after value target (by decide) (by decide) (by decide)) ?_ ?_
    · rw [value.frame.owners]
      exact client
    · rw [value.frame.owners]
      rfl
  | fence target client server =>
    have same : kind = .fence := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    refine .resume (target_after value target (by decide) (by decide) (by decide)) ?_ ?_
    · rw [value.frame.owners]
      exact client
    · rw [value.frame.owners]
      exact server
  | resume target client server =>
    have same : kind = .resume := Option.some.inj (by simpa only [W.controlDemand, modeEq] using selected.symm)
    subst kind
    refine .finished ⟨value.frame.paused, value.frame.sealed.trans target.sealed,
      value.frame.fenced.trans target.fenced, ?_, ?_, ?_⟩
    · rw [value.frame.owners]
      exact client
    · rw [value.frame.owners]
      exact server
    · obtain ⟨installed, present, _, _⟩ := consistent_after value (by decide) target.consistent
      rw [present]
      rfl
  | finished fields => simp only [W.controlDemand, modeEq] at selected; cases selected

structure Advanced (current : Cut input complete) (cfg : CampusTCPTwoTransferMonitor.Config)
    (monitor : W.Monitor) (kind : W.Control) (actual : Step input) where
  value : T.Control current (kind.event cfg) actual
  stored : Stored kind actual
  observed : W.observe cfg monitor actual = CampusTCPTwoTransferControlObserve.afterControl monitor kind
  next : Phase value.move.after.report.final kind.after (afterLocation kind)

private theorem enabled_stored (kind : W.Control) (ready : G.Ready current.report.final kind)
    (cfg : CampusTCPTwoTransferMonitor.Config) (namespaceEq : cfg.executionNS = (input.deployment .standby).executionNS) :
    ∃ actual, ∃ _value : T.Control current (kind.event cfg) actual, Stored kind actual := by
  cases kind with
  | pause =>
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTransferEnabled.pause_at ready
    exact ⟨actual, value, trivial⟩
  | capture =>
    obtain ⟨actual, checkpoint, ⟨value⟩, present⟩ := CampusTCPTransferEnabled.stage_at ready
    exact ⟨actual, value, checkpoint, present⟩
  | install =>
    obtain ⟨actual, installation, ⟨value⟩, present⟩ := CampusTCPTransferEnabled.install_at ready
    refine ⟨actual, ?_, installation, present⟩
    simpa only [CampusTCPTwoTransferMonitor.Control.event, namespaceEq] using value
  | clientRoute =>
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTransferEnabled.route_at ready .client
    exact ⟨actual, value, trivial⟩
  | serverRoute =>
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTransferEnabled.route_at ready .server
    exact ⟨actual, value, trivial⟩
  | fence =>
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTransferEnabled.fence_at ready
    exact ⟨actual, value, trivial⟩
  | resume =>
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTransferEnabled.resume_at ready
    exact ⟨actual, value, trivial⟩

theorem control_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : Phase current.report.final monitor.mode location) (selected : W.controlDemand monitor = some kind)
    (drainless : W.drainTicket current.report.final monitor = none) :
    ∃ actual, Nonempty (Advanced current (config initial checks routing quantum allowance reverseLower reverseUpper) monitor kind actual) := by
  let cfg := config initial checks routing quantum allowance reverseLower reverseUpper
  obtain ⟨actual, value, stored⟩ := enabled_stored kind (ready core phase selected drainless) cfg rfl
  exact ⟨actual, ⟨⟨value, stored, CampusTCPTwoTransferControlObserve.control_observe value selected drainless,
    control_next phase value selected drainless stored⟩⟩⟩

theorem Advanced.next_observed (advance : Advanced current cfg monitor kind actual) :
    Phase advance.value.move.after.report.final (W.observe cfg monitor actual).mode (afterLocation kind) := by
  rw [advance.observed]
  exact advance.next

theorem Advanced.mode (advance : Advanced current cfg monitor kind actual) :
    (W.observe cfg monitor actual).mode = kind.after := by rw [advance.observed]; rfl

theorem Step.control (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : Phase current.report.final monitor.mode location) (selected : W.controlDemand monitor = some kind)
    (drainless : W.drainTicket current.report.final monitor = none) (actual : Step input)
    (before : actual.before = current.report.final)
    (event : actual.event = kind.event (config initial checks routing quantum allowance reverseLower reverseUpper)) :
    Nonempty (Advanced current (config initial checks routing quantum allowance reverseLower reverseUpper) monitor kind actual) := by
  obtain ⟨enabled, ⟨advance⟩⟩ := control_at core phase selected drainless
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (advance.value.move.beforeEq.trans before.symm) (advance.value.eventEq.trans event.symm)
  exact ⟨same ▸ advance⟩

private theorem source_snapshot (state : State input) (paused : Bool) :
    Source (CampusTCPRoundStutter.snapshot state) paused ↔ Source state paused := by
  constructor <;> rintro ⟨a, b, c, d, e, f, g⟩ <;> exact ⟨a, b, c, d, e, f, g⟩

private theorem captured_snapshot (state : State input) :
    Captured (CampusTCPRoundStutter.snapshot state) ↔ Captured state := by
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, b⟩

private theorem target_snapshot (state : State input) (fenced : Bool) :
    Target (CampusTCPRoundStutter.snapshot state) fenced ↔ Target state fenced := by
  constructor <;> rintro ⟨a, b, c, d, e⟩ <;> exact ⟨a, b, c, d, e⟩

private theorem finished_snapshot (state : State input) :
    Finished (CampusTCPRoundStutter.snapshot state) ↔ Finished state := by
  constructor <;> rintro ⟨a, b, c, d, e, f⟩ <;> exact ⟨a, b, c, d, e, f⟩

private theorem snapshot_phase (state : State input) (mode : W.Mode) (location : Gateway) :
    Phase (CampusTCPRoundStutter.snapshot state) mode location ↔ Phase state mode location := by
  constructor <;> intro phase <;> cases phase <;> constructor
  all_goals first
    | assumption
    | (apply (source_snapshot _ _).mp; assumption)
    | (apply (source_snapshot _ _).mpr; assumption)
    | (apply (captured_snapshot _).mp; assumption)
    | (apply (captured_snapshot _).mpr; assumption)
    | (apply (target_snapshot _ _).mp; assumption)
    | (apply (target_snapshot _ _).mpr; assumption)
    | (apply (finished_snapshot _).mp; assumption)
    | (apply (finished_snapshot _).mpr; assumption)

theorem Phase.clock (phase : Phase current.report.final monitor.mode location)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : Phase next.report.final monitor.mode location := by
  have fixed := (snapshot_phase current.report.final monitor.mode location).mpr phase
  rw [placement.frame.fixed] at fixed
  exact (snapshot_phase next.report.final monitor.mode location).mp fixed

private theorem write_standby (state : State input) (gateway : Gateway) (resident : Local) (primary : gateway = .primary) :
    (state.write gateway resident).standby = state.standby := by cases primary; rfl

private theorem service_standby
    (value : CampusTCPTwoTransferNetwork.Service current item hit session actual served emission emitted)
    (primary : item.value.gateway = .primary) : value.move.after.report.final.standby = current.report.final.standby := by
  obtain ⟨completed, accepted, itemEq, _⟩ := value.facts.completed
  have gateway : completed.item.value.gateway = .primary := by rw [itemEq]; exact primary
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  rw [value.facts.event] at computed
  simp only [processCore, accepted, Except.mapError, bind, Except.bind] at computed
  rw [value.move.final, ← value.move.beforeEq]
  repeat' first
    | (solve | cases computed; rw [result]; first | rfl | exact write_standby _ _ _ gateway)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem Source.primary_service {paused : Bool} (source : Source current.report.final paused)
    (value : CampusTCPTwoTransferNetwork.Service current item hit session actual served emission emitted)
    (primary : item.value.gateway = .primary) : Source value.move.after.report.final paused := by
  have standby := service_standby value primary
  have fixed := value.environment
  have pausedEq := congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused fixed
  have sealedEq := congrArg CampusTCPRoundEnvironment.Environment.primarySealed fixed
  have fencedEq := congrArg CampusTCPRoundEnvironment.Environment.primaryFenced fixed
  have ownersEq := congrArg CampusTCPRoundEnvironment.Environment.owners fixed
  change current.report.final.owners = value.move.after.report.final.owners at ownersEq
  exact ⟨pausedEq.symm.trans source.paused, sealedEq.symm.trans source.unsealed, fencedEq.symm.trans source.unfenced,
    by rw [← ownersEq]; exact source.client, by rw [← ownersEq]; exact source.server,
    by rw [standby]; exact source.empty, by rw [standby]; exact source.namespaceEq⟩

end Netlib.Check.CampusTCPTwoTransferControlState
