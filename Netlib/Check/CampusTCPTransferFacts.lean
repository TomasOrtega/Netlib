import Netlib.Check.CampusTCPFacts
import Netlib.Check.CampusTCPTransferHistory

/-!
# Checked campus TCP transfer controls

The witnesses below come from actual joint operations and their stored results.
-/

namespace Netlib.Check.CampusTCPTransferFacts

open Packet Protocol
namespace M
export Check.CampusTCPModel (Input State Step Event CachedCheckpoint InstalledCheckpoint)
end M

private theorem mapError_ok (value : Except ε α) (map : ε → ε') (output : α)
    (computed : value.mapError map = .ok output) : value = .ok output := by
  cases value <;> simp_all [Except.mapError]

theorem checkpoint_origin (step : M.Step input) (event : step.event = .stageCheckpoint)
    (checkpoint : M.CachedCheckpoint) (present : step.result.checkpoint = some checkpoint) :
    TCP.Checkpoint.capture step.before.primary.history = .ok checkpoint.snapshot ∧
      checkpoint.time = step.before.time ∧ checkpoint.id = step.before.checkpoints.length ∧
      checkpoint.snapshot.source = step.before.primary.transport ∧
      checkpoint.snapshot.cut = step.before.primary.history.length ∧
      step.result.state.cache = some checkpoint ∧
      step.result.state.connection = step.before.connection ∧ step.result.state.work = step.before.work := by
  obtain ⟨effect, computed, result⟩ := step.processed
  have selected : effect.checkpoint = some checkpoint := by simpa only [result] using present
  rw [event] at computed
  simp only [Check.CampusTCPModel.process, Check.CampusTCPModel.transferControl] at computed
  repeat' first
    | (cases computed <;> simp only at selected <;> cases selected)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  all_goals
    have raw := mapError_ok (TCP.Checkpoint.capture step.before.primary.history)
      (fun reason => Check.CampusTCPModel.Error.input reason.message) _ (by assumption)
    have captured := TCP.Checkpoint.capture_source step.before.primary.history _ raw
    exact ⟨raw, rfl, rfl, captured.1, captured.2.1, by rw [result], by rw [result], by rw [result]⟩

structure InstallationOrigin (step : M.Step input) (executionNS : IngressAttachment.NamespaceRef)
    (value : M.InstalledCheckpoint) : Prop where
  paused : step.before.assignmentPaused = true
  drained : step.before.outstanding .primary = 0
  namespaceEq : executionNS = (input.deployment .standby).executionNS
  guardNamespace : step.before.standby.guard.source.ns = executionNS
  cache : step.before.cache = some value.checkpoint
  time : value.time = step.before.time
  source : value.source = step.before.primary.transport
  history : HEq value.history step.before.primary.history
  target : value.target = step.before.standby.transport
  cut : step.before.primary.transport = value.checkpoint.snapshot.source
  empty : step.before.standby.transport = TCP.Checkpoint.Gateway.initial
  copied : step.result.state.standby.transport = value.checkpoint.snapshot.source
  sealed : step.result.state.primarySealed = true
  stored : step.result.state.installation = some value
  work : step.result.state.work = step.before.work
  connection : step.result.state.connection = step.before.connection
  sourcePreserved : step.result.state.primary.transport = step.before.primary.transport

theorem installation_origin (step : M.Step input) (executionNS : IngressAttachment.NamespaceRef)
    (event : step.event = .installCheckpoint executionNS) (value : M.InstalledCheckpoint)
    (present : step.result.installation = some value) : InstallationOrigin step executionNS value := by
  obtain ⟨effect, computed, result⟩ := step.processed
  have selected : effect.installation = some value := by simpa only [result] using present
  rw [event] at computed
  simp only [Check.CampusTCPModel.process, Check.CampusTCPModel.transferControl] at computed
  repeat' first
    | (cases computed <;> simp only at selected <;> cases selected)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  all_goals
    rename_i checkpoint cached copied installed
    refine ⟨?_, ?_, ?_, ?_, cached, rfl, rfl, HEq.rfl, rfl, copied.sourceSame,
      copied.targetEmpty, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · simpa only [result] using copied.copied
    · rw [result]
    · rw [result]
    · rw [result]
    · rw [result]
    · rw [result]

theorem fence_origin (step : M.Step input) (event : step.event = .fencePrimary) :
    step.before.assignmentPaused = true ∧ step.before.primarySealed = true ∧
      step.before.installation.isSome = true ∧ step.before.owners.client = .standby ∧
      step.before.owners.server = .standby ∧ step.before.outstanding .primary = 0 ∧
      step.result.state.primaryFenced = true ∧ step.result.state.work = step.before.work ∧
      step.result.state.connection = step.before.connection := by
  obtain ⟨effect, computed, result⟩ := step.processed
  rw [event] at computed
  simp only [Check.CampusTCPModel.process, Check.CampusTCPModel.transferControl] at computed
  repeat' first
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  all_goals
    cases client : step.before.owners.client <;> cases server : step.before.owners.server <;>
      simp_all [bne, BEq.beq, StatefulFailover.instBEqGateway.beq, StatefulFailover.Gateway.ctorIdx]
  all_goals cases installed : step.before.installation <;> simp_all

theorem resume_origin (step : M.Step input) (event : step.event = .resume) :
    step.before.assignmentPaused = true ∧ step.before.primaryFenced = true ∧
      step.before.owners.client = .standby ∧ step.before.owners.server = .standby ∧
      step.result.state.assignmentPaused = false ∧ step.result.state.connection = step.before.connection ∧
      step.result.state.work = step.before.work := by
  obtain ⟨effect, computed, result⟩ := step.processed
  rw [event] at computed
  simp only [Check.CampusTCPModel.process, Check.CampusTCPModel.transferControl] at computed
  repeat' first
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  all_goals
    cases client : step.before.owners.client <;> cases server : step.before.owners.server <;>
      simp_all [bne, BEq.beq, StatefulFailover.instBEqGateway.beq, StatefulFailover.Gateway.ctorIdx]
  all_goals cases installed : step.before.installation <;> simp_all

theorem route_origin (step : M.Step input) (actor : Check.CampusTCPModel.Actor) (gateway)
    (event : step.event = .switchRoute actor gateway) :
    step.before.assignmentPaused = true ∧ step.before.primarySealed = true ∧ gateway = .standby ∧
      step.result.state.owner actor = .standby ∧ step.result.state.routeEpoch = step.before.routeEpoch + 1 ∧
      step.result.state.work = step.before.work ∧ step.result.state.connection = step.before.connection := by
  obtain ⟨effect, computed, result⟩ := step.processed
  rw [event] at computed
  simp only [Check.CampusTCPModel.process, Check.CampusTCPModel.transferControl] at computed
  repeat' first
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  all_goals
    cases gateway <;> cases actor <;>
      simp_all [bne, BEq.beq, StatefulFailover.instBEqGateway.beq, StatefulFailover.Gateway.ctorIdx,
        Check.CampusTCPModel.State.owner, Check.CampusTCPModel.Actor.leg, StatefulFailover.Owners.get,
        StatefulFailover.Owners.set]

theorem assignment_origin (step : M.Step input) (index : Nat) (ingress : IngressAttachment.InterfaceRef)
    (event : step.event = .assign index ingress) :
    ∃ produced, step.before.outputs[index]? = some produced ∧ step.before.assignmentPaused = false ∧
      (step.before.owner produced.actor = .primary → step.before.primarySealed = false ∧ step.before.primaryFenced = false) ∧
      (step.before.owner produced.actor = .standby → step.before.installation.isSome = true) := by
  obtain ⟨produced, found, work⟩ := CampusTCPFacts.assign_origin step index ingress event
  obtain ⟨effect, computed, result⟩ := step.processed
  rw [event] at computed
  simp only [Check.CampusTCPModel.process, Check.CampusTCPModel.get, found, bind, Except.bind] at computed
  repeat' first
    | (cases computed)
    | (split at computed)
    | (dsimp only [Check.CampusTCPModel.get, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at computed)
  all_goals
    refine ⟨produced, found, ?_, ?_, ?_⟩
    · simp_all
    · intro primary
      simp_all [BEq.beq, StatefulFailover.instBEqGateway.beq, StatefulFailover.Gateway.ctorIdx]
    · intro standby
      cases installed : step.before.installation <;>
        simp_all [BEq.beq, StatefulFailover.instBEqGateway.beq, StatefulFailover.Gateway.ctorIdx]

theorem service_after_fence (step : M.Step input) (served : Check.CampusTCPModel.Served input)
    (present : step.result.service = some served) (fenced : step.before.primaryFenced = true) :
    served.ticket.value.gateway = .standby := by
  obtain ⟨id, observed, completed, event, _, _, _, _⟩ := CampusTCPOrigins.service_origin step served present
  rcases CampusTCPFacts.serve_live step id observed event served present with live | standby
  · simp only [fenced, Bool.true_eq_false] at live
  · exact standby

inductive ControlKind where
  | pause
  | route (actor : Check.CampusTCPModel.Actor)
  | fence
  | resume
  deriving DecidableEq

def ControlKind.event : ControlKind → M.Event
  | .pause => .pause
  | .route actor => .switchRoute actor .standby
  | .fence => .fencePrimary
  | .resume => .resume

def controlKind : M.Event → Option ControlKind
  | .pause => some .pause
  | .switchRoute actor .standby => some (.route actor)
  | .fencePrimary => some .fence
  | .resume => some .resume
  | _ => none

theorem controlKind_correct (event : M.Event) (kind : ControlKind)
    (selected : controlKind event = some kind) : event = kind.event := by
  cases event <;> simp only [controlKind] at selected
  all_goals first
    | (solve | cases selected <;> rfl)
    | (rename_i actor gateway
       cases gateway <;> simp only at selected <;> cases selected <;> rfl)

structure Control (report : Check.CampusTCPModel.Report input events) (kind : ControlKind) (lower upper : Nat) where
  step : M.Step input
  member : step ∈ report.steps
  event : step.event = kind.event
  lower : lower ≤ step.before.time
  upper : step.before.time < upper

def findControl (report : Check.CampusTCPModel.Report input events) (kind : ControlKind) (lower upper : Nat) :
    Except String (Control report kind lower upper) :=
  match found : report.steps.find? (fun step => decide (controlKind step.event = some kind ∧
      lower ≤ step.before.time ∧ step.before.time < upper)) with
  | none => .error "An ordered planned-transfer control is absent from the actual replay."
  | some step =>
    have selected : controlKind step.event = some kind ∧ lower ≤ step.before.time ∧ step.before.time < upper :=
      of_decide_eq_true (List.find?_some (p := fun step : M.Step input => decide (controlKind step.event = some kind ∧
        lower ≤ step.before.time ∧ step.before.time < upper)) found)
    .ok ⟨step, List.mem_of_find?_eq_some found, controlKind_correct step.event kind selected.1,
      selected.2.1, selected.2.2⟩

structure Assurance (report : Check.CampusTCPModel.Report input events) where
  application : CampusTCPFacts.Assurance report
  step : M.Step input
  member : step ∈ report.steps
  executionNS : IngressAttachment.NamespaceRef
  event : step.event = .installCheckpoint executionNS
  installation : M.InstalledCheckpoint
  present : step.result.installation = some installation
  origin : InstallationOrigin step executionNS installation
  staging : CampusTCPFacts.At report installation.checkpoint.time
  stageEvent : staging.step.event = .stageCheckpoint
  stagePresent : staging.step.result.checkpoint = some installation.checkpoint
  captured : TCP.Checkpoint.capture staging.step.before.primary.history = .ok installation.checkpoint.snapshot
  stageEarlier : staging.step.before.time < step.before.time
  pause : Control report .pause 0 step.before.time
  clientRoute : Control report (.route .client) (step.before.time + 1) report.final.time
  serverRoute : Control report (.route .server) (step.before.time + 1) report.final.time
  fence : Control report .fence (max clientRoute.step.before.time serverRoute.step.before.time + 1) report.final.time
  resume : Control report .resume (fence.step.before.time + 1) report.final.time
  finalClient : report.final.owners.client = .standby
  finalServer : report.final.owners.server = .standby
  finalFenced : report.final.primaryFenced = true
  finalResumed : report.final.assignmentPaused = false
  finalSource : report.final.primary.transport = installation.checkpoint.snapshot.source

private def finish (report : Check.CampusTCPModel.Report input events)
    (application : CampusTCPFacts.Assurance report) (step : M.Step input) (member : step ∈ report.steps)
    (executionNS : IngressAttachment.NamespaceRef) (event : step.event = .installCheckpoint executionNS)
    (installation : M.InstalledCheckpoint) (present : step.result.installation = some installation)
    (staging : CampusTCPFacts.At report installation.checkpoint.time)
    (stageEvent : staging.step.event = .stageCheckpoint)
    (stagePresent : staging.step.result.checkpoint = some installation.checkpoint)
    (stageEarlier : staging.step.before.time < step.before.time) : Except String (Assurance report) := do
  let origin := installation_origin step executionNS event installation present
  let captured := (checkpoint_origin staging.step stageEvent installation.checkpoint stagePresent).1
  let pause ← findControl report .pause 0 step.before.time
  let client ← findControl report (.route .client) (step.before.time + 1) report.final.time
  let server ← findControl report (.route .server) (step.before.time + 1) report.final.time
  let fence ← findControl report .fence (max client.step.before.time server.step.before.time + 1) report.final.time
  let resume ← findControl report .resume (fence.step.before.time + 1) report.final.time
  if final : report.final.owners.client = .standby ∧ report.final.owners.server = .standby ∧
      report.final.primaryFenced = true ∧ report.final.assignmentPaused = false then
    return ⟨application, step, member, executionNS, event, installation, present, origin,
      staging, stageEvent, stagePresent, captured, stageEarlier, pause, client, server, fence, resume,
      final.1, final.2.1, final.2.2.1, final.2.2.2,
      (CampusTCPTransferHistory.Report.source_after_seal report step member origin.sealed).trans
        (origin.sourcePreserved.trans origin.cut)⟩
  else throw "The final replay does not retain standby ownership, fencing, resumption, and the exact archived source."

private theorem cached_stage (report : Check.CampusTCPModel.Report input events) (step : M.Step input)
    (member : step ∈ report.steps) (installation : M.InstalledCheckpoint)
    (cached : step.before.cache = some installation.checkpoint)
    (staging : CampusTCPFacts.At report installation.checkpoint.time) :
    staging.step.result.checkpoint = some installation.checkpoint ∧ staging.step.before.time < step.before.time := by
  obtain ⟨prior, later, split, preceding, _, _⟩ := CampusTCPFacts.step_origin report step member
  rcases CampusTCPTransferHistory.Trace.cache_origin preceding installation.checkpoint cached with initial | origin
  · simp [Check.CampusTCPModel.Input.initial] at initial
  · obtain ⟨source, inside, present, stamped, earlier⟩ := origin
    have global : source ∈ report.steps := by rw [split]; simp [inside]
    let found : CampusTCPFacts.At report installation.checkpoint.time := ⟨source, global, stamped.symm⟩
    have same := CampusTCPFacts.At.unique found staging
    rw [← same]
    exact ⟨present, earlier⟩

def assure (report : Check.CampusTCPModel.Report input events) : Except String (Assurance report) := do
  let application ← CampusTCPFacts.assure report
  match found : report.steps.find? (fun step => step.result.installation.isSome) with
  | none => throw "The joint replay contains no actual checkpoint installation."
  | some step =>
    have member := List.mem_of_find?_eq_some found
    match event : step.event with
    | .installCheckpoint executionNS =>
      match present : step.result.installation with
      | none => throw "The selected checkpoint operation has no installation result."
      | some installation =>
        let origin := installation_origin step executionNS event installation present
        let staging ← CampusTCPFacts.findStep report installation.checkpoint.time
        have actual := cached_stage report step member installation origin.cache staging
        match stageEvent : staging.step.event with
        | .stageCheckpoint =>
          finish report application step member executionNS event installation present staging stageEvent actual.1 actual.2
        | _ => throw "The cached checkpoint does not name an actual earlier staging operation."
    | _ => throw "The reported checkpoint result has a different operation."

theorem Assurance.ordered (value : Assurance report) :
    value.pause.step.before.time < value.step.before.time ∧
      value.staging.step.before.time < value.step.before.time ∧
      value.step.before.time < value.clientRoute.step.before.time ∧
      value.step.before.time < value.serverRoute.step.before.time ∧
      value.clientRoute.step.before.time < value.fence.step.before.time ∧
      value.serverRoute.step.before.time < value.fence.step.before.time ∧
      value.fence.step.before.time < value.resume.step.before.time := by
  have paused := value.pause.upper
  have staged := value.stageEarlier
  have client := value.clientRoute.lower
  have server := value.serverRoute.lower
  have fenced := value.fence.lower
  have resumed := value.resume.lower
  have first := Nat.le_max_left value.clientRoute.step.before.time value.serverRoute.step.before.time
  have second := Nat.le_max_right value.clientRoute.step.before.time value.serverRoute.step.before.time
  omega

theorem Assurance.capture_exact (value : Assurance report) :
    value.installation.checkpoint.snapshot.source = value.staging.step.before.primary.transport ∧
      value.installation.checkpoint.snapshot.cut = value.staging.step.before.primary.history.length ∧
      HEq value.installation.checkpoint.snapshot.history value.staging.step.before.primary.history :=
  TCP.Checkpoint.capture_source _ _ value.captured

theorem Assurance.application_prefix (value : Assurance report) :
    value.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written :=
  value.application.application_prefix

end Netlib.Check.CampusTCPTransferFacts
