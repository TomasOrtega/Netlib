import Netlib.Check.CampusTCPTransferEnabled
import Netlib.Check.CampusTCPTwoProgressGatewayAt

/-!
# Seven actual planned-transfer controls

Each current guard follows from the preceding stored control.
The sequence retains endpoint, packet, source, and policy history.
-/

namespace Netlib.Check.CampusTCPTransferSequence

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTransferEnabled

local notation "Event" => CampusTCPModel.Event

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {current : Cut input complete} {actual : Step input} {event : Event}

private theorem not_install_pause : ∀ ns, Event.pause ≠ .installCheckpoint ns := by intro ns impossible; cases impossible
private theorem not_install_stage : ∀ ns, Event.stageCheckpoint ≠ .installCheckpoint ns := by intro ns impossible; cases impossible
private theorem not_install_route (actor : Actor) : ∀ ns, Event.switchRoute actor .standby ≠ .installCheckpoint ns := by
  intro ns impossible; cases impossible
private theorem not_install_fence : ∀ ns, Event.fencePrimary ≠ .installCheckpoint ns := by intro ns impossible; cases impossible
private theorem not_install_resume : ∀ ns, Event.resume ≠ .installCheckpoint ns := by intro ns impossible; cases impossible

private theorem control_drained (value : Control current event actual) (drained : current.report.final.outstanding .primary = 0) :
    value.move.after.report.final.outstanding .primary = 0 := by
  simpa only [State.outstanding, value.frame.work] using drained

private theorem consistent_after (value : Control current event actual) (noninstall : ∀ ns, event ≠ .installCheckpoint ns)
    (consistent : ∃ installed, current.report.final.installation = some installed ∧
      current.report.final.primary.transport = installed.checkpoint.snapshot.source ∧
      current.report.final.standby.transport = installed.installed.state) :
    ∃ installed, value.move.after.report.final.installation = some installed ∧
      value.move.after.report.final.primary.transport = installed.checkpoint.snapshot.source ∧
      value.move.after.report.final.standby.transport = installed.installed.state := by
  obtain ⟨installed, stored, source, target⟩ := consistent
  exact ⟨installed, (value.frame.installation noninstall).trans stored,
    (congrArg Local.transport value.frame.primary).trans source,
    (congrArg Local.transport (value.frame.standby noninstall)).trans target⟩

private theorem stage_ready (ready : Ready current.report.final) (value : Control current .pause actual) :
    StageReady value.move.after.report.final := {
  configured := ready.configured
  unsealed := value.frame.sealed.trans ready.unsealed
  unfenced := value.frame.fenced.trans ready.unfenced
  capture := by rw [value.frame.primary]; exact ready.capture }

private theorem stage_capture (value : Control current .stageCheckpoint actual) (checkpoint : CachedCheckpoint)
    (present : actual.result.checkpoint = some checkpoint) :
    Checkpoint.capture current.report.final.primary.history = .ok checkpoint.snapshot := by
  have captured := (CampusTCPTransferFacts.checkpoint_origin actual value.eventEq checkpoint present).1
  rw [value.move.beforeEq] at captured
  exact captured

private theorem install_ready (ready : Ready current.report.final) (pause : Step input) (paused : Control current .pause pause)
    (stage : Step input) (staged : Control paused.move.after .stageCheckpoint stage) (checkpoint : CachedCheckpoint)
    (present : stage.result.checkpoint = some checkpoint) : InstallReady staged.move.after.report.final := by
  have standby := (staged.frame.standby not_install_stage).trans (paused.frame.standby not_install_pause)
  have captured := stage_capture staged checkpoint present
  have fields := Checkpoint.capture_source _ _ captured
  have stored := (CampusTCPTransferFacts.checkpoint_origin stage staged.eventEq checkpoint present).2.2.2.2.2.1
  rw [← staged.move.final] at stored
  exact {
    configured := ready.configured
    paused := staged.frame.paused.trans paused.frame.paused
    unsealed := staged.frame.sealed.trans (paused.frame.sealed.trans ready.unsealed)
    unfenced := staged.frame.fenced.trans (paused.frame.fenced.trans ready.unfenced)
    drained := control_drained staged (control_drained paused ready.drained)
    namespaceEq := by rw [standby]; exact ready.namespaceEq
    empty := by rw [standby]; exact ready.empty
    fresh := ⟨checkpoint, stored, by rw [staged.frame.primary]; exact fields.1.symm,
      by rw [staged.frame.primary]; exact fields.2.1.symm⟩ }

private theorem route_ready (ready : InstallReady current.report.final)
    (value : Control current (.installCheckpoint (input.deployment .standby).executionNS) actual)
    (installed : InstalledCheckpoint) (present : actual.result.installation = some installed) :
    RouteReady value.move.after.report.final := by
  have origin := CampusTCPTransferFacts.installation_origin actual _ value.eventEq installed present
  exact {
    configured := ready.configured
    paused := value.frame.paused.trans ready.paused
    sealed := value.frame.sealed
    consistent := ⟨installed, by rw [value.move.final]; exact origin.stored,
      by rw [value.frame.primary, ← value.move.beforeEq]; exact origin.cut,
      by rw [value.move.final]; exact origin.copied.trans installed.installed.copied.symm⟩ }

private theorem route_preserved (ready : RouteReady current.report.final)
    (value : Control current (.switchRoute actor .standby) actual) : RouteReady value.move.after.report.final := {
  configured := ready.configured
  paused := value.frame.paused.trans ready.paused
  sealed := value.frame.sealed.trans ready.sealed
  consistent := consistent_after value (not_install_route actor) ready.consistent }

private theorem resume_ready (ready : RouteReady current.report.final)
    (value : Control current .fencePrimary actual) (client : current.report.final.owners.client = .standby)
    (server : current.report.final.owners.server = .standby) : ResumeReady value.move.after.report.final := {
  configured := ready.configured
  paused := value.frame.paused.trans ready.paused
  fenced := value.frame.fenced
  client := by rw [value.frame.owners]; exact client
  server := by rw [value.frame.owners]; exact server
  consistent := consistent_after value not_install_fence ready.consistent }

structure Seven (current : Cut input complete) where
  pause : Step input
  paused : Control current .pause pause
  stage : Step input
  staged : Control paused.move.after .stageCheckpoint stage
  checkpoint : CachedCheckpoint
  captured : stage.result.checkpoint = some checkpoint
  install : Step input
  installed : Control staged.move.after (.installCheckpoint (input.deployment .standby).executionNS) install
  installation : InstalledCheckpoint
  copied : install.result.installation = some installation
  clientRoute : Step input
  clientRouted : Control installed.move.after (.switchRoute .client .standby) clientRoute
  serverRoute : Step input
  serverRouted : Control clientRouted.move.after (.switchRoute .server .standby) serverRoute
  fence : Step input
  fenced : Control serverRouted.move.after .fencePrimary fence
  resume : Step input
  resumed : Control fenced.move.after .resume resume

theorem of_ready (ready : Ready current.report.final) : Nonempty (Seven current) := by
  obtain ⟨pause, ⟨paused⟩⟩ := pause_at ready.toPauseReady
  obtain ⟨stage, checkpoint, ⟨staged⟩, captured⟩ := stage_at (stage_ready ready paused)
  have installReady := install_ready ready pause paused stage staged checkpoint captured
  obtain ⟨install, installation, ⟨installed⟩, copied⟩ := install_at installReady
  have routeReady := route_ready installReady installed installation copied
  obtain ⟨clientRoute, ⟨clientRouted⟩⟩ := route_at routeReady .client
  have clientReady := route_preserved routeReady clientRouted
  obtain ⟨serverRoute, ⟨serverRouted⟩⟩ := route_at clientReady .server
  have serverReady := route_preserved clientReady serverRouted
  have client : serverRouted.move.after.report.final.owners.client = .standby := by
    rw [serverRouted.frame.owners]
    change clientRouted.move.after.report.final.owners.client = .standby
    rw [clientRouted.frame.owners]
    rfl
  have server : serverRouted.move.after.report.final.owners.server = .standby := by rw [serverRouted.frame.owners]; rfl
  have fenceReady : FenceReady serverRouted.move.after.report.final := {
    configured := ready.configured, paused := serverReady.paused, sealed := serverReady.sealed
    installed := by obtain ⟨installation, stored, _, _⟩ := serverReady.consistent; rw [stored]; rfl
    client, server
    drained := control_drained serverRouted (control_drained clientRouted
      (control_drained installed installReady.drained)) }
  obtain ⟨fence, ⟨fenced⟩⟩ := fence_at fenceReady
  obtain ⟨resume, ⟨resumed⟩⟩ := resume_at (resume_ready serverReady fenced client server)
  exact ⟨⟨pause, paused, stage, staged, checkpoint, captured, install, installed, installation, copied,
    clientRoute, clientRouted, serverRoute, serverRouted, fence, fenced, resume, resumed⟩⟩

def Seven.final (value : Seven current) : Cut input complete := value.resumed.move.after

def Seven.steps (value : Seven current) : List (Step input) :=
  [value.pause, value.stage, value.install, value.clientRoute, value.serverRoute, value.fence, value.resume]

theorem Seven.length (value : Seven current) : value.steps.length = 7 := rfl

theorem Seven.events (value : Seven current) : value.steps.map (·.event) =
    [.pause, .stageCheckpoint, .installCheckpoint (input.deployment .standby).executionNS,
      .switchRoute .client .standby, .switchRoute .server .standby, .fencePrimary, .resume] := by
  simp only [Seven.steps, List.map_cons, List.map_nil, value.paused.eventEq, value.staged.eventEq,
    value.installed.eventEq, value.clientRouted.eventEq, value.serverRouted.eventEq, value.fenced.eventEq, value.resumed.eventEq]

theorem Seven.first (value : Seven current) : value.steps[0]? = some value.pause := rfl
theorem Seven.last (value : Seven current) : value.steps[6]? = some value.resume := rfl

theorem Seven.history (value : Seven current) : value.final.report.steps = current.report.steps ++ value.steps := by
  rw [Seven.final, value.resumed.move.history, value.fenced.move.history, value.serverRouted.move.history,
    value.clientRouted.move.history, value.installed.move.history, value.staged.move.history, value.paused.move.history]
  simp only [Seven.steps, List.append_assoc, List.cons_append, List.nil_append]

theorem Seven.retained (value : Seven current) : current.report.steps <+: value.final.report.steps := by
  rw [value.history]
  exact List.prefix_append _ _

theorem Seven.member (value : Seven current) (step : Step input) (member : step ∈ value.steps) : step ∈ value.final.report.steps := by
  rw [value.history]
  exact List.mem_append_right _ member

private theorem control_cons (value : Control current event actual)
    (tail : Trace input value.move.after.report.final events steps final []) :
    Trace input current.report.final (actual.event :: events) (actual :: steps) final [] := by
  rw [← value.move.beforeEq]
  exact .next actual value.move.supported (by rw [← value.move.final]; exact tail)

theorem Seven.trace (value : Seven current) :
    Trace input current.report.final (value.steps.map (·.event)) value.steps value.final.report.final [] :=
  control_cons value.paused (control_cons value.staged (control_cons value.installed (control_cons value.clientRouted
    (control_cons value.serverRouted (control_cons value.fenced (control_cons value.resumed (.done _)))))))

theorem Seven.endpoints (value : Seven current) : value.final.endpoints = current.endpoints :=
  value.resumed.endpoints.trans (value.fenced.endpoints.trans (value.serverRouted.endpoints.trans
    (value.clientRouted.endpoints.trans (value.installed.endpoints.trans (value.staged.endpoints.trans value.paused.endpoints)))))

theorem Seven.final_unpaused (value : Seven current) : value.final.report.final.assignmentPaused = false := value.resumed.frame.paused

theorem Seven.final_sealed (value : Seven current) : value.final.report.final.primarySealed = true :=
  value.resumed.frame.sealed.trans (value.fenced.frame.sealed.trans (value.serverRouted.frame.sealed.trans
    (value.clientRouted.frame.sealed.trans value.installed.frame.sealed)))

theorem Seven.final_fenced (value : Seven current) : value.final.report.final.primaryFenced = true :=
  value.resumed.frame.fenced.trans value.fenced.frame.fenced

theorem Seven.owners (value : Seven current) : value.final.report.final.owners.client = .standby ∧
    value.final.report.final.owners.server = .standby := by
  change value.resumed.move.after.report.final.owners.client = .standby ∧
    value.resumed.move.after.report.final.owners.server = .standby
  rw [value.resumed.frame.owners]
  change value.fenced.move.after.report.final.owners.client = .standby ∧ value.fenced.move.after.report.final.owners.server = .standby
  rw [value.fenced.frame.owners]
  change value.serverRouted.move.after.report.final.owners.client = .standby ∧ value.serverRouted.move.after.report.final.owners.server = .standby
  rw [value.serverRouted.frame.owners]
  change value.clientRouted.move.after.report.final.owners.client = .standby ∧
    StatefulFailover.Gateway.standby = .standby
  rw [value.clientRouted.frame.owners]
  exact ⟨rfl, rfl⟩

structure Stable (before after : State input) : Prop where
  connection : after.connection = before.connection
  authentication : after.authentication = before.authentication
  work : after.work = before.work
  custody : after.custody = before.custody
  outputs : after.outputs = before.outputs
  services : after.services = before.services
  receipts : after.receipts = before.receipts
  primary : after.primary = before.primary
  policy : ∀ gateway, (beforeService input after gateway).environment = (beforeService input before gateway).environment

private theorem control_stable (value : Control current event actual) : Stable current.report.final value.move.after.report.final := {
  connection := value.frame.connection, authentication := value.frame.authentication, work := value.frame.work
  custody := value.frame.custody, outputs := value.frame.outputs, services := value.frame.services
  receipts := value.frame.receipts, primary := value.frame.primary, policy := value.frame.policy }

theorem Stable.trans (first : Stable before middle) (second : Stable middle after) : Stable before after := {
  connection := second.connection.trans first.connection
  authentication := second.authentication.trans first.authentication
  work := second.work.trans first.work
  custody := second.custody.trans first.custody
  outputs := second.outputs.trans first.outputs
  services := second.services.trans first.services
  receipts := second.receipts.trans first.receipts
  primary := second.primary.trans first.primary
  policy := fun gateway => (second.policy gateway).trans (first.policy gateway) }

theorem Seven.stable (value : Seven current) : Stable current.report.final value.final.report.final :=
  (control_stable value.paused).trans ((control_stable value.staged).trans ((control_stable value.installed).trans
    ((control_stable value.clientRouted).trans ((control_stable value.serverRouted).trans
      ((control_stable value.fenced).trans (control_stable value.resumed))))))

theorem Seven.primary (value : Seven current) : value.final.report.final.primary.transport = current.report.final.primary.transport :=
  congrArg Local.transport value.stable.primary

theorem Seven.policy (value : Seven current) (gateway : StatefulFailover.Gateway) :
    (beforeService input value.final.report.final gateway).environment = (beforeService input current.report.final gateway).environment :=
  value.stable.policy gateway

theorem Seven.work (value : Seven current) : value.final.report.final.work = current.report.final.work := value.stable.work
theorem Seven.custody (value : Seven current) : value.final.report.final.custody = current.report.final.custody := value.stable.custody
theorem Seven.outputs (value : Seven current) : value.final.report.final.outputs = current.report.final.outputs := value.stable.outputs
theorem Seven.services (value : Seven current) : value.final.report.final.services = current.report.final.services := value.stable.services
theorem Seven.receipts (value : Seven current) : value.final.report.final.receipts = current.report.final.receipts := value.stable.receipts

private theorem control_time (value : Control current event actual) :
    value.move.after.report.final.time = current.report.final.time + 1 :=
  (congrArg State.time value.move.final).trans (actual.clock.trans (congrArg (· + 1) (congrArg State.time value.move.beforeEq)))

theorem Seven.time (value : Seven current) : value.final.report.final.time = current.report.final.time + 7 := by
  have first := control_time value.paused
  have second := control_time value.staged
  have third := control_time value.installed
  have fourth := control_time value.clientRouted
  have fifth := control_time value.serverRouted
  have sixth := control_time value.fenced
  have seventh := control_time value.resumed
  change value.resumed.move.after.report.final.time = _
  omega

theorem Seven.origin (value : Seven current) : CampusTCPTransferFacts.InstallationOrigin value.install
    (input.deployment .standby).executionNS value.installation :=
  CampusTCPTransferFacts.installation_origin value.install _ value.installed.eventEq value.installation value.copied

theorem Seven.final_drained (value : Seven current) : value.final.report.final.outstanding .primary = 0 := by
  have drained := value.origin.drained
  rw [value.installed.move.beforeEq] at drained
  exact control_drained value.resumed (control_drained value.fenced (control_drained value.serverRouted
    (control_drained value.clientRouted (control_drained value.installed drained))))

theorem Seven.checkpoint_matches (value : Seven current) : value.installation.checkpoint = value.checkpoint := by
  have cached := value.origin.cache
  rw [value.installed.move.beforeEq] at cached
  have stored := (CampusTCPTransferFacts.checkpoint_origin value.stage value.staged.eventEq value.checkpoint value.captured).2.2.2.2.2.1
  rw [← value.staged.move.final] at stored
  exact Option.some.inj (cached.symm.trans stored)

theorem Seven.final_installation (value : Seven current) : value.final.report.final.installation = some value.installation := by
  change value.resumed.move.after.report.final.installation = _
  rw [value.resumed.frame.installation not_install_resume, value.fenced.frame.installation not_install_fence,
    value.serverRouted.frame.installation (not_install_route .server), value.clientRouted.frame.installation (not_install_route .client),
    value.installed.move.final]
  exact value.origin.stored

theorem Seven.actual_capture (value : Seven current) :
    Checkpoint.capture current.report.final.primary.history = .ok value.checkpoint.snapshot := by
  have captured := stage_capture value.staged value.checkpoint value.captured
  rw [value.paused.frame.primary] at captured
  exact captured

theorem Seven.snapshot_source (value : Seven current) : value.checkpoint.snapshot.source = current.report.final.primary.transport :=
  (Checkpoint.capture_source _ _ value.actual_capture).1

theorem Seven.snapshot_cut (value : Seven current) : value.checkpoint.snapshot.cut = current.report.final.primary.history.length :=
  (Checkpoint.capture_source _ _ value.actual_capture).2.1

theorem Seven.snapshot_history (value : Seven current) : HEq value.checkpoint.snapshot.history current.report.final.primary.history :=
  (Checkpoint.capture_source _ _ value.actual_capture).2.2

private theorem target_frame (value : Seven current) : value.final.report.final.standby = value.installed.move.after.report.final.standby :=
  (value.resumed.frame.standby not_install_resume).trans ((value.fenced.frame.standby not_install_fence).trans
    ((value.serverRouted.frame.standby (not_install_route .server)).trans (value.clientRouted.frame.standby (not_install_route .client))))

theorem Seven.target (value : Seven current) : value.final.report.final.standby.transport = current.report.final.primary.transport := by
  rw [target_frame, value.installed.move.final]
  exact value.origin.copied.trans ((congrArg (fun checkpoint => checkpoint.snapshot.source) value.checkpoint_matches).trans value.snapshot_source)

private theorem local_history_congr {before after : Local} (same : before = after) : HEq before.history after.history := by
  cases same
  rfl

theorem Seven.target_history (value : Seven current) :
    HEq value.final.report.final.standby.history value.checkpoint.snapshot.history := by
  have copied := CampusTCPTwoProgressGatewayAt.install_history value.installed.move _ value.installed.eventEq value.installation value.copied
  rw [value.checkpoint_matches] at copied
  exact (local_history_congr (target_frame value)).trans copied

theorem Seven.target_original_history (value : Seven current) :
    HEq value.final.report.final.standby.history current.report.final.primary.history :=
  value.target_history.trans value.snapshot_history

structure PausedReady (state : State input) : Prop extends StageReady state where
  paused : state.assignmentPaused = true
  drained : state.outstanding .primary = 0
  namespaceEq : state.standby.guard.source.ns = (input.deployment .standby).executionNS
  empty : state.standby.transport = Checkpoint.Gateway.initial

private theorem paused_install_ready (ready : PausedReady current.report.final)
    (staged : Control current .stageCheckpoint actual) (checkpoint : CachedCheckpoint)
    (present : actual.result.checkpoint = some checkpoint) : InstallReady staged.move.after.report.final := by
  have standby := staged.frame.standby not_install_stage
  have fields := Checkpoint.capture_source _ _ (stage_capture staged checkpoint present)
  have stored := (CampusTCPTransferFacts.checkpoint_origin actual staged.eventEq checkpoint present).2.2.2.2.2.1
  rw [← staged.move.final] at stored
  exact {
    configured := ready.configured
    paused := staged.frame.paused.trans ready.paused
    unsealed := staged.frame.sealed.trans ready.unsealed
    unfenced := staged.frame.fenced.trans ready.unfenced
    drained := control_drained staged ready.drained
    namespaceEq := by rw [standby]; exact ready.namespaceEq
    empty := by rw [standby]; exact ready.empty
    fresh := ⟨checkpoint, stored, by rw [staged.frame.primary]; exact fields.1.symm,
      by rw [staged.frame.primary]; exact fields.2.1.symm⟩ }

structure Six (current : Cut input complete) where
  stage : Step input
  staged : Control current .stageCheckpoint stage
  checkpoint : CachedCheckpoint
  captured : stage.result.checkpoint = some checkpoint
  install : Step input
  installed : Control staged.move.after (.installCheckpoint (input.deployment .standby).executionNS) install
  installation : InstalledCheckpoint
  copied : install.result.installation = some installation
  clientRoute : Step input
  clientRouted : Control installed.move.after (.switchRoute .client .standby) clientRoute
  serverRoute : Step input
  serverRouted : Control clientRouted.move.after (.switchRoute .server .standby) serverRoute
  fence : Step input
  fenced : Control serverRouted.move.after .fencePrimary fence
  resume : Step input
  resumed : Control fenced.move.after .resume resume

theorem of_paused_ready (ready : PausedReady current.report.final) : Nonempty (Six current) := by
  obtain ⟨stage, checkpoint, ⟨staged⟩, captured⟩ := stage_at ready.toStageReady
  have installReady := paused_install_ready ready staged checkpoint captured
  obtain ⟨install, installation, ⟨installed⟩, copied⟩ := install_at installReady
  have routeReady := route_ready installReady installed installation copied
  obtain ⟨clientRoute, ⟨clientRouted⟩⟩ := route_at routeReady .client
  have clientReady := route_preserved routeReady clientRouted
  obtain ⟨serverRoute, ⟨serverRouted⟩⟩ := route_at clientReady .server
  have serverReady := route_preserved clientReady serverRouted
  have client : serverRouted.move.after.report.final.owners.client = .standby := by
    rw [serverRouted.frame.owners]
    change clientRouted.move.after.report.final.owners.client = .standby
    rw [clientRouted.frame.owners]
    rfl
  have server : serverRouted.move.after.report.final.owners.server = .standby := by rw [serverRouted.frame.owners]; rfl
  have fenceReady : FenceReady serverRouted.move.after.report.final := {
    configured := ready.configured, paused := serverReady.paused, sealed := serverReady.sealed
    installed := by obtain ⟨installation, stored, _, _⟩ := serverReady.consistent; rw [stored]; rfl
    client, server
    drained := control_drained serverRouted (control_drained clientRouted
      (control_drained installed installReady.drained)) }
  obtain ⟨fence, ⟨fenced⟩⟩ := fence_at fenceReady
  obtain ⟨resume, ⟨resumed⟩⟩ := resume_at (resume_ready serverReady fenced client server)
  exact ⟨⟨stage, staged, checkpoint, captured, install, installed, installation, copied,
    clientRoute, clientRouted, serverRoute, serverRouted, fence, fenced, resume, resumed⟩⟩

def Six.final (value : Six current) : Cut input complete := value.resumed.move.after

def Six.steps (value : Six current) : List (Step input) :=
  [value.stage, value.install, value.clientRoute, value.serverRoute, value.fence, value.resume]

theorem Six.length (value : Six current) : value.steps.length = 6 := rfl

theorem Six.events (value : Six current) : value.steps.map (·.event) =
    [.stageCheckpoint, .installCheckpoint (input.deployment .standby).executionNS,
      .switchRoute .client .standby, .switchRoute .server .standby, .fencePrimary, .resume] := by
  simp only [Six.steps, List.map_cons, List.map_nil, value.staged.eventEq, value.installed.eventEq,
    value.clientRouted.eventEq, value.serverRouted.eventEq, value.fenced.eventEq, value.resumed.eventEq]

theorem Six.first (value : Six current) : value.steps[0]? = some value.stage := rfl
theorem Six.last (value : Six current) : value.steps[5]? = some value.resume := rfl

theorem Six.history (value : Six current) : value.final.report.steps = current.report.steps ++ value.steps := by
  rw [Six.final, value.resumed.move.history, value.fenced.move.history, value.serverRouted.move.history,
    value.clientRouted.move.history, value.installed.move.history, value.staged.move.history]
  simp only [Six.steps, List.append_assoc, List.cons_append, List.nil_append]

theorem Six.retained (value : Six current) : current.report.steps <+: value.final.report.steps := by
  rw [value.history]
  exact List.prefix_append _ _

theorem Six.member (value : Six current) (step : Step input) (member : step ∈ value.steps) : step ∈ value.final.report.steps := by
  rw [value.history]
  exact List.mem_append_right _ member

theorem Six.trace (value : Six current) :
    Trace input current.report.final (value.steps.map (·.event)) value.steps value.final.report.final [] :=
  control_cons value.staged (control_cons value.installed (control_cons value.clientRouted
    (control_cons value.serverRouted (control_cons value.fenced (control_cons value.resumed (.done _))))))

theorem Six.endpoints (value : Six current) : value.final.endpoints = current.endpoints :=
  value.resumed.endpoints.trans (value.fenced.endpoints.trans (value.serverRouted.endpoints.trans
    (value.clientRouted.endpoints.trans (value.installed.endpoints.trans value.staged.endpoints))))

theorem Six.final_unpaused (value : Six current) : value.final.report.final.assignmentPaused = false := value.resumed.frame.paused

theorem Six.final_sealed (value : Six current) : value.final.report.final.primarySealed = true :=
  value.resumed.frame.sealed.trans (value.fenced.frame.sealed.trans (value.serverRouted.frame.sealed.trans
    (value.clientRouted.frame.sealed.trans value.installed.frame.sealed)))

theorem Six.final_fenced (value : Six current) : value.final.report.final.primaryFenced = true :=
  value.resumed.frame.fenced.trans value.fenced.frame.fenced

theorem Six.owners (value : Six current) : value.final.report.final.owners.client = .standby ∧
    value.final.report.final.owners.server = .standby := by
  change value.resumed.move.after.report.final.owners.client = .standby ∧
    value.resumed.move.after.report.final.owners.server = .standby
  rw [value.resumed.frame.owners]
  change value.fenced.move.after.report.final.owners.client = .standby ∧ value.fenced.move.after.report.final.owners.server = .standby
  rw [value.fenced.frame.owners]
  change value.serverRouted.move.after.report.final.owners.client = .standby ∧ value.serverRouted.move.after.report.final.owners.server = .standby
  rw [value.serverRouted.frame.owners]
  change value.clientRouted.move.after.report.final.owners.client = .standby ∧ StatefulFailover.Gateway.standby = .standby
  rw [value.clientRouted.frame.owners]
  exact ⟨rfl, rfl⟩

theorem Six.stable (value : Six current) : Stable current.report.final value.final.report.final :=
  (control_stable value.staged).trans ((control_stable value.installed).trans
    ((control_stable value.clientRouted).trans ((control_stable value.serverRouted).trans
      ((control_stable value.fenced).trans (control_stable value.resumed)))))

theorem Six.primary (value : Six current) : value.final.report.final.primary.transport = current.report.final.primary.transport :=
  congrArg Local.transport value.stable.primary

theorem Six.policy (value : Six current) (gateway : StatefulFailover.Gateway) :
    (beforeService input value.final.report.final gateway).environment = (beforeService input current.report.final gateway).environment :=
  value.stable.policy gateway

theorem Six.work (value : Six current) : value.final.report.final.work = current.report.final.work := value.stable.work
theorem Six.custody (value : Six current) : value.final.report.final.custody = current.report.final.custody := value.stable.custody
theorem Six.outputs (value : Six current) : value.final.report.final.outputs = current.report.final.outputs := value.stable.outputs
theorem Six.services (value : Six current) : value.final.report.final.services = current.report.final.services := value.stable.services
theorem Six.receipts (value : Six current) : value.final.report.final.receipts = current.report.final.receipts := value.stable.receipts

theorem Six.time (value : Six current) : value.final.report.final.time = current.report.final.time + 6 := by
  have first := control_time value.staged
  have second := control_time value.installed
  have third := control_time value.clientRouted
  have fourth := control_time value.serverRouted
  have fifth := control_time value.fenced
  have sixth := control_time value.resumed
  change value.resumed.move.after.report.final.time = _
  omega

theorem Six.origin (value : Six current) : CampusTCPTransferFacts.InstallationOrigin value.install
    (input.deployment .standby).executionNS value.installation :=
  CampusTCPTransferFacts.installation_origin value.install _ value.installed.eventEq value.installation value.copied

theorem Six.final_drained (value : Six current) : value.final.report.final.outstanding .primary = 0 := by
  have drained := value.origin.drained
  rw [value.installed.move.beforeEq] at drained
  exact control_drained value.resumed (control_drained value.fenced (control_drained value.serverRouted
    (control_drained value.clientRouted (control_drained value.installed drained))))

theorem Six.checkpoint_matches (value : Six current) : value.installation.checkpoint = value.checkpoint := by
  have cached := value.origin.cache
  rw [value.installed.move.beforeEq] at cached
  have stored := (CampusTCPTransferFacts.checkpoint_origin value.stage value.staged.eventEq value.checkpoint value.captured).2.2.2.2.2.1
  rw [← value.staged.move.final] at stored
  exact Option.some.inj (cached.symm.trans stored)

theorem Six.final_installation (value : Six current) : value.final.report.final.installation = some value.installation := by
  change value.resumed.move.after.report.final.installation = _
  rw [value.resumed.frame.installation not_install_resume, value.fenced.frame.installation not_install_fence,
    value.serverRouted.frame.installation (not_install_route .server), value.clientRouted.frame.installation (not_install_route .client),
    value.installed.move.final]
  exact value.origin.stored

theorem Six.actual_capture (value : Six current) :
    Checkpoint.capture current.report.final.primary.history = .ok value.checkpoint.snapshot :=
  stage_capture value.staged value.checkpoint value.captured

theorem Six.snapshot_source (value : Six current) : value.checkpoint.snapshot.source = current.report.final.primary.transport :=
  (Checkpoint.capture_source _ _ value.actual_capture).1

theorem Six.snapshot_cut (value : Six current) : value.checkpoint.snapshot.cut = current.report.final.primary.history.length :=
  (Checkpoint.capture_source _ _ value.actual_capture).2.1

theorem Six.snapshot_history (value : Six current) : HEq value.checkpoint.snapshot.history current.report.final.primary.history :=
  (Checkpoint.capture_source _ _ value.actual_capture).2.2

private theorem six_target_frame (value : Six current) : value.final.report.final.standby = value.installed.move.after.report.final.standby :=
  (value.resumed.frame.standby not_install_resume).trans ((value.fenced.frame.standby not_install_fence).trans
    ((value.serverRouted.frame.standby (not_install_route .server)).trans (value.clientRouted.frame.standby (not_install_route .client))))

theorem Six.target (value : Six current) : value.final.report.final.standby.transport = current.report.final.primary.transport := by
  rw [six_target_frame, value.installed.move.final]
  exact value.origin.copied.trans ((congrArg (fun checkpoint => checkpoint.snapshot.source) value.checkpoint_matches).trans value.snapshot_source)

theorem Six.target_history (value : Six current) :
    HEq value.final.report.final.standby.history value.checkpoint.snapshot.history := by
  have copied := CampusTCPTwoProgressGatewayAt.install_history value.installed.move _ value.installed.eventEq value.installation value.copied
  rw [value.checkpoint_matches] at copied
  exact (local_history_congr (six_target_frame value)).trans copied

theorem Six.target_original_history (value : Six current) :
    HEq value.final.report.final.standby.history current.report.final.primary.history :=
  value.target_history.trans value.snapshot_history

end Netlib.Check.CampusTCPTransferSequence
