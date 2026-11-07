import Netlib.Check.CampusTCPRecoveryStartupReceiveIndex
import Netlib.Check.CampusTCPStartupOutputJob

/-!
# Actual campus expiry of a due startup timer

The retry keeps its original control and receives a new event stamp.
The real endpoint output creates a fresh ingress job.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupTimeoutEnabled

open Protocol.TCP CampusTCPModel

namespace J
export CampusTCPStartupJobs (Source Job inventory)
end J

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : C.State input.active input.passive} {actor : Actor}
variable {flight : HandshakeTimer.Flight} {generation : Nat}

private theorem run_output (control : C.Step input.active input.passive)
    (connected : before.connection = .recovering control.before) (stamp : control.index = before.time)
    (emitted : control.result.output = some occurrence) :
    ∃ effect, runRecovery input before control.event = .ok effect ∧
      effect.recovery = some control ∧ effect.supported = true ∧ effect.passed = true ∧
      effect.output = some (.recovery control occurrence emitted) ∧
      effect.state.connection = .recovering control.result.state ∧ effect.state.work = before.work ∧
      effect.service = none ∧ effect.receipt = none ∧
      effect.application = control.result.application.map (fun pair => (Actor.ofRecovery pair.1, pair.2)) := by
  cases control with
  | mk state index event result computed =>
    dsimp only at connected stamp emitted ⊢
    subst index
    simp only [runRecovery, connected]
    split
    · rename_i reason failed
      rw [computed] at failed
      cases failed
    · rename_i actual actualAt
      have same : actual = result := Except.ok.inj (actualAt.symm.trans computed)
      subst actual
      cases result with
      | mk state decision output receipt application =>
        cases output with
        | none => cases emitted
        | some selected =>
          have same : selected = occurrence := Option.some.inj emitted
          subst occurrence
          exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure Timeout (report : Report input events) (current : C.State input.active input.passive)
    (actor : Actor) (generation : Nat) (flight : HandshakeTimer.Flight) (actual : Step input) where
  before : actual.before = report.final
  event : actual.event = .startupTimeout actor generation true
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  pending : (current.timer actor.recoverySide).status = .pending flight
  generationEq : generation = flight.retries
  due : flight.deadline ≤ (current.timer actor.recoverySide).now
  control : C.Step input.active input.passive
  controlBefore : control.before = current
  controlIndex : control.index = report.final.time
  controlEvent : control.event = .timeout actor.recoverySide generation true
  recorded : actual.result.recovery = some control
  accepted : control.result.decision = .accepted
  original : C.Emission
  selected : current.source flight.source = some original
  originalIndex : original.index = flight.source
  originalActor : original.actor = actor.recoverySide
  originalKind : original.kind = (match actor.recoverySide with | .active => .syn | .passive => .synAck)
  originalEarlier : original.index < report.final.time
  occurrence : C.Emission
  emitted : control.result.output = some occurrence
  produced : actual.result.output = some (.recovery control occurrence emitted)
  occurrenceIndex : occurrence.index = report.final.time
  occurrenceActor : occurrence.actor = actor.recoverySide
  occurrenceKind : occurrence.kind = original.kind
  packet : occurrence.packet = original.packet
  cause : occurrence.cause = .timeout original.index generation
  timer : HandshakeTimer.State
  expired : HandshakeTimer.expire (current.timer actor.recoverySide) generation = .ok timer
  phase : control.result.state.phase = current.phase
  selectedTimer : control.result.state.timer actor.recoverySide = timer
  peerTimer : control.result.state.timer actor.recoverySide.other = current.timer actor.recoverySide.other
  controlReceipt : control.result.receipt = none
  controlApplication : control.result.application = none
  connection : actual.result.state.connection = .recovering control.result.state
  work : actual.result.state.work = report.final.work
  service : actual.result.service = none
  receipt : actual.result.receipt = none
  application : actual.result.application = none
  job : J.Job input
  jobMember : job ∈ J.inventory actual.result.state
  jobIndex : job.outputIndex = report.final.outputs.length
  jobSource : job.source = ⟨control, occurrence, emitted⟩
  jobStage : job.stage = .ingress

theorem timeout_current (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (pending : (current.timer actor.recoverySide).status = .pending flight)
    (generationEq : generation = flight.retries)
    (due : flight.deadline ≤ (current.timer actor.recoverySide).now) :
    ∃ actual, Nonempty (Timeout report current actor generation flight actual) := by
  let reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected
  have ordered := CampusTCPRecoveryStartupReceiveIndex.Report.receive_index report connected
  obtain ⟨result, original, occurrence, computed, selected, originalIndex, originalActor, originalKind,
      emitted, occurrenceIndex, occurrenceActor, occurrenceKind, packet, cause⟩ :=
    TCPHandshakeRecovery.evaluate_timeout_enabled reachable.invariant.phase reachable.history.emissionOrder
      pending generationEq due ordered
  obtain ⟨timer, expired, phase, selectedTimer, peerTimer, accepted, controlReceipt, controlApplication⟩ :=
    TCPHandshakeRecovery.evaluate_timeout_effect pending generationEq computed
  let control : C.Step input.active input.passive :=
    ⟨current, report.final.time, .timeout actor.recoverySide generation true, result, computed⟩
  obtain ⟨core, runComputed, recorded, supported, passed, output, connection, work,
      service, receipt, application⟩ := run_output (before := report.final) control connected rfl emitted
  have coreComputed : processCore input report.final (.startupTimeout actor generation true) = .ok core := runComputed
  let effect : Effect input := { core with state := { core.state with
    custody := finishCustody report.final core report.final.custody, time := report.final.time + 1 } }
  have actualComputed : step input report.final (.startupTimeout actor generation true) = .ok effect := by
    simp only [step, process, coreComputed, prepareCustody, bind, Except.bind, pure, Except.pure]
    rfl
  let actual : Step input := ⟨report.final, .startupTimeout actor generation true, effect, actualComputed⟩
  let source : J.Source input := ⟨control, occurrence, emitted⟩
  have actualOutput : actual.result.output = some source.produced := output
  obtain ⟨job, jobMember, jobIndex, jobSource, jobStage⟩ :=
    CampusTCPStartupOutputJob.Step.output_job actual source actualOutput
  have originalEarlier := CampusTCPRecoveryStartupReceiveIndex.Report.recovery_emission_before report connected
    (List.mem_of_find?_eq_some selected)
  refine ⟨actual, ⟨⟨rfl, rfl, supported, passed, pending, generationEq, due, control, rfl, rfl, rfl, recorded, accepted,
    original, selected, originalIndex, originalActor, originalKind, originalEarlier, occurrence, emitted, output,
    occurrenceIndex, occurrenceActor, occurrenceKind, packet, cause, timer, expired, phase,
    selectedTimer, peerTimer, controlReceipt, controlApplication, connection, work, service,
    receipt, ?_, job, jobMember, jobIndex, jobSource, jobStage⟩⟩⟩
  change core.application = none
  rw [application]
  exact congrArg (Option.map (fun pair => (Actor.ofRecovery pair.1, pair.2))) controlApplication

theorem Timeout.backoff (value : Timeout report current actor generation flight actual) :
    value.timer.now = (current.timer actor.recoverySide).now ∧
      value.timer.rto = 2 * (current.timer actor.recoverySide).rto ∧
      value.timer.estimator = (current.timer actor.recoverySide).estimator ∧
      ((current.timer actor.recoverySide).rto < 3000 → value.timer.shortSynTimeout = true) :=
  HandshakeTimer.expire_fields value.expired

theorem Timeout.pending_after (value : Timeout report current actor generation flight actual) :
    value.timer.status = .pending { flight with
      lastAt := (current.timer actor.recoverySide).now,
      retries := flight.retries + 1,
      deadline := (current.timer actor.recoverySide).now + 2 * (current.timer actor.recoverySide).rto } := by
  obtain ⟨selected, status, _, _, after⟩ := HandshakeTimer.expire_eq value.expired
  have same : selected = flight := HandshakeTimer.Status.pending.inj (status.symm.trans value.pending)
  subst selected
  rw [after]

theorem Timeout.job_actor (value : Timeout report current actor generation flight actual) : value.job.actor = actor := by
  simp only [CampusTCPStartupJobs.Job.actor, value.jobSource, value.occurrenceActor]
  cases actor <;> rfl

theorem Timeout.job_kind (value : Timeout report current actor generation flight actual) :
    value.job.kind = (match actor.recoverySide with | .active => .syn | .passive => .synAck) := by
  simp only [CampusTCPStartupJobs.Job.kind, value.jobSource, value.occurrenceKind, value.originalKind]

def Timeout.on_step (value : Timeout report current actor generation flight actual) (supplied : Step input)
    (before : supplied.before = report.final) (event : supplied.event = .startupTimeout actor generation true) :
    Timeout report current actor generation flight supplied := by
  have computed := actual.computed
  rw [value.before.trans before.symm, value.event.trans event.symm, supplied.computed] at computed
  have result : actual.result = supplied.result := (Except.ok.inj computed).symm
  have beforeEq := value.before.trans before.symm
  have eventEq := value.event.trans event.symm
  have same : actual = supplied := by
    cases actual
    cases supplied
    simp_all only
  exact same ▸ value

end Netlib.Check.CampusTCPRecoveryStartupTimeoutEnabled
