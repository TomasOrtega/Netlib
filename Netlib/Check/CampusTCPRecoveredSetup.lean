import Netlib.Check.CampusTCPRecoveryStartupOrigins
import Netlib.Check.TCPHandshakeRecoveryInvariant
import Netlib.Check.TCPHandshakeRecoveryApplicationHistory
import Netlib.Check.CampusTCPEnabled
import Netlib.Check.CampusTCPChronology
import Netlib.Check.CampusTCPSchedule

/-!
# Setup from an actual recovery drain

Drain keeps the current endpoint cursors and their checked ACK operations.
The guards close every startup ticket and packet in the same report.
-/

namespace Netlib.Check.CampusTCPRecoveredSetup

open Protocol.TCP CampusTCPModel CampusTCPEnabled
namespace R
export TCPHandshakeRecovery (PreData PreDataClean)
end R

variable {input : Input} {events : List Event} {report : Report input events}

def EarlyPrefix (drained : Nat) (steps : List T.Step) : Prop :=
  ∀ actual ∈ steps, ∃ packet, actual.event = .receive packet ∧ Handshake.Profile packet 16 ∧
    actual.stamp < drained ∧ actual.result.decision = .accepted (.receive 0 0) ∧
    actual.result.output = none ∧ actual.result.read = []

theorem EarlyPrefix.before (early : EarlyPrefix drained current.steps) :
    (Cursor.ofPreData current).beforeRecoveryTransport drained = true := by
  apply List.all_eq_true.mpr
  intro actual member
  obtain ⟨packet, event, profile, earlier, accepted, quiet, read⟩ := early actual member
  simp only [event, earlier, profile, decide_true, accepted, quiet, read, Bool.and_self,
    Option.isNone_none, List.isEmpty_nil]

structure DrainReady (report : Report input events) where
  supported : report.supported = true
  finished : report.remaining = []
  current : C.State input.active input.passive
  connection : report.final.connection = .recovering current
  complete : H.Completed input.active input.passive
  client : R.PreData complete.certificate.activeSeed
  server : R.PreData complete.certificate.passiveSeed
  phase : current.phase = .complete complete client server
  fresh : report.final.recoveryArchive = none
  tickets : report.final.work.pending.any (fun item => item.value.produced.isRecovery) = false
  packets : report.final.custody.pending.any (fun item => item.value.payload.isRecovery) = false

def DrainReady.reachable (ready : DrainReady report) : TCPHandshakeRecovery.Reachable ready.current :=
  CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report ready.connection

theorem DrainReady.clean (ready : DrainReady report) :
    R.PreDataClean ready.complete.certificate.activeSeed ready.client ∧
      R.PreDataClean ready.complete.certificate.passiveSeed ready.server :=
  (ready.reachable.complete ready.phase).2.2

private theorem DrainReady.early (ready : DrainReady report) (actor : TCPHandshakeRecovery.Side) :
    EarlyPrefix report.final.time (ready.current.applicationSteps actor) := by
  have chronological : ∀ actor actual, actual ∈ ready.current.applicationSteps actor → actual.stamp < report.final.time := by
    simpa only [CampusTCPChronology.Chronological, ready.connection, CampusTCPChronology.Earlier] using
      CampusTCPChronology.Report.chronological report
  intro actual member
  obtain ⟨origin⟩ := ready.reachable.application_origin member
  obtain ⟨profile, event, accepted, quiet, read, stamp⟩ := origin.fields
  exact ⟨origin.receipt.delivery.input, event, profile, chronological actor actual member, accepted, quiet, read⟩

theorem DrainReady.early_prefix (ready : DrainReady report) :
    EarlyPrefix report.final.time ready.client.steps ∧ EarlyPrefix report.final.time ready.server.steps := by
  constructor
  · simpa only [TCPHandshakeRecovery.State.applicationSteps, ready.phase] using ready.early .active
  · simpa only [TCPHandshakeRecovery.State.applicationSteps, ready.phase] using ready.early .passive

structure Prefix (input : Input) (events : List Event) (archive : RecoveryArchive input.active input.passive) where
  report : Report input events
  supported : report.supported = true
  finished : report.remaining = []
  endpoints : Applications archive.complete
  connection : report.final.connection = .application archive.complete endpoints
  archived : report.final.recoveryArchive = some archive
  clientBefore : endpoints.client.beforeRecoveryTransport archive.time = true
  serverBefore : endpoints.server.beforeRecoveryTransport archive.time = true

structure Drained (ready : DrainReady report) (archive : RecoveryArchive input.active input.passive) where
  next : Prefix input (events ++ [.finishStartup]) archive
  actual : Step input
  before : actual.before = report.final
  event : actual.event = .finishStartup
  supported : actual.result.supported = true
  history : next.report.steps = report.steps ++ [actual]
  final : next.report.final = actual.result.state
  current : archive.current = ready.current
  complete : archive.complete = ready.complete
  time : archive.time = report.final.time
  client : next.endpoints.client = Cursor.ofPreData archive.client
  server : next.endpoints.server = Cursor.ofPreData archive.server

private theorem drain_core (before : State input) (archive : RecoveryArchive input.active input.passive)
    (connection : before.connection = .recovering archive.current) (time : archive.time = before.time)
    (fresh : before.recoveryArchive = none)
    (tickets : before.work.pending.any (fun item => item.value.produced.isRecovery) = false)
    (packets : before.custody.pending.any (fun item => item.value.payload.isRecovery) = false) :
    processCore input before .finishStartup = .ok
      { state := { before with connection := .application archive.complete ⟨Cursor.ofPreData archive.client, Cursor.ofPreData archive.server⟩, recoveryArchive := some archive } } := by
  cases archive with
  | mk archiveTime current complete client server phase activeData activeHandoff passiveData passiveHandoff =>
    dsimp only at time connection
    subst archiveTime
    cases current with
    | mk currentPhase activeTimer passiveTimer activeValid passiveValid emissions receipts last =>
      dsimp only at phase
      subst currentPhase
      simp only [processCore, finishStartup, fresh, tickets, packets, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, connection]
      split
      · rename_i absent
        rw [absent] at activeHandoff
        cases activeHandoff
      · rename_i selected present
        have same := Option.some.inj (present.symm.trans activeHandoff)
        subst selected
        split
        · rename_i absent
          rw [absent] at passiveHandoff
          cases passiveHandoff
        · rename_i selected present
          have same := Option.some.inj (present.symm.trans passiveHandoff)
          subst selected
          rfl

theorem drain (ready : DrainReady report) : ∃ archive, Nonempty (Drained ready archive) := by
  obtain ⟨active, passive, _, _⟩ := ready.reachable.complete ready.phase
  obtain ⟨activeFlight, activeAt, activeStatus, _, _⟩ := active
  obtain ⟨passiveFlight, passiveAt, passiveStatus, _, _⟩ := passive
  let activeData : HandshakeTimer.Data :=
    ⟨ready.current.activeTimer.now, HandshakeTimer.dataRTO ready.current.activeTimer,
      ready.current.activeTimer.estimator, decide (activeFlight.retries ≠ 0)⟩
  let passiveData : HandshakeTimer.Data :=
    ⟨ready.current.passiveTimer.now, HandshakeTimer.dataRTO ready.current.passiveTimer,
      ready.current.passiveTimer.estimator, decide (passiveFlight.retries ≠ 0)⟩
  have activeHandoff : HandshakeTimer.handoff ready.current.activeTimer = some activeData := by
    simp only [HandshakeTimer.handoff, activeStatus, activeData]
  have passiveHandoff : HandshakeTimer.handoff ready.current.passiveTimer = some passiveData := by
    simp only [HandshakeTimer.handoff, passiveStatus, passiveData]
  let archive : RecoveryArchive input.active input.passive :=
    ⟨report.final.time, ready.current, ready.complete, ready.client, ready.server, ready.phase,
      activeData, activeHandoff, passiveData, passiveHandoff⟩
  let endpoints : Applications archive.complete := ⟨Cursor.ofPreData archive.client, Cursor.ofPreData archive.server⟩
  let coreEffect : Effect input :=
    { state := { report.final with connection := .application archive.complete endpoints, recoveryArchive := some archive } }
  have computed : processCore input report.final .finishStartup = .ok coreEffect :=
    drain_core report.final archive ready.connection rfl ready.fresh ready.tickets ready.packets

  obtain ⟨effect, checked, supportEq, outputEq, applicationEq, readEq⟩ :=
    finish_step report.final .finishStartup coreEffect computed rfl
  let actual : Step input := ⟨report.final, .finishStartup, effect, checked⟩
  have supported : actual.result.supported = true := supportEq
  have connection : actual.result.state.connection = .application archive.complete endpoints := by
    obtain ⟨core, custody, processed, result⟩ := actual.processed
    have same : core = coreEffect := Except.ok.inj (processed.symm.trans computed)
    rw [result, same]
  have archived : actual.result.state.recoveryArchive = some archive := by
    obtain ⟨core, custody, processed, result⟩ := actual.processed
    have same : core = coreEffect := Except.ok.inj (processed.symm.trans computed)
    rw [result, same]
  let nextReport := CampusTCPSchedule.Report.appendStep report ready.supported ready.finished actual rfl supported
  have early := ready.early_prefix
  let next : Prefix input (events ++ [.finishStartup]) archive :=
    ⟨nextReport, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl, endpoints,
      connection, archived, early.1.before, early.2.before⟩
  exact ⟨archive, ⟨⟨next, actual, rfl, rfl, supported, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩

theorem Prefix.archive_clean (prior : Prefix input events archive) :
    R.PreDataClean archive.complete.certificate.activeSeed archive.client ∧
      R.PreDataClean archive.complete.certificate.passiveSeed archive.server :=
  ((CampusTCPRecoveryStartupOrigins.Report.archiveReachable prior.report prior.archived).complete archive.phase).2.2

theorem Drained.frames (drained : Drained ready archive) :
    TCPHandshakeRecovery.WindowFrame archive.complete.certificate.activeSeed drained.next.endpoints.client.current ∧
      TCPHandshakeRecovery.WindowFrame archive.complete.certificate.passiveSeed drained.next.endpoints.server.current := by
  rw [drained.client, drained.server]
  exact ⟨drained.next.archive_clean.1.1, drained.next.archive_clean.2.1⟩


theorem Drained.cursors (drained : Drained ready archive) :
    drained.next.endpoints.client.current = archive.client.current ∧
      drained.next.endpoints.server.current = archive.server.current ∧
      drained.next.endpoints.client.steps = archive.client.steps ∧
      drained.next.endpoints.server.steps = archive.server.steps := by
  rw [drained.client, drained.server]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem Drained.window_markers (drained : Drained ready archive) :
    drained.next.endpoints.client.current.sendWL1 = archive.client.current.sendWL1 ∧
      drained.next.endpoints.client.current.sendWL2 = archive.client.current.sendWL2 ∧
      drained.next.endpoints.server.current.sendWL1 = archive.server.current.sendWL1 ∧
      drained.next.endpoints.server.current.sendWL2 = archive.server.current.sendWL2 := by
  rw [drained.client, drained.server]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Netlib.Check.CampusTCPRecoveredSetup
