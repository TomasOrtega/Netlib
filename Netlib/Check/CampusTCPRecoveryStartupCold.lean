import Netlib.Check.CampusTCPRecoveryStartupSources

/-!
# Recovery sources from a cold startup event profile

The profile is a predicate on past actual events. Producer ancestry rules out
ordinary output revival; it does not assume the kinds of future service.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupCold

open Protocol.TCP CampusTCPModel

variable {input : Input}

def ColdEvent : Event → Prop
  | .openRecovering .. | .startupClock .. | .startupTimeout .. | .finishStartup
  | .authentication .. | .install .. | .stage .. | .installGuard ..
  | .installAt .. | .stageAt .. | .installGuardAt ..
  | .assign .. | .serve .. | .deliver .. | .copyPacket .. | .dropPacket .. => True
  | _ => False

def ColdProfile (report : Report input events) : Prop :=
  ∀ actual ∈ report.steps, ColdEvent actual.event

private def RecoveryOutput (effect : Effect input) : Prop :=
  ∀ produced, effect.output = some produced → produced.isRecovery = true

private theorem recovery_output (computed : runRecovery input before event = .ok effect) : RecoveryOutput effect := by
  unfold runRecovery at computed
  cases connection : before.connection with
  | startup stage pending | application complete endpoints =>
    simp only [connection] at computed
    cases computed
    intro produced selected
    cases selected
  | recovering current =>
    simp only [connection] at computed
    split at computed
    · cases computed
    · rename_i result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals
          subst effect
          intro produced selected
          cases selected <;> rfl

private theorem open_output (computed : openRecovering input before remote policy = .ok effect) : RecoveryOutput effect := by
  unfold openRecovering at computed
  repeat' first
    | (solve | exact recovery_output computed)
    | (solve | cases computed; intro produced selected; cases selected)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem finish_output (computed : finishStartup input before = .ok effect) : RecoveryOutput effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; intro produced selected; cases selected)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem process_output (computed : processCore input before event = .ok effect) (cold : ColdEvent event)
    (services : ∀ served ∈ before.services, served.ticket.value.produced.isRecovery = true) : RecoveryOutput effect := by
  cases event with
  | openRecovering remote policy => exact open_output computed
  | startupClock actor millis | startupTimeout actor generation policy => exact recovery_output computed
  | finishStartup => exact finish_output computed
  | deliver index bytes policy =>
    cases found : before.services[index]? with
    | none => simp [processCore, CampusTCPModel.get, found, bind, Except.bind] at computed
    | some served =>
      have only := services served (List.mem_of_getElem? found)
      cases production : served.ticket.value.produced with
      | startup actual packet present | application actor actual packet origin =>
        simp only [production, Produced.isRecovery] at only
        cases only
      | recovery actual occurrence present =>
        simp only [processCore, CampusTCPModel.get, found, bind, Except.bind, production] at computed
        repeat' first
          | (solve |
            rename_i applicationEffect applicationAt
            have raw := applicationAt
            change runRecovery input before _ = .ok applicationEffect at raw
            have correct := recovery_output raw
            simp only [Except.ok.injEq] at computed
            subst effect
            exact correct)
          | (solve | cases computed)
          | (split at computed)
          | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
              throw, throwThe, MonadExceptOf.throw] at computed)
  | authentication index | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id
  | installGuardAt gateway id | assign index ingress | serve id observed | copyPacket id | dropPacket id =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress] at computed
    repeat' first
      | (solve | cases computed; intro produced selected; cases selected)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | «open» remote policy | write actor bytes | send actor count policy | read actor count | emitAck actor policy
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy | enableAck actor
  | enableStartupRecovery actor | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway
  | fencePrimary | resume => cases cold

theorem Step.recovery_output (actual : Step input) (cold : ColdEvent actual.event)
    (services : ∀ served ∈ actual.before.services, served.ticket.value.produced.isRecovery = true)
    (produced : Produced input.active input.passive) (recorded : actual.result.output = some produced) :
    produced.isRecovery = true := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  exact process_output computed cold services produced (by simpa only [final] using recorded)

theorem Report.recovery_outputs (report : Report input events) (cold : ColdProfile report)
    (actual : Step input) (member : actual ∈ report.steps) (produced : Produced input.active input.passive)
    (recorded : actual.result.output = some produced) : produced.isRecovery = true := by
  generalize stampEq : actual.before.time = stamp
  induction stamp using Nat.strongRecOn generalizing actual produced with
  | ind stamp ih =>
    apply Step.recovery_output actual (cold actual member) _ produced recorded
    intro served servedMember
    obtain ⟨prior, later, history, preceding, _, _⟩ := CampusTCPFacts.step_origin report actual member
    let beforeReport : Report input (prior.map (·.event)) := ⟨actual.before, prior, [], preceding⟩
    obtain ⟨source⟩ := CampusTCPRecoveryStartupSources.Report.service_source beforeReport served servedMember
    obtain ⟨_, _, _, serviceTime, servicePast⟩ := CampusTCPOrigins.Report.services_origin beforeReport served servedMember
    rw [← serviceTime] at servicePast
    have producerFull : source.producer ∈ report.steps := by
      rw [history]
      exact List.mem_append_left _ source.producerMember
    have earlier : source.producer.before.time < stamp := by
      have before := source.earlier
      change served.time < actual.before.time at servicePast
      omega
    exact ih source.producer.before.time earlier source.producer producerFull served.ticket.value.produced source.produced rfl

theorem Report.recovery_services (report : Report input events) (cold : ColdProfile report)
    (served : Served input) (member : served ∈ report.final.services) : served.ticket.value.produced.isRecovery = true := by
  obtain ⟨source⟩ := CampusTCPRecoveryStartupSources.Report.service_source report served member
  exact Report.recovery_outputs report cold source.producer source.producerMember served.ticket.value.produced source.produced

end Netlib.Check.CampusTCPRecoveryStartupCold
