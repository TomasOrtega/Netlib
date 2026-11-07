import Netlib.Check.CampusTCPStartupOpening
import Netlib.Check.CampusTCPRecoveryStartupCurrentNative
import Netlib.Check.CampusTCPStartupPrimaryServices
import Netlib.Check.CampusTCPTraceSlices

/-!
# Current native startup facts at every actual drive cut

The fixed preparation prefix and actual OPEN precede the literal drive slice.
One whole Actions check derives the current connection and native history.
-/

namespace Netlib.Check.CampusTCPStartupCurrentAt

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupCurrentNative (Current)
open CampusTCPRecoveryStartupCurrentEntry (History)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions actions_correct)
end E
namespace P
export CampusTCPStartupMonitor (Monitor Mode observe allowed)
end P
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S
namespace C
export TCPHandshakeRecovery (State)
end C
namespace O
export CampusTCPStartupOpening (preparation_before mode_at drive_at opening_event preparation_event)
end O
namespace R
export CampusTCPRoundEnvironment (TransportOnly)
end R

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : P.Monitor} {count : Nat}
variable {id : String}

private theorem install_connection (computed : installConfiguration input before gateway id = .ok effect) :
    effect.state.connection = before.connection := by
  unfold installConfiguration at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem stage_connection (computed : stageAttachment input before gateway id = .ok effect) :
    effect.state.connection = before.connection := by
  unfold stageAttachment at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem guard_connection (computed : installIngress input before gateway id = .ok effect) :
    effect.state.connection = before.connection := by
  unfold installIngress at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem Step.preparation_connection (actual : Step input)
    (preparation : CampusTCPStartupProfile.PreparationEvent actual.event) :
    actual.result.state.connection = actual.before.connection := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  have frame : effect.state.connection = actual.before.connection := by
    cases event : actual.event with
    | authentication index =>
      simp only [processCore, event] at computed
      repeat' first
        | (solve | cases computed; rfl)
        | (solve | cases computed)
        | (split at computed)
        | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
    | install id | installAt gateway id => rw [event] at computed; exact install_connection computed
    | stage id | stageAt gateway id => rw [event] at computed; exact stage_connection computed
    | installGuard id | installGuardAt gateway id => rw [event] at computed; exact guard_connection computed
    | _ => simp only [event, CampusTCPStartupProfile.PreparationEvent] at preparation
  simpa only [final] using frame

private theorem Trace.preparation_connection (trace : Trace input before events steps after remaining)
    (preparation : ∀ actual ∈ steps, CampusTCPStartupProfile.PreparationEvent actual.event) :
    after.connection = before.connection := by
  induction trace with
  | done => rfl
  | stop head blocked rest => exact Step.preparation_connection head (preparation head List.mem_cons_self)
  | next head supported rest ih =>
    exact (ih (fun actual member => preparation actual (List.mem_cons_of_mem head member))).trans
      (Step.preparation_connection head (preparation head List.mem_cons_self))

private theorem stage_recovering {state : State input} {current : C.State input.active input.passive} (connected : CampusTCPRecoveryStartupOrigins.stage state.connection = .recovering current) :
    state.connection = .recovering current := by
  cases connection : state.connection with
  | startup stage pending | application complete endpoints =>
    simp only [connection, CampusTCPRecoveryStartupOrigins.stage, reduceCtorEq] at connected
  | recovering selected =>
    simp only [connection, CampusTCPRecoveryStartupOrigins.stage] at connected
    exact congrArg Connection.recovering (CampusTCPRecoveryStartupOrigins.Stage.recovering.inj connected)

private theorem Step.recovering (actual : Step input) (connected : actual.before.connection = .recovering current)
    (unfinished : actual.event ≠ .finishStartup) : ∃ next, actual.result.state.connection = .recovering next := by
  cases CampusTCPRecoveryStartupOrigins.Step.linked actual with
  | quiet ordinary recovery same =>
    refine ⟨current, stage_recovering ?_⟩
    rw [same, connected]
    rfl
  | ordinary selected recorded recovery prior after stamp pending supported =>
    simp only [connected, CampusTCPRecoveryStartupOrigins.stage, reduceCtorEq] at prior
  | recovery selected recorded ordinary prior after stamp => exact ⟨selected.result.state, stage_recovering after⟩
  | drain archive ordinary recovery event prior after retained stamp => exact False.elim (unfinished event)

private theorem Trace.recovering (trace : Trace input before events steps after remaining)
    (connected : before.connection = .recovering current)
    (unfinished : ∀ actual ∈ steps, actual.event ≠ .finishStartup) : ∃ next, after.connection = .recovering next := by
  induction trace generalizing current with
  | done => exact ⟨current, connected⟩
  | stop head blocked rest => exact Step.recovering head connected (unfinished head List.mem_cons_self)
  | next head supported rest ih =>
    obtain ⟨next, after⟩ := Step.recovering head connected (unfinished head List.mem_cons_self)
    exact ih after (fun actual member => unfinished actual (List.mem_cons_of_mem head member))

private theorem job_transport (allowed : CampusTCPStartupSelection.jobAllowed config state event = true) :
    R.TransportOnly event := by
  obtain ⟨job, member, selected⟩ := List.any_eq_true.mp allowed
  have same := of_decide_eq_true selected
  rw [← same]
  cases job <;> trivial

private theorem selection_transport (allowed : CampusTCPStartupSelection.allowed config state held event = true) :
    R.TransportOnly event := by
  cases event <;> first | trivial | exact job_transport allowed

private theorem drive_not_finish (prior : P.Monitor) (actual : Step input)
    (drive : prior.mode = .drive) (later : (P.observe config prior actual).mode = .drive) :
    actual.event ≠ .finishStartup := by
  intro finished
  simp only [P.observe, drive, finished] at later
  split at later <;> cases later

private theorem slice_member (member : actual ∈ CampusTCPTraceSlices.slice steps start length) :
    ∃ slot, start ≤ slot ∧ slot < start + length ∧ steps[slot]? = some actual := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have lengthBound : (CampusTCPTraceSlices.slice steps start length).length ≤ length := by
    simp only [CampusTCPTraceSlices.slice, List.length_take]
    exact Nat.min_le_left _ _
  have inside : index < length := by omega
  exact ⟨start + index, by omega, by omega,
    (CampusTCPTraceSlices.getElem?_slice steps inside).symm.trans found⟩

private theorem drive_step (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (early : config.startup.preparation.length < slot) (later : slot < count)
    (found : whole.steps[slot]? = some actual) :
    R.TransportOnly actual.event ∧ actual.event ≠ .finishStartup := by
  obtain ⟨prior, priorAt, priorMode⟩ := O.drive_at within ending drive early (Nat.le_of_lt later)
  obtain ⟨next, nextAt, nextMode⟩ := O.drive_at within ending drive (by omega) (by omega : slot + 1 ≤ count)
  obtain ⟨selected, selectedAt, before, event, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot (by omega)
  have same : selected = actual := Option.some.inj (selectedAt.symm.trans found)
  subst selected
  have observed := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found
  rw [priorAt] at observed
  have update := CampusTCPStartupEntry.observe_startup_eq prior actual next (observed.symm.trans nextAt)
  have permitted := (E.actions_correct _ _ _ _).mp actions slot (by omega)
  rw [priorAt] at permitted
  have allowed : CampusTCPStartupSelection.allowed config actual.before prior.protection actual.event = true := by
    simpa only [← before, ← event, CampusTCPStartupTransferExecution.allowed, P.allowed, priorMode] using permitted
  exact ⟨selection_transport allowed, drive_not_finish prior actual priorMode (by rw [update]; exact nextMode)⟩

structure At (whole : Report input events) (config : CampusTCPStartupTransferMonitor.Config)
    (count : Nat) (within : count ≤ whole.steps.length)
    (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
      (beforeService input (S.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
      input.zone (Handshake.outbound input.active config.startup.remote)) where
  baseWithin : config.startup.preparation.length ≤ whole.steps.length
  history : History (CampusTCPSchedule.Report.cut whole config.startup.preparation.length baseWithin)
    (CampusTCPSchedule.Report.cut whole count within)
  current : C.State input.active input.passive
  value : Current (CampusTCPSchedule.Report.cut whole config.startup.preparation.length baseWithin) profile
    (CampusTCPSchedule.Report.cut whole count within) current

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (S.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem at_drive (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive) :
    Nonempty (At whole config count within profile) := by
  have available := O.preparation_before within ending drive
  have baseWithin : config.startup.preparation.length ≤ whole.steps.length := by omega
  have preparations : ∀ actual ∈ whole.steps.take config.startup.preparation.length,
      CampusTCPStartupProfile.PreparationEvent actual.event := by
    intro actual member
    obtain ⟨slot, found⟩ := List.mem_iff_getElem?.mp member
    have inside := (List.getElem?_eq_some_iff.mp found).1
    have early : slot < config.startup.preparation.length := by rw [List.length_take] at inside; omega
    have actualAt : whole.steps[slot]? = some actual := by simpa only [List.getElem?_take_of_lt early] using found
    exact O.preparation_event prep actions within ending drive early actual actualAt
  have prepared := Trace.preparation_connection (CampusTCPSchedule.Trace.take whole.trace _ baseWithin) preparations
  have idle : (S.stateAt input.initial whole.steps config.startup.preparation.length).connection = .startup .idle rfl := prepared
  obtain ⟨opening, found, beforeOpen, eventOpen, afterOpen⟩ := O.opening_event actions within ending drive
  have initialOpen : opening.before.connection = .startup .idle rfl := by rw [beforeOpen]; exact idle
  obtain ⟨opened⟩ := CampusTCPRecoveryStartupOpened.Step.opened opening initialOpen eventOpen
  let currentReport := CampusTCPSchedule.Report.cut whole count within
  let baseReport := CampusTCPSchedule.Report.cut whole config.startup.preparation.length baseWithin
  let suffix := CampusTCPTraceSlices.slice whole.steps config.startup.preparation.length (count - config.startup.preparation.length)
  have sum : config.startup.preparation.length + (count - config.startup.preparation.length) = count := by omega
  have history : currentReport.steps = baseReport.steps ++ suffix := by
    change whole.steps.take count = whole.steps.take config.startup.preparation.length ++ suffix
    rw [← sum, List.take_add]
    rfl
  have trace : Trace input baseReport.final (suffix.map (·.event)) suffix currentReport.final [] := by
    have selected := CampusTCPTraceSlices.Trace.slice whole.trace (by omega : config.startup.preparation.length +
      (count - config.startup.preparation.length) ≤ whole.steps.length)
    simpa only [sum, currentReport, baseReport, suffix, CampusTCPSchedule.Report.cut] using selected
  have cold := CampusTCPStartupProfileFacts.Report.cut_cold_profile whole prep actions within ending (by rw [drive]; trivial)
  have primary := CampusTCPStartupPrimaryServices.Report.primary_services currentReport cold
  have transport : ∀ actual ∈ suffix, R.TransportOnly actual.event := by
    intro actual member
    obtain ⟨slot, lower, upper, stored⟩ := slice_member member
    by_cases first : slot = config.startup.preparation.length
    · rw [first] at stored
      have same : actual = opening := Option.some.inj (stored.symm.trans found)
      rw [same, eventOpen]
      trivial
    · exact (drive_step actions within ending drive (by omega) (by omega) stored).1
  have suffixPrimary : ∀ served ∈ suffix.filterMap (·.result.service), served.ticket.value.gateway = .primary := by
    intro served member
    obtain ⟨actual, member, recorded⟩ := List.mem_filterMap.mp member
    apply primary served
    rw [history, List.filterMap_append]
    exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨actual, member, recorded⟩)
  let nativeHistory : History baseReport currentReport := ⟨suffix, suffix.map (·.event), [], trace, history, transport, suffixPrimary⟩
  have currentAfterOpen : (S.stateAt input.initial whole.steps (config.startup.preparation.length + 1)).connection =
      .recovering opened.control.result.state := by rw [← afterOpen]; exact opened.after
  have laterTrace := CampusTCPTraceSlices.Trace.slice whole.trace (by omega : config.startup.preparation.length + 1 +
    (count - (config.startup.preparation.length + 1)) ≤ whole.steps.length)
  have noFinish : ∀ actual ∈ CampusTCPTraceSlices.slice whole.steps (config.startup.preparation.length + 1)
      (count - (config.startup.preparation.length + 1)), actual.event ≠ .finishStartup := by
    intro actual member
    obtain ⟨slot, lower, upper, stored⟩ := slice_member member
    exact (drive_step actions within ending drive (by omega) (by omega) stored).2
  obtain ⟨current, connected⟩ := Trace.recovering laterTrace currentAfterOpen noFinish
  have connected : currentReport.final.connection = .recovering current := by
    have sum : config.startup.preparation.length + 1 + (count - (config.startup.preparation.length + 1)) = count := by omega
    simpa only [sum, currentReport, CampusTCPSchedule.Report.cut] using connected
  have openingMember : opening ∈ currentReport.steps := List.mem_of_getElem? (by
    change (whole.steps.take count)[config.startup.preparation.length]? = some opening
    rw [List.getElem?_take_of_lt available]
    exact found)
  exact ⟨⟨baseWithin, nativeHistory, current,
    CampusTCPRecoveryStartupCurrentNative.of_open nativeHistory profile cold connected primary opening openingMember initialOpen eventOpen⟩⟩

end Netlib.Check.CampusTCPStartupCurrentAt
