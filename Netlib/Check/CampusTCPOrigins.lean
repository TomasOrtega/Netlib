import Netlib.Check.CampusTCPModel

/-!
# Origins in the joint campus TCP replay

Stored packets, queued tickets, and gateway services retain their actual earlier operations.
-/

namespace Netlib.Check.CampusTCPOrigins

open Packet Protocol
namespace M
export Check.CampusTCPModel
  (Input State Step Trace Report Actor Produced Ticket Served Receipt Effect Event)
end M
namespace O
export Theory.Outstanding (Item newItem)
end O

@[simp] private theorem write_outputs (before : M.State input) (gateway) (resident) :
    (before.write gateway resident).outputs = before.outputs := by cases gateway <;> rfl
@[simp] private theorem write_services (before : M.State input) (gateway) (resident) :
    (before.write gateway resident).services = before.services := by cases gateway <;> rfl
@[simp] private theorem write_work (before : M.State input) (gateway) (resident) :
    (before.write gateway resident).work = before.work := by cases gateway <;> rfl

private def Produces (before : M.State input) (effect : M.Effect input) : Prop :=
  effect.state.outputs = before.outputs ++ effect.output.toList ∧
    effect.state.services = before.services ∧ effect.state.work = before.work ∧
    (∀ produced, effect.output = some produced → produced.time = before.time) ∧
    effect.service = none

private theorem parsed_ok (value : Except String α) (output : α)
    (accepted : Check.CampusTCPModel.parsed value = .ok output) : value = .ok output := by
  cases value <;> simp_all [Check.CampusTCPModel.parsed, Except.mapError]

private theorem cursor_stamp (before : Check.CampusTCPModel.Cursor seed) (event : TCP.ApplicationTrace.Event)
    (stamp : Nat) (applied : Check.CampusTCPModel.Applied before)
    (accepted : before.apply event stamp = .ok applied) : applied.step.stamp = stamp := by
  unfold Check.CampusTCPModel.Cursor.apply at accepted
  split at accepted
  · simp only [pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    rfl
  · cases accepted

private theorem startup_produces (input : M.Input) (before : M.State input)
    (event : Check.TCPHandshake.Event) (effect : M.Effect input)
    (accepted : Check.CampusTCPModel.startup input before event = .ok effect) : Produces before effect := by
  unfold Check.CampusTCPModel.startup at accepted
  split at accepted
  · simp only [pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    simp [Produces, Check.CampusTCPModel.unsupported]
  · split at accepted
    · cases accepted
    · split at accepted
      · simp only [pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        simp [Produces]
      · simp only [pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        simp [Produces, Check.CampusTCPModel.publish, Check.CampusTCPModel.Produced.time]

private theorem application_produces (input : M.Input) (before : M.State input)
    (actor : M.Actor) (event : TCP.ApplicationTrace.Event) (effect : M.Effect input)
    (accepted : Check.CampusTCPModel.applyApplication input before actor event = .ok effect) : Produces before effect := by
  unfold Check.CampusTCPModel.applyApplication at accepted
  split at accepted
  · simp only [pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    simp [Produces, Check.CampusTCPModel.unsupported]
  · rename_i complete endpoints phase
    cases actor <;> simp only at accepted
    all_goals
      simp only [Check.CampusTCPModel.parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
      split at accepted
      next error found => cases accepted
      next applied found =>
        have stamp := cursor_stamp _ event before.time applied (parsed_ok _ _ found)
        split at accepted
        · simp only [Except.ok.injEq] at accepted
          cases accepted
          simp [Produces]
        · split at accepted
          · cases accepted
          · simp only [Except.ok.injEq] at accepted
            cases accepted
            simp [Produces, Check.CampusTCPModel.publish, Check.CampusTCPModel.Produced.time, stamp]

def Assignment (before : M.State input) (event : M.Event)
    (item : O.Item (M.Ticket input.active input.passive)) : Prop :=
  ∃ index ingress produced, event = .assign index ingress ∧
    before.outputs[index]? = some produced ∧
    item = O.newItem before.work ⟨index, produced, ingress, before.owner produced.actor, before.routeEpoch⟩

private structure Changes (before : M.State input) (event : M.Event) (effect : M.Effect input) : Prop where
  outputs : effect.state.outputs = before.outputs ++ effect.output.toList
  services : effect.state.services = before.services ++ effect.service.toList
  pending : ∀ item ∈ effect.state.work.pending, item ∈ before.work.pending ∨ Assignment before event item
  outputTime : ∀ produced, effect.output = some produced → produced.time = before.time
  serviceTime : ∀ served, effect.service = some served → served.time = before.time
  serviceOrigin : ∀ served, effect.service = some served →
    ∃ id observed, ∃ completed : Theory.Outstanding.Completed before.work id,
      event = .serve id observed ∧ Theory.Outstanding.complete before.work id = .ok completed ∧
      served.ticket = completed.item ∧ served.before = Check.CampusTCPModel.beforeService input before served.ticket.value.gateway ∧
      served.time = before.time

private theorem produces_changes (event : M.Event) (produces : Produces before effect) : Changes before event effect := by
  obtain ⟨outputs, services, work, stamp, noService⟩ := produces
  refine ⟨outputs, ?_, ?_, stamp, ?_, ?_⟩
  · simp only [noService, Option.toList_none, List.append_nil]
    exact services
  · intro item member
    exact .inl (work ▸ member)
  · intro served present
    rw [noService] at present
    cases present
  · intro served present
    rw [noService] at present
    cases present

private theorem process_changes (input : M.Input) (before : M.State input) (event : M.Event)
    (effect : M.Effect input) (accepted : Check.CampusTCPModel.process input before event = .ok effect) :
    Changes before event effect := by
  cases event with
  | «open» remote policy => exact produces_changes _ (startup_produces _ _ _ _ accepted)
  | write actor bytes | send actor bytes policy | read actor bytes | emitAck actor policy =>
    exact produces_changes _ (application_produces _ _ _ _ _ accepted)
  | enableRecovery actor | advanceClock actor millis | timeout actor policy =>
    exact produces_changes _ (application_produces _ _ _ _ _ accepted)
  | authentication index =>
    simp only [Check.CampusTCPModel.process] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · simp only [pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        exact produces_changes _ (by simp [Produces])
      · cases accepted
  | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id =>
    simp only [Check.CampusTCPModel.process, Check.CampusTCPModel.installConfiguration,
      Check.CampusTCPModel.stageAttachment, Check.CampusTCPModel.installIngress] at accepted
    repeat' first
      | (solve | apply produces_changes; simp [Produces])
      | (solve | apply produces_changes; simp [Produces])
      | (cases accepted)
      | (split at accepted)
      | (dsimp only [Check.CampusTCPModel.parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [Check.CampusTCPModel.process, Check.CampusTCPModel.transferControl] at accepted
    repeat' first
      | (solve | apply produces_changes; simp [Produces])
      | (cases accepted)
      | (split at accepted)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)
  | assign index ingress =>
    simp only [Check.CampusTCPModel.process] at accepted
    split at accepted
    · simp [throw, bind, Except.bind] at accepted
    · cases found : before.outputs[index]? with
      | none => simp [Check.CampusTCPModel.get, found, bind, Except.bind] at accepted
      | some produced =>
        simp only [Check.CampusTCPModel.get, found, bind, Except.bind, pure, Except.pure] at accepted
        repeat' first
          | (cases accepted)
          | (split at accepted)
          | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)
        all_goals
          refine ⟨by simp, by simp, ?_, by simp, by simp, by simp⟩
          intro item member
          rcases List.mem_append.mp member with old | fresh
          · exact .inl old
          · exact .inr ⟨index, ingress, produced, rfl, found, List.mem_singleton.mp fresh⟩
  | serve id observed =>
    simp only [Check.CampusTCPModel.process] at accepted
    cases completed : Theory.Outstanding.complete before.work id with
    | error reason => simp [completed, Except.mapError, bind, Except.bind] at accepted
    | ok work =>
      simp only [completed, Except.mapError, bind, Except.bind] at accepted
      repeat' first
        | (solve | apply produces_changes; simp [Produces, Check.CampusTCPModel.unsupported])
        | (cases accepted)
        | (split at accepted)
        | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)
      all_goals
        refine ⟨?_, ?_, ?_, by simp, ?_, ?_⟩
        · simp only [write_outputs, Option.toList_none, List.append_nil]
        · rfl
        · intro item member
          exact .inl (work.pendingPerm.mem_iff.mpr (List.mem_cons_of_mem _ member))
        · intro served present
          cases present
          rfl
        · intro served present
          cases present
          exact ⟨id, observed, work, rfl, completed, rfl, rfl, rfl⟩
  | deliver index bytes policy =>
    simp only [Check.CampusTCPModel.process] at accepted
    cases found : before.services[index]? with
    | none => simp [Check.CampusTCPModel.get, found, bind, Except.bind] at accepted
    | some served =>
      simp only [Check.CampusTCPModel.get, found, bind, Except.bind] at accepted
      repeat' first
        | (solve | apply produces_changes; simpa only [Produces] using (startup_produces input before _ _ (by assumption)))
        | (solve | apply produces_changes; simpa only [Produces] using (application_produces input before _ _ _ (by assumption)))
        | (cases accepted)
        | (split at accepted)
        | (dsimp only [Check.CampusTCPModel.parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)

private theorem step_changes (step : M.Step input) : Changes step.before step.event step.result := by
  obtain ⟨effect, computed, same⟩ := step.processed
  have changes := process_changes input step.before step.event effect computed
  rw [same]
  exact ⟨changes.outputs, changes.services, changes.pending, changes.outputTime, changes.serviceTime, changes.serviceOrigin⟩

theorem service_origin (step : M.Step input) (served : M.Served input)
    (present : step.result.service = some served) :
    ∃ id observed, ∃ completed : Theory.Outstanding.Completed step.before.work id,
      step.event = .serve id observed ∧ Theory.Outstanding.complete step.before.work id = .ok completed ∧
      served.ticket = completed.item ∧ served.before = Check.CampusTCPModel.beforeService input step.before served.ticket.value.gateway ∧
      served.time = step.before.time :=
  (step_changes step).serviceOrigin served present

theorem service_run (step : M.Step input) (served : M.Served input)
    (present : step.result.service = some served) :
    ∃ evidence : Check.CampusTCPService.Evidence (input.contextFor served.ticket.value.gateway)
        (Check.CampusTCPModel.beforeService input step.before served.ticket.value.gateway) served.ticket.value.source input.zone served.ticket.value.ingress,
      Check.CampusTCPService.run (input.contextFor served.ticket.value.gateway) (Check.CampusTCPModel.beforeService input step.before served.ticket.value.gateway)
        served.ticket.value.source input.zone served.ticket.value.ingress = .ok evidence := by
  obtain ⟨id, observed, completed, event, finished, ticket, before, time⟩ := service_origin step served present
  have computed : ∃ evidence : Check.CampusTCPService.Evidence (input.contextFor served.ticket.value.gateway) served.before
      served.ticket.value.source input.zone served.ticket.value.ingress,
      Check.CampusTCPService.run (input.contextFor served.ticket.value.gateway) served.before served.ticket.value.source input.zone
        served.ticket.value.ingress = .ok evidence := ⟨served.evidence, served.computed⟩
  rw [← before]
  exact computed

namespace Trace

theorem time (trace : M.Trace input initial events steps final remaining) :
    final.time = initial.time + steps.length := by
  induction trace with
  | done state => simp
  | stop head blocked tail => simpa using head.clock
  | next head supported rest ih =>
    have clock := head.clock
    simp only [List.length_cons]
    omega

private theorem list_origin {α : Type} (stored : M.State input → List α)
    (emitted : M.Effect input → Option α) (stamp : α → Nat)
    (appended : ∀ step : M.Step input, stored step.result.state = stored step.before ++ (emitted step.result).toList)
    (stamped : ∀ (step : M.Step input) (value : α), emitted step.result = some value → stamp value = step.before.time)
    (trace : M.Trace input initial events steps final remaining) (value : α) (member : value ∈ stored final) :
    value ∈ stored initial ∨ ∃ step, step ∈ steps ∧ emitted step.result = some value ∧
      stamp value = step.before.time ∧ step.before.time < final.time := by
  induction trace with
  | done state => exact .inl member
  | stop head blocked tail =>
    rw [appended head] at member
    rcases List.mem_append.mp member with old | created
    · exact .inl old
    · have emitted : emitted head.result = some value := by simpa using created
      exact .inr ⟨head, by simp, emitted, stamped head value emitted, by have clock := head.clock; omega⟩
  | next head supported rest ih =>
    rcases ih member with old | later
    · rw [appended head] at old
      rcases List.mem_append.mp old with old | created
      · exact .inl old
      · have emitted : emitted head.result = some value := by simpa using created
        refine .inr ⟨head, by simp, emitted, stamped head value emitted, ?_⟩
        have clock := head.clock
        have elapsed := time rest
        omega
    · obtain ⟨step, inside, emitted, stamped, earlier⟩ := later
      exact .inr ⟨step, by simp [inside], emitted, stamped, earlier⟩

theorem outputs_origin (trace : M.Trace input initial events steps final remaining)
    (produced : M.Produced input.active input.passive) (member : produced ∈ final.outputs) :
    produced ∈ initial.outputs ∨ ∃ step, step ∈ steps ∧ step.result.output = some produced ∧
      produced.time = step.before.time ∧ step.before.time < final.time :=
  list_origin (·.outputs) (·.output) Check.CampusTCPModel.Produced.time
    (fun step => (step_changes step).outputs) (fun step => (step_changes step).outputTime) trace produced member

theorem services_origin (trace : M.Trace input initial events steps final remaining)
    (served : M.Served input) (member : served ∈ final.services) :
    served ∈ initial.services ∨ ∃ step, step ∈ steps ∧ step.result.service = some served ∧
      served.time = step.before.time ∧ step.before.time < final.time :=
  list_origin (·.services) (·.service) (·.time)
    (fun step => (step_changes step).services) (fun step => (step_changes step).serviceTime) trace served member

theorem pending_origin (trace : M.Trace input initial events steps final remaining)
    (item : O.Item (M.Ticket input.active input.passive)) (member : item ∈ final.work.pending) :
    item ∈ initial.work.pending ∨ ∃ step index ingress produced, step ∈ steps ∧
      step.event = .assign index ingress ∧ step.before.outputs[index]? = some produced ∧
      item = O.newItem step.before.work ⟨index, produced, ingress, step.before.owner produced.actor, step.before.routeEpoch⟩ ∧ step.before.time < final.time := by
  induction trace with
  | done state => exact .inl member
  | stop head blocked tail =>
    rcases (step_changes head).pending item member with old | created
    · exact .inl old
    · obtain ⟨index, ingress, produced, event, selected, exactItem⟩ := created
      exact .inr ⟨head, index, ingress, produced, by simp, event, selected, exactItem,
        by have clock := head.clock; omega⟩
  | next head supported rest ih =>
    rcases ih member with old | later
    · rcases (step_changes head).pending item old with old | created
      · exact .inl old
      · obtain ⟨index, ingress, produced, event, selected, exactItem⟩ := created
        refine .inr ⟨head, index, ingress, produced, by simp, event, selected, exactItem, ?_⟩
        have clock := head.clock
        have elapsed := time rest
        omega
    · obtain ⟨step, index, ingress, produced, inside, event, selected, exactItem, earlier⟩ := later
      exact .inr ⟨step, index, ingress, produced, by simp [inside], event, selected, exactItem, earlier⟩

end Trace

namespace Report

theorem outputs_origin (report : M.Report input events) (produced : M.Produced input.active input.passive)
    (member : produced ∈ report.final.outputs) :
    ∃ step, step ∈ report.steps ∧ step.result.output = some produced ∧
      produced.time = step.before.time ∧ step.before.time < report.final.time := by
  rcases Trace.outputs_origin report.trace produced member with initial | origin
  · simp [Check.CampusTCPModel.Input.initial] at initial
  · exact origin

theorem services_origin (report : M.Report input events) (served : M.Served input)
    (member : served ∈ report.final.services) :
    ∃ step, step ∈ report.steps ∧ step.result.service = some served ∧
      served.time = step.before.time ∧ step.before.time < report.final.time := by
  rcases Trace.services_origin report.trace served member with initial | origin
  · simp [Check.CampusTCPModel.Input.initial] at initial
  · exact origin

theorem pending_origin (report : M.Report input events)
    (item : O.Item (M.Ticket input.active input.passive)) (member : item ∈ report.final.work.pending) :
    ∃ step index ingress produced, step ∈ report.steps ∧
      step.event = .assign index ingress ∧ step.before.outputs[index]? = some produced ∧
      item = O.newItem step.before.work ⟨index, produced, ingress, step.before.owner produced.actor, step.before.routeEpoch⟩ ∧ step.before.time < report.final.time := by
  rcases Trace.pending_origin report.trace item member with initial | origin
  · simp [Check.CampusTCPModel.Input.initial, Theory.Outstanding.State.initial] at initial
  · exact origin

end Report

end Netlib.Check.CampusTCPOrigins
