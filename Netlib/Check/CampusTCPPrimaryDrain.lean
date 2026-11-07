import Netlib.Check.CampusTCPFacts
import Netlib.Check.CampusTCPCustodyFacts

/-!
# Primary ticket drain in the actual campus trace

A stored service consumes its selected work ticket. It does not run an endpoint.
-/

namespace Netlib.Check.CampusTCPPrimaryDrain

open CampusTCPModel

variable {input : Input}

private theorem write_connection (before : State input) (gateway : Gateway) (resident : Local) :
    (before.write gateway resident).connection = before.connection := by cases gateway <;> rfl

theorem serve_completed (actual : Step input) (id : Nat)
    (observed : Option (List UInt8 × Option (List UInt8)))
    (event : actual.event = .serve id observed) (served : Served input)
    (present : actual.result.service = some served) :
    ∃ completed : Theory.Outstanding.Completed actual.before.work id,
      Theory.Outstanding.complete actual.before.work id = .ok completed ∧
      served.ticket = completed.item ∧ actual.result.state.work = completed.state ∧
      actual.result.state.connection = actual.before.connection ∧
      actual.result.output = none ∧ actual.result.application = none ∧ actual.result.read = [] := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  have selected : effect.service = some served := by simpa only [result] using present
  rw [event] at computed
  simp only [processCore] at computed
  cases completed : Theory.Outstanding.complete actual.before.work id with
  | error reason => simp [completed, Except.mapError, bind, Except.bind] at computed
  | ok work =>
    simp only [completed, Except.mapError, bind, Except.bind] at computed
    repeat' first
      | (solve | cases computed <;> simp [unsupported] at selected)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
    cases computed
    cases selected
    refine ⟨work, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [result]
    all_goals first | rfl | apply write_connection

theorem serve_count (actual : Step input) (id : Nat)
    (observed : Option (List UInt8 × Option (List UInt8)))
    (event : actual.event = .serve id observed) (served : Served input)
    (present : actual.result.service = some served) (gateway : Gateway) :
    actual.result.state.outstanding gateway + (if served.ticket.value.gateway = gateway then 1 else 0) =
      actual.before.outstanding gateway := by
  obtain ⟨completed, _, ticket, work, _⟩ := serve_completed actual id observed event served present
  have counted := (completed.pendingPerm.filter
    (fun item => decide (item.value.gateway = gateway))).length_eq
  by_cases matching : completed.item.value.gateway = gateway
  all_goals simpa [State.outstanding, work, ticket, matching] using counted.symm

theorem serve_primary_count (actual : Step input) (id : Nat)
    (event : actual.event = .serve id none) (served : Served input)
    (present : actual.result.service = some served) (primary : served.ticket.value.gateway = .primary) :
    actual.result.state.outstanding .primary + 1 = actual.before.outstanding .primary := by
  simpa [primary] using serve_count actual id none event served present .primary

theorem serve_ticket_eq (actual : Step input) (id : Nat)
    (observed : Option (List UInt8 × Option (List UInt8)))
    (event : actual.event = .serve id observed) (served : Served input)
    (present : actual.result.service = some served) (valid : actual.before.work.Valid)
    (item : Theory.Outstanding.Item (Ticket input.active input.passive))
    (member : item ∈ actual.before.work.pending) (selected : item.id = id) : served.ticket = item := by
  obtain ⟨completed, _, ticket, _⟩ := serve_completed actual id observed event served present
  exact ticket.trans (completed.item_eq valid item member selected)

theorem serve_primary_head (actual : Step input)
    (item : Theory.Outstanding.Item (Ticket input.active input.passive))
    (head : actual.before.work.pending.find? (fun ticket => decide (ticket.value.gateway = .primary)) = some item)
    (event : actual.event = .serve item.id none) (served : Served input)
    (present : actual.result.service = some served) (valid : actual.before.work.Valid) :
    served.ticket = item ∧ actual.result.state.outstanding .primary + 1 = actual.before.outstanding .primary := by
  have ticket := serve_ticket_eq actual item.id none event served present valid item
    (List.mem_of_find?_eq_some head) rfl
  refine ⟨ticket, serve_primary_count actual item.id event served present ?_⟩
  rw [ticket]
  exact of_decide_eq_true (List.find?_some
    (p := fun ticket : Theory.Outstanding.Item (Ticket input.active input.passive) =>
      decide (ticket.value.gateway = .primary)) head)

theorem serve_connection (actual : Step input) (id : Nat)
    (observed : Option (List UInt8 × Option (List UInt8)))
    (event : actual.event = .serve id observed) (served : Served input)
    (present : actual.result.service = some served) :
    actual.result.state.connection = actual.before.connection := by
  obtain ⟨_, _, _, _, connection, _⟩ := serve_completed actual id observed event served present
  exact connection

def serviceCustody (before : State input) (served : Served input) : Custody input :=
  match emitted : served.evidence.output with
  | none => before.custody
  | some emission => Theory.PacketCustody.mint before.custody
      (.link before.services.length served emission emitted)

theorem serve_custody (actual : Step input) (id : Nat)
    (observed : Option (List UInt8 × Option (List UInt8)))
    (event : actual.event = .serve id observed) (served : Served input)
    (present : actual.result.service = some served) :
    actual.result.state.custody = serviceCustody actual.before served := by
  obtain ⟨_, _, _, _, _, output, _⟩ := serve_completed actual id observed event served present
  obtain ⟨effect, custody, _, prepared, result⟩ := actual.transaction
  have noOutput : effect.output = none := by simpa only [result] using output
  have service : effect.service = some served := by simpa only [result] using present
  have same : custody = actual.before.custody := by
    simpa only [event, prepareCustody, pure, Except.pure, Except.ok.injEq] using prepared.symm
  simp only [result, finishCustody, noOutput, service, same, serviceCustody]
  rfl

private theorem application_work (before : State input) (actor : Actor)
    (event : Protocol.TCP.ApplicationTrace.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) : effect.state.work = before.work := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

theorem clock_work (actual : Step input) (actor : Actor) (now : Nat)
    (event : actual.event = .advanceClock actor now) : actual.result.state.work = actual.before.work := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  have applied : applyApplication input actual.before actor (.advanceClock now) = .ok effect := by
    simpa only [event, processCore] using computed
  simpa only [result] using application_work _ _ _ _ applied

def isControl : CampusTCPModel.Event → Prop
  | .pause | .stageCheckpoint | .installCheckpoint _ | .switchRoute .. | .fencePrimary | .resume => True
  | _ => False

private theorem transfer_work (before : State input) (event : CampusTCPModel.Event) (effect : Effect input)
    (computed : transferControl input before event = .ok effect) : effect.state.work = before.work := by
  unfold transferControl at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem control_work (actual : Step input) (control : isControl actual.event) :
    actual.result.state.work = actual.before.work := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  have applied : transferControl input actual.before actual.event = .ok effect := by
    cases event : actual.event <;> simp only [event, isControl] at control
    all_goals first
      | contradiction
      | (simpa only [event, processCore] using computed)
  simpa only [result] using transfer_work _ _ _ applied

end Netlib.Check.CampusTCPPrimaryDrain
