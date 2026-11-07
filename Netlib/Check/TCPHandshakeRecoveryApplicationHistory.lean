import Netlib.Check.TCPHandshakeRecoveryFacts

/-!
# Actual early endpoint operations

Each side's current history is the projection of the same recovery trace.
Every local ACK operation retains its actual receipt and earlier output source.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : Handshake.Local}
variable {startState final : State active passive} {events : List Event} {steps : List (Step active passive)}

theorem Trace.application_steps (trace : Trace startState events steps final) (actor : Side) :
    final.applicationSteps actor = startState.applicationSteps actor ++
      steps.filterMap (fun actual => applicationFor actor actual.result.application) := by
  induction trace with
  | done => simp
  | next actual tail ih =>
    rw [ih, actual.application_steps actor]
    cases selected : applicationFor actor actual.result.application <;> simp [selected, List.append_assoc]

theorem Trace.initial_application_steps (trace : Trace .initial events steps final) (actor : Side) :
    final.applicationSteps actor = steps.filterMap (fun actual => applicationFor actor actual.result.application) := by
  simpa only [State.initial, State.applicationSteps, List.nil_append] using trace.application_steps actor

theorem Reachable.application_steps (value : Reachable final) (actor : Side) :
    final.applicationSteps actor = value.steps.filterMap (fun actual => applicationFor actor actual.result.application) :=
  value.trace.initial_application_steps actor

theorem Reachable.acknowledged_application_steps (value : Reachable final)
    (current : final.phase = .acknowledged ready client) :
    client.steps = value.steps.filterMap (fun actual => applicationFor .active actual.result.application) := by
  simpa only [State.applicationSteps, current] using value.application_steps .active

theorem Reachable.complete_application_steps (value : Reachable final) {certificate : O.Completed active passive}
    {client : PreData certificate.certificate.activeSeed} {server : PreData certificate.certificate.passiveSeed}
    (current : final.phase = .complete certificate client server) :
    client.steps = value.steps.filterMap (fun actual => applicationFor .active actual.result.application) ∧
      server.steps = value.steps.filterMap (fun actual => applicationFor .passive actual.result.application) := by
  constructor
  · simpa only [State.applicationSteps, current] using value.application_steps .active
  · simpa only [State.applicationSteps, current] using value.application_steps .passive

private theorem applicationFor_some (selected : applicationFor actor record = some operation) :
    record = some (actor, operation) := by
  cases record with
  | none => cases selected
  | some pair =>
    obtain ⟨side, retained⟩ := pair
    by_cases same : side = actor
    · subst side
      simp only [applicationFor, Option.bind_some, ite_true, Option.some.injEq] at selected
      subst retained
      rfl
    · simp only [applicationFor, Option.bind_some, same, ite_false, reduceCtorEq] at selected

structure ApplicationOrigin (state : State active passive) (steps : List (Step active passive))
    (actor : Side) (operation : A.Step) where
  receipt : Receipt
  origin : ReceiptOrigin steps receipt
  selected : origin.actual.result.application = some (actor, operation)
  receiver : receipt.actor = actor
  ack : AckOperation receipt.delivery.input origin.actual.index operation
  source : state.source receipt.source.index = some receipt.source

theorem Trace.application_origin (trace : Trace .initial events steps final)
    (member : operation ∈ final.applicationSteps actor) : Nonempty (ApplicationOrigin final steps actor operation) := by
  rw [trace.initial_application_steps actor] at member
  obtain ⟨actual, retained, selected⟩ := List.mem_filterMap.mp member
  have localRecord := applicationFor_some selected
  obtain ⟨receipt, received, receiver, ack⟩ := actual.application_receipt localRecord
  obtain ⟨prior, later, history, preceding, _⟩ := trace.cut actual retained
  have sourceMember : receipt.source ∈ actual.before.emissions :=
    List.mem_of_find?_eq_some (actual.records.source receipt received)
  obtain ⟨producer, earlier, produced, sourceIndex⟩ := preceding.emission_origin sourceMember
  have receiptMember : receipt ∈ final.receipts := by
    rw [trace.receipts]
    change receipt ∈ [] ++ steps.filterMap (·.result.receipt)
    exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨actual, retained, received⟩)
  exact ⟨⟨receipt, ⟨prior, actual, later, history, received, actual.records.receiptIndex receipt received,
    producer, earlier, produced, sourceIndex⟩, localRecord, receiver, ack,
    (trace.history History.initial).source receipt receiptMember⟩⟩

theorem Reachable.application_origin (value : Reachable final) (member : operation ∈ final.applicationSteps actor) :
    Nonempty (ApplicationOrigin final value.steps actor operation) := value.trace.application_origin member

theorem ApplicationOrigin.fields (value : ApplicationOrigin final steps actor operation) :
    Handshake.Profile value.receipt.delivery.input 16 ∧
      operation.event = .receive value.receipt.delivery.input ∧
      operation.result.decision = .accepted (.receive 0 0) ∧ operation.result.output = none ∧
      operation.result.read = [] ∧ operation.stamp = value.origin.actual.index :=
  ⟨value.ack.1, value.ack.2.1, value.ack.2.2.2.2.2⟩

theorem ApplicationOrigin.source_earlier (value : ApplicationOrigin final steps actor operation) :
    value.origin.producer.index < operation.stamp := by
  rw [value.fields.2.2.2.2.2]
  exact value.origin.source_earlier

end Netlib.Check.TCPHandshakeRecovery
