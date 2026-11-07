import Netlib.Check.CampusTCPRecoveryReceipts

/-!
# Actual local receive cases

Application packets and startup controls keep separate source witnesses.
The startup receiver role is resolved by the full report history.
-/

namespace Netlib.Check.CampusTCPReceiveCases

open Protocol.TCP CampusTCPModel

namespace R
export CampusTCPRecoveryReceipts (Delivery LocalAck Source)
end R

variable {input : Input}

private theorem parsed_ok (value : Except String α) (output : α) (computed : parsed value = .ok output) : value = .ok output := by
  cases value <;> simp_all [parsed, Except.mapError]

private theorem cursor_metadata (before : Cursor seed) (event : T.Event) (stamp : Nat) (applied : Applied before)
    (computed : before.apply event stamp = .ok applied) : applied.step.event = event ∧ applied.step.stamp = stamp := by
  unfold Cursor.apply at computed
  split at computed
  · cases computed; exact ⟨rfl, rfl⟩
  · cases computed

private theorem application_metadata (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) :
    ∀ chosen operation, effect.application = some (chosen, operation) →
      chosen = actor ∧ operation.event = event ∧ operation.stamp = before.time := by
  unfold applyApplication at computed
  split at computed
  · cases computed; intro chosen operation recorded; cases recorded
  · cases computed; intro chosen operation recorded; cases recorded
  · cases actor
    all_goals
      simp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed
      split at computed
      · cases computed
      · rename_i applied accepted
        have metadata := cursor_metadata _ event before.time applied (parsed_ok _ _ accepted)
        repeat' first
          | (solve | cases computed; intro chosen operation recorded; cases recorded; exact ⟨rfl, metadata⟩)
          | (cases computed)
          | (split at computed)
          | (dsimp only [bind, Except.bind, pure, Except.pure, parsed, Except.mapError] at computed)

private theorem recovery_application (computed : runRecovery input before event = .ok effect)
    (recorded : effect.application = some (actor, operation)) :
    ∃ control : C.Step input.active input.passive, effect.recovery = some control ∧ control.event = event ∧
      ∃ side, control.result.application = some (side, operation) ∧ Actor.ofRecovery side = actor := by
  unfold runRecovery at computed
  split at computed
  · cases computed; cases recorded
  · cases computed; cases recorded
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals
          subst effect
          dsimp only at recorded
          obtain ⟨⟨side, applied⟩, selected, same⟩ := Option.map_eq_some_iff.mp recorded
          have sameOperation : applied = operation := congrArg Prod.snd same
          subst applied
          exact ⟨_, rfl, rfl, side, selected, congrArg Prod.fst same⟩

private theorem recovery_none (computed : runRecovery input before event = .ok effect)
    (absent : ∀ source bytes path policy, event ≠ .receive source bytes path policy) : effect.application = none := by
  cases recorded : effect.application with
  | none => rfl
  | some pair =>
    obtain ⟨actor, operation⟩ := pair
    obtain ⟨control, _, eventEq, side, applied, _⟩ := recovery_application computed recorded
    obtain ⟨source, bytes, path, policy, received⟩ := control.application_event applied
    exact False.elim (absent source bytes path policy (eventEq.symm.trans received))

private theorem startup_none (computed : startup input before event = .ok effect) : effect.application = none := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem open_none (computed : openRecovering input before remote policy = .ok effect) : effect.application = none := by
  unfold openRecovering at computed
  repeat' first
    | (solve | exact recovery_none computed (by intros; intro impossible; cases impossible))
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem drain_none (computed : finishStartup input before = .ok effect) : effect.application = none := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem ack_metadata (computed : enableAck input before actor = .ok effect) :
    ∀ chosen operation, effect.application = some (chosen, operation) →
      chosen = actor ∧ operation.event = .enableAck ∧ operation.stamp = before.time := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_metadata _ _ _ _ computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem handoff_not_receive (computed : enableStartupRecovery input before actor = .ok effect)
    (recorded : effect.application = some (chosen, operation)) (received : operation.event = .receive packet) : False := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; cases recorded
  · have metadata := application_metadata _ _ _ _ computed chosen operation recorded
    rw [received] at metadata
    cases metadata.2.1

structure ApplicationCase (before : State input) (jointEvent : Event) (effect : Effect input)
    (actor : Actor) (operation : T.Step) (packet : EstablishedReceive.Input) where
  service : Nat
  raw : List UInt8
  policy : Bool
  event : jointEvent = .deliver service raw policy
  receipt : Receipt input
  recorded : effect.receipt = some receipt
  same : receipt.received = packet
  receiver : receipt.actor = actor
  stamp : operation.stamp = before.time
  localRecord : receipt.application = some operation
  sourceActor : Actor
  sourceStep : T.Step
  output : EstablishedReceive.Input
  origin : T.OutputOrigin sourceStep output
  production : receipt.served.ticket.value.produced = .application sourceActor sourceStep output origin

private theorem process_receive (before : State input) (jointEvent : Event) (effect : Effect input)
    (computed : processCore input before jointEvent = .ok effect) (actor : Actor) (operation : T.Step)
    (recorded : effect.application = some (actor, operation)) (packet : EstablishedReceive.Input)
    (received : operation.event = .receive packet) :
    Nonempty (ApplicationCase before jointEvent effect actor operation packet) ∨
      ∃ control : C.Step input.active input.passive, effect.recovery = some control ∧
        ∃ service raw policy, jointEvent = .deliver service raw policy := by
  cases jointEvent with
  | «open» remote policy => rw [startup_none computed] at recorded; cases recorded
  | openRecovering remote policy => rw [open_none computed] at recorded; cases recorded
  | finishStartup => rw [drain_none computed] at recorded; cases recorded
  | startupClock actor millis | startupTimeout actor generation policy =>
    have absent := recovery_none computed (by intros; intro impossible; cases impossible)
    rw [absent] at recorded
    cases recorded
  | write chosen bytes | send chosen count policy | read chosen count | emitAck chosen policy
  | enableRecovery chosen | advanceClock chosen millis | timeout chosen policy | dispatchAck chosen policy =>
    have metadata := application_metadata _ _ _ _ computed actor operation recorded
    rw [received] at metadata
    cases metadata.2.1
  | enableAck chosen =>
    have metadata := ack_metadata computed actor operation recorded
    rw [received] at metadata
    cases metadata.2.1
  | enableStartupRecovery chosen => exact False.elim (handoff_not_receive computed recorded received)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; have absent := startup_none (input := input) (before := before) (by assumption); rw [absent] at recorded; cases recorded)
      | (solve |
        rename_i appliedEffect appliedAt
        have evaluated := appliedAt
        change runRecovery input before _ = .ok appliedEffect at evaluated
        cases computed
        have selected : appliedEffect.application = some (actor, operation) := recorded
        obtain ⟨control, present, _⟩ := recovery_application (input := input) (before := before)
          (effect := appliedEffect) evaluated selected
        exact Or.inr ⟨control, present, index, bytes, policy, rfl⟩)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
    all_goals
      rename_i sourceActor sourceStep output origin production result appliedEffect appliedAt
      have localRecorded : appliedEffect.application = some (actor, operation) := recorded
      have metadata := application_metadata before _ _ appliedEffect appliedAt actor operation localRecorded
      have same := ApplicationTrace.Event.receive.inj (metadata.2.1.symm.trans received)
      refine Or.inl ⟨⟨index, bytes, policy, rfl, _, rfl, same, metadata.1.symm, metadata.2.2, ?_,
        sourceActor, sourceStep, output, origin, production⟩⟩
      · simp only [localRecorded, Option.map_some]
  | authentication index | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id
  | installGuardAt gateway id | assign index ingress | serve id observed | copyPacket id | dropPacket id
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute chosen gateway | fencePrimary | resume =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress, transferControl] at computed
    repeat' first
      | (solve | cases computed; cases recorded)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

inductive Cases (joint : Step input) (actor : Actor) (operation : T.Step) (packet : EstablishedReceive.Input) where
  | application (value : ApplicationCase joint.before joint.event joint.result actor operation packet)
  | recovery (control : C.Step input.active input.passive) (recorded : joint.result.recovery = some control)
      (delivery : R.Delivery joint control) (ack : R.LocalAck delivery actor operation)
      (same : delivery.receipt.received = packet)

theorem Step.receive_cases (joint : Step input) (actor : Actor) (operation : T.Step)
    (recorded : joint.result.application = some (actor, operation)) (packet : EstablishedReceive.Input)
    (received : operation.event = .receive packet) : Nonempty (Cases joint actor operation packet) := by
  obtain ⟨effect, custody, computed, result⟩ := joint.processed
  have selected : effect.application = some (actor, operation) := by simpa only [result] using recorded
  rcases process_receive joint.before joint.event effect computed actor operation selected packet received with application | recovery
  · obtain ⟨value⟩ := application
    exact ⟨.application ⟨value.service, value.raw, value.policy, value.event, value.receipt,
      by simpa only [result] using value.recorded, value.same, value.receiver, value.stamp, value.localRecord,
      value.sourceActor, value.sourceStep, value.output, value.origin, value.production⟩⟩
  · obtain ⟨control, present, service, raw, policy, event⟩ := recovery
    have recordedC : joint.result.recovery = some control := by simpa only [result] using present
    obtain ⟨delivery⟩ := CampusTCPRecoveryReceipts.Step.recovery_delivery joint recordedC event
    obtain ⟨ack⟩ := delivery.local_ack recorded
    have same := ApplicationTrace.Event.receive.inj (ack.ack.2.1.symm.trans received)
    exact ⟨.recovery control recordedC delivery ack same⟩

end Netlib.Check.CampusTCPReceiveCases
