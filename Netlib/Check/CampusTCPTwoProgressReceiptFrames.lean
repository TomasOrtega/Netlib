import Netlib.Check.CampusTCPRecoveryRoundOrigins

/-!
# Receipt frames from the actual event

Only a delivery can record a new receipt.
The other event branches retain an empty receipt result.
-/

namespace Netlib.Check.CampusTCPTwoProgressReceiptFrames

open Protocol.TCP CampusTCPModel CampusTCPEnabled

variable {input : Input}

def NonDelivery : Event → Prop
  | .deliver .. => False
  | _ => True

private theorem application_none (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) : effect.receipt = none := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, parsed, Except.mapError] at computed)

private theorem startup_none (before : State input) (event : TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : effect.receipt = none := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enableAck_none (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) : effect.receipt = none := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_none _ _ _ _ computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_none (before : State input) (event : C.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) : effect.receipt = none := by
  unfold runRecovery at computed
  cases connection : before.connection with
  | startup stage pending | application complete endpoints =>
    simp only [connection] at computed
    cases computed
    rfl
  | recovering current =>
    simp only [connection] at computed
    split at computed
    · cases computed
    · split at computed <;> cases computed <;> rfl

private theorem openRecovery_none (before : State input) (remote : Handshake.Socket) (policy : Bool)
    (effect : Effect input) (computed : openRecovering input before remote policy = .ok effect) : effect.receipt = none := by
  unfold openRecovering at computed
  repeat' first
    | (solve | exact recovery_none _ _ _ computed)
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem finishStartup_none (before : State input) (effect : Effect input)
    (computed : finishStartup input before = .ok effect) : effect.receipt = none := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem startupRecovery_none (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableStartupRecovery input before actor = .ok effect) : effect.receipt = none := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; rfl
  · exact application_none _ _ _ _ computed

private theorem process_none (before : State input) (event : Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) (nonDelivery : NonDelivery event) : effect.receipt = none := by
  cases event with
  | «open» remote policy => exact startup_none _ _ _ computed
  | openRecovering remote policy => exact openRecovery_none _ _ _ _ computed
  | startupClock actor millis | startupTimeout actor generation policy => exact recovery_none _ _ _ computed
  | finishStartup => exact finishStartup_none _ _ computed
  | enableStartupRecovery actor => exact startupRecovery_none _ _ _ computed
  | write actor bytes | send actor count policy | read actor count | emitAck actor policy | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_none _ _ _ _ computed
  | enableAck actor => exact enableAck_none _ _ _ computed
  | deliver index bytes policy => cases nonDelivery
  | authentication index | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id | assign index ingress | serve id observed | copyPacket id | dropPacket id | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress, transferControl] at computed
    repeat' first
      | (solve | cases computed; rfl)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.receipt_none (actual : Step input) (nonDelivery : NonDelivery actual.event) : actual.result.receipt = none := by
  obtain ⟨effect, custody, computed, same⟩ := actual.processed
  simpa only [same] using process_none actual.before actual.event effect computed nonDelivery

theorem Step.receipt_event (actual : Step input) (receipt : Receipt input) (recorded : actual.result.receipt = some receipt) :
    ∃ index bytes policy, actual.event = .deliver index bytes policy := by
  cases event : actual.event
  all_goals first
    | exact ⟨_, _, _, rfl⟩
    | have absent := Step.receipt_none actual (by rw [event]; trivial)
      rw [absent] at recorded
      cases recorded

end Netlib.Check.CampusTCPTwoProgressReceiptFrames
