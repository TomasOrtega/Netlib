import Netlib.Check.CampusTCPRoundClock
import Netlib.Check.CampusTCPRoundEnvironment

/-!
# State frames across actual clock slots

Each clock slot keeps packet and gateway state fixed.
The local cursor history and global slot number can grow.
-/

namespace Netlib.Check.CampusTCPRoundStutter

open CampusTCPModel CampusTCPEnabled

variable {input : Input} {events : List Event}
variable {complete : H.Completed input.active input.passive}
variable {before middle after : State input}
variable {endpoints next last : Applications complete}

def snapshot (state : State input) : State input :=
  { state with time := 0, connection := .startup .idle rfl }

structure Frame (before : State input) (endpoints : Applications complete)
    (after : State input) (updated : Applications complete) : Prop where
  beforeConnection : before.connection = .application complete endpoints
  afterConnection : after.connection = .application complete updated
  fixed : snapshot before = snapshot after
  endpointEq : ∀ actor, endpoint updated actor = endpoint endpoints actor

theorem Frame.refl (state : State input) (endpoints : Applications complete)
    (connection : state.connection = .application complete endpoints) : Frame state endpoints state endpoints :=
  ⟨connection, connection, rfl, fun _ => rfl⟩

theorem Frame.trans (first : Frame before endpoints middle next) (second : Frame middle next after last) :
    Frame before endpoints after last :=
  ⟨first.beforeConnection, second.afterConnection, first.fixed.trans second.fixed,
    fun actor => (second.endpointEq actor).trans (first.endpointEq actor)⟩

theorem Frame.work (frame : Frame before endpoints after next) : after.work = before.work :=
  (congrArg State.work frame.fixed).symm

theorem Frame.outputs (frame : Frame before endpoints after next) : after.outputs = before.outputs :=
  (congrArg State.outputs frame.fixed).symm

theorem Frame.services (frame : Frame before endpoints after next) : after.services = before.services :=
  (congrArg State.services frame.fixed).symm

theorem Frame.receipts (frame : Frame before endpoints after next) : after.receipts = before.receipts :=
  (congrArg State.receipts frame.fixed).symm

theorem Frame.custody (frame : Frame before endpoints after next) : after.custody = before.custody :=
  (congrArg State.custody frame.fixed).symm

theorem Frame.primary (frame : Frame before endpoints after next) : after.primary = before.primary :=
  (congrArg State.primary frame.fixed).symm

theorem Frame.standby (frame : Frame before endpoints after next) : after.standby = before.standby :=
  (congrArg State.standby frame.fixed).symm

theorem Frame.authentication (frame : Frame before endpoints after next) : after.authentication = before.authentication :=
  (congrArg State.authentication frame.fixed).symm

theorem Frame.owners (frame : Frame before endpoints after next) : after.owners = before.owners :=
  (congrArg State.owners frame.fixed).symm

theorem Frame.routeEpoch (frame : Frame before endpoints after next) : after.routeEpoch = before.routeEpoch :=
  (congrArg State.routeEpoch frame.fixed).symm

theorem Frame.assignmentPaused (frame : Frame before endpoints after next) : after.assignmentPaused = before.assignmentPaused :=
  (congrArg State.assignmentPaused frame.fixed).symm

theorem Frame.primarySealed (frame : Frame before endpoints after next) : after.primarySealed = before.primarySealed :=
  (congrArg State.primarySealed frame.fixed).symm

theorem Frame.primaryFenced (frame : Frame before endpoints after next) : after.primaryFenced = before.primaryFenced :=
  (congrArg State.primaryFenced frame.fixed).symm

theorem Frame.checkpoints (frame : Frame before endpoints after next) : after.checkpoints = before.checkpoints :=
  (congrArg State.checkpoints frame.fixed).symm

theorem Frame.cache (frame : Frame before endpoints after next) : after.cache = before.cache :=
  (congrArg State.cache frame.fixed).symm

theorem Frame.installation (frame : Frame before endpoints after next) : after.installation = before.installation :=
  (congrArg State.installation frame.fixed).symm

theorem Frame.resident (frame : Frame before endpoints after next) (gateway : Gateway) :
    after.resident gateway = before.resident gateway := by
  cases gateway
  · exact frame.primary
  · exact frame.standby

theorem Frame.beforeService (frame : Frame before endpoints after next) (gateway : Gateway) :
    CampusTCPModel.beforeService input after gateway = CampusTCPModel.beforeService input before gateway :=
  (congrArg (fun state => CampusTCPModel.beforeService input state gateway) frame.fixed).symm

theorem Frame.environment (frame : Frame before endpoints after next) :
    CampusTCPRoundEnvironment.environment after = CampusTCPRoundEnvironment.environment before :=
  (congrArg CampusTCPRoundEnvironment.environment frame.fixed).symm

theorem Step.frame (actual : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : actual.before.connection = .application complete endpoints)
    (actor : Actor) (event : actual.event = .advanceClock actor (endpoint endpoints actor).now)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < actual.before.time)
    (coherent : Protocol.TCP.Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Protocol.TCP.Endpoint.AckPrepared (endpoint endpoints actor))
    (runtime : (endpoint endpoints actor).recovery.isSome = true) :
    ∃ updated : Applications complete, Frame actual.before endpoints actual.result.state updated := by
  obtain ⟨value, same⟩ := CampusTCPRoundClock.Step.same_clock actual complete endpoints connection actor event
    earlier coherent prepared runtime
  have final := value.stateEq
  rw [same] at final
  refine ⟨value.after, connection, ?_, ?_, ?_⟩
  · rw [final]
  · rw [final]
    rfl
  · intro receiver
    by_cases selected : receiver = actor
    · subst receiver
      exact value.selected
    · have peer : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
      rw [peer]
      exact value.peer

theorem Report.frame (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actual : Step input) (before : actual.before = report.final)
    (actor : Actor) (event : actual.event = .advanceClock actor (endpoint endpoints actor).now)
    (coherent : Protocol.TCP.Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Protocol.TCP.Endpoint.AckPrepared (endpoint endpoints actor))
    (runtime : (endpoint endpoints actor).recovery.isSome = true) :
    ∃ updated : Applications complete, Frame report.final endpoints actual.result.state updated := by
  have bounds := CampusTCPChronology.Report.application_before report complete endpoints connection
  have earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < actual.before.time := by
    rw [before]
    cases actor
    · exact bounds.1
    · exact bounds.2
  obtain ⟨updated, frame⟩ := Step.frame actual complete endpoints (before.symm ▸ connection) actor event
    earlier coherent prepared runtime
  exact ⟨updated, before ▸ frame⟩

structure ClockAppend (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (actual : Step input) where
  next : Report input (events ++ [actual.event])
  supported : next.supported = true
  finished : next.remaining = []
  history : next.steps = report.steps ++ [actual]
  final : next.final = actual.result.state
  updated : Applications complete
  frame : Frame report.final endpoints next.final updated

theorem Report.append_clock (report : Report input events) (supported : report.supported = true)
    (finished : report.remaining = []) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actual : Step input) (before : actual.before = report.final)
    (actor : Actor) (event : actual.event = .advanceClock actor (endpoint endpoints actor).now)
    (coherent : Protocol.TCP.Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Protocol.TCP.Endpoint.AckPrepared (endpoint endpoints actor))
    (runtime : (endpoint endpoints actor).recovery.isSome = true) :
    Nonempty (ClockAppend report complete endpoints actual) := by
  have bounds := CampusTCPChronology.Report.application_before report complete endpoints connection
  have earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < actual.before.time := by
    rw [before]
    cases actor
    · exact bounds.1
    · exact bounds.2
  obtain ⟨value, same⟩ := CampusTCPRoundClock.Step.same_clock actual complete endpoints
    (before.symm ▸ connection) actor event earlier coherent prepared runtime
  have actualSupported : actual.result.supported = true := same ▸ value.supported
  let next := CampusTCPSchedule.Report.appendStep report supported finished actual before actualSupported
  obtain ⟨updated, frame⟩ := Report.frame report complete endpoints connection actual before actor event
    coherent prepared runtime
  exact ⟨⟨next, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl, rfl, rfl, updated, frame⟩⟩

end Netlib.Check.CampusTCPRoundStutter
