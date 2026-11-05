import Netlib.Protocol.EAPAuth
import Netlib.Protocol.Transition

/-!
# EAP-derived session authentication

Only the guarded EAP authorization state controls session authentication.
Application events cannot set that Boolean directly.
Method results and credential integrity remain supplied evidence.
-/

namespace Netlib.Protocol.EAPSession

def authContext (context : Context) : EAPAuth.Context := { subject := context.consumer }

structure State where
  auth : EAPAuth.State
  session : Session
  deriving Repr, DecidableEq

def State.initial : State := ⟨EAPAuth.State.initial, Session.initial⟩

inductive ApplicationEvent where
  | install (credential : Credential)
  | advance (now : Nat)
  | request (scope : Scope)
  | revoke
  deriving Repr, DecidableEq

def ApplicationEvent.toSession : ApplicationEvent → Protocol.Event
  | .install credential => .install credential
  | .advance now => .advance now
  | .request scope => .request scope
  | .revoke => .revoke

inductive Event where
  | authentication (event : EAPAuth.Event)
  | application (event : ApplicationEvent)
  | close
  deriving Repr, DecidableEq

def synchronize (context : Context) (before : State) (after : EAPAuth.State) : State :=
  ⟨after, if before.auth.round = after.round ∧ before.auth.authorized = after.authorized then before.session
    else Session.step context before.session (.authenticate after.authorized)⟩

def step (context : Context) (state : State) : Event → State
  | .authentication event => synchronize context state (EAPAuth.step (authContext context) state.auth event)
  | .application event => { state with session := Session.step context state.session event.toSession }
  | .close => synchronize context state (EAPAuth.step (authContext context) state.auth .disconnect)

def State.Coupled (state : State) : Prop := state.session.authenticated = state.auth.authorized

def State.Safe (context : Context) (state : State) : Prop :=
  EAPAuth.State.Safe (authContext context) state.auth ∧ state.Coupled ∧ Session.Safe context state.session

theorem initial_safe (context : Context) : State.Safe context State.initial := by
  exact ⟨EAPAuth.initial_safe _, rfl, Session.initial_safe _⟩

theorem synchronize_coupled (context : Context) (before : State) (after : EAPAuth.State)
    (coupled : before.Coupled) : (synchronize context before after).Coupled := by
  unfold synchronize State.Coupled
  split
  · rename_i same
    exact coupled.trans same.2
  · rfl

theorem synchronize_session_safe (context : Context) (before : State) (after : EAPAuth.State)
    (safe : Session.Safe context before.session) : Session.Safe context (synchronize context before after).session := by
  unfold synchronize
  split
  · exact safe
  · exact Session.step_safe _ _ _

theorem synchronize_resets (context : Context) (before : State) (after : EAPAuth.State)
    (changed : before.auth.round ≠ after.round ∨ before.auth.authorized ≠ after.authorized) :
    (synchronize context before after).session.credential = none ∧
      (synchronize context before after).session.admitted = none := by
  have different : ¬(before.auth.round = after.round ∧ before.auth.authorized = after.authorized) := by
    rintro ⟨round, authorized⟩
    rcases changed with changed | changed
    · exact changed round
    · exact changed authorized
  simp [synchronize, different, Session.step]

theorem step_safe (context : Context) (state : State) (event : Event) (safe : state.Safe context) :
    (step context state event).Safe context := by
  rcases safe with ⟨authSafe, coupled, sessionSafe⟩
  cases event with
  | authentication event =>
    exact ⟨EAPAuth.step_safe _ _ _ authSafe, synchronize_coupled _ _ _ coupled,
      synchronize_session_safe _ _ _ sessionSafe⟩
  | close =>
    exact ⟨EAPAuth.step_safe _ _ _ authSafe, synchronize_coupled _ _ _ coupled,
      synchronize_session_safe _ _ _ sessionSafe⟩
  | application event =>
    refine ⟨authSafe, ?_, Session.step_safe _ _ _⟩
    cases event <;> simpa [step, ApplicationEvent.toSession, State.Coupled, Session.step] using coupled

def run (context : Context) (initial : State) (events : List Event) : State := events.foldl (step context) initial

theorem run_safe (context : Context) (initial : State) (events : List Event) (safe : initial.Safe context) :
    (run context initial events).Safe context := by
  induction events generalizing initial with
  | nil => exact safe
  | cons event events ih => exact ih (step context initial event) (step_safe context initial event safe)

theorem unauthorized_denied (context : Context) (state : State) (scope : Scope)
    (coupled : state.Coupled) (denied : state.auth.authorized = false) : state.session.permits context scope = false := by
  have authenticated : state.session.authenticated = false := coupled.trans denied
  simp [Session.permits, authenticated]

theorem admitted_valid (context : Context) (initial : State) (events : List Event) (scope : Scope)
    (safe : initial.Safe context) (admitted : (run context initial events).session.admitted = some scope) :
    Session.Valid context (run context initial events).session scope ∧
      EAPAuth.State.Ready (authContext context) (run context initial events).auth := by
  obtain ⟨authSafe, coupled, sessionSafe⟩ := run_safe context initial events safe
  have valid := (Session.permits_iff _ _ _).mp (sessionSafe scope admitted)
  have authorized : (run context initial events).auth.authorized = true := by
    rw [← coupled]
    exact valid.1
  exact ⟨valid, authSafe authorized⟩

def transition (context : Context) : Transition State Event := Transition.ofFunction (step context)

theorem transition_safe (context : Context) : (transition context).Invariant (State.Safe context) := by
  intro before event after safe edge
  change step context before event = after at edge
  subst after
  exact step_safe context before event safe

private theorem synchronize_session_trace (context : Context) (before : State) (after : EAPAuth.State) :
    ∃ events, (Session.transition context).Trace before.session events (synchronize context before after).session := by
  unfold synchronize
  split
  · exact ⟨[], .nil _⟩
  · exact ⟨[.authenticate after.authorized], .cons rfl (.nil _)⟩

theorem step_session_trace (context : Context) (state : State) (event : Event) :
    ∃ events, (Session.transition context).Trace state.session events (step context state event).session := by
  cases event with
  | authentication event => exact synchronize_session_trace _ _ _
  | close => exact synchronize_session_trace _ _ _
  | application event => exact ⟨[event.toSession], .cons rfl (.nil _)⟩

theorem run_session_trace (context : Context) (initial : State) (events : List Event) :
    ∃ projected, (Session.transition context).Trace initial.session projected (run context initial events).session := by
  induction events generalizing initial with
  | nil => exact ⟨[], .nil _⟩
  | cons event events ih =>
    obtain ⟨head, first⟩ := step_session_trace context initial event
    obtain ⟨tail, rest⟩ := ih (step context initial event)
    exact ⟨head ++ tail, first.append rest⟩

end Netlib.Protocol.EAPSession
