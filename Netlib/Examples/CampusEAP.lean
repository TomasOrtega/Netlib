import Netlib.Examples.Campus
import Netlib.Protocol.EAPSession

/-!
# Campus admission from an EAP session

The guarded EAP method result supplies session authentication.
Credential guards and the existing campus graph then control application reachability.
Cryptography, physical enforcement, and native campus bindings remain assumptions.
-/

namespace Netlib.Examples.CampusEAP

open Network Protocol
abbrev State := EAPSession.State
abbrev Event := EAPSession.Event

def run (events : List Event) : State := EAPSession.run Campus.context EAPSession.State.initial events

def network (state : State) (fault : Fault Campus.Node) : Network Campus.Node :=
  Campus.applicationNetwork state.session fault

theorem run_safe (events : List Event) : (run events).Safe Campus.context :=
  EAPSession.run_safe _ _ _ (EAPSession.initial_safe _)

theorem reachable_has_current_authentication (events : List Event) (fault : Fault Campus.Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault)
    (reachable : (network (run events) fault).Reachable .client .server) :
    Session.Valid Campus.context (run events).session Campus.application ∧
      EAPAuth.State.Ready (EAPSession.authContext Campus.context) (run events).auth := by
  have permitted := (Campus.application_reachable_iff _ fault admissible).mp reachable
  have valid := (Session.permits_iff _ _ _).mp permitted
  obtain ⟨authSafe, coupled, _⟩ := run_safe events
  have authorized : (run events).auth.authorized = true := by
    rw [← coupled]
    exact valid.1
  exact ⟨valid, authSafe authorized⟩

theorem admission_available (events : List Event)
    (admitted : (run events).session.admitted = some Campus.application)
    (fault : Fault Campus.Node) (admissible : singleInternalNode Campus.clients Campus.servers fault) :
    EAPAuth.State.Ready (EAPSession.authContext Campus.context) (run events).auth ∧
      Session.Valid Campus.context (run events).session Campus.application ∧
      (network (run events) fault).Available Campus.clients Campus.servers := by
  obtain ⟨valid, ready⟩ := EAPSession.admitted_valid Campus.context EAPSession.State.initial events Campus.application
    (EAPSession.initial_safe _) admitted
  exact ⟨ready, valid, Campus.permitted_available _ fault admissible ((Session.permits_iff _ _ _).mpr valid)⟩

theorem unauthorized_isolated (events : List Event) (fault : Fault Campus.Node)
    (denied : (run events).auth.authorized = false) :
    (network (run events) fault).Isolated Campus.clients Campus.servers :=
  Campus.denied_isolated _ fault (EAPSession.unauthorized_denied _ _ _ (run_safe events).2.1 denied)

theorem missing_method_isolated (events : List Event) (fault : Fault Campus.Node)
    (missing : (run events).auth.evidence = none) :
    (network (run events) fault).Isolated Campus.clients Campus.servers := by
  apply unauthorized_isolated events fault
  cases authorized : (run events).auth.authorized with
  | false => rfl
  | true =>
    obtain ⟨evidence, found, _⟩ := EAPAuth.authorized_evidence _ _ (run_safe events).1 authorized
    rw [missing] at found
    cases found

def contract (state : State) : Prop :=
  state.Safe Campus.context ∧
    ∀ fault, singleInternalNode Campus.clients Campus.servers fault →
      (network state fault).Isolated Campus.clients Campus.managers ∧
      ((network state fault).Reachable .client .server ↔ state.session.permits Campus.context Campus.application = true)

theorem updates_preserve (events : List Event) :
    Upgrade.Preserves (EAPSession.step Campus.context) contract EAPSession.State.initial events := by
  apply Upgrade.of_invariant
  · intro before event after safe edge
    change EAPSession.step Campus.context before event = after at edge
    subst after
    exact ⟨EAPSession.step_safe _ _ _ safe.1, fun fault admissible =>
      ⟨Campus.application_management_isolated _ fault, Campus.application_reachable_iff _ fault admissible⟩⟩
  · exact ⟨EAPSession.initial_safe _, fun fault admissible =>
      ⟨Campus.application_management_isolated _ fault, Campus.application_reachable_iff _ fault admissible⟩⟩

end Netlib.Examples.CampusEAP
