import Netlib.Examples.Campus

namespace NetlibTest.Campus

open Netlib Netlib.Network Netlib.Protocol Netlib.Examples.Campus

private def token : Credential where
  issuer := context.issuer
  subject := context.consumer
  audience := context.producer
  scopes := [application]
  expiresAt := 60
  integrity := true

private def conversation (credential : Credential) (authenticated : Bool := true) : List Event :=
  [.authenticate authenticated, .install credential, .advance 10, .request application]

private def good : Session := Session.run context Session.initial (conversation token)

example : good.admitted = some application := by decide

example : Session.Valid context good application ∧
    (applicationNetwork good (Fault.node .apA)).Available clients servers := by
  exact run_admission_available (conversation token) (by decide) (Fault.node .apA)
    (singleInternalNode_node (sources := clients) (targets := servers) Node.apA
      (by simp [clients]) (by simp [servers]))

example : Session.Valid context good application ∧
    (applicationNetwork good (Fault.node .gatewayB)).Available clients servers := by
  exact trace_admission_available (Session.transition_run context Session.initial (conversation token))
    (by decide) (Fault.node .gatewayB)
    (singleInternalNode_node (sources := clients) (targets := servers) Node.gatewayB
      (by simp [clients]) (by simp [servers]))

example (events : List Event) :
    Upgrade.Preserves (Session.step context) sessionContract Session.initial events :=
  session_updates_preserve events

private def bypass : Network Node :=
  Network.union base ⟨fun a b => a = .client ∧ b = .server⟩

/-- A direct link defeats denial when it avoids both gateways. -/
example : (ZeroTrust.enforce bypass gateways (Session.policy context Session.initial) request).Reachable
    .client .server := by
  apply Reachable.single
  refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
  intro incident
  simp [gateways] at incident

private def bothAccessPoints : Fault Node :=
  ⟨fun node => node = .apA ∨ node = .apB, fun _ _ => False⟩

example : ¬(base.afterFault bothAccessPoints).Reachable .client .server := by
  intro path
  cases path with
  | @step _ next _ edge _ =>
    have failed : bothAccessPoints.nodes next := by
      simpa [base, Network.union, access, distribution, bothAccessPoints] using edge.1
    exact edge.2.2.1 failed

private def checkThat (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  checkThat (good.permits context application) "The supplied valid session did not permit access."
  checkThat (good.admitted == some application) "The accepted application request was not recorded."
  let expired := Session.run context good [.advance 60, .request application]
  checkThat (!expired.permits context application && expired.admitted.isNone)
    "An expired token preserved application access."
  let revoked := Session.run context good [.revoke, .request application]
  checkThat (!revoked.permits context application && revoked.admitted.isNone)
    "Revocation preserved application access."
  let wrongAudience := Session.run context Session.initial
    (conversation { token with audience := "another-service" })
  checkThat (!wrongAudience.permits context application && wrongAudience.admitted.isNone)
    "A token for another service permitted access."
  let wrongIdentity := Session.run context Session.initial (conversation token false)
  checkThat (!wrongIdentity.permits context application && wrongIdentity.admitted.isNone)
    "A failed identity observation permitted access."
  let badIntegrity := Session.run context Session.initial (conversation { token with integrity := false })
  checkThat (!badIntegrity.permits context application && badIntegrity.admitted.isNone)
    "A failed integrity observation permitted access."
  let closed := Session.run context good [.close, .request application]
  checkThat (!closed.permits context application && closed.admitted.isNone)
    "A closed session preserved application access."
  IO.println "Campus composition tests passed."

end NetlibTest.Campus
