import Netlib.Examples.CampusEAP

namespace NetlibTest.CampusEAP

open Netlib Netlib.Network Netlib.Protocol Netlib.Examples

private def anonymous : List UInt8 := [97, 110, 111, 110, 121, 109, 111, 117, 115]
private def token : Credential :=
  ⟨Campus.context.issuer, Campus.context.consumer, Campus.context.producer, [Campus.application], 60, true⟩
private def verified : EAPAuth.Evidence := ⟨1, Campus.context.consumer, 13, true, some "trusted EAP-TLS verifier"⟩
private def exchange : List EAPSession.Event := [
  .authentication .start,
  .authentication (.server (.request 1 1 [])), .authentication (.peer (.response 1 1 anonymous)),
  .authentication (.server (.request 2 13 [0x20])), .authentication (.peer (.response 2 13 [0])),
  .authentication (.server (.success 2))]
private def permitted : List EAPSession.Event := exchange ++ [.authentication (.method verified),
  .application (.install token), .application (.advance 10), .application (.request Campus.application)]
private def missing : List EAPSession.Event := exchange ++
  [.application (.install token), .application (.request Campus.application)]

example : (Netlib.Examples.CampusEAP.run permitted).session.admitted = some Campus.application := by decide

theorem available_under_internal_fault (fault : Fault Campus.Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault) :
    EAPAuth.State.Ready (EAPSession.authContext Campus.context) (Netlib.Examples.CampusEAP.run permitted).auth ∧
      Session.Valid Campus.context (Netlib.Examples.CampusEAP.run permitted).session Campus.application ∧
      (CampusEAP.network (Netlib.Examples.CampusEAP.run permitted) fault).Available Campus.clients Campus.servers :=
  CampusEAP.admission_available permitted (by decide) fault admissible

example (fault : Fault Campus.Node) :
    (CampusEAP.network (Netlib.Examples.CampusEAP.run missing) fault).Isolated Campus.clients Campus.servers :=
  CampusEAP.missing_method_isolated missing fault (by decide)

example (events : List EAPSession.Event) (fault : Fault Campus.Node) :
    (CampusEAP.network (Netlib.Examples.CampusEAP.run events) fault).Isolated Campus.clients Campus.managers :=
  Campus.application_management_isolated _ fault

example (events : List EAPSession.Event) (fault : Fault Campus.Node) :
    (CampusEAP.network (Netlib.Examples.CampusEAP.run events) fault).Mediated Campus.clients Campus.servers Campus.gateways :=
  Campus.application_gateway_mediated _ fault

example (events : List EAPSession.Event) :
    Upgrade.Preserves (EAPSession.step Campus.context) CampusEAP.contract EAPSession.State.initial events :=
  CampusEAP.updates_preserve events

example (events : List EAPSession.Event) (fault : Fault Campus.Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault)
    (path : (CampusEAP.network (Netlib.Examples.CampusEAP.run events) fault).Reachable .client .server) :
    Session.Valid Campus.context (Netlib.Examples.CampusEAP.run events).session Campus.application ∧
      EAPAuth.State.Ready (EAPSession.authContext Campus.context) (Netlib.Examples.CampusEAP.run events).auth :=
  CampusEAP.reachable_has_current_authentication events fault admissible path

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let good := Netlib.Examples.CampusEAP.run permitted
  let absent := Netlib.Examples.CampusEAP.run missing
  ensure (good.auth.authorized && good.session.permits Campus.context Campus.application &&
    good.session.admitted == some Campus.application && good.auth.outerIdentity == some anonymous)
    "Accepted current method evidence and a fresh scoped credential must enable campus application admission."
  ensure (!absent.auth.authorized && !absent.session.permits Campus.context Campus.application && absent.session.admitted.isNone)
    "An otherwise valid campus credential and matched Success must not replace missing method evidence."
  let loggedOff := EAPSession.run Campus.context good [.authentication .logoff, .application (.request Campus.application)]
  ensure (!loggedOff.auth.authorized && !loggedOff.session.permits Campus.context Campus.application &&
    loggedOff.session.admitted.isNone && loggedOff.session.credential.isNone)
    "Logoff must remove the campus session's application permission."
  let wrongSubject := Netlib.Examples.CampusEAP.run (exchange ++ [.authentication (.method { verified with subject := "anonymous" }),
    .application (.install token), .application (.request Campus.application)])
  ensure (!wrongSubject.auth.authorized && wrongSubject.session.admitted.isNone)
    "The campus principal must come from trusted expected-subject evidence rather than outer Identity bytes."
  IO.println "Campus EAP admission tests passed."

end NetlibTest.CampusEAP
