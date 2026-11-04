import Netlib.Examples.EAPDeployment

namespace NetlibTest.EAPDeployment

open Netlib Netlib.Network Netlib.Protocol Netlib.Examples

theorem checked_admission_under_internal_fault {context : Context} {initial : EAPSession.State}
    {observations : List Check.EAP.Observation} (report : Check.EAP.Report context initial observations)
    (safe : initial.Safe context) (compliant : report.compliant = true)
    (finding : Check.EAP.Finding) (member : finding ∈ report.findings)
    (event : finding.observation.event = .application (.request Campus.application))
    (accepted : finding.observation.accepted = some true)
    (fault : Fault Campus.Node) (admissible : singleInternalNode Campus.clients Campus.servers fault) :
    EAPAuth.State.Ready (EAPSession.authContext context) finding.result.auth ∧
      Session.Valid context finding.result.session Campus.application ∧
      (Examples.EAPDeployment.network context finding.result fault).Available Campus.clients Campus.servers :=
  Examples.EAPDeployment.observed_admission_available report safe compliant finding member event accepted fault admissible

example (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node) :
    (Examples.EAPDeployment.network context state fault).Isolated Campus.clients Campus.managers :=
  Examples.EAPDeployment.management_isolated context state fault

example (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node) :
    (Examples.EAPDeployment.network context state fault).Mediated Campus.clients Campus.servers Campus.gateways :=
  Examples.EAPDeployment.gateway_mediated context state fault

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def prove (proposition : Prop) [Decidable proposition] (message : String) : IO (PLift proposition) :=
  if proof : proposition then pure ⟨proof⟩ else throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def synthetic (index : Nat) (event : EAPSession.Event) (accepted : Option Bool := none) : Check.EAP.Observation :=
  ⟨index, event, none, accepted, none, Lean.Json.mkObj [("source", .str "synthetic application unit test")]⟩

def run : IO Unit := do
  let input ← unwrap (Check.EAP.Input.parse (← IO.FS.readFile "examples/eap/success.json"))
  ensure (input.context.consumer == "alice@campus.example.test" && input.context.consumer != Campus.context.consumer)
    "The deployment test must use the captured certificate principal rather than the old campus constant."
  ensure (input.observations.all fun observation => match observation.event with
    | .application _ => false
    | _ => true) "Native EAP evidence must not claim an application request or credential installation."
  let nativePrefix := input.observations.take 18
  let checkpoint := Check.EAP.audit input.context EAPSession.State.initial nativePrefix
  ensure (checkpoint.compliant && checkpoint.final.auth.authorized && checkpoint.final.session.credential.isNone &&
      checkpoint.final.auth.evidence.any (fun evidence => evidence.subject == input.context.consumer) &&
      checkpoint.final.auth.outerIdentity != some input.context.consumer.toUTF8.toList)
    "The native positive checkpoint must bind the certificate subject while retaining an independent anonymous outer Identity."
  let ⟨missing⟩ ← prove (checkpoint.final.session.credential = none) "The native checkpoint must have no application credential."
  have isolated := Examples.EAPDeployment.without_credential_isolated input.context checkpoint.final Fault.none missing
  have _ : ¬(Examples.EAPDeployment.network input.context checkpoint.final Fault.none).Reachable .client .server :=
    isolated _ _ rfl rfl
  let token : Credential := ⟨input.context.issuer, input.context.consumer, input.context.producer,
    [Campus.application], 60, true⟩
  let syntheticEvents := nativePrefix ++ [synthetic 18 (.application (.install token)),
    synthetic 19 (.application (.request Campus.application)) (some true)]
  let report := Check.EAP.audit input.context EAPSession.State.initial syntheticEvents
  let ⟨compliant⟩ ← prove (report.compliant = true) "The explicitly synthetic application observations must match the guarded session."
  let attached ← match report.findings.attach.getLast? with
    | some finding => pure finding
    | none => throw (IO.userError "The synthetic request finding is missing.")
  let finding := attached.val
  have member : finding ∈ report.findings := attached.property
  let ⟨event⟩ ← prove (finding.observation.event = .application (.request Campus.application))
    "The final synthetic event must request the campus application."
  let ⟨accepted⟩ ← prove (finding.observation.accepted = some true) "The synthetic request must carry its explicit acceptance observation."
  let ⟨_, _, available⟩ := Examples.EAPDeployment.observed_admission_available report
    (EAPSession.initial_safe _) compliant finding member event accepted Fault.none
    (singleInternalNode_none _ _)
  have _ : (Examples.EAPDeployment.network input.context finding.result Fault.none).Reachable .client .server :=
    available _ _ rfl rfl
  ensure (finding.result.session.admitted == some Campus.application &&
      finding.result.session.permits input.context Campus.application)
    "Only the explicit synthetic credential and application request should exercise the generic deployment theorem."
  let foreign := EAPSession.run input.context checkpoint.final [
    .application (.install { token with subject := Campus.context.consumer }),
    .application (.request Campus.application)]
  ensure (foreign.auth.authorized && foreign.session.admitted.isNone &&
      !foreign.session.permits input.context Campus.application)
    "A credential for the old campus constant must not grant the captured principal's application request."
  IO.println "Checked EAP deployment tests passed."

end NetlibTest.EAPDeployment
