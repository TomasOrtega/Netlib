import Netlib.Examples.SessionFirewallDeployment

namespace NetlibTest.SessionFirewallDeployment

open Netlib Packet Protocol
open Netlib.Examples.SessionFirewallDeployment

private def context : Context := ⟨"alice@campus.example.test", "campus-application", "campus-authority"⟩
private def scope : Scope := ⟨"reports", "read"⟩
private def token : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 60, true⟩
private def authentication : List EAPSession.Event := [
  .authentication .begin,
  .authentication (.server (.request 7 13 [32])), .authentication (.peer (.response 7 13 [0])),
  .authentication (.server (.success 7)),
  .authentication (.method ⟨1, context.consumer, 13, true, some "SYNTHETIC trusted method result"⟩),
  .application (.install token)]
private def active : EAPSession.State := EAPSession.run context EAPSession.State.initial authentication

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 32000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def cached : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def oldInput : ConntrackLifecycle.Input := ⟨0, original, none⟩
private def routes : List (Routing.Entry String) := [Routing.defaultRoute (some "egress")]
private def service : Match := {
  source := some ⟨original.source, 32⟩
  destination := some ⟨wire.destination, 32⟩
  protocol := some Packet.Protocol.udp
  destinationPorts := some (PortRange.single wire.destinationPort) }
private def requirement : Compile.SessionFirewall.Intent := ⟨"REPORTS-READ", scope, service⟩
private def requirements : List Compile.SessionFirewall.Intent := [requirement]

example : active.Safe context := EAPSession.run_safe _ _ _ (EAPSession.initial_safe _)
example : active.auth.authorized = true ∧ active.session.permits context scope = true := by decide
example : cached.Valid := (ConntrackLifecycle.State.check_correct _).mp (by decide)

example (compiled : Compile.SessionFirewall.Certified context active requirements)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input)
    (outcome : ConntrackLifecycle.Outcome) (packet : Header)
    (accepted : ConntrackLifecycle.step (pipeline compiled routes [] .permit) tracker input = .ok outcome)
    (output : outcome.output = some packet) (matched : requirement.test.Holds outcome.afterDestination) :
    Session.Valid context active.session scope ∧ EAPAuth.State.Ready (EAPSession.authContext context) active.auth :=
  output_matching_scope_valid compiled (EAPSession.run_safe _ _ _ (EAPSession.initial_safe _)) _
    (pipeline_equivalent compiled routes [] .permit) tracker input outcome packet accepted output requirement (by simp [requirements]) matched

example (before : EAPSession.State) (safe : before.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context before (.authentication .logoff)) requirements)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input) (outcome : ConntrackLifecycle.Outcome)
    (accepted : ConntrackLifecycle.step (pipeline compiled routes [] .permit) tracker input = .ok outcome) :
    outcome.output = none := postlogoff_output_none context before safe compiled _
      (pipeline_equivalent compiled routes [] .permit) tracker input outcome accepted

example (compiled : Compile.SessionFirewall.Certified context active requirements)
    (before : BufferedLifecycle.State) (input : ConntrackLifecycle.Input) (result : BufferedLifecycle.Result) (packet : Header)
    (accepted : BufferedLifecycle.step before (.operation (.packet ⟨pipeline compiled routes [] .permit, input⟩)) = .ok result)
    (admitted : packet ∈ result.admitted) :
    ∃ outcome, ConntrackLifecycle.step (pipeline compiled routes [] .permit) before.tracker input = .ok outcome ∧
      outcome.output = some packet ∧ ∃ selected ∈ requirements, selected.test.Holds outcome.afterDestination ∧
        Session.Valid context active.session selected.scope ∧ EAPAuth.State.Ready (EAPSession.authContext context) active.auth :=
  buffered_admission_current_permission compiled (EAPSession.run_safe _ _ _ (EAPSession.initial_safe _)) _
    (pipeline_equivalent compiled routes [] .permit) before input result packet accepted admitted

private def build (state : EAPSession.State) : IO (Compile.SessionFirewall.Certified context state requirements) :=
  match Compile.SessionFirewall.compile context state requirements with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError error.describe)

private def load (value : Except ConntrackLifecycle.Error α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error.describe)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def checkedNativeSnapshot (firewall : Lean.Json) : IO Unit := do
  let object := Lean.Json.mkObj
  let native ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/eap/success.json"))
  let events ← unwrap ((← unwrap (native.getObjVal? "events")).getArr?)
  let scope := object [("resource", .str scope.resource), ("operation", .str scope.operation)]
  let credential := object [
    ("issuer", .str context.issuer), ("subject", .str context.consumer), ("audience", .str context.producer),
    ("scopes", Lean.toJson [scope]), ("expiresAt", Lean.toJson (60 : Nat)), ("integrity", .bool true)]
  let install := object [("type", .str "install"), ("credential", credential), ("authorized", .bool true)]
  let authentication := native.setObjVal! "events" (.arr ((events.toList.take 18 ++ [install]).toArray))
  let block (address : Address) := object [("address", Lean.toJson address.val), ("length", Lean.toJson (32 : Nat))]
  let test := object [
    ("source", block original.source), ("destination", block wire.destination),
    ("protocol", Lean.toJson (17 : Nat)), ("sourcePorts", .null),
    ("destinationPorts", object [("first", Lean.toJson wire.destinationPort.val), ("last", Lean.toJson wire.destinationPort.val)])]
  let intent := object [("schema", Lean.toJson (1 : Nat)), ("requirements", Lean.toJson [
    object [("id", .str "REPORTS-READ"), ("scope", scope), ("match", test)]])]
  let json := object [("schema", Lean.toJson (1 : Nat)), ("authentication", authentication), ("intent", intent),
    ("snapshots", Lean.toJson [object [("after", Lean.toJson (19 : Nat)), ("firewall", firewall)]])]
  let input ← unwrap (Check.SessionFirewall.Input.parse json.compress)
  let report ← unwrap input.check
  if compliant : report.compliant = true then
    match report.findings.attach with
    | [] => throw (IO.userError "The parsed native snapshot finding is missing.")
    | attached :: _ =>
      let finding := attached.val
      let active := snapshotPipeline finding.checkpoint.firewall routes [] .permit
      match accepted : ConntrackLifecycle.step active cached oldInput with
      | .error error => throw (IO.userError error.describe)
      | .ok outcome =>
        if output : outcome.output = some wire then
          have _ := checked_output_current_permission report compliant finding attached.property routes [] .permit
            cached oldInput outcome wire accepted output
          ensure (outcome.attachment.classification == .established && !outcome.attachment.fresh)
            "The parsed snapshot proof must apply to the actual cached established packet execution."
        else throw (IO.userError "The checked parsed forward snapshot must produce the expected NAT output.")
  else throw (IO.userError "The native EAP prefix and SYNTHETIC credential must certify the parsed generated snapshot.")

def run : IO Unit := do
  let granted ← build active
  checkedNativeSnapshot granted.toJson
  let allowed := pipeline granted routes [] .permit
  let forwarded ← load (ConntrackLifecycle.step allowed cached oldInput)
  ensure (forwarded.output == some wire && forwarded.attachment.classification == .established &&
      !forwarded.attachment.fresh && forwarded.state == cached && service.accepts forwarded.afterDestination &&
      !service.accepts original && !service.accepts wire)
    "The generated forward policy must select the post-DNAT class before SNAT on an actual cached established path."
  let fresh ← load (ConntrackLifecycle.step allowed ConntrackLifecycle.State.initial ⟨0, original, some entry⟩)
  ensure (fresh.output == some wire && fresh.attachment.fresh && fresh.state.records.length == 1)
    "The same current scope policy must also govern a fresh candidate before confirmation."
  let loggedOff := EAPSession.step context active (.authentication .logoff)
  let closed := EAPSession.step context active .close
  let revoked := EAPSession.step context active (.application .revoke)
  let expired := EAPSession.step context active (.application (.advance 60))
  let unauthenticated := EAPSession.step context EAPSession.State.initial (.application (.install token))
  let authenticatedOnly := EAPSession.run context EAPSession.State.initial (authentication.take 5)
  for current in [loggedOff, closed, revoked, expired, unauthenticated, authenticatedOnly] do
    let denied ← build current
    let currentPipeline := pipeline denied routes [] .permit
    let blocked ← load (ConntrackLifecycle.step currentPipeline cached oldInput)
    ensure (blocked.output.isNone && blocked.disposition == .forwardDrop && blocked.state == cached &&
        blocked.attachment.classification == .established && !blocked.attachment.fresh)
      "The current deny policy must block the existing established NAT binding without deleting it."
    let freshBlocked ← load (ConntrackLifecycle.step currentPipeline ConntrackLifecycle.State.initial ⟨0, original, some entry⟩)
    ensure (freshBlocked.output.isNone && freshBlocked.state.records.isEmpty)
      "The current deny policy must also prevent fresh confirmation."
  let deny ← build loggedOff
  let installed := pipeline deny routes [] .permit
  let stale ← load (ConntrackLifecycle.step allowed cached oldInput)
  ensure (stale.output == some wire && !loggedOff.auth.authorized)
    "A stale installed allow snapshot can forward after Logoff; current-snapshot installation is a required assumption."
  let exception := { installed with forward := ConntrackLifecycle.establishedPermit :: installed.forward }
  let bypass ← load (ConntrackLifecycle.step exception cached oldInput)
  ensure (bypass.output == some wire)
    "An extra established permit violates filter equivalence and can bypass the regenerated deny policy."
  let wrongStage ← load (ConntrackLifecycle.step
    { allowed with forward := [], forwardDefault := .permit, late := granted.statefulSnapshot.compile, lateDefault := .deny }
    cached oldInput)
  ensure (wrongStage.output.isNone && wrongStage.disposition == .lateDrop)
    "Moving a post-DNAT class policy after SNAT changes which header it tests."
  let queued ← load (BufferedLifecycle.step ⟨cached, {}⟩ (.operation (.packet ⟨allowed, oldInput⟩)))
  ensure (queued.admitted == [wire] && queued.state.queue.pending == [wire])
    "A permitted computed output must enter the FIFO as one new admission."
  let blockedQueued ← load (BufferedLifecycle.step queued.state (.operation (.packet ⟨installed, oldInput⟩)))
  ensure (blockedQueued.admitted.isEmpty && blockedQueued.state.queue.pending == [wire] && blockedQueued.served.isEmpty)
    "Current session revocation must enqueue nothing while retaining the earlier pending packet."
  let delivered ← load (BufferedLifecycle.step blockedQueued.state (.serve 1))
  ensure (delivered.served == [wire] && delivered.state.queue.pending.isEmpty)
    "An earlier queued output can still be delivered after Logoff; admission denial does not flush the FIFO."
  IO.println "Session firewall forwarding deployment tests passed."

end NetlibTest.SessionFirewallDeployment
