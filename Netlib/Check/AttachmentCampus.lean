import Netlib.Check.CampusDeployment
import Netlib.Check.IngressGuard
import Netlib.Protocol.GuardedHandoff
import Netlib.Protocol.IngressProbe

/-!
# Ingress attachments in the campus operation history

The unsafe prelude uses the installed rules and can establish an impersonated flow.
An explicit empty-table reset precedes the guarded suffix.
Actual early rejection bypasses ordinary tracking and retires any selected ticket.
-/

namespace Netlib.Check.AttachmentCampus

open Packet Protocol
open StatefulFailover (Gateway)
open IngressAttachment (NamespaceRef InterfaceRef ExpectedAttachment OwnedBinding)
abbrev Maintenance := Compile.IngressAttachment.Maintenance
abbrev Config := Check.ConntrackLifecycle.Config
abbrev Source := Protocol.SafeHandoff.Source

structure Specification where
  id : String
  gateway : Gateway
  ingress : InterfaceRef
  direction : FlowNAT.Direction
  traffic : Match

structure GuardConfig where
  id : String
  gateway : Gateway
  source : Import.NftablesIngress.Snapshot

structure Input where
  campus : Check.CampusDeployment.Input
  namespaces : Gateway → NamespaceRef
  authenticationPort : InterfaceRef
  live : List InterfaceRef
  specifications : List Specification
  guards : List GuardConfig

structure Staged where
  specification : String
  value : ExpectedAttachment

structure State where
  authentication : Nat := 0
  network : Nat := 0
  deployment : CampusWithdrawal.State
  live : List InterfaceRef
  attachments : List Staged := []
  maintenance : List Maintenance := []
  guards : Gateway → Option GuardConfig := fun _ => none
  enforced : Bool := false
  owners : Gateway → Option OwnedBinding := fun _ => none
  resetObserved : Bool := false

def Input.initial (input : Input) : State :=
  ⟨0, 0, input.campus.initial.deployment, input.live, [], [], fun _ => none, false, fun _ => none, false⟩

def current (input : Input) (state : State) : IngressAttachment.Current :=
  ⟨input.campus.authentication.context, state.authentication,
    SessionInstallation.current input.campus.authentication state.authentication, state.live⟩

theorem current_safe (input : Input) (state : State) : (current input state).Safe :=
  Check.SessionFirewall.stateAt_safe _ _

def classes (input : Input) : List Match := input.specifications.map (·.traffic)
def staged (state : State) : List ExpectedAttachment := state.attachments.map (·.value)

def actualPolicy (state : State) (gateway : Gateway) : IngressPolicy.Policy :=
  match state.guards gateway with
  | none => ⟨[], .permit⟩
  | some configured => configured.source.compile

def desiredPolicy (input : Input) (state : State) (gateway : Gateway) : IngressPolicy.Policy :=
  Compile.IngressAttachment.compile (current input state) (input.namespaces gateway) (staged state) state.maintenance

def guardMatches (input : Input) (state : State) (gateway : Gateway) : Bool :=
  IngressPolicy.check (actualPolicy state gateway) (desiredPolicy input state gateway)

def OriginValid (input : Input) (state : State) (attachment : ExpectedAttachment) : Prop :=
  attachment.origin.context = input.campus.authentication.context ∧
    attachment.origin.after ≤ state.authentication ∧
    attachment.origin.source = SessionInstallation.current input.campus.authentication attachment.origin.after ∧
    attachment.origin.authenticationPort = input.authenticationPort ∧ attachment.scope = input.campus.application ∧
    Session.Valid input.campus.authentication.context attachment.origin.source.session attachment.scope

def originCheck (input : Input) (state : State) (attachment : ExpectedAttachment) : Bool :=
  decide (attachment.origin.context = input.campus.authentication.context) &&
    decide (attachment.origin.after ≤ state.authentication) &&
    decide (attachment.origin.source = SessionInstallation.current input.campus.authentication attachment.origin.after) &&
    decide (attachment.origin.authenticationPort = input.authenticationPort) && decide (attachment.scope = input.campus.application) &&
    attachment.origin.source.session.permits input.campus.authentication.context attachment.scope

theorem originCheck_correct (input : Input) (state : State) (attachment : ExpectedAttachment) :
    originCheck input state attachment = true ↔ OriginValid input state attachment := by
  simp [originCheck, OriginValid, Session.permits_iff, and_assoc]

def OwnerValid (state : State) (gateway : Gateway) (owner : OwnedBinding) : Prop :=
  (∃ attachment ∈ staged state, owner.origin = attachment.origin) ∧
    ∃ record ∈ (state.deployment.handoff.gateways.table gateway).records, record.entry = owner.entry

def ownerCheck (state : State) (gateway : Gateway) (owner : OwnedBinding) : Bool :=
  (staged state).any (fun attachment => decide (owner.origin = attachment.origin)) &&
    (state.deployment.handoff.gateways.table gateway).records.any (fun record => decide (record.entry = owner.entry))

theorem ownerCheck_correct (state : State) (gateway : Gateway) (owner : OwnedBinding) :
    ownerCheck state gateway owner = true ↔ OwnerValid state gateway owner := by
  simp [ownerCheck, OwnerValid]

def provenanceCheck (input : Input) (state : State) : Bool :=
  (staged state).all (originCheck input state) &&
    [Gateway.primary, Gateway.standby].all (fun gateway => (state.owners gateway).all (ownerCheck state gateway))

def Provenance (input : Input) (state : State) : Prop :=
  (∀ attachment ∈ staged state, OriginValid input state attachment) ∧
    ∀ gateway owner, state.owners gateway = some owner → OwnerValid state gateway owner

theorem provenanceCheck_correct (input : Input) (state : State) :
    provenanceCheck input state = true ↔ Provenance input state := by
  have gatewayCases : (∀ gateway : Gateway, ∀ owner, state.owners gateway = some owner → OwnerValid state gateway owner) ↔
      (∀ owner, state.owners .primary = some owner → OwnerValid state .primary owner) ∧
      (∀ owner, state.owners .standby = some owner → OwnerValid state .standby owner) := by
    constructor
    · intro valid; exact ⟨valid .primary, valid .standby⟩
    · rintro ⟨primary, standby⟩ gateway; cases gateway <;> assumption
  simp only [provenanceCheck, Provenance, Bool.and_eq_true, List.all_eq_true, originCheck_correct]
  rw [gatewayCases]
  simp [ownerCheck_correct, Option.all_eq_true]

def State.Safe (input : Input) (state : State) : Prop :=
  state.authentication ≤ input.campus.authentication.observations.length ∧
    state.network ≤ input.campus.handoff.events.length ∧ state.deployment.Safe ∧
    Compile.IngressAttachment.LiveUnique (current input state) ∧ Provenance input state

def State.check (input : Input) (state : State) : Bool :=
  decide (state.authentication ≤ input.campus.authentication.observations.length) &&
    decide (state.network ≤ input.campus.handoff.events.length) && state.deployment.check &&
    Compile.IngressAttachment.liveUnique (current input state) && provenanceCheck input state

theorem State.check_correct (input : Input) (state : State) : state.check input = true ↔ state.Safe input := by
  simp [check, Safe, CampusWithdrawal.State.check_correct, Compile.IngressAttachment.liveUnique_correct,
    provenanceCheck_correct, and_assoc]

def tablesEmpty (state : State) : Bool :=
  state.deployment.handoff.gateways.primary.records.isEmpty && state.deployment.handoff.gateways.standby.records.isEmpty &&
    state.deployment.handoff.gateways.cache.isNone && state.deployment.handoff.work.pending.isEmpty

private def resetState (state : State) : State :=
  { state with
    deployment := { state.deployment with
      handoff := { state.deployment.handoff with
        gateways := { state.deployment.handoff.gateways with
          primary := .initial
          standby := .initial
          cache := none
          epoch := state.deployment.handoff.gateways.epoch + 1 } } }
    owners := fun _ => none
    resetObserved := true }

def reset (input : Input) (before : State) : Except String State := do
  if before.enforced || before.deployment.withdrawn || before.deployment.handoff.binding.isSome ||
      !before.deployment.handoff.work.pending.isEmpty then
    throw "Tracking reset is restricted to the unsafe prelude before protected work."
  if !before.check input then throw "The prelude reset state violates its contract."
  return resetState before

def stage (input : Input) (before : State) (specification : Specification) : Except String State := do
  if before.attachments.any (·.specification == specification.id) then throw "The attachment specification is already staged."
  if specification.ingress.ns ≠ input.namespaces specification.gateway then
    throw "The attachment ingress belongs to another gateway namespace."
  let value ← (IngressAttachment.stage (current input before) (current_safe input before) input.authenticationPort
    specification.ingress specification.direction input.campus.application specification.traffic).mapError (·.describe)
  return { before with attachments := before.attachments ++ [⟨specification.id, value⟩] }

def installGuard (input : Input) (before : State) (configured : GuardConfig) : Except String State := do
  if before.deployment.withdrawn && decide (configured.gateway = .primary) then
    throw "A withdrawn gateway cannot receive an ingress configuration."
  if configured.source.ns ≠ input.namespaces configured.gateway then
    throw "The ingress configuration belongs to another namespace lifetime."
  return { before with guards := fun gateway => if gateway = configured.gateway then some configured else before.guards gateway }

def protect (input : Input) (before : State) (budget : Nat) : Except String State := do
  if before.enforced then throw "The guarded suffix has already begun."
  if !before.resetObserved then throw "Record the explicit tracking reset before beginning the guarded suffix."
  if !tablesEmpty before || before.deployment.handoff.binding.isSome || before.deployment.withdrawn then
    throw "Begin ingress enforcement only after the explicit empty-table prelude reset."
  if !input.specifications.all (fun specification => before.attachments.any (·.specification == specification.id)) then
    throw "Stage every declared ingress attachment before beginning the guarded suffix."
  let separated ← Compile.IngressAttachment.checkDisjointBudget before.maintenance (classes input) budget
  if !separated then throw "Maintenance traffic overlaps a protected application class."
  for gateway in [Gateway.primary, Gateway.standby] do
    let checked ← IngressPolicy.checkBudget (actualPolicy before gateway) (desiredPolicy input before gateway) budget
    if !checked then throw "Install the current ingress guard at both gateways before beginning the guarded suffix."
  return { before with enforced := true }

structure PacketCheck (input : Input) (before : State) where
  gateway : Gateway
  ingress : InterfaceRef
  source : Source
  currentLive : ingress ∈ before.live
  namespaceEq : ingress.ns = input.namespaces gateway
  guardEquivalent : Bool
  compared : IngressPolicy.check (actualPolicy before gateway) (desiredPolicy input before gateway) = guardEquivalent

def PacketCheck.context (packet : PacketCheck input before) : IngressAttachment.Input :=
  ⟨packet.ingress, packet.source.packet.header⟩

def PacketCheck.decision (packet : PacketCheck input before) : Bool :=
  (actualPolicy before packet.gateway).allows packet.ingress.ifindex.val packet.source.packet.header

def PacketCheck.covered (packet : PacketCheck input before) : Bool :=
  (classes input).any (·.accepts packet.source.packet.header)

def PacketCheck.passed (packet : PacketCheck input before) : Bool :=
  packet.covered && (!before.enforced || packet.guardEquivalent)

def packet (input : Input) (before : State) (gateway : Gateway) (ingress : InterfaceRef) (source : Source)
    (budget : Nat) : Except String (PacketCheck input before) := do
  if live : ingress ∈ before.live then
    if namespaceEq : ingress.ns = input.namespaces gateway then
      if before.deployment.withdrawn && decide (gateway = .primary) then throw "The packet targets a withdrawn gateway."
      if before.deployment.handoff.gateways.isFenced gateway then throw "The packet targets a fenced gateway."
      match compared : IngressPolicy.checkBudget (actualPolicy before gateway) (desiredPolicy input before gateway) budget with
      | .error reason => throw reason
      | .ok value =>
        have exactDecision : IngressPolicy.check (actualPolicy before gateway) (desiredPolicy input before gateway) = value := by
          unfold IngressPolicy.checkBudget at compared
          split at compared
          · exact Except.ok.inj compared
          · cases compared
        return ⟨gateway, ingress, source, live, namespaceEq, value, exactDecision⟩
    else throw "The packet ingress belongs to another gateway namespace."
  else throw "The packet ingress lifetime is absent from the current registry."

theorem PacketCheck.application_permission (packet : PacketCheck input before) (safe : before.Safe input)
    (enforced : before.enforced = true) (matched : packet.passed = true) (accepted : packet.decision = true)
    (disjoint : Compile.IngressAttachment.checkDisjoint before.maintenance (classes input) = true) :
    ∃ attachment ∈ staged before, IngressAttachment.allows (current input before) attachment packet.context = true ∧
      Session.Valid input.campus.authentication.context (current input before).state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext input.campus.authentication.context) (current input before).state.auth ∧
      packet.ingress = attachment.ingress ∧ attachment.origin.principal = input.campus.authentication.context.consumer := by
  have conditions : packet.covered = true ∧ packet.guardEquivalent = true := by
    simpa only [PacketCheck.passed, enforced, Bool.not_true, Bool.false_or, Bool.and_eq_true] using matched
  have equivalent : IngressPolicy.check (actualPolicy before packet.gateway) (desiredPolicy input before packet.gateway) = true :=
    packet.compared.trans conditions.2
  have covered : ∃ traffic ∈ classes input, traffic.Holds packet.source.packet.header := by
    simpa only [PacketCheck.covered, List.any_eq_true, Match.accepts_iff] using conditions.1
  exact Compile.IngressAttachment.actual_application_permission (current input before) (current_safe input before)
    (input.namespaces packet.gateway) (staged before) before.maintenance (classes input) packet.context
    safe.2.2.2.1 packet.currentLive packet.namespaceEq disjoint covered (actualPolicy before packet.gateway) equivalent accepted

def State.base (state : State) : CampusDeployment.State :=
  ⟨state.authentication, state.network, state.deployment⟩

def State.withBase (state : State) (next : CampusDeployment.State) : State :=
  { state with authentication := next.authentication, network := next.network, deployment := next.deployment }

structure Probe where
  gateway : Gateway
  ingress : InterfaceRef
  direction : FlowNAT.Direction
  source : Source
  guard : Bool
  observed : Check.WireForwarding.PacketObservation
  primary : Option Import.ConntrackNetlink.Snapshot
  standby : Option Import.ConntrackNetlink.Snapshot

inductive Event where
  | authentication (index : Nat)
  | network (index : Nat) (ingress : Option InterfaceRef) (guard : Option Bool)
  | withdraw
  | reset
  | stage (id : String)
  | maintenance (entries : List Maintenance)
  | installGuard (id : String)
  | protect
  | probe (value : Probe)

structure Observation where
  index : Nat
  event : Event
  raw : Lean.Json

def rejectedObservation (observed : Check.WireForwarding.PacketObservation) : Bool :=
  observed.classification.isNone && observed.fresh.isNone && observed.afterDestination.isNone &&
    observed.afterSource.isNone && observed.nextHop.isNone && observed.disposition.isNone && observed.output.isNone

def RejectedObservation (observed : Check.WireForwarding.PacketObservation) : Prop :=
  observed.classification = none ∧ observed.fresh = none ∧ observed.afterDestination = none ∧
    observed.afterSource = none ∧ observed.nextHop = none ∧ observed.disposition = none ∧ observed.output = none

theorem rejectedObservation_correct (observed : Check.WireForwarding.PacketObservation) :
    rejectedObservation observed = true ↔ RejectedObservation observed := by
  simp [rejectedObservation, RejectedObservation, and_assoc]

structure Gate (input : Input) (before : State) where
  checked : PacketCheck input before
  observed : Bool

def Gate.passed (gate : Gate input before) : Bool := gate.checked.passed && decide (gate.checked.decision = gate.observed)

def Gate.Matches (gate : Gate input before) : Prop :=
  gate.checked.covered = true ∧ (before.enforced = true → gate.checked.guardEquivalent = true) ∧
    gate.checked.decision = gate.observed

theorem Gate.passed_correct (gate : Gate input before) : gate.passed = true ↔ gate.Matches := by
  cases enforced : before.enforced <;> simp [passed, Matches, PacketCheck.passed, enforced, and_assoc]

private def selectedPacket (before : State) : Check.SafeHandoff.Event → Except String (Option (Gateway × Source))
  | .establish _ source _ => return some (.primary, source)
  | .serve id _ _ => do
    let some ticket := before.deployment.handoff.work.pending.find? (·.id == id)
      | throw "The gateway observation has no pending source ticket."
    return some (ticket.value.gateway, ticket.value.source)
  | _ => return none

private def gate (input : Input) (before : State) (source : Check.SafeHandoff.Observation)
    (ingress : Option InterfaceRef) (observed : Option Bool) (budget : Nat) : Except String (Option (Gate input before)) := do
  match ← selectedPacket before source.event with
  | none =>
    if ingress.isSome || observed.isSome then throw "A control operation cannot claim a packet ingress decision."
    return none
  | some (gateway, immutable) =>
    let some ingress := ingress | throw "An actual packet execution requires its ingress lifetime."
    let some observed := observed | throw "An actual packet execution requires its observed ingress decision."
    return some ⟨← packet input before gateway ingress immutable budget, observed⟩

structure RejectedServe (input : Input) (before : State) where
  available : before.network < input.campus.handoff.events.length
  gate : Gate input before
  id : Nat
  observedInput : Source
  observed : Check.WireForwarding.PacketObservation
  dropped : GuardedHandoff.Dropped before.deployment id
  computed : GuardedHandoff.retire before.deployment id = .ok dropped

def RejectedServe.source (evidence : RejectedServe input before) : Check.SafeHandoff.Observation :=
  input.campus.handoff.events[before.network]'evidence.available

def RejectedServe.passed (evidence : RejectedServe input before) : Bool :=
  evidence.gate.passed && decide (evidence.dropped.ticket.value.source.bytes = evidence.observedInput.bytes) &&
    rejectedObservation evidence.observed && Check.SafeHandoff.stateMatches evidence.source evidence.dropped.state.handoff

def RejectedServe.Matches (evidence : RejectedServe input before) : Prop :=
  evidence.gate.Matches ∧ evidence.dropped.ticket.value.source.bytes = evidence.observedInput.bytes ∧
    RejectedObservation evidence.observed ∧ Check.SafeHandoff.StateMatches evidence.source evidence.dropped.state.handoff

theorem RejectedServe.passed_correct (evidence : RejectedServe input before) : evidence.passed = true ↔ evidence.Matches := by
  simp [passed, Matches, Gate.passed_correct, rejectedObservation_correct, Check.SafeHandoff.stateMatches_correct, and_assoc]

def Probe.snapshot (value : Probe) : Check.SafeHandoff.Observation :=
  ⟨0, .forget, value.primary, value.standby, none, .null⟩

def probeInput (input : Input) (before : State) (value : Probe) : Except String IngressProbe.Input := do
  let id := (before.deployment.handoff.configurations value.gateway).id
  let some configuration := input.campus.handoff.configs.find? (·.id == id)
    | throw "The probe pipeline has no supplied installed configuration."
  let candidate := if (before.deployment.handoff.gateways.table value.gateway).model.lookup 0 value.source.packet.header |>.isNone then
    some (configuration.nat.candidate 0 value.source.packet.header) else none
  return ⟨value.gateway, value.direction, value.source, candidate⟩

inductive ProbeExecution (input : Input) (before : State) (value : Probe) where
  | rejected
  | processed (call : IngressProbe.Input) (selected : probeInput input before value = .ok call)
      (result : IngressProbe.Result before.deployment call)
      (computed : IngressProbe.process before.deployment call = .ok result)
      (certificate : CampusDeployment.Certification input.campus before.authentication
        (some (before.deployment.handoff.configurations value.gateway)))

def ProbeExecution.state : ProbeExecution input before value → CampusWithdrawal.State
  | .rejected => before.deployment
  | .processed _ _ result _ _ => result.state

def ProbeExecution.passed (execution : ProbeExecution input before value) : Bool :=
  Check.SafeHandoff.stateMatches value.snapshot execution.state.handoff && match execution with
  | .rejected => rejectedObservation value.observed
  | .processed _ _ result _ certificate => value.observed.matches result.outcome && certificate.passed &&
      decide (result.outcome.nextHop = some (match value.direction with | .original => "server" | .reply => "client")) &&
      input.campus.requirements.any (fun requirement => requirement.test.accepts result.outcome.afterDestination)

def ProbeExecution.Matches (execution : ProbeExecution input before value) : Prop :=
  Check.SafeHandoff.StateMatches value.snapshot execution.state.handoff ∧ match execution with
  | .rejected => RejectedObservation value.observed
  | .processed _ _ result _ certificate => value.observed.Matches result.outcome ∧ certificate.Valid ∧
      result.outcome.nextHop = some (match value.direction with | .original => "server" | .reply => "client") ∧
      ∃ requirement ∈ input.campus.requirements, requirement.test.Holds result.outcome.afterDestination

theorem ProbeExecution.passed_correct (execution : ProbeExecution input before value) :
    execution.passed = true ↔ execution.Matches := by
  cases execution <;> simp [passed, Matches, Check.SafeHandoff.stateMatches_correct, rejectedObservation_correct,
    Check.WireForwarding.PacketObservation.matches_correct, CampusDeployment.Certification.passed_correct,
    Match.accepts_iff, and_assoc]

private def ownership (input : Input) (before : State) (evidence : CampusDeployment.NetworkEvidence input.campus before.base)
    (gate : Option (Gate input before)) : Except String (Gateway → Option OwnedBinding) := do
  if !before.enforced then return before.owners
  match evidence.event with
  | .establish _ =>
    let some checked := gate | throw "Protected establishment requires an actual ingress decision."
    let some established := evidence.model.established | throw "Establishment has no computed ordinary result."
    if !established.outcome.attachment.fresh || established.outcome.output.isNone then return before.owners
    let some origin := (staged before).find? (fun attachment => IngressAttachment.allows (current input before)
      attachment checked.checked.context) | return before.owners
    if (before.owners .primary).isSome then throw "Fresh establishment cannot overwrite historical ownership."
    if !(established.outcome.state.records.any (fun record => decide (record.entry = established.outcome.attachment.entry))) then
      throw "Historical ownership requires an actual confirmed ordinary record."
    return fun gateway => if gateway = .primary then some ⟨established.outcome.attachment.entry, origin.origin⟩ else before.owners gateway
  | .stage .. =>
    let some source := before.owners .primary | throw "Replication requires the historical source owner."
    let some selected := evidence.model.state.gateways.cache | throw "Replication selected no actual source record."
    let _ ← (IngressAttachment.selectOwner source selected).mapError (·.describe)
    return before.owners
  | .commit timeout =>
    let some source := before.owners .primary | throw "Commit requires the historical source owner."
    let some selected := before.deployment.handoff.gateways.cache | throw "Commit has no actual staged source record."
    match owned : IngressAttachment.selectOwner source selected with
    | .error reason => throw reason.describe
    | .ok owner =>
      match computed : ConntrackReplication.commit before.deployment.handoff.gateways.standby selected timeout with
      | .error reason => throw reason.describe
      | .ok installed =>
        if installed.state ≠ evidence.model.state.gateways.standby then throw "The inherited owner has no matching actual installed table."
        let chosen := (ConntrackReplication.commit_fields _ _ _ _ computed).2.1.trans
          (IngressAttachment.selectOwner_fields _ _ _ owned).2.symm
        return fun gateway => if gateway = .standby then some (owner.inherit installed chosen) else before.owners gateway
  | _ => return before.owners

inductive Detail (input : Input) (before : State) where
  | simple (name : String)
  | authentication (evidence : CampusDeployment.AuthenticationEvidence input.campus before.base)
  | ordinary (evidence : CampusDeployment.NetworkEvidence input.campus before.base) (gate : Option (Gate input before))
  | rejectedServe (evidence : RejectedServe input before)
  | probe (value : Probe) (gate : Gate input before) (execution : ProbeExecution input before value)

def Detail.passed : Detail input before → Bool
  | .simple _ => true
  | .authentication evidence => evidence.finding.passed
  | .ordinary evidence gate => evidence.passed && gate.all Gate.passed && evidence.topologyMatches && evidence.applicationMatches
  | .rejectedServe evidence => evidence.passed
  | .probe _ gate execution => gate.passed && execution.passed

def Detail.Matches : Detail input before → Prop
  | .simple _ => True
  | .authentication evidence => Check.EAP.Matches evidence.source evidence.finding.result
  | .ordinary evidence gate => evidence.Matches ∧ (∀ value, gate = some value → value.Matches) ∧
      evidence.topologyMatches = true ∧ evidence.applicationMatches = true
  | .rejectedServe evidence => evidence.Matches
  | .probe _ gate execution => gate.Matches ∧ execution.Matches

theorem Detail.passed_correct (detail : Detail input before) : detail.passed = true ↔ detail.Matches := by
  cases detail with
  | simple => simp [passed, Matches]
  | authentication evidence => exact Check.EAP.finding_correct _ _
  | ordinary evidence gate => cases gate <;> simp [passed, Matches, CampusDeployment.NetworkEvidence.passed_correct,
      Gate.passed_correct, and_assoc]
  | rejectedServe evidence => exact evidence.passed_correct
  | probe value gate execution => simp [passed, Matches, Gate.passed_correct, ProbeExecution.passed_correct]

structure Transition (input : Input) (before : State) where
  state : State
  detail : Detail input before

def process (input : Input) (before : State) (observation : Observation) (budget : Nat) : Except String (Transition input before) := do
  match observation.event with
  | .authentication index =>
    if index != before.authentication then throw "Consume the next authentication observation exactly once."
    if available : before.authentication < input.campus.authentication.observations.length then
      return ⟨{ before with authentication := before.authentication + 1 }, .authentication ⟨available⟩⟩
    else throw "No authentication observation remains."
  | .network index ingress observed =>
    if index != before.network then throw "Consume the next network observation exactly once."
    if available : before.network < input.campus.handoff.events.length then
      let source := input.campus.handoff.events[before.network]
      if before.deployment.withdrawn && source.primary.isSome then throw "A withdrawn gateway has no live primary observation."
      let selected ← gate input before source ingress observed budget
      match selected with
      | some checked =>
        if !checked.checked.decision then
          match source.event with
          | .serve id observedInput observed =>
            match computed : GuardedHandoff.retire before.deployment id with
            | .error reason => throw reason
            | .ok dropped => return ⟨{ before with network := before.network + 1, deployment := dropped.state },
                .rejectedServe ⟨available, checked, id, observedInput, observed, dropped, computed⟩⟩
          | _ => throw "Use a probe for early rejection before protected establishment."
      | none => pure ()
      let baseObservation : CampusDeployment.Observation := ⟨observation.index, .network index, source.raw⟩
      let operated ← CampusDeployment.process input.campus before.base baseObservation budget
      match operated with
      | .network evidence =>
        let owners ← ownership input before evidence selected
        return ⟨{ (before.withBase operated.state) with owners := owners }, .ordinary evidence selected⟩
      | _ => throw "The network operation produced no ordinary campus evidence."
    else throw "No network observation remains."
  | .withdraw =>
    let operated ← CampusWithdrawal.step before.deployment .withdraw
    return ⟨{ before with
      deployment := operated.state
      live := before.live.filter (fun reference => decide (reference.ns ≠ input.namespaces .primary)) }, .simple "withdraw"⟩
  | .reset => return ⟨← reset input before, .simple "reset"⟩
  | .stage id =>
    let some specification := input.specifications.find? (·.id == id) | throw "Unknown ingress attachment specification."
    return ⟨← stage input before specification, .simple "stage"⟩
  | .maintenance entries =>
    if before.enforced then throw "Activate maintenance bindings before the guarded suffix."
    if !entries.all (fun entry => decide (entry.ingress ∈ before.live)) then throw "Maintenance uses a noncurrent ingress lifetime."
    let separated ← Compile.IngressAttachment.checkDisjointBudget entries (classes input) budget
    if !separated then throw "Maintenance traffic overlaps a protected application class."
    return ⟨{ before with maintenance := entries }, .simple "maintenance"⟩
  | .installGuard id =>
    let some configured := input.guards.find? (·.id == id) | throw "Unknown installed ingress configuration."
    return ⟨← installGuard input before configured, .simple "installGuard"⟩
  | .protect => return ⟨← protect input before budget, .simple "protect"⟩
  | .probe value =>
    if before.deployment.withdrawn && value.primary.isSome then throw "A probe cannot observe the withdrawn primary."
    let checked ← packet input before value.gateway value.ingress value.source budget
    let execution ← if checked.decision then do
      match selected : probeInput input before value with
      | .error reason => throw reason
      | .ok call =>
        match computed : IngressProbe.process before.deployment call with
        | .error reason => throw reason
        | .ok result =>
          let certificate ← CampusDeployment.certify input.campus before.authentication
            (some (before.deployment.handoff.configurations value.gateway)) budget
          pure (ProbeExecution.processed call selected result computed certificate)
      else pure ProbeExecution.rejected
    return ⟨{ before with deployment := execution.state }, .probe value ⟨checked, value.guard⟩ execution⟩

structure Result (input : Input) where
  before : State
  transition : Transition input before
  safe : transition.state.Safe input

def Result.state (result : Result input) : State := result.transition.state

def step (input : Input) (budget : Nat) (before : State) (observation : Observation) : Except String (Result input) := do
  if before.check input = true then
    let next ← process input before observation budget
    if checked : next.state.check input = true then
      return ⟨before, next, (State.check_correct input next.state).mp checked⟩
    else throw "The attachment transition violates its prefix, lifetime, or withdrawal invariant."
  else throw "The attachment replay state violates its prefix, lifetime, or withdrawal invariant."

theorem step_before (input : Input) (budget : Nat) (before : State) (observation : Observation) (result : Result input)
    (accepted : step input budget before observation = .ok result) : result.before = before := by
  unfold step at accepted
  split at accepted
  · cases computed : process input before observation budget with
    | error reason => simp [computed, bind, Except.bind] at accepted
    | ok next =>
      simp only [computed, bind, Except.bind] at accepted
      split at accepted
      · cases accepted; rfl
      · simp [throw, throwThe] at accepted
  · simp [throw, throwThe] at accepted

def replay (input : Input) (budget : Nat) : Replay.System State Observation (Result input) where
  step := step input budget
  state := Result.state
  passed _ result := result.transition.detail.passed
  Matches _ result := result.transition.detail.Matches
  correct _ result := result.transition.detail.passed_correct

abbrev Report (input : Input) (budget : Nat) (observations : List Observation) :=
  Replay.Report (replay input budget) input.initial observations

def Report.complete (report : Report input budget observations) : Bool :=
  decide (report.final.authentication = input.campus.authentication.observations.length) &&
    decide (report.final.network = input.campus.handoff.events.length) && report.final.enforced && report.final.deployment.withdrawn

def Report.compliant (report : Report input budget observations) : Bool :=
  report.findings.all (·.passed) && report.complete

theorem Report.finding_matches (report : Report input budget observations) (passed : Report.compliant report = true)
    (finding : Replay.Finding Observation (Result input)) (member : finding ∈ report.findings) :
    finding.result.transition.detail.Matches := by
  have conditions : report.findings.all (·.passed) = true ∧ report.complete = true := by
    simpa only [Report.compliant, Bool.and_eq_true] using passed
  exact Replay.Report.finding_matches report conditions.1 finding member

theorem Report.prefixes_safe (report : Report input budget observations) (initial : input.initial.check input = true) :
    report.final.Safe input ∧ ∀ finding ∈ report.findings, finding.result.state.Safe input :=
  report.trace.invariant (fun state => state.Safe input) (fun _ _ result _ _ => result.safe)
    ((State.check_correct _ _).mp initial)

theorem Report.finding_prefix (report : Report input budget observations)
    (finding : Replay.Finding Observation (Result input)) (member : finding ∈ report.findings) :
    ∃ prior later, report.findings = prior ++ finding :: later ∧
      Replay.Trace (replay input budget) input.initial prior finding.result.before ∧
      step input budget finding.result.before finding.observation = .ok finding.result := by
  obtain ⟨prior, later, before, covered, preceding, computed, _⟩ := report.trace.prefix finding member
  have same := step_before input budget before finding.observation finding.result computed
  exact ⟨prior, later, covered, same ▸ preceding, same ▸ computed⟩

theorem Report.final_origins (report : Report input budget observations) (initial : input.initial.check input = true)
    (attachment : ExpectedAttachment) (member : attachment ∈ staged report.final) : OriginValid input report.final attachment :=
  (report.prefixes_safe initial).1.2.2.2.2.1 attachment member

theorem Report.final_owner (report : Report input budget observations) (initial : input.initial.check input = true)
    (gateway : Gateway) (owner : OwnedBinding) (found : report.final.owners gateway = some owner) :
    OwnerValid report.final gateway owner :=
  (report.prefixes_safe initial).1.2.2.2.2.2 gateway owner found

theorem PacketCheck.application_origin (packet : PacketCheck input before) (safe : before.Safe input)
    (enforced : before.enforced = true) (matched : packet.passed = true) (accepted : packet.decision = true)
    (disjoint : Compile.IngressAttachment.checkDisjoint before.maintenance (classes input) = true) :
    ∃ attachment ∈ staged before, IngressAttachment.allows (current input before) attachment packet.context = true ∧
      OriginValid input before attachment ∧
      Session.Valid input.campus.authentication.context (current input before).state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext input.campus.authentication.context) (current input before).state.auth := by
  obtain ⟨attachment, member, allowed, valid, ready, _⟩ := packet.application_permission safe enforced matched accepted disjoint
  exact ⟨attachment, member, allowed, safe.2.2.2.2.1 attachment member, valid, ready⟩

theorem PacketCheck.wrong_ingress_rejected (packet : PacketCheck input before) (safe : before.Safe input)
    (enforced : before.enforced = true) (matched : packet.passed = true)
    (disjoint : Compile.IngressAttachment.checkDisjoint before.maintenance (classes input) = true)
    (different : ∀ attachment ∈ staged before, packet.ingress ≠ attachment.ingress) : packet.decision = false := by
  cases accepted : packet.decision with
  | false => rfl
  | true =>
    obtain ⟨attachment, member, _, _, _, same, _⟩ := packet.application_permission safe enforced matched accepted disjoint
    exact False.elim (different attachment member same)

end Netlib.Check.AttachmentCampus
