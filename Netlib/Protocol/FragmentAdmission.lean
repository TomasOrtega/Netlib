import Netlib.Compile.FragmentAttachment
import Netlib.Protocol.IngressAttachment
import Netlib.Protocol.ReassemblyForwarding
import Netlib.Protocol.IPv4ReassemblyFacts
import Netlib.Protocol.IPv4ReassemblySourcesBy

/-!
# Admission on both sides of IPv4 reassembly

The early guard reads no transport selectors.
Reassembly retains its actual user/vif key within one namespace lifetime.
The completing interface supplies the later full-datagram guard context.
-/

namespace Netlib.Protocol.FragmentAdmission

open Packet
open IngressAttachment (NamespaceRef InterfaceRef Current)

structure EarlyGuard where
  policy : IngressPolicy.Policy
  noPorts : IngressPolicy.NoPorts policy

def EarlyGuard.checked (policy : IngressPolicy.Policy) : Except String EarlyGuard :=
  if checked : IngressPolicy.noPorts policy = true then .ok ⟨policy, (IngressPolicy.noPorts_correct _).mp checked⟩
  else .error "A guard before defragmentation cannot read transport selectors."

structure Input where
  now : Nat
  ingress : InterfaceRef
  domain : IPv4Reassembly.Domain
  zone : Nat
  fragment : IPv4Fragment.Decoded

def Input.envelope (input : Input) : IPv4Envelope := IPv4Envelope.ofFragment input.fragment

def EarlyGuard.allows (guard : EarlyGuard) (input : Input) : Bool :=
  guard.policy.allows input.ingress.ifindex.val input.envelope.toHeader

theorem EarlyGuard.port_independent (guard : EarlyGuard) (index : Nat) (first second : Header)
    (same : IPv4Envelope.ofHeader first = IPv4Envelope.ofHeader second) :
    guard.policy.allows index first = guard.policy.allows index second :=
  IngressPolicy.noPorts_port_independent guard.policy guard.noPorts index first second same

structure Receipt where
  input : Input
  authentication : Current
  guard : EarlyGuard
  accepted : guard.allows input = true

def Receipt.fragment (receipt : Receipt) : IPv4Fragment.Decoded := receipt.input.fragment

def Receipt.Source (history : List Receipt) (domain : IPv4Reassembly.Domain) (fragment : IPv4Fragment.Decoded) : Prop :=
  ∃ receipt ∈ history, receipt.input.domain = domain ∧ receipt.fragment = fragment

structure State where
  ns : NamespaceRef
  fragments : IPv4Reassembly.State
  conntrack : ConntrackLifecycle.State
  history : List Receipt
  clock : Nat
  fragmentsValid : fragments.Valid
  conntrackValid : conntrack.Valid
  sources : fragments.Sources (history.map Receipt.fragment)
  sourcesBy : fragments.SourcesBy (Receipt.Source history)
  namespaces : ∀ receipt ∈ history, receipt.input.ingress.ns = ns
  past : ∀ receipt ∈ history, receipt.input.now ≤ clock
  clockBound : fragments.lastTime ≤ clock

def State.initial (ns : NamespaceRef) : State where
  ns := ns
  fragments := .initial
  conntrack := .initial
  history := []
  clock := 0
  fragmentsValid := IPv4Reassembly.State.initial_valid
  conntrackValid := ConntrackLifecycle.State.initial_valid
  sources := IPv4Reassembly.State.initial_sources
  sourcesBy := IPv4Reassembly.State.initial_sourcesBy _
  namespaces := by simp
  past := by simp
  clockBound := Nat.le_refl _

def State.observe (before : State) (now : Nat) (monotonic : before.clock ≤ now) : State :=
  { before with
    clock := now
    clockBound := Nat.le_trans before.clockBound monotonic
    past := fun receipt member => Nat.le_trans (before.past receipt member) monotonic }

private def received (before : State) (input : Input) (current : Current) (guard : EarlyGuard)
    (accepted : guard.allows input = true) (same : input.ingress.ns = before.ns)
    (monotonic : before.clock ≤ input.now)
    (result : IPv4Reassembly.Result)
    (computed : IPv4Reassembly.arrive policy before.fragments input.now input.domain input.fragment = .ok result) : State :=
  { ns := before.ns
    fragments := result.state
    conntrack := before.conntrack
    history := ⟨input, current, guard, accepted⟩ :: before.history
    clock := input.now
    fragmentsValid := IPv4Reassembly.arrive_valid _ _ _ _ _ _ computed before.fragmentsValid
    conntrackValid := before.conntrackValid
    sources := IPv4Reassembly.arrive_sources _ _ _ _ _ _ _ computed before.sources
    sourcesBy := by
      refine IPv4Reassembly.arrive_sourcesBy policy before.fragments input.now input.domain input.fragment result
        (Receipt.Source (⟨input, current, guard, accepted⟩ :: before.history)) computed ?_ ?_
      · exact before.fragments.sourcesBy_mono _ _ before.sourcesBy (by
          rintro domain fragment ⟨receipt, member, domainEq, bytesEq⟩
          exact ⟨receipt, List.mem_cons_of_mem _ member, domainEq, bytesEq⟩)
      · exact ⟨⟨input, current, guard, accepted⟩, by simp, rfl, rfl⟩
    namespaces := by
      intro receipt member
      rcases List.mem_cons.mp member with rfl | old
      · exact same
      · exact before.namespaces receipt old
    past := by
      intro receipt member
      rcases List.mem_cons.mp member with rfl | old
      · exact Nat.le_refl _
      · exact Nat.le_trans (before.past receipt old) monotonic
    clockBound := by
      obtain ⟨processed, _, _, _⟩ := IPv4Reassembly.arrive_processed _ _ _ _ _ _ computed
      rw [processed]
      unfold IPv4Reassembly.process
      split
      · exact Nat.le_refl _
      · dsimp only
        split
        · exact Nat.le_refl _
        · unfold IPv4Reassembly.accept
          split
          · exact Nat.le_refl _
          · split
            · exact Nat.le_refl _
            · split
              · exact Nat.le_refl _
              · dsimp only
                split <;> exact Nat.le_refl _ }

def State.withTracker (before : State) (tracker : ConntrackLifecycle.State) (valid : tracker.Valid) : State :=
  { before with conntrack := tracker, conntrackValid := valid }

structure Ordinary (pipeline : ReassemblyForwarding.Pipeline) (before : State) (input : Input)
    (assembled : IPv4Reassembly.Output) (source : ReassemblyForwarding.Source assembled) where
  wire : WireForwarding.Input
  chosen : wire = ReassemblyForwarding.input pipeline before.conntrack input.zone source
  same : wire.packet = source.packet
  prepared : ConntrackLifecycle.Prepared wire.lifecycle
  attached : ConntrackLifecycle.prepare before.conntrack wire.lifecycle = .ok prepared
  outcome : ReassemblyForwarding.Outcome wire.packet
  processed : ReassemblyForwarding.process pipeline assembled source wire same prepared = .ok outcome

def ordinary (pipeline : ReassemblyForwarding.Pipeline) (before : State) (input : Input)
    (assembled : IPv4Reassembly.Output) (source : ReassemblyForwarding.Source assembled) :
    Except String (Ordinary pipeline before input assembled source) := do
  let wire := ReassemblyForwarding.input pipeline before.conntrack input.zone source
  match attached : ConntrackLifecycle.prepare before.conntrack wire.lifecycle with
  | .error reason => throw reason.describe
  | .ok prepared =>
    match processed : ReassemblyForwarding.process pipeline assembled source wire rfl prepared with
    | .error reason => throw reason
    | .ok outcome => return ⟨wire, rfl, rfl, prepared, attached, outcome, processed⟩

inductive Completion (pipeline : ReassemblyForwarding.Pipeline) (before : State) (input : Input)
    (fine : IngressPolicy.Policy) (result : IPv4Reassembly.Result) where
  | waiting (absent : result.output = none)
  | rejected (assembled : IPv4Reassembly.Output) (emitted : result.output = some assembled)
      (source : ReassemblyForwarding.Source assembled)
      (denied : fine.allows input.ingress.ifindex.val source.packet.header = false)
  | processed (assembled : IPv4Reassembly.Output) (emitted : result.output = some assembled)
      (source : ReassemblyForwarding.Source assembled) (operation : Ordinary pipeline before input assembled source)
      (allowed : fine.allows input.ingress.ifindex.val source.packet.header = true)

def Completion.state (before : State) : Completion pipeline original input fine fragments → State
  | .waiting _ | .rejected .. => before
  | .processed _ _ _ operation _ => before.withTracker operation.outcome.state operation.outcome.valid

theorem Completion.history_eq (completion : Completion pipeline original input fine fragments) (before : State) :
    (completion.state before).history = before.history := by
  cases completion <;> rfl

theorem Completion.clock_eq (completion : Completion pipeline original input fine fragments) (before : State) :
    (completion.state before).clock = before.clock := by
  cases completion <;> rfl

theorem Completion.namespace_eq (completion : Completion pipeline original input fine fragments) (before : State) :
    (completion.state before).ns = before.ns := by
  cases completion <;> rfl

def complete (pipeline : ReassemblyForwarding.Pipeline) (before : State) (input : Input)
    (fine : IngressPolicy.Policy) (result : IPv4Reassembly.Result) :
    Except String (Completion pipeline before input fine result) := do
  match emitted : result.output with
  | none => return .waiting emitted
  | some assembled =>
    let source ← ReassemblyForwarding.source assembled
    if allowed : fine.allows input.ingress.ifindex.val source.packet.header = true then
      let operation ← ordinary pipeline before input assembled source
      return .processed assembled emitted source operation allowed
    else return .rejected assembled emitted source (Bool.eq_false_iff.mpr allowed)

structure Accepted (pipeline : ReassemblyForwarding.Pipeline) (policy : IPv4Reassembly.Policy)
    (before : State) (input : Input) (current : Current) (early : EarlyGuard) (fine : IngressPolicy.Policy) where
  allowed : early.allows input = true
  namespaceEq : input.ingress.ns = before.ns
  monotonic : before.clock ≤ input.now
  result : IPv4Reassembly.Result
  arrived : IPv4Reassembly.arrive policy before.fragments input.now input.domain input.fragment = .ok result
  completion : Completion pipeline before input fine result

def Accepted.state (accepted : Accepted pipeline policy before input current early fine) : State :=
  accepted.completion.state (received before input current early accepted.allowed accepted.namespaceEq accepted.monotonic accepted.result accepted.arrived)

inductive Result (pipeline : ReassemblyForwarding.Pipeline) (policy : IPv4Reassembly.Policy)
    (before : State) (input : Input) (current : Current) (early : EarlyGuard) (fine : IngressPolicy.Policy) where
  | rejected (denied : early.allows input = false) (monotonic : before.clock ≤ input.now)
  | accepted (evidence : Accepted pipeline policy before input current early fine)

def Result.state : Result pipeline policy before input current early fine → State
  | .rejected _ monotonic => before.observe input.now monotonic
  | .accepted evidence => evidence.state

def step (pipeline : ReassemblyForwarding.Pipeline) (policy : IPv4Reassembly.Policy) (before : State)
    (input : Input) (current : Current) (early : EarlyGuard) (fine : IngressPolicy.Policy) :
    Except String (Result pipeline policy before input current early fine) := do
  if namespaceEq : input.ingress.ns = before.ns then
    if monotonic : before.clock ≤ input.now then
      if allowed : early.allows input = true then
        match arrived : IPv4Reassembly.arrive policy before.fragments input.now input.domain input.fragment with
        | .error reason => throw reason.describe
        | .ok result =>
          let completion ← complete pipeline before input fine result
          return .accepted ⟨allowed, namespaceEq, monotonic, result, arrived, completion⟩
      else return .rejected (Bool.eq_false_iff.mpr allowed) monotonic
    else throw "Fragment observations must have monotonic arrival times."
  else throw "The fragment arrived in a different namespace lifetime."

theorem Result.early_rejected_unchanged (denied : early.allows input = false) (monotonic : before.clock ≤ input.now) :
    (Result.state (.rejected denied monotonic : Result pipeline policy before input current early fine)).fragments = before.fragments ∧
      (Result.state (.rejected denied monotonic : Result pipeline policy before input current early fine)).conntrack = before.conntrack ∧
      (Result.state (.rejected denied monotonic : Result pipeline policy before input current early fine)).history = before.history :=
  ⟨rfl, rfl, rfl⟩

theorem Accepted.output_sources (accepted : Accepted pipeline policy before input current early fine)
    (output : IPv4Reassembly.Output) (emitted : accepted.result.output = some output)
    (piece : IPv4Reassembly.Piece) (member : piece ∈ output.pieces) :
    ∃ receipt ∈ accepted.state.history, receipt.fragment = piece.fragment := by
  have origin := IPv4Reassembly.arrive_output_sources _ _ _ _ _ _ _ _ accepted.arrived emitted before.sources piece member
  change piece.fragment ∈ input.fragment :: before.history.map Receipt.fragment at origin
  have source : piece.fragment ∈ (⟨input, current, early, accepted.allowed⟩ :: before.history).map Receipt.fragment := origin
  obtain ⟨receipt, member, same⟩ := List.mem_map.mp source
  refine ⟨receipt, ?_, same⟩
  change receipt ∈ (accepted.completion.state _).history
  rw [Completion.history_eq]
  exact member

theorem Accepted.output_early_admitted (accepted : Accepted pipeline policy before input current early fine)
    (output : IPv4Reassembly.Output) (emitted : accepted.result.output = some output)
    (piece : IPv4Reassembly.Piece) (member : piece ∈ output.pieces) :
    ∃ receipt ∈ accepted.state.history, receipt.fragment = piece.fragment ∧ receipt.guard.allows receipt.input = true := by
  obtain ⟨receipt, stored, same⟩ := accepted.output_sources output emitted piece member
  exact ⟨receipt, stored, same, receipt.accepted⟩

theorem Accepted.output_domain_source (accepted : Accepted pipeline policy before input current early fine)
    (output : IPv4Reassembly.Output) (emitted : accepted.result.output = some output)
    (piece : IPv4Reassembly.Piece) (member : piece ∈ output.pieces) :
    ∃ receipt ∈ accepted.state.history, receipt.fragment = piece.fragment ∧ receipt.input.domain = input.domain ∧
      receipt.input.now ≤ input.now ∧ receipt.guard.allows receipt.input = true := by
  let history : List Receipt := ⟨input, current, early, accepted.allowed⟩ :: before.history
  have previous : before.fragments.SourcesBy (Receipt.Source history) :=
    before.fragments.sourcesBy_mono _ _ before.sourcesBy (by
      rintro domain fragment ⟨receipt, stored, domainEq, bytesEq⟩
      exact ⟨receipt, List.mem_cons_of_mem _ stored, domainEq, bytesEq⟩)
  have head : Receipt.Source history input.domain input.fragment :=
    ⟨⟨input, current, early, accepted.allowed⟩, by simp [history], rfl, rfl⟩
  obtain ⟨receipt, stored, domainEq, same⟩ := IPv4Reassembly.arrive_output_sourcesBy _ _ _ _ _ _ _ _
    accepted.arrived emitted previous head piece member
  have member : receipt ∈ accepted.state.history := by
    change receipt ∈ (accepted.completion.state _).history
    rw [Completion.history_eq]
    exact stored
  have clock : accepted.state.clock = input.now := by
    change (accepted.completion.state _).clock = _
    rw [Completion.clock_eq]
    rfl
  exact ⟨receipt, member, same, domainEq, clock ▸ accepted.state.past receipt member, receipt.accepted⟩

def Receipt.context (receipt : Receipt) : Compile.FragmentAttachment.Input :=
  ⟨receipt.input.ingress, receipt.input.envelope⟩

theorem Receipt.application_permission (receipt : Receipt) (safe : receipt.authentication.Safe)
    (executionNS : NamespaceRef) (attachments : List IngressAttachment.ExpectedAttachment)
    (maintenance : List Compile.IngressAttachment.Maintenance) (application : List Match)
    (unique : Compile.IngressAttachment.LiveUnique receipt.authentication)
    (live : receipt.input.ingress ∈ receipt.authentication.live) (sameNS : receipt.input.ingress.ns = executionNS)
    (separated : Compile.FragmentAttachment.checkDisjoint maintenance application = true)
    (covered : ∃ traffic ∈ application, traffic.erasePorts.Holds receipt.input.envelope.toHeader)
    (compared : IngressPolicy.check receipt.guard.policy
      (Compile.FragmentAttachment.compile receipt.authentication executionNS attachments maintenance) = true) :
    ∃ attachment ∈ attachments, Compile.FragmentAttachment.allows receipt.authentication attachment receipt.context = true ∧
      Session.Valid receipt.authentication.context receipt.authentication.state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext receipt.authentication.context) receipt.authentication.state.auth ∧
      receipt.input.ingress = attachment.ingress ∧ attachment.origin.principal = receipt.authentication.context.consumer :=
  Compile.FragmentAttachment.actual_application_permission receipt.authentication safe executionNS attachments maintenance
    application receipt.context unique live sameNS separated covered receipt.guard.policy compared receipt.accepted

structure Residency where
  active : Option State
  archive : List State := []

def Residency.initial (ns : NamespaceRef) : Residency := ⟨some (State.initial ns), []⟩

def Residency.retire (before : Residency) : Except String Residency :=
  match before.active with
  | none => .error "There is no live namespace to retire."
  | some state => .ok ⟨none, before.archive ++ [state]⟩

def Residency.fresh (before : Residency) (ns : NamespaceRef) : Except String Residency :=
  if before.active.isSome then .error "Retire the active namespace before creating its successor."
  else if before.archive.any (fun state => decide (state.ns = ns)) then
    .error "A retired namespace lifetime cannot be reopened with its old fragment queues."
  else .ok ⟨some (State.initial ns), before.archive⟩

theorem Residency.retire_archive (before after : Residency) (retired : before.retire = .ok after) :
    ∃ state, before.active = some state ∧ after.active = none ∧ after.archive = before.archive ++ [state] := by
  unfold retire at retired
  cases selected : before.active with
  | none => simp [selected] at retired
  | some state =>
    simp only [selected, Except.ok.injEq] at retired
    cases retired
    exact ⟨state, rfl, rfl, rfl⟩

theorem Residency.fresh_state (before after : Residency) (ns : NamespaceRef) (created : before.fresh ns = .ok after) :
    after.active = some (State.initial ns) ∧ after.archive = before.archive ∧
      ∀ state ∈ before.archive, state.ns ≠ ns := by
  unfold fresh at created
  split at created
  · cases created
  · split at created
    · cases created
    · rename_i unused
      simp only [Except.ok.injEq] at created
      cases created
      refine ⟨rfl, rfl, ?_⟩
      intro state member same
      exact unused (List.any_eq_true.mpr ⟨state, member, by simp [same]⟩)

structure ResidentStep (pipeline : ReassemblyForwarding.Pipeline) (policy : IPv4Reassembly.Policy)
    (before : Residency) (input : Input) (current : Current) (early : EarlyGuard) (fine : IngressPolicy.Policy) where
  selected : State
  active : before.active = some selected
  operation : Result pipeline policy selected input current early fine
  computed : step pipeline policy selected input current early fine = .ok operation

def ResidentStep.state (result : ResidentStep pipeline policy before input current early fine) : Residency :=
  ⟨some result.operation.state, before.archive⟩

def Residency.step (pipeline : ReassemblyForwarding.Pipeline) (policy : IPv4Reassembly.Policy)
    (before : Residency) (input : Input) (current : Current) (early : EarlyGuard) (fine : IngressPolicy.Policy) :
    Except String (ResidentStep pipeline policy before input current early fine) :=
  match active : before.active with
  | none => .error "A retired namespace has no live packet operation."
  | some selected =>
    match computed : FragmentAdmission.step pipeline policy selected input current early fine with
    | .error reason => .error reason
    | .ok operation => .ok ⟨selected, active, operation, computed⟩

theorem ResidentStep.archive_unchanged (result : ResidentStep pipeline policy before input current early fine) :
    result.state.archive = before.archive := rfl

theorem Residency.retired_no_step (before after : Residency) (retired : before.retire = .ok after)
    (pipeline : ReassemblyForwarding.Pipeline) (policy : IPv4Reassembly.Policy) (input : Input)
    (current : Current) (early : EarlyGuard) (fine : IngressPolicy.Policy) :
    Residency.step pipeline policy after input current early fine = .error "A retired namespace has no live packet operation." := by
  obtain ⟨_, _, inactive, _⟩ := Residency.retire_archive before after retired
  unfold Residency.step
  split
  · rfl
  · rename_i selected active
    cases active.symm.trans inactive

structure SessionResidency where
  namespaces : Residency
  round : Nat

def SessionResidency.initial (ns : NamespaceRef) (current : Current) : Except String SessionResidency :=
  if current.state.auth.authorized then .ok ⟨Residency.initial ns, current.state.auth.round⟩
  else .error "Bind a namespace residency only after the authentication round is authorized."

def SessionResidency.retire (before : SessionResidency) : Except String SessionResidency := do
  return ⟨← before.namespaces.retire, before.round⟩

def SessionResidency.fresh (before : SessionResidency) (ns : NamespaceRef) (current : Current) : Except String SessionResidency := do
  if !current.state.auth.authorized then throw "A successor namespace requires a currently authorized authentication round."
  return ⟨← before.namespaces.fresh ns, current.state.auth.round⟩

def SessionResidency.step (pipeline : ReassemblyForwarding.Pipeline) (policy : IPv4Reassembly.Policy)
    (before : SessionResidency) (input : Input) (current : Current) (early : EarlyGuard) (fine : IngressPolicy.Policy) :
    Except String (ResidentStep pipeline policy before.namespaces input current early fine) :=
  if before.round = current.state.auth.round then Residency.step pipeline policy before.namespaces input current early fine
  else .error "A new authentication round requires retirement and a fresh namespace lifetime."

theorem SessionResidency.round_change (before : SessionResidency) (input : Input) (current : Current)
    (different : before.round ≠ current.state.auth.round) (pipeline : ReassemblyForwarding.Pipeline)
    (policy : IPv4Reassembly.Policy) (early : EarlyGuard) (fine : IngressPolicy.Policy) :
    SessionResidency.step pipeline policy before input current early fine =
      .error "A new authentication round requires retirement and a fresh namespace lifetime." := by
  simp only [SessionResidency.step, different, ite_false]

end Netlib.Protocol.FragmentAdmission
