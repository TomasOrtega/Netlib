import Netlib.Compile.IngressAttachment
import Netlib.Packet.IPv4Envelope

/-!
# Session attachment guards before IPv4 reassembly

Compilation erases every transport-port predicate.
Current interface lifetimes and session permission remain separate from installed numeric rules.
-/

namespace Netlib.Compile.FragmentAttachment

open Packet
open Protocol.IngressAttachment (Current NamespaceRef InterfaceRef ExpectedAttachment)
abbrev Maintenance := IngressAttachment.Maintenance

structure Input where
  ingress : InterfaceRef
  envelope : IPv4Envelope
  deriving Repr, DecidableEq

def Input.context (input : Input) : Protocol.IngressAttachment.Input := ⟨input.ingress, input.envelope.toHeader⟩

def coarse (attachment : ExpectedAttachment) : ExpectedAttachment :=
  { attachment with traffic := attachment.traffic.erasePorts }

def coarseMaintenance (entry : Maintenance) : Maintenance := { entry with traffic := entry.traffic.erasePorts }

def allows (current : Current) (attachment : ExpectedAttachment) (input : Input) : Bool :=
  Protocol.IngressAttachment.allows current (coarse attachment) input.context

def maintenanceAllows (current : Current) (entry : Maintenance) (input : Input) : Bool :=
  (coarseMaintenance entry).allows current input.context

def compile (current : Current) (executionNS : NamespaceRef) (attachments : List ExpectedAttachment)
    (maintenance : List Maintenance) : IngressPolicy.Policy :=
  IngressAttachment.compile current executionNS (attachments.map coarse) (maintenance.map coarseMaintenance)

def Disjoint (maintenance : List Maintenance) (application : List Match) : Prop :=
  IngressAttachment.Disjoint (maintenance.map coarseMaintenance) (application.map Match.erasePorts)

def checkDisjoint (maintenance : List Maintenance) (application : List Match) : Bool :=
  IngressAttachment.checkDisjoint (maintenance.map coarseMaintenance) (application.map Match.erasePorts)

def checkDisjointBudget (maintenance : List Maintenance) (application : List Match) (budget : Nat := 100000) :
    Except String Bool :=
  IngressAttachment.checkDisjointBudget (maintenance.map coarseMaintenance) (application.map Match.erasePorts) budget

theorem checkDisjoint_correct (maintenance : List Maintenance) (application : List Match) :
    checkDisjoint maintenance application = true ↔ Disjoint maintenance application :=
  IngressAttachment.checkDisjoint_correct _ _

theorem checkDisjointBudget_correct (maintenance : List Maintenance) (application : List Match)
    (budget : Nat) (value : Bool) (accepted : checkDisjointBudget maintenance application budget = .ok value) :
    value = true ↔ Disjoint maintenance application :=
  IngressAttachment.checkDisjointBudget_correct _ _ budget value accepted

@[simp] theorem coarse_valid (attachment : ExpectedAttachment) (current : Current) :
    (coarse attachment).Valid current ↔ attachment.Valid current := Iff.rfl

@[simp] theorem coarse_active (current : Current) (executionNS : NamespaceRef) (attachment : ExpectedAttachment) :
    IngressAttachment.activeAttachment current executionNS (coarse attachment) =
      IngressAttachment.activeAttachment current executionNS attachment := rfl

@[simp] theorem coarseMaintenance_active (current : Current) (executionNS : NamespaceRef) (entry : Maintenance) :
    IngressAttachment.activeMaintenance current executionNS (coarseMaintenance entry) =
      IngressAttachment.activeMaintenance current executionNS entry := rfl

theorem allows_correct (current : Current) (attachment : ExpectedAttachment) (input : Input) :
    allows current attachment input = true ↔ attachment.Valid current ∧ input.ingress = attachment.ingress ∧
      attachment.traffic.erasePorts.Holds input.envelope.toHeader :=
  Protocol.IngressAttachment.allows_correct current (coarse attachment) input.context

theorem allows_permission (current : Current) (safe : current.Safe) (attachment : ExpectedAttachment) (input : Input)
    (accepted : allows current attachment input = true) :
    Protocol.Session.Valid current.context current.state.session attachment.scope ∧
      Protocol.EAPAuth.State.Ready (Protocol.EAPSession.authContext current.context) current.state.auth :=
  Protocol.IngressAttachment.allows_permission current safe (coarse attachment) input.context accepted

theorem allows_source (current : Current) (attachment : ExpectedAttachment) (input : Input)
    (accepted : allows current attachment input = true) :
    input.ingress = attachment.ingress ∧ attachment.traffic.erasePorts.Holds input.envelope.toHeader ∧
      attachment.origin.context = current.context ∧ attachment.origin.principal = current.context.consumer ∧
      attachment.origin.after ≤ current.after ∧ attachment.origin.round = current.state.auth.round ∧
      attachment.origin.authenticationPort ∈ current.live ∧ input.ingress ∈ current.live :=
  Protocol.IngressAttachment.allows_source current (coarse attachment) input.context accepted

theorem full_selection_implies_coarse (current : Current) (attachment : ExpectedAttachment)
    (input : Protocol.IngressAttachment.Input) (selected : Protocol.IngressAttachment.allows current attachment input = true) :
    allows current attachment ⟨input.ingress, IPv4Envelope.ofHeader input.header⟩ = true := by
  obtain ⟨valid, ingress, selected⟩ := (Protocol.IngressAttachment.allows_correct _ _ _).mp selected
  apply (allows_correct _ _ _).mpr
  refine ⟨valid, ingress, ?_⟩
  apply (Match.accepts_iff _ _).mp
  rw [← Match.erasePorts_representative attachment.traffic input.header]
  exact Match.full_acceptance_implies_coarse _ _ ((Match.accepts_iff _ _).mpr selected)

theorem compile_numeric_allows (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (index : Nat) (header : Header) :
    (compile current executionNS attachments maintenance).allows index header = true ↔
      (∃ attachment ∈ attachments, IngressAttachment.activeAttachment current executionNS attachment = true ∧
        index = attachment.ingress.ifindex.val ∧ attachment.traffic.erasePorts.Holds header) ∨
      (∃ entry ∈ maintenance, IngressAttachment.activeMaintenance current executionNS entry = true ∧
        index = entry.ingress.ifindex.val ∧ entry.traffic.erasePorts.Holds header) := by
  rw [compile, IngressAttachment.compile_numeric_allows]
  constructor
  · intro accepted
    rcases accepted with ⟨attachment, member, active, selected, matched⟩ | ⟨entry, member, active, selected, matched⟩
    · obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
      exact .inl ⟨source, included, active, selected, matched⟩
    · obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
      exact .inr ⟨source, included, active, selected, matched⟩
  · intro accepted
    rcases accepted with ⟨attachment, member, active, selected, matched⟩ | ⟨entry, member, active, selected, matched⟩
    · exact .inl ⟨coarse attachment, List.mem_map.mpr ⟨attachment, member, rfl⟩, active, selected, matched⟩
    · exact .inr ⟨coarseMaintenance entry, List.mem_map.mpr ⟨entry, member, rfl⟩, active, selected, matched⟩

theorem compile_allows (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (input : Input)
    (unique : IngressAttachment.LiveUnique current) (live : input.ingress ∈ current.live)
    (sameNS : input.ingress.ns = executionNS) :
    (compile current executionNS attachments maintenance).allows input.ingress.ifindex.val input.envelope.toHeader = true ↔
      (∃ attachment ∈ attachments, allows current attachment input = true) ∨
      (∃ entry ∈ maintenance, maintenanceAllows current entry input = true) := by
  change (IngressAttachment.compile current executionNS (attachments.map coarse) (maintenance.map coarseMaintenance)).allows
    input.context.ingress.ifindex.val input.context.header = true ↔ _
  rw [IngressAttachment.compile_allows current executionNS _ _ input.context unique live sameNS]
  constructor
  · intro accepted
    rcases accepted with ⟨attachment, member, selected⟩ | ⟨entry, member, selected⟩
    · obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
      exact .inl ⟨source, included, selected⟩
    · obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
      exact .inr ⟨source, included, selected⟩
  · intro accepted
    rcases accepted with ⟨attachment, member, selected⟩ | ⟨entry, member, selected⟩
    · exact .inl ⟨coarse attachment, List.mem_map.mpr ⟨attachment, member, rfl⟩, selected⟩
    · exact .inr ⟨coarseMaintenance entry, List.mem_map.mpr ⟨entry, member, rfl⟩, selected⟩

theorem compile_port_independent (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (index : Nat) (first second : Header)
    (same : IPv4Envelope.ofHeader first = IPv4Envelope.ofHeader second) :
    (compile current executionNS attachments maintenance).allows index first =
      (compile current executionNS attachments maintenance).allows index second := by
  apply Bool.eq_iff_iff.mpr
  rw [compile_numeric_allows, compile_numeric_allows]
  have selectors (traffic : Match) : traffic.erasePorts.Holds first ↔ traffic.erasePorts.Holds second := by
    rw [← Match.accepts_iff, ← Match.accepts_iff, Match.erasePorts_sameEnvelope traffic first second same]
  simp only [selectors]

theorem compile_rules_no_ports (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (rule : IngressPolicy.Rule)
    (member : rule ∈ (compile current executionNS attachments maintenance).rules) :
    rule.traffic.sourcePorts = none ∧ rule.traffic.destinationPorts = none := by
  simp only [compile, IngressAttachment.compile] at member
  rcases List.mem_append.mp member with application | control
  · obtain ⟨attachment, filtered, rfl⟩ := List.mem_map.mp application
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp filtered).1
    exact ⟨rfl, rfl⟩
  · obtain ⟨entry, filtered, rfl⟩ := List.mem_map.mp control
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp filtered).1
    exact ⟨rfl, rfl⟩

theorem compile_noPorts (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) :
    IngressPolicy.NoPorts (compile current executionNS attachments maintenance) :=
  compile_rules_no_ports current executionNS attachments maintenance

theorem actual_port_independent (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (actual : IngressPolicy.Policy)
    (compared : IngressPolicy.check actual (compile current executionNS attachments maintenance) = true)
    (index : Nat) (first second : Header) (same : IPv4Envelope.ofHeader first = IPv4Envelope.ofHeader second) :
    actual.allows index first = actual.allows index second := by
  have equivalent := (IngressPolicy.check_correct _ _).mp compared
  rw [equivalent index first, equivalent index second]
  exact compile_port_independent current executionNS attachments maintenance index first second same

theorem compilecoarse_application (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (application : List Match) (input : Input)
    (unique : IngressAttachment.LiveUnique current) (live : input.ingress ∈ current.live)
    (sameNS : input.ingress.ns = executionNS) (disjoint : Disjoint maintenance application)
    (covered : ∃ traffic ∈ application, traffic.erasePorts.Holds input.envelope.toHeader)
    (accepted : (compile current executionNS attachments maintenance).allows input.ingress.ifindex.val input.envelope.toHeader = true) :
    ∃ attachment ∈ attachments, allows current attachment input = true := by
  have coverage : ∃ traffic ∈ application.map Match.erasePorts, traffic.Holds input.context.header := by
    obtain ⟨traffic, member, selected⟩ := covered
    exact ⟨traffic.erasePorts, List.mem_map.mpr ⟨traffic, member, rfl⟩, selected⟩
  obtain ⟨attachment, member, selected⟩ := IngressAttachment.compile_application current executionNS
    (attachments.map coarse) (maintenance.map coarseMaintenance) (application.map Match.erasePorts)
    input.context unique live sameNS disjoint coverage accepted
  obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
  exact ⟨source, included, selected⟩

theorem actual_application_permission (current : Current) (safe : current.Safe) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (application : List Match) (input : Input)
    (unique : IngressAttachment.LiveUnique current) (live : input.ingress ∈ current.live)
    (sameNS : input.ingress.ns = executionNS) (separated : checkDisjoint maintenance application = true)
    (covered : ∃ traffic ∈ application, traffic.erasePorts.Holds input.envelope.toHeader)
    (actual : IngressPolicy.Policy) (compared : IngressPolicy.check actual (compile current executionNS attachments maintenance) = true)
    (accepted : actual.allows input.ingress.ifindex.val input.envelope.toHeader = true) :
    ∃ attachment ∈ attachments, allows current attachment input = true ∧
      Protocol.Session.Valid current.context current.state.session attachment.scope ∧
      Protocol.EAPAuth.State.Ready (Protocol.EAPSession.authContext current.context) current.state.auth ∧
      input.ingress = attachment.ingress ∧ attachment.origin.principal = current.context.consumer := by
  have equivalent := (IngressPolicy.check_correct _ _).mp compared
  have compiled := (equivalent input.ingress.ifindex.val input.envelope.toHeader).symm.trans accepted
  obtain ⟨attachment, member, allowed⟩ := compilecoarse_application current executionNS attachments maintenance application input
    unique live sameNS ((checkDisjoint_correct _ _).mp separated) covered compiled
  obtain ⟨valid, ready⟩ := Protocol.IngressAttachment.allows_permission current safe (coarse attachment) input.context allowed
  have source := Protocol.IngressAttachment.allows_source current (coarse attachment) input.context allowed
  exact ⟨attachment, member, allowed, valid, ready, source.1, source.2.2.2.1⟩

end Netlib.Compile.FragmentAttachment
