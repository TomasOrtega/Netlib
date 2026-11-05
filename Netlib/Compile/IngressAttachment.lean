import Netlib.Protocol.IngressAttachment
import Netlib.Packet.IngressPolicy

/-!
# Numeric guards for current ingress attachments

Compilation describes desired rules without installing them.
Maintenance traffic remains separate from session-derived application access.
-/

namespace Netlib.Compile.IngressAttachment

open Packet
open Protocol.IngressAttachment (Current NamespaceRef InterfaceRef ExpectedAttachment Input)

structure Maintenance where
  ingress : InterfaceRef
  traffic : Match
  deriving Repr, DecidableEq

def Maintenance.allows (maintenance : Maintenance) (current : Current) (input : Input) : Bool :=
  decide (maintenance.ingress ∈ current.live) && decide (input.ingress = maintenance.ingress) &&
    maintenance.traffic.accepts input.header

def activeAttachment (current : Current) (executionNS : NamespaceRef) (attachment : ExpectedAttachment) : Bool :=
  current.attached attachment && current.state.session.permits current.context attachment.scope &&
    decide (attachment.ingress.ns = executionNS)

def activeMaintenance (current : Current) (executionNS : NamespaceRef) (maintenance : Maintenance) : Bool :=
  decide (maintenance.ingress ∈ current.live) && decide (maintenance.ingress.ns = executionNS)

def compile (current : Current) (executionNS : NamespaceRef) (attachments : List ExpectedAttachment)
    (maintenance : List Maintenance) : Packet.IngressPolicy.Policy where
  rules := ((attachments.filter (activeAttachment current executionNS)).map fun attachment =>
    ⟨some attachment.ingress.ifindex.val, attachment.traffic, .permit⟩) ++
    ((maintenance.filter (activeMaintenance current executionNS)).map fun entry =>
      ⟨some entry.ingress.ifindex.val, entry.traffic, .permit⟩)
  fallback := .deny

def LiveUnique (current : Current) : Prop :=
  ∀ first ∈ current.live, ∀ second ∈ current.live,
    first.ns = second.ns → first.ifindex.val = second.ifindex.val → first = second

def Disjoint (maintenance : List Maintenance) (application : List Match) : Prop :=
  ∀ entry ∈ maintenance, ∀ traffic ∈ application, ∀ header,
    entry.traffic.Holds header → ¬traffic.Holds header

private def maintenanceACL (maintenance : List Maintenance) : Packet.ACL :=
  maintenance.map fun entry => ⟨entry.traffic, .permit⟩

private def applicationComplement (application : List Match) : Packet.ACL :=
  (application.map fun traffic => ⟨traffic, .deny⟩) ++ [⟨{}, .permit⟩]

def checkDisjoint (maintenance : List Maintenance) (application : List Match) : Bool :=
  Partition.checkACLRefines (maintenanceACL maintenance) (applicationComplement application)

def checkDisjointBudget (maintenance : List Maintenance) (application : List Match) (budget : Nat := 100000) :
    Except String Bool := Partition.checkACLRefinesBudget (maintenanceACL maintenance) (applicationComplement application) budget

private theorem specialize_cons (rule : Packet.IngressPolicy.Rule) (rules : List Packet.IngressPolicy.Rule) (index : Nat) :
    (Packet.IngressPolicy.Policy.mk (rule :: rules) .deny).specialize index =
      if rule.interfaceMatches index then ⟨rule.traffic, rule.action⟩ :: (Packet.IngressPolicy.Policy.mk rules .deny).specialize index
      else (Packet.IngressPolicy.Policy.mk rules .deny).specialize index := by
  unfold Packet.IngressPolicy.Policy.specialize
  split
  · rename_i accepted
    conv =>
      lhs
      change (if rule.interfaceMatches index then _ else _) ++ _
      rw [ite_eq_left accepted]
    rfl
  · rename_i rejected
    conv =>
      lhs
      change (if rule.interfaceMatches index then _ else _) ++ _
      rw [ite_eq_right rejected]


private theorem acl_permit_cons (traffic : Match) (rules : Packet.ACL) (header : Header) :
    Packet.ACL.allows (⟨traffic, .permit⟩ :: rules) header = true ↔ traffic.accepts header = true ∨ rules.allows header = true := by
  cases matched : traffic.accepts header with
  | false =>
    have same : Packet.ACL.allows (⟨traffic, .permit⟩ :: rules) header = rules.allows header := by
      unfold Packet.ACL.allows
      rw [Packet.ACL.evaluate_cons_rejects _ _ _ _ matched]
    rw [same]
    simp only [Bool.false_eq_true, false_or]
  | true => simp [Packet.ACL.allows, Packet.ACL.evaluate, Packet.ACL.lookup, matched]

private theorem numeric_permits (rules : List Packet.IngressPolicy.Rule)
    (permitted : ∀ rule ∈ rules, rule.action = .permit) (index : Nat) (header : Header) :
    (Packet.IngressPolicy.Policy.mk rules .deny).allows index header = true ↔
      ∃ rule ∈ rules, rule.accepts index header = true := by
  induction rules with
  | nil =>
    change Packet.ACL.allows [⟨{}, .deny⟩] header = true ↔ ∃ rule ∈ [], _
    simp [Packet.ACL.allows, Packet.ACL.evaluate, Packet.ACL.lookup]
  | cons rule rules ih =>
    have action := permitted rule (by simp)
    have rest := ih (fun next member => permitted next (List.mem_cons_of_mem _ member))
    simp only [Packet.IngressPolicy.Policy.allows] at rest ⊢
    rw [specialize_cons]
    cases matchedInterface : rule.interfaceMatches index with
    | false => simpa [matchedInterface, Packet.IngressPolicy.Rule.accepts] using rest
    | true =>
      simp only [ite_true, action, acl_permit_cons, rest]
      simp [Packet.IngressPolicy.Rule.accepts, matchedInterface]


theorem activeAttachment_correct (current : Current) (executionNS : NamespaceRef) (attachment : ExpectedAttachment) :
    activeAttachment current executionNS attachment = true ↔
      attachment.Valid current ∧ attachment.ingress.ns = executionNS := by
  simp [activeAttachment, Protocol.IngressAttachment.ExpectedAttachment.Valid,
    Protocol.IngressAttachment.Current.attached_correct, Protocol.Session.permits_iff, and_assoc]

theorem activeMaintenance_correct (current : Current) (executionNS : NamespaceRef) (maintenance : Maintenance) :
    activeMaintenance current executionNS maintenance = true ↔
      maintenance.ingress ∈ current.live ∧ maintenance.ingress.ns = executionNS := by
  simp [activeMaintenance]

theorem Maintenance.allows_correct (maintenance : Maintenance) (current : Current) (input : Input) :
    maintenance.allows current input = true ↔ maintenance.ingress ∈ current.live ∧
      input.ingress = maintenance.ingress ∧ maintenance.traffic.Holds input.header := by
  simp [Maintenance.allows, Match.accepts_iff, and_assoc]

private theorem compile_permitted (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance)
    (rule : Packet.IngressPolicy.Rule) (member : rule ∈ (compile current executionNS attachments maintenance).rules) :
    rule.action = .permit := by
  simp only [compile] at member
  rcases List.mem_append.mp member with application | control
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp application
    rfl
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp control
    rfl

theorem compile_numeric_allows (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (index : Nat) (header : Header) :
    (compile current executionNS attachments maintenance).allows index header = true ↔
      (∃ attachment ∈ attachments, activeAttachment current executionNS attachment = true ∧
        index = attachment.ingress.ifindex.val ∧ attachment.traffic.Holds header) ∨
      (∃ entry ∈ maintenance, activeMaintenance current executionNS entry = true ∧
        index = entry.ingress.ifindex.val ∧ entry.traffic.Holds header) := by
  change (Packet.IngressPolicy.Policy.mk (compile current executionNS attachments maintenance).rules .deny).allows index header = true ↔ _
  rw [numeric_permits _ (compile_permitted current executionNS attachments maintenance)]
  constructor
  · rintro ⟨rule, member, accepts⟩
    simp only [compile] at member
    rcases List.mem_append.mp member with application | control
    · obtain ⟨attachment, filtered, generated⟩ := List.mem_map.mp application
      subst rule
      obtain ⟨member, active⟩ := List.mem_filter.mp filtered
      have pair : index = attachment.ingress.ifindex.val ∧ attachment.traffic.accepts header = true := by
        simpa only [Packet.IngressPolicy.Rule.accepts, Packet.IngressPolicy.Rule.interfaceMatches,
          Bool.and_eq_true, decide_eq_true_eq] using accepts
      exact .inl ⟨attachment, member, active, pair.1, (Match.accepts_iff _ _).mp pair.2⟩
    · obtain ⟨entry, filtered, generated⟩ := List.mem_map.mp control
      subst rule
      obtain ⟨member, active⟩ := List.mem_filter.mp filtered
      have pair : index = entry.ingress.ifindex.val ∧ entry.traffic.accepts header = true := by
        simpa only [Packet.IngressPolicy.Rule.accepts, Packet.IngressPolicy.Rule.interfaceMatches,
          Bool.and_eq_true, decide_eq_true_eq] using accepts
      exact .inr ⟨entry, member, active, pair.1, (Match.accepts_iff _ _).mp pair.2⟩
  · intro permitted
    rcases permitted with ⟨attachment, member, active, indexEq, headerMatch⟩ | ⟨entry, member, active, indexEq, headerMatch⟩
    · refine ⟨⟨some attachment.ingress.ifindex.val, attachment.traffic, .permit⟩, ?_, ?_⟩
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨attachment, List.mem_filter.mpr ⟨member, active⟩, rfl⟩)
      · simp [Packet.IngressPolicy.Rule.accepts, Packet.IngressPolicy.Rule.interfaceMatches, indexEq,
          (Match.accepts_iff _ _).mpr headerMatch]
    · refine ⟨⟨some entry.ingress.ifindex.val, entry.traffic, .permit⟩, ?_, ?_⟩
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨member, active⟩, rfl⟩)
      · simp [Packet.IngressPolicy.Rule.accepts, Packet.IngressPolicy.Rule.interfaceMatches, indexEq,
          (Match.accepts_iff _ _).mpr headerMatch]

theorem compile_allows (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (input : Input)
    (unique : LiveUnique current) (live : input.ingress ∈ current.live) (sameNS : input.ingress.ns = executionNS) :
    (compile current executionNS attachments maintenance).allows input.ingress.ifindex.val input.header = true ↔
      (∃ attachment ∈ attachments, Protocol.IngressAttachment.allows current attachment input = true) ∨
      (∃ entry ∈ maintenance, entry.allows current input = true) := by
  rw [compile_numeric_allows]
  constructor
  · intro allowed
    rcases allowed with ⟨attachment, member, active, indexEq, headerMatch⟩ | ⟨entry, member, active, indexEq, headerMatch⟩
    · obtain ⟨valid, namespaceEq⟩ := (activeAttachment_correct _ _ _).mp active
      have ingressEq := unique input.ingress live attachment.ingress valid.1.2.2.2.2
        (sameNS.trans namespaceEq.symm) indexEq
      exact .inl ⟨attachment, member, (Protocol.IngressAttachment.allows_correct _ _ _).mpr ⟨valid, ingressEq, headerMatch⟩⟩
    · obtain ⟨entryLive, namespaceEq⟩ := (activeMaintenance_correct _ _ _).mp active
      have ingressEq := unique input.ingress live entry.ingress entryLive (sameNS.trans namespaceEq.symm) indexEq
      exact .inr ⟨entry, member, (Maintenance.allows_correct _ _ _).mpr ⟨entryLive, ingressEq, headerMatch⟩⟩
  · intro allowed
    rcases allowed with ⟨attachment, member, accepted⟩ | ⟨entry, member, accepted⟩
    · obtain ⟨valid, ingressEq, headerMatch⟩ := (Protocol.IngressAttachment.allows_correct _ _ _).mp accepted
      have namespaceEq : attachment.ingress.ns = executionNS := (congrArg InterfaceRef.ns ingressEq).symm.trans sameNS
      exact .inl ⟨attachment, member, (activeAttachment_correct _ _ _).mpr ⟨valid, namespaceEq⟩,
        congrArg (fun port => port.ifindex.val) ingressEq, headerMatch⟩
    · obtain ⟨entryLive, ingressEq, headerMatch⟩ := (Maintenance.allows_correct _ _ _).mp accepted
      have namespaceEq : entry.ingress.ns = executionNS := (congrArg InterfaceRef.ns ingressEq).symm.trans sameNS
      exact .inr ⟨entry, member, (activeMaintenance_correct _ _ _).mpr ⟨entryLive, namespaceEq⟩,
        congrArg (fun port => port.ifindex.val) ingressEq, headerMatch⟩


private theorem maintenance_allows (maintenance : List Maintenance) (header : Header) :
    Packet.ACL.allows (maintenanceACL maintenance) header = true ↔
      ∃ entry ∈ maintenance, entry.traffic.Holds header := by
  induction maintenance with
  | nil => simp [maintenanceACL]
  | cons entry maintenance ih =>
    change Packet.ACL.allows (⟨entry.traffic, .permit⟩ :: maintenanceACL maintenance) header = true ↔ _
    rw [acl_permit_cons, ih]
    simp [Match.accepts_iff]

private theorem application_complement (application : List Match) (header : Header) :
    Packet.ACL.allows (applicationComplement application) header = true ↔
      ∀ traffic ∈ application, ¬traffic.Holds header := by
  induction application with
  | nil => simp [applicationComplement, Packet.ACL.allows, Packet.ACL.evaluate, Packet.ACL.lookup, Match.accepts]
  | cons traffic application ih =>
    cases matched : traffic.accepts header with
    | true =>
      have holds := (Match.accepts_iff _ _).mp matched
      simp [applicationComplement, Packet.ACL.allows, Packet.ACL.evaluate, Packet.ACL.lookup, matched, holds]
    | false =>
      have rejected : ¬traffic.Holds header := by
        intro holds
        have accepted := (Match.accepts_iff _ _).mpr holds
        simp [matched] at accepted
      have same : Packet.ACL.allows (applicationComplement (traffic :: application)) header =
          Packet.ACL.allows (applicationComplement application) header := by
        change Packet.ACL.allows (⟨traffic, .deny⟩ :: applicationComplement application) header = _
        unfold Packet.ACL.allows
        rw [Packet.ACL.evaluate_cons_rejects _ _ _ _ matched]
      rw [same, ih]
      simp [rejected]

theorem checkDisjoint_correct (maintenance : List Maintenance) (application : List Match) :
    checkDisjoint maintenance application = true ↔ Disjoint maintenance application := by
  change Partition.checkACLRefines (maintenanceACL maintenance) (applicationComplement application) = true ↔ _
  rw [Partition.checkACLRefines_iff]
  change (∀ header, Packet.ACL.allows (maintenanceACL maintenance) header = true →
    Packet.ACL.allows (applicationComplement application) header = true) ↔ _
  simp only [maintenance_allows, application_complement]
  constructor
  · intro checked entry member traffic included header selected
    exact checked header ⟨entry, member, selected⟩ traffic included
  · intro disjoint header ⟨entry, member, selected⟩ traffic included
    exact disjoint entry member traffic included header selected

theorem checkDisjointBudget_correct (maintenance : List Maintenance) (application : List Match)
    (budget : Nat) (value : Bool) (accepted : checkDisjointBudget maintenance application budget = .ok value) :
    value = true ↔ Disjoint maintenance application := by
  have correct := Partition.checkACLRefinesBudget_correct (maintenanceACL maintenance) (applicationComplement application)
    budget value accepted
  exact correct.trans ((Partition.checkACLRefines_iff _ _).symm.trans (checkDisjoint_correct maintenance application))

theorem compile_application (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (application : List Match) (input : Input)
    (unique : LiveUnique current) (live : input.ingress ∈ current.live) (sameNS : input.ingress.ns = executionNS)
    (disjoint : Disjoint maintenance application) (covered : ∃ traffic ∈ application, traffic.Holds input.header)
    (accepted : (compile current executionNS attachments maintenance).allows input.ingress.ifindex.val input.header = true) :
    ∃ attachment ∈ attachments, Protocol.IngressAttachment.allows current attachment input = true := by
  rcases (compile_allows current executionNS attachments maintenance input unique live sameNS).mp accepted with owned | control
  · exact owned
  · obtain ⟨entry, member, permit⟩ := control
    have headerMatch := ((Maintenance.allows_correct entry current input).mp permit).2.2
    obtain ⟨traffic, included, selected⟩ := covered
    exact False.elim (disjoint entry member traffic included input.header headerMatch selected)

theorem actual_application_permission (current : Current) (safe : current.Safe) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (application : List Match) (input : Input)
    (unique : LiveUnique current) (live : input.ingress ∈ current.live) (sameNS : input.ingress.ns = executionNS)
    (separated : checkDisjoint maintenance application = true) (covered : ∃ traffic ∈ application, traffic.Holds input.header)
    (actual : Packet.IngressPolicy.Policy) (compared : Packet.IngressPolicy.check actual (compile current executionNS attachments maintenance) = true)
    (accepted : actual.allows input.ingress.ifindex.val input.header = true) :
    ∃ attachment ∈ attachments, Protocol.IngressAttachment.allows current attachment input = true ∧
      Protocol.Session.Valid current.context current.state.session attachment.scope ∧
      Protocol.EAPAuth.State.Ready (Protocol.EAPSession.authContext current.context) current.state.auth ∧
      input.ingress = attachment.ingress ∧ attachment.origin.principal = current.context.consumer := by
  have equivalent := (Packet.IngressPolicy.check_correct _ _).mp compared
  have compiled := (equivalent input.ingress.ifindex.val input.header).symm.trans accepted
  obtain ⟨attachment, member, allowed⟩ := compile_application current executionNS attachments maintenance application input
    unique live sameNS ((checkDisjoint_correct _ _).mp separated) covered compiled
  obtain ⟨valid, ready⟩ := Protocol.IngressAttachment.allows_permission current safe attachment input allowed
  have source := Protocol.IngressAttachment.allows_source current attachment input allowed
  exact ⟨attachment, member, allowed, valid, ready, source.1, source.2.2.2.1⟩

def liveUnique (current : Current) : Bool :=
  current.live.all fun first => current.live.all fun second =>
    if first.ns = second.ns ∧ first.ifindex.val = second.ifindex.val then decide (first = second) else true

theorem liveUnique_correct (current : Current) : liveUnique current = true ↔ LiveUnique current := by
  simp only [liveUnique, List.all_eq_true]
  constructor
  · intro checked first firstLive second secondLive sameNS sameIndex
    have tested := checked first firstLive second secondLive
    simpa only [sameNS, sameIndex, and_self, ite_true, decide_eq_true_eq] using tested
  · intro unique first firstLive second secondLive
    split
    · rename_i same
      exact decide_eq_true (unique first firstLive second secondLive same.1 same.2)
    · rfl

theorem compile_unknown_index (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (index : Nat) (header : Header)
    (unknown : ∀ port ∈ current.live, port.ns = executionNS → index ≠ port.ifindex.val) :
    (compile current executionNS attachments maintenance).allows index header = false := by
  cases allowed : (compile current executionNS attachments maintenance).allows index header with
  | false => rfl
  | true =>
    rcases (compile_numeric_allows current executionNS attachments maintenance index header).mp allowed with
      ⟨attachment, _, active, selected, _⟩ | ⟨entry, _, active, selected, _⟩
    · obtain ⟨valid, namespaceEq⟩ := (activeAttachment_correct _ _ _).mp active
      exact False.elim (unknown attachment.ingress valid.1.2.2.2.2 namespaceEq selected)
    · obtain ⟨live, namespaceEq⟩ := (activeMaintenance_correct _ _ _).mp active
      exact False.elim (unknown entry.ingress live namespaceEq selected)

theorem compile_maintenance (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (entry : Maintenance)
    (member : entry ∈ maintenance) (live : entry.ingress ∈ current.live) (sameNS : entry.ingress.ns = executionNS)
    (header : Header) (selected : entry.traffic.Holds header) :
    (compile current executionNS attachments maintenance).allows entry.ingress.ifindex.val header = true :=
  (compile_numeric_allows current executionNS attachments maintenance _ _).mpr
    (.inr ⟨entry, member, (activeMaintenance_correct _ _ _).mpr ⟨live, sameNS⟩, rfl, selected⟩)

end Netlib.Compile.IngressAttachment
