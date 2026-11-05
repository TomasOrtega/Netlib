import Netlib.Compile.IngressAttachment
import Netlib.Import.NftablesIngress

/-!
# Actual ingress policy versus current session attachments

Comparison never replaces the installed numeric decision.
Maintenance exceptions must be disjoint from the selected application classes.
-/

namespace Netlib.Check.IngressGuard

open Packet Protocol
open IngressAttachment (Current NamespaceRef ExpectedAttachment)
abbrev Maintenance := Compile.IngressAttachment.Maintenance

structure Checked (current : Current) (executionNS : NamespaceRef)
    (attachments : List ExpectedAttachment) (maintenance : List Maintenance) (application : List Match) where
  source : Import.NftablesIngress.Snapshot
  namespaceEq : source.ns = executionNS
  unique : Compile.IngressAttachment.LiveUnique current
  separated : Compile.IngressAttachment.checkDisjoint maintenance application = true

def Checked.expected (_checked : Checked current executionNS attachments maintenance application) : IngressPolicy.Policy :=
  Compile.IngressAttachment.compile current executionNS attachments maintenance

def Checked.passed (checked : Checked current executionNS attachments maintenance application) : Bool :=
  IngressPolicy.check checked.source.compile checked.expected

def Checked.decision (checked : Checked current executionNS attachments maintenance application)
    (input : IngressAttachment.Input) : Bool := checked.source.permits input.ingress.ifindex.val input.header

theorem Checked.actual_decision (checked : Checked current executionNS attachments maintenance application)
    (input : IngressAttachment.Input) :
    checked.decision input = checked.source.compile.allows input.ingress.ifindex.val input.header :=
  (checked.source.compile_allows _ _).symm

theorem Checked.application_permission (checked : Checked current executionNS attachments maintenance application)
    (safe : current.Safe) (passed : checked.passed = true) (input : IngressAttachment.Input)
    (live : input.ingress ∈ current.live) (sameNS : input.ingress.ns = executionNS)
    (covered : ∃ traffic ∈ application, traffic.Holds input.header) (accepted : checked.decision input = true) :
    ∃ attachment ∈ attachments, IngressAttachment.allows current attachment input = true ∧
      Session.Valid current.context current.state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext current.context) current.state.auth ∧
      input.ingress = attachment.ingress ∧ attachment.origin.principal = current.context.consumer := by
  rw [checked.actual_decision] at accepted
  exact Compile.IngressAttachment.actual_application_permission current safe executionNS attachments maintenance application input
    checked.unique live sameNS checked.separated covered checked.source.compile passed accepted

theorem Checked.denied_application (checked : Checked current executionNS attachments maintenance application)
    (passed : checked.passed = true) (input : IngressAttachment.Input)
    (live : input.ingress ∈ current.live) (sameNS : input.ingress.ns = executionNS)
    (covered : ∃ traffic ∈ application, traffic.Holds input.header)
    (denied : ∀ attachment ∈ attachments, IngressAttachment.allows current attachment input = false) :
    checked.decision input = false := by
  cases actual : checked.decision input with
  | false => rfl
  | true =>
    have equivalent := (IngressPolicy.check_correct _ _).mp passed
    have compiled : checked.expected.allows input.ingress.ifindex.val input.header = true :=
      (equivalent _ _).symm.trans ((checked.actual_decision input).symm.trans actual)
    obtain ⟨attachment, member, allowed⟩ := Compile.IngressAttachment.compile_application current executionNS
      attachments maintenance application input checked.unique live sameNS
      ((Compile.IngressAttachment.checkDisjoint_correct _ _).mp checked.separated) covered compiled
    simp [denied attachment member] at allowed

def check (current : Current) (executionNS : NamespaceRef) (attachments : List ExpectedAttachment)
    (maintenance : List Maintenance) (application : List Match) (source : Import.NftablesIngress.Snapshot)
    (budget : Nat := 1000000) : Except String (Checked current executionNS attachments maintenance application) := do
  if namespaceEq : source.ns = executionNS then
    if unique : Compile.IngressAttachment.liveUnique current = true then
      match computed : Compile.IngressAttachment.checkDisjointBudget maintenance application budget with
      | .error reason => throw reason
      | .ok separated =>
        if disjoint : separated = true then
          have separatedTrue : Compile.IngressAttachment.checkDisjoint maintenance application = true :=
            (Compile.IngressAttachment.checkDisjoint_correct _ _).mpr
              ((Compile.IngressAttachment.checkDisjointBudget_correct _ _ budget separated computed).mp disjoint)
          let checked : Checked current executionNS attachments maintenance application :=
            ⟨source, namespaceEq, (Compile.IngressAttachment.liveUnique_correct _).mp unique, separatedTrue⟩
          let _ ← IngressPolicy.checkBudget checked.source.compile checked.expected budget
          return checked
        else throw "A maintenance exception overlaps the protected application class."
    else throw "Current namespace and interface indices have conflicting lifetimes."
  else throw "The installed ingress guard belongs to a different namespace lifetime."

end Netlib.Check.IngressGuard
