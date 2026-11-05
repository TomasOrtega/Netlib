import Netlib.Protocol.FragmentAdmissionFacts
import Netlib.Check.IngressGuard
import Netlib.Check.SessionInstallation

/-!
# Current-session checks for fragment admission

The installed guards compute transitions before comparison with desired policy.
Coarse admission and full-datagram permission remain separate checks.
-/

namespace Netlib.Check.FragmentAdmission

open Packet Protocol
abbrev ModelState := Protocol.FragmentAdmission.State
abbrev ModelInput := Protocol.FragmentAdmission.Input
abbrev EarlyGuard := Protocol.FragmentAdmission.EarlyGuard
abbrev ModelResult := Protocol.FragmentAdmission.Result

structure Contract where
  current : IngressAttachment.Current
  safe : current.Safe
  ns : IngressAttachment.NamespaceRef
  attachments : List IngressAttachment.ExpectedAttachment
  maintenance : List Compile.IngressAttachment.Maintenance
  application : List Match

def Contract.at (authentication : Check.EAP.Input) (after : Nat) (ns : IngressAttachment.NamespaceRef)
    (live : List IngressAttachment.InterfaceRef) (attachments : List IngressAttachment.ExpectedAttachment)
    (maintenance : List Compile.IngressAttachment.Maintenance) (application : List Match) : Except String Contract :=
  if after ≤ authentication.observations.length then
    .ok ⟨⟨authentication.context, after, SessionInstallation.current authentication after, live⟩,
      Check.SessionFirewall.stateAt_safe authentication after, ns, attachments, maintenance, application⟩
  else .error "The fragment contract cannot name an unconsumed authentication prefix."

def Contract.early (contract : Contract) : IngressPolicy.Policy :=
  Compile.FragmentAttachment.compile contract.current contract.ns contract.attachments contract.maintenance

def Contract.fine (contract : Contract) : IngressPolicy.Policy :=
  Compile.IngressAttachment.compile contract.current contract.ns contract.attachments contract.maintenance

def coarseCovered (contract : Contract) (input : ModelInput) : Bool :=
  contract.application.any (fun traffic => traffic.erasePorts.accepts input.envelope.toHeader)

def completedHeader : ModelResult pipeline policy before input current early fine → Option Header
  | .rejected .. => none
  | .accepted evidence => match evidence.completion with
    | .waiting _ => none
    | .rejected _ _ source _ | .processed _ _ source _ _ => some source.packet.header

structure Checked (contract : Contract) (pipeline : ReassemblyForwarding.Pipeline) (policy : IPv4Reassembly.Policy)
    (before : ModelState) (input : ModelInput) (early : EarlyGuard) (fine : IngressPolicy.Policy) where
  result : ModelResult pipeline policy before input contract.current early fine
  computed : Protocol.FragmentAdmission.step pipeline policy before input contract.current early fine = .ok result
  live : input.ingress ∈ contract.current.live
  namespaceEq : input.ingress.ns = contract.ns
  unique : Compile.IngressAttachment.LiveUnique contract.current
  earlyEquivalent : Bool
  earlyCompared : earlyEquivalent = true ↔ IngressPolicy.Equivalent early.policy contract.early
  fineEquivalent : Bool
  fineCompared : fineEquivalent = true ↔ IngressPolicy.Equivalent fine contract.fine
  separated : Bool
  separation : separated = true ↔ Compile.FragmentAttachment.Disjoint contract.maintenance contract.application

def Checked.state (checked : Checked contract pipeline policy before input early fine) : ModelState := checked.result.state

def Checked.fineCovered (checked : Checked contract pipeline policy before input early fine) : Bool :=
  (completedHeader checked.result).all (fun header => contract.application.any (·.accepts header))

def Checked.passed (checked : Checked contract pipeline policy before input early fine) : Bool :=
  checked.earlyEquivalent && checked.separated && coarseCovered contract input && checked.fineCovered &&
    ((completedHeader checked.result).isNone || checked.fineEquivalent)

def check (contract : Contract) (pipeline : ReassemblyForwarding.Pipeline) (policy : IPv4Reassembly.Policy)
    (before : ModelState) (input : ModelInput) (early : EarlyGuard) (fine : IngressPolicy.Policy)
    (budget : Nat := 1000000) : Except String (Checked contract pipeline policy before input early fine) := do
  if live : input.ingress ∈ contract.current.live then
    if sameNS : input.ingress.ns = contract.ns then
      if unique : Compile.IngressAttachment.liveUnique contract.current = true then
        match computed : Protocol.FragmentAdmission.step pipeline policy before input contract.current early fine with
        | .error reason => throw reason
        | .ok result =>
          match earlyCompared : IngressPolicy.checkBudget early.policy contract.early budget with
          | .error reason => throw reason
          | .ok earlyEquivalent =>
            match fineCompared : IngressPolicy.checkBudget fine contract.fine budget with
            | .error reason => throw reason
            | .ok fineEquivalent =>
              match separation : Compile.FragmentAttachment.checkDisjointBudget contract.maintenance contract.application budget with
              | .error reason => throw reason
              | .ok separated =>
                return ⟨result, computed, live, sameNS, (Compile.IngressAttachment.liveUnique_correct _).mp unique,
                  earlyEquivalent, IngressPolicy.checkBudget_correct _ _ _ _ earlyCompared,
                  fineEquivalent, IngressPolicy.checkBudget_correct _ _ _ _ fineCompared,
                  separated, Compile.FragmentAttachment.checkDisjointBudget_correct _ _ _ _ separation⟩
      else throw "Current ingress lifetimes conflict within a namespace."
    else throw "The fragment contract belongs to another namespace lifetime."
  else throw "The observed ingress lifetime is not in the current registry."

theorem Checked.early_permission (checked : Checked contract pipeline policy before input early fine)
    (passed : checked.passed = true) (allowed : early.allows input = true) :
    ∃ attachment ∈ contract.attachments, Compile.FragmentAttachment.allows contract.current attachment
      ⟨input.ingress, input.envelope⟩ = true ∧
      Session.Valid contract.current.context contract.current.state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext contract.current.context) contract.current.state.auth ∧
      input.ingress = attachment.ingress ∧ attachment.origin.principal = contract.current.context.consumer := by
  have conditions : checked.earlyEquivalent = true ∧ checked.separated = true ∧ coarseCovered contract input = true ∧
      checked.fineCovered = true ∧ ((completedHeader checked.result).isNone || checked.fineEquivalent) = true := by
    simpa only [Checked.passed, Bool.and_eq_true, and_assoc] using passed
  have covered : ∃ traffic ∈ contract.application, traffic.erasePorts.Holds input.envelope.toHeader := by
    simpa only [coarseCovered, List.any_eq_true, Match.accepts_iff] using conditions.2.2.1
  exact Compile.FragmentAttachment.actual_application_permission contract.current contract.safe contract.ns
    contract.attachments contract.maintenance contract.application ⟨input.ingress, input.envelope⟩ checked.unique checked.live
    checked.namespaceEq (Compile.FragmentAttachment.checkDisjoint_correct _ _ |>.mpr (checked.separation.mp conditions.2.1))
    covered early.policy (IngressPolicy.check_correct _ _ |>.mpr (checked.earlyCompared.mp conditions.1)) allowed

theorem coarse_disjoint_implies_fine (maintenance : List Compile.IngressAttachment.Maintenance) (application : List Match)
    (separated : Compile.FragmentAttachment.Disjoint maintenance application) :
    Compile.IngressAttachment.Disjoint maintenance application := by
  intro entry member traffic selected header accepted matched
  exact separated (Compile.FragmentAttachment.coarseMaintenance entry) (List.mem_map.mpr ⟨entry, member, rfl⟩)
    traffic.erasePorts (List.mem_map.mpr ⟨traffic, selected, rfl⟩) header
    (Match.full_selection_implies_coarse entry.traffic header accepted)
    (Match.full_selection_implies_coarse traffic header matched)

theorem Checked.completed_permission (checked : Checked contract pipeline policy before input early fine)
    (passed : checked.passed = true) (header : Header) (completed : completedHeader checked.result = some header)
    (allowed : fine.allows input.ingress.ifindex.val header = true) :
    ∃ attachment ∈ contract.attachments, IngressAttachment.allows contract.current attachment ⟨input.ingress, header⟩ = true ∧
      Session.Valid contract.current.context contract.current.state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext contract.current.context) contract.current.state.auth ∧
      input.ingress = attachment.ingress ∧ attachment.origin.principal = contract.current.context.consumer := by
  have conditions : checked.earlyEquivalent = true ∧ checked.separated = true ∧ coarseCovered contract input = true ∧
      checked.fineCovered = true ∧ ((completedHeader checked.result).isNone || checked.fineEquivalent) = true := by
    simpa only [Checked.passed, Bool.and_eq_true, and_assoc] using passed
  have fineCompared : checked.fineEquivalent = true := by
    simpa only [completed, Option.isNone_some, Bool.false_or] using conditions.2.2.2.2
  have covered : ∃ traffic ∈ contract.application, traffic.Holds header := by
    simpa only [Checked.fineCovered, completed, Option.all_some, List.any_eq_true, Match.accepts_iff]
      using conditions.2.2.2.1
  have separated := coarse_disjoint_implies_fine contract.maintenance contract.application
    (checked.separation.mp conditions.2.1)
  exact Compile.IngressAttachment.actual_application_permission contract.current contract.safe contract.ns
    contract.attachments contract.maintenance contract.application ⟨input.ingress, header⟩ checked.unique checked.live
    checked.namespaceEq (Compile.IngressAttachment.checkDisjoint_correct _ _ |>.mpr separated) covered fine
    (IngressPolicy.check_correct _ _ |>.mpr (checked.fineCompared.mp fineCompared)) allowed

end Netlib.Check.FragmentAdmission
