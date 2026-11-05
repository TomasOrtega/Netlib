import Netlib.Protocol.EAPSession
import Netlib.Protocol.ConntrackReplication

/-!
# Session attachments at ingress

Namespace and interface births are supplied lifetime identities.
Installed numeric guards remain separate from the desired current attachments.
-/

namespace Netlib.Protocol.IngressAttachment

open Packet

structure NamespaceRef where
  id : Nat
  birth : Nat
  deriving Repr, DecidableEq

abbrev IfIndex := { value : Nat // 0 < value ∧ value ≤ 2147483647 }

structure InterfaceRef where
  ns : NamespaceRef
  ifindex : IfIndex
  birth : Nat
  deriving Repr, DecidableEq

structure Input where
  ingress : InterfaceRef
  header : Header
  deriving Repr, DecidableEq

inductive Role where
  | client
  | server
  deriving Repr, BEq, DecidableEq

def role : FlowNAT.Direction → Role
  | .original => .client
  | .reply => .server

structure Current where
  context : Context
  after : Nat
  state : EAPSession.State
  live : List InterfaceRef

def Current.Safe (current : Current) : Prop := current.state.Safe current.context

structure Origin where
  context : Context
  after : Nat
  source : EAPSession.State
  authenticationPort : InterfaceRef
  deriving Repr, DecidableEq

def Origin.principal (origin : Origin) : String := origin.context.consumer
def Origin.round (origin : Origin) : Nat := origin.source.auth.round

structure ExpectedAttachment where
  origin : Origin
  ingress : InterfaceRef
  direction : FlowNAT.Direction
  scope : Scope
  traffic : Match
  deriving Repr, DecidableEq

def ExpectedAttachment.role (attachment : ExpectedAttachment) : Role := IngressAttachment.role attachment.direction

def Current.Attached (current : Current) (attachment : ExpectedAttachment) : Prop :=
  attachment.origin.context = current.context ∧ attachment.origin.after ≤ current.after ∧
    attachment.origin.round = current.state.auth.round ∧ attachment.origin.authenticationPort ∈ current.live ∧
    attachment.ingress ∈ current.live

def Current.attached (current : Current) (attachment : ExpectedAttachment) : Bool :=
  decide (attachment.origin.context = current.context) && decide (attachment.origin.after ≤ current.after) &&
    decide (attachment.origin.round = current.state.auth.round) &&
    decide (attachment.origin.authenticationPort ∈ current.live) && decide (attachment.ingress ∈ current.live)

theorem Current.attached_correct (current : Current) (attachment : ExpectedAttachment) :
    current.attached attachment = true ↔ current.Attached attachment := by
  simp [attached, Attached, and_assoc]

def ExpectedAttachment.Valid (attachment : ExpectedAttachment) (current : Current) : Prop :=
  current.Attached attachment ∧ Session.Valid current.context current.state.session attachment.scope

def allows (current : Current) (attachment : ExpectedAttachment) (input : Input) : Bool :=
  current.attached attachment && current.state.session.permits current.context attachment.scope &&
    decide (input.ingress = attachment.ingress) && attachment.traffic.accepts input.header

inductive Error where
  | missingAuthenticationPort
  | missingIngress
  | deniedScope
  | mismatchedBinding
  deriving Repr, BEq, DecidableEq

def Error.describe : Error → String
  | .missingAuthenticationPort => "The authentication port lifetime is not current."
  | .missingIngress => "The data ingress lifetime is not current."
  | .deniedScope => "The current session does not permit the attachment scope."
  | .mismatchedBinding => "The selected conntrack record differs from the owned binding."

def stage (current : Current) (_safe : current.Safe) (authenticationPort ingress : InterfaceRef)
    (direction : FlowNAT.Direction) (scope : Scope) (traffic : Match) : Except Error ExpectedAttachment := do
  if authenticationPort ∉ current.live then throw .missingAuthenticationPort
  if ingress ∉ current.live then throw .missingIngress
  if !current.state.session.permits current.context scope then throw .deniedScope
  return ⟨⟨current.context, current.after, current.state, authenticationPort⟩, ingress, direction, scope, traffic⟩

inductive Guarded (State : Type u) (Result : Type v) where
  | rejected (state : State)
  | processed (result : Result)

/-- The supplied decision represents the actual installed guard. -/
def precheck (actualDecision : Bool) (before : State) (next : State → Except ErrorType Result) :
    Except ErrorType (Guarded State Result) :=
  if actualDecision then Guarded.processed <$> next before else .ok (.rejected before)

structure OwnedBinding where
  entry : NetfilterNAT.Entry
  origin : Origin
  deriving Repr, DecidableEq

structure OwnedSelection where
  source : OwnedBinding
  selection : ConntrackReplication.Selection
  selected : selection.record.entry = source.entry

def selectOwner (source : OwnedBinding) (selection : ConntrackReplication.Selection) : Except Error OwnedSelection :=
  if same : selection.record.entry = source.entry then .ok ⟨source, selection, same⟩ else .error .mismatchedBinding

/-- Ownership is controller provenance, separate from native conntrack attributes. -/
def OwnedSelection.inherit (selected : OwnedSelection) (installed : ConntrackReplication.Installed)
    (_chosen : installed.selection = selected.selection) : OwnedBinding :=
  ⟨installed.selection.recordForInstall.entry, selected.source.origin⟩

theorem allows_correct (current : Current) (attachment : ExpectedAttachment) (input : Input) :
    allows current attachment input = true ↔ attachment.Valid current ∧
      input.ingress = attachment.ingress ∧ attachment.traffic.Holds input.header := by
  simp [allows, ExpectedAttachment.Valid, Current.attached_correct, Session.permits_iff, Match.accepts_iff, and_assoc]

theorem allows_permission (current : Current) (safe : current.Safe) (attachment : ExpectedAttachment) (input : Input)
    (accepted : allows current attachment input = true) :
    Session.Valid current.context current.state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext current.context) current.state.auth := by
  have valid := ((allows_correct current attachment input).mp accepted).1.2
  have authorized : current.state.auth.authorized = true := safe.2.1.symm.trans valid.1
  exact ⟨valid, safe.1 authorized⟩

theorem allows_source (current : Current) (attachment : ExpectedAttachment) (input : Input)
    (accepted : allows current attachment input = true) :
    input.ingress = attachment.ingress ∧ attachment.traffic.Holds input.header ∧
      attachment.origin.context = current.context ∧ attachment.origin.principal = current.context.consumer ∧
      attachment.origin.after ≤ current.after ∧ attachment.origin.round = current.state.auth.round ∧
      attachment.origin.authenticationPort ∈ current.live ∧ input.ingress ∈ current.live := by
  obtain ⟨⟨attached, _⟩, ingress, traffic⟩ := (allows_correct current attachment input).mp accepted
  exact ⟨ingress, traffic, attached.1, congrArg Context.consumer attached.1,
    attached.2.1, attached.2.2.1, attached.2.2.2.1, by rw [ingress]; exact attached.2.2.2.2⟩

theorem reject_ingress (current : Current) (attachment : ExpectedAttachment) (input : Input)
    (different : input.ingress ≠ attachment.ingress) : allows current attachment input = false := by
  simp [allows, different]

theorem reject_namespace (current : Current) (attachment : ExpectedAttachment) (input : Input)
    (different : input.ingress.ns ≠ attachment.ingress.ns) : allows current attachment input = false :=
  reject_ingress current attachment input (fun same => different (congrArg InterfaceRef.ns same))

theorem reject_birth (current : Current) (attachment : ExpectedAttachment) (input : Input)
    (different : input.ingress.birth ≠ attachment.ingress.birth) : allows current attachment input = false :=
  reject_ingress current attachment input (fun same => different (congrArg InterfaceRef.birth same))

theorem reject_round (current : Current) (attachment : ExpectedAttachment) (input : Input)
    (different : attachment.origin.round ≠ current.state.auth.round) : allows current attachment input = false := by
  simp [allows, Current.attached, different]

theorem reject_authentication_port (current : Current) (attachment : ExpectedAttachment) (input : Input)
    (missing : attachment.origin.authenticationPort ∉ current.live) : allows current attachment input = false := by
  simp [allows, Current.attached, missing]

theorem reject_scope (current : Current) (attachment : ExpectedAttachment) (input : Input)
    (denied : current.state.session.permits current.context attachment.scope = false) :
    allows current attachment input = false := by simp [allows, denied]

private theorem stage_shape (current : Current) (safe : current.Safe) (authenticationPort ingress : InterfaceRef)
    (direction : FlowNAT.Direction) (scope : Scope) (traffic : Match) (attachment : ExpectedAttachment)
    (accepted : stage current safe authenticationPort ingress direction scope traffic = .ok attachment) :
    attachment = ⟨⟨current.context, current.after, current.state, authenticationPort⟩, ingress, direction, scope, traffic⟩ ∧
      authenticationPort ∈ current.live ∧ ingress ∈ current.live ∧ current.state.session.permits current.context scope = true := by
  by_cases authentication : authenticationPort ∈ current.live
  · by_cases data : ingress ∈ current.live
    · by_cases permitted : current.state.session.permits current.context scope = true
      · exact ⟨by simpa [stage, authentication, data, permitted, pure, Except.pure] using accepted.symm, authentication, data, permitted⟩
      · have denied : current.state.session.permits current.context scope = false := Bool.eq_false_iff.mpr permitted
        simp [stage, authentication, data, denied, throw, Functor.map, Except.map] at accepted
    · simp [stage, authentication, data, throw, bind, Except.bind] at accepted
  · simp [stage, authentication, throw, bind, Except.bind] at accepted

theorem stage_fields (current : Current) (safe : current.Safe) (authenticationPort ingress : InterfaceRef)
    (direction : FlowNAT.Direction) (scope : Scope) (traffic : Match) (attachment : ExpectedAttachment)
    (accepted : stage current safe authenticationPort ingress direction scope traffic = .ok attachment) :
    attachment.origin = ⟨current.context, current.after, current.state, authenticationPort⟩ ∧
      attachment.ingress = ingress ∧ attachment.direction = direction ∧ attachment.scope = scope ∧ attachment.traffic = traffic := by
  obtain ⟨rfl, _⟩ := stage_shape current safe authenticationPort ingress direction scope traffic attachment accepted
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stage_valid (current : Current) (safe : current.Safe) (authenticationPort ingress : InterfaceRef)
    (direction : FlowNAT.Direction) (scope : Scope) (traffic : Match) (attachment : ExpectedAttachment)
    (accepted : stage current safe authenticationPort ingress direction scope traffic = .ok attachment) : attachment.Valid current := by
  obtain ⟨rfl, authentication, data, permitted⟩ := stage_shape current safe authenticationPort ingress direction scope traffic attachment accepted
  exact ⟨⟨rfl, Nat.le_refl _, rfl, authentication, data⟩, (Session.permits_iff _ _ _).mp permitted⟩

theorem stage_completes (current : Current) (safe : current.Safe) (authenticationPort ingress : InterfaceRef)
    (direction : FlowNAT.Direction) (scope : Scope) (traffic : Match)
    (authentication : authenticationPort ∈ current.live) (data : ingress ∈ current.live)
    (permitted : current.state.session.permits current.context scope = true) :
    ∃ attachment, stage current safe authenticationPort ingress direction scope traffic = .ok attachment ∧ attachment.Valid current := by
  let attachment : ExpectedAttachment := ⟨⟨current.context, current.after, current.state, authenticationPort⟩, ingress, direction, scope, traffic⟩
  have accepted : stage current safe authenticationPort ingress direction scope traffic = .ok attachment := by
    simp only [stage, attachment, authentication, not_true_eq_false, ite_false, data, permitted, Bool.not_true, Bool.false_eq_true,
      pure, Except.pure]
  exact ⟨attachment, accepted, stage_valid current safe authenticationPort ingress direction scope traffic attachment accepted⟩

theorem stage_origin (current : Current) (safe : current.Safe) (authenticationPort ingress : InterfaceRef)
    (direction : FlowNAT.Direction) (scope : Scope) (traffic : Match) (attachment : ExpectedAttachment)
    (accepted : stage current safe authenticationPort ingress direction scope traffic = .ok attachment) :
    attachment.origin.source = current.state ∧ attachment.origin.after = current.after ∧
      attachment.origin.principal = current.context.consumer ∧ attachment.origin.round = current.state.auth.round ∧
      attachment.origin.authenticationPort = authenticationPort := by
  have origin := (stage_fields current safe authenticationPort ingress direction scope traffic attachment accepted).1
  simp [origin, Origin.principal, Origin.round]

theorem precheck_reject (before : State) (next : State → Except ErrorType Result) :
    precheck false before next = .ok (.rejected before) := rfl

theorem precheck_rejected (decision : Bool) (before after : State) (next : State → Except ErrorType Result)
    (accepted : precheck decision before next = .ok (.rejected after)) : decision = false ∧ after = before := by
  cases decision
  · simp only [precheck, Bool.false_eq_true, ite_false, Except.ok.injEq, Guarded.rejected.injEq] at accepted
    exact ⟨rfl, accepted.symm⟩
  · cases computed : next before <;> simp [precheck, computed, Functor.map, Except.map] at accepted

theorem precheck_processed (decision : Bool) (before : State) (next : State → Except ErrorType Result) (result : Result)
    (accepted : precheck decision before next = .ok (.processed result)) : decision = true ∧ next before = .ok result := by
  cases decision
  · simp [precheck] at accepted
  · cases computed : next before with
    | error error => simp [precheck, computed, Functor.map, Except.map] at accepted
    | ok actual =>
      simp only [precheck, ite_true, Functor.map, Except.map, computed, Except.ok.injEq, Guarded.processed.injEq] at accepted
      cases accepted
      exact ⟨rfl, rfl⟩

theorem processed_permission (current : Current) (safe : current.Safe) (attachment : ExpectedAttachment) (input : Input)
    (decision : Bool) (before : State) (next : State → Except ErrorType Result) (result : Result)
    (refines : decision = true → allows current attachment input = true)
    (accepted : precheck decision before next = .ok (.processed result)) :
    Session.Valid current.context current.state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext current.context) current.state.auth :=
  allows_permission current safe attachment input (refines (precheck_processed decision before next result accepted).1)

theorem selectOwner_fields (source : OwnedBinding) (selection : ConntrackReplication.Selection) (selected : OwnedSelection)
    (accepted : selectOwner source selection = .ok selected) : selected.source = source ∧ selected.selection = selection := by
  unfold selectOwner at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, rfl⟩
  · cases accepted

theorem OwnedSelection.inherit_fields (selected : OwnedSelection) (installed : ConntrackReplication.Installed)
    (chosen : installed.selection = selected.selection) :
    (selected.inherit installed chosen).entry = selected.source.entry ∧
      (selected.inherit installed chosen).origin = selected.source.origin := by
  constructor
  · simpa only [OwnedSelection.inherit, chosen, ConntrackReplication.Selection.recordForInstall] using selected.selected
  · rfl

theorem precheck_denied (current : Current) (attachment : ExpectedAttachment) (input : Input)
    (decision : Bool) (before : State) (next : State → Except ErrorType Result)
    (refines : decision = true → allows current attachment input = true)
    (denied : allows current attachment input = false) : precheck decision before next = .ok (.rejected before) := by
  cases decision
  · rfl
  · have accepted := refines rfl
    simp [denied] at accepted

theorem stage_permission (current : Current) (safe : current.Safe) (authenticationPort ingress : InterfaceRef)
    (direction : FlowNAT.Direction) (scope : Scope) (traffic : Match) (attachment : ExpectedAttachment)
    (accepted : stage current safe authenticationPort ingress direction scope traffic = .ok attachment) :
    Session.Valid attachment.origin.context attachment.origin.source.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext attachment.origin.context) attachment.origin.source.auth := by
  have valid := stage_valid current safe authenticationPort ingress direction scope traffic attachment accepted
  have fields := stage_fields current safe authenticationPort ingress direction scope traffic attachment accepted
  have authorized : current.state.auth.authorized = true := safe.2.1.symm.trans valid.2.1
  have ready := safe.1 authorized
  rw [fields.1]
  exact ⟨valid.2, ready⟩

theorem stage_same_origin (current : Current) (safe : current.Safe) (authenticationPort : InterfaceRef)
    (firstPort secondPort : InterfaceRef) (firstDirection secondDirection : FlowNAT.Direction)
    (firstScope secondScope : Scope) (firstTraffic secondTraffic : Match)
    (first second : ExpectedAttachment)
    (firstAccepted : stage current safe authenticationPort firstPort firstDirection firstScope firstTraffic = .ok first)
    (secondAccepted : stage current safe authenticationPort secondPort secondDirection secondScope secondTraffic = .ok second) :
    first.origin = second.origin :=
  (stage_fields current safe authenticationPort firstPort firstDirection firstScope firstTraffic first firstAccepted).1.trans
    (stage_fields current safe authenticationPort secondPort secondDirection secondScope secondTraffic second secondAccepted).1.symm

end Netlib.Protocol.IngressAttachment
