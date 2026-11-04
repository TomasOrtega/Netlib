import Netlib.Packet.Partition

namespace Netlib.Compile.ACL

open Packet

/-- Each requirement permits or forbids a complete packet class. -/
structure Intent where
  id : String
  test : Match
  action : Action
  deriving Repr, BEq, DecidableEq

def Permitted (intents : List Intent) (header : Header) : Prop :=
  ∃ intent ∈ intents, intent.action = .permit ∧ intent.test.accepts header = true

def Forbidden (intents : List Intent) (header : Header) : Prop :=
  ∃ intent ∈ intents, intent.action = .deny ∧ intent.test.accepts header = true

/-- Unspecified traffic is denied. Conflicting requirements have no priority. -/
def Meaning (intents : List Intent) (header : Header) : Prop :=
  Permitted intents header ∧ ¬Forbidden intents header

def Consistent (intents : List Intent) : Prop :=
  ∀ header, ¬(Permitted intents header ∧ Forbidden intents header)

def Satisfies (intents : List Intent) (rules : Packet.ACL) : Prop :=
  (∀ header, Permitted intents header → rules.allows header = true) ∧
  (∀ header, Forbidden intents header → rules.allows header = false)

structure Entry where
  requirementId : String
  rule : Rule
  deriving Repr, BEq, DecidableEq

/-- Permit order follows the input. Hard prohibitions are checked before emission. -/
def emit : List Intent → List Entry
  | [] => []
  | intent :: intents =>
    if intent.action = .permit then
      ⟨intent.id, ⟨intent.test, .permit⟩⟩ :: emit intents
    else emit intents

theorem emit_allows_iff (intents : List Intent) (header : Header) :
    Packet.ACL.allows ((emit intents).map Entry.rule) header = true ↔ Permitted intents header := by
  induction intents with
  | nil => simp [emit, Permitted]
  | cons intent intents ih =>
    cases action : intent.action with
    | deny => simpa [emit, action, Permitted] using ih
    | permit =>
      cases accepted : intent.test.accepts header with
      | false =>
        have same : Packet.ACL.allows ((emit (intent :: intents)).map Entry.rule) header =
            Packet.ACL.allows ((emit intents).map Entry.rule) header := by
          simp only [emit, action, ite_true, List.map_cons]
          unfold Packet.ACL.allows
          rw [Packet.ACL.evaluate_cons_rejects _ _ _ _ accepted]
        rw [same, ih]
        simp [Permitted, action, accepted]
      | true =>
        simp [emit, action, Permitted, Packet.ACL.allows, Packet.ACL.evaluate,
          Packet.ACL.lookup, accepted]

theorem emit_ids (intents : List Intent) :
    (emit intents).map Entry.requirementId =
      (intents.filter (fun intent => decide (intent.action = .permit))).map Intent.id := by
  induction intents with
  | nil => rfl
  | cons intent intents ih =>
    by_cases permitted : intent.action = .permit <;> simp [emit, permitted, ih]

structure Certified (intents : List Intent) where
  entries : List Entry
  generated : entries = emit intents
  consistent : Consistent intents

namespace Certified

def rules (compiled : Certified intents) : Packet.ACL := compiled.entries.map (·.rule)

def ruleIds (compiled : Certified intents) : List String := compiled.entries.map (·.requirementId)

def requirementIds (_compiled : Certified intents) : List String := intents.map (·.id)

theorem ruleIds_eq (compiled : Certified intents) :
    compiled.ruleIds = (intents.filter (fun intent => decide (intent.action = .permit))).map Intent.id := by
  rw [ruleIds, compiled.generated, emit_ids]

theorem correct (compiled : Certified intents) (header : Header) :
    compiled.rules.allows header = true ↔ Meaning intents header := by
  rw [rules, compiled.generated, emit_allows_iff]
  exact ⟨fun permitted => ⟨permitted, fun forbidden => compiled.consistent header ⟨permitted, forbidden⟩⟩,
    fun meaning => meaning.1⟩

theorem satisfies (compiled : Certified intents) : Satisfies intents compiled.rules := by
  constructor
  · intro header permitted
    apply (compiled.correct header).mpr
    exact ⟨permitted, fun forbidden => compiled.consistent header ⟨permitted, forbidden⟩⟩
  · intro header forbidden
    cases allowed : compiled.rules.allows header with
    | false => rfl
    | true => exact False.elim (((compiled.correct header).mp allowed).2 forbidden)

end Certified

structure Conflict (intents : List Intent) where
  permitted : Intent
  forbidden : Intent
  header : Header
  permitted_mem : permitted ∈ intents
  forbidden_mem : forbidden ∈ intents
  permitted_action : permitted.action = .permit
  forbidden_action : forbidden.action = .deny
  permitted_accepts : permitted.test.accepts header = true
  forbidden_accepts : forbidden.test.accepts header = true

theorem Conflict.unsatisfiable (conflict : Conflict intents) (rules : Packet.ACL) :
    ¬Satisfies intents rules := by
  intro satisfies
  have permitted := satisfies.1 conflict.header ⟨conflict.permitted, conflict.permitted_mem,
    conflict.permitted_action, conflict.permitted_accepts⟩
  have forbidden := satisfies.2 conflict.header ⟨conflict.forbidden, conflict.forbidden_mem,
    conflict.forbidden_action, conflict.forbidden_accepts⟩
  simp [permitted] at forbidden

inductive InputError where
  | emptyPolicy
  | invalidId (id : String)
  | duplicateId (id : String)
  deriving Repr, BEq, DecidableEq

inductive Error (intents : List Intent) where
  | invalid (reason : InputError)
  | exhausted (required budget : Nat)
  | conflict (evidence : Conflict intents)

def Error.describe : Error intents → String
  | .invalid .emptyPolicy => "Supply at least one intent requirement."
  | .invalid (.invalidId id) => s!"Invalid intent requirement ID: {id}."
  | .invalid (.duplicateId id) => s!"Duplicate intent requirement ID: {id}."
  | .exhausted required budget => s!"Intent partition needs {required} cells; budget is {budget}."
  | .conflict evidence =>
    s!"Requirements {evidence.permitted.id} and {evidence.forbidden.id} conflict for packet {repr evidence.header}."

private def validId (id : String) : Bool :=
  !id.isEmpty && id.toList.all (fun char => char.isAlphanum || char == '_' || char == '-' || char == '.')

private def duplicateId : List String → Option String
  | [] => none
  | id :: ids => if ids.contains id then some id else duplicateId ids

def validate (intents : List Intent) : Option InputError :=
  if intents.isEmpty then some .emptyPolicy
  else match intents.find? (fun intent => !validId intent.id) with
    | some intent => some (.invalidId intent.id)
    | none => (duplicateId (intents.map (·.id))).map InputError.duplicateId

def partition (intents : List Intent) : Packet.Partition where
  tests := intents.map (·.test)

private def acceptsAction (action : Action) (intent : Intent) (header : Header) : Bool :=
  decide (intent.action = action) && intent.test.accepts header

private def hasAction (intents : List Intent) (action : Action) (header : Header) : Bool :=
  intents.any (fun intent => acceptsAction action intent header)

private theorem hasAction_iff (intents : List Intent) (action : Action) (header : Header) :
    hasAction intents action header = true ↔
      ∃ intent ∈ intents, intent.action = action ∧ intent.test.accepts header = true := by
  simp only [hasAction, List.any_eq_true, acceptsAction, Bool.and_eq_true, decide_eq_true_eq]

private theorem hasAction_stable (original intents : List Intent) (action : Action) (header : Header)
    (included : ∀ intent ∈ intents, intent ∈ original) :
    hasAction intents action ((partition original).representative header) = hasAction intents action header := by
  induction intents with
  | nil => rfl
  | cons intent intents ih =>
    change (acceptsAction action intent ((partition original).representative header) ||
      hasAction intents action ((partition original).representative header)) =
        (acceptsAction action intent header || hasAction intents action header)
    have same : acceptsAction action intent ((partition original).representative header) =
        acceptsAction action intent header := by
      unfold acceptsAction
      rw [(partition original).match_stable intent.test
        (List.mem_map.mpr ⟨intent, included intent (by simp), rfl⟩) header]
    rw [same, ih (fun next member => included next (List.mem_cons_of_mem _ member))]

private def overlaps (intents : List Intent) (header : Header) : Bool :=
  hasAction intents .permit header && hasAction intents .deny header

private theorem consistent_of_none (intents : List Intent)
    (none : (partition intents).representatives.find? (overlaps intents) = none) : Consistent intents := by
  intro header conflict
  have representativeMember := (partition intents).representative_mem header
  have rejected := (List.find?_eq_none.mp none) _ representativeMember
  have same : overlaps intents ((partition intents).representative header) = overlaps intents header := by
    unfold overlaps
    rw [hasAction_stable intents intents .permit header (fun _ member => member),
      hasAction_stable intents intents .deny header (fun _ member => member)]
  have accepted : overlaps intents header = true := by
    simp only [overlaps, Bool.and_eq_true]
    exact ⟨(hasAction_iff intents .permit header).mpr conflict.1,
      (hasAction_iff intents .deny header).mpr conflict.2⟩
  exact rejected (same.trans accepted)

private def conflictAt (intents : List Intent) (header : Header)
    (overlap : overlaps intents header = true) : Conflict intents := by
  have overlapPair : hasAction intents .permit header = true ∧ hasAction intents .deny header = true := by
    simpa only [overlaps, Bool.and_eq_true] using overlap
  exact
  match permittedFound : intents.find? (fun intent => acceptsAction .permit intent header) with
  | none => False.elim (by
      obtain ⟨intent, member, accepted⟩ := List.any_eq_true.mp overlapPair.1
      exact (List.find?_eq_none.mp permittedFound) intent member accepted)
  | some permitted =>
    match forbiddenFound : intents.find? (fun intent => acceptsAction .deny intent header) with
    | none => False.elim (by
        obtain ⟨intent, member, accepted⟩ := List.any_eq_true.mp overlapPair.2
        exact (List.find?_eq_none.mp forbiddenFound) intent member accepted)
    | some forbidden =>
      have permittedValid : permitted.action = .permit ∧ permitted.test.accepts header = true := by
        simpa only [acceptsAction, Bool.and_eq_true, decide_eq_true_eq] using List.find?_some permittedFound
      have forbiddenValid : forbidden.action = .deny ∧ forbidden.test.accepts header = true := by
        simpa only [acceptsAction, Bool.and_eq_true, decide_eq_true_eq] using List.find?_some forbiddenFound
      ⟨permitted, forbidden, header,
        List.mem_of_find?_eq_some permittedFound, List.mem_of_find?_eq_some forbiddenFound,
        permittedValid.1, forbiddenValid.1,
        permittedValid.2, forbiddenValid.2⟩

/-- Empty classes have no effect. Forbidden-only policies emit a deny-default empty ACL. -/
def compile (intents : List Intent) (budget : Nat := 100000) : Except (Error intents) (Certified intents) :=
  match validate intents with
  | some invalid => .error (.invalid invalid)
  | none =>
    if (partition intents).cellCount > budget then
      .error (.exhausted (partition intents).cellCount budget)
    else match found : (partition intents).representatives.find? (overlaps intents) with
      | some header => .error (.conflict (conflictAt intents header (List.find?_some found)))
      | none => .ok ⟨emit intents, rfl, consistent_of_none intents found⟩

theorem compile_valid (intents : List Intent) (budget : Nat) (compiled : Certified intents)
    (completed : compile intents budget = .ok compiled) : validate intents = none := by
  cases valid : validate intents with
  | none => rfl
  | some error => simp [compile, valid] at completed

theorem compile_within_budget (intents : List Intent) (budget : Nat) (compiled : Certified intents)
    (completed : compile intents budget = .ok compiled) :
    (partition intents).representatives.length ≤ budget := by
  rw [(partition intents).representatives_length]
  have valid := compile_valid intents budget compiled completed
  by_cases exhausted : (partition intents).cellCount > budget
  · simp [compile, valid, exhausted] at completed
  · exact Nat.le_of_not_gt exhausted

end Netlib.Compile.ACL
