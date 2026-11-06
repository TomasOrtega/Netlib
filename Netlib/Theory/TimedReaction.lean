import Std

/-!
# Timed reactions from checked operations

Each cause supplies one response credit in its local clock domain.
Coalescing retains the earliest due time. One response retires all covered causes.
The checked history below connects these records to actual operations and output.
-/

namespace Netlib.Theory.TimedReaction

universe u v w

structure Cause (Domain : Type u) (Demand : Type v) where
  id : Nat
  domain : Domain
  issuedAt : Nat
  due : Nat
  demand : Demand
  deriving Repr, BEq, DecidableEq

structure Discharge (Domain : Type u) (Demand : Type v) (Output : Type w) where
  id : Nat
  domain : Domain
  time : Nat
  output : Output
  causes : List (Cause Domain Demand)
  deriving Repr, BEq, DecidableEq

structure State (Domain : Type u) (Demand : Type v) (Output : Type w) where
  domain : Domain
  nextID : Nat := 0
  nextDischarge : Nat := 0
  pending : List (Cause Domain Demand) := []
  completed : List (Discharge Domain Demand Output) := []
  deriving Repr, BEq, DecidableEq

def initial (domain : Domain) : State Domain Demand Output := ⟨domain, 0, 0, [], []⟩

def credit (state : State Domain Demand Output) : Nat := state.pending.length

def earliest : List (Cause Domain Demand) → Option Nat
  | [] => none
  | cause :: rest => some (match earliest rest with | none => cause.due | some due => min cause.due due)

def pendingDue (state : State Domain Demand Output) : Option Nat := earliest state.pending

def fresh (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat) : Cause Domain Demand :=
  ⟨state.nextID, state.domain, now, now + delay, demand⟩

def issue (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat) : State Domain Demand Output :=
  { state with nextID := state.nextID + 1, pending := state.pending ++ [fresh state now demand delay] }

inductive Error where
  | noCredit | clock | deadline | coverage
  deriving Repr, BEq, DecidableEq

def checkTime (state : State Domain Demand Output) (now : Nat) : Except Error Unit :=
  if state.pending.any (fun cause => decide (now < cause.issuedAt)) then .error .clock
  else if state.pending.any (fun cause => decide (cause.due < now)) then .error .deadline
  else .ok ()

def completedState (state : State Domain Demand Output) (now : Nat) (output : Output) : State Domain Demand Output :=
  { state with
    nextDischarge := state.nextDischarge + 1
    pending := []
    completed := state.completed ++ [⟨state.nextDischarge, state.domain, now, output, state.pending⟩] }

def complete (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) : Except Error (State Domain Demand Output) :=
  if state.pending.isEmpty then .error .noCredit
  else match checkTime state now with
    | .error reason => .error reason
    | .ok _ =>
      if state.pending.all (fun cause => covers cause.demand output) then .ok (completedState state now output)
      else .error .coverage

inductive OutputKind where
  | response | independent
  deriving Repr, BEq, DecidableEq

structure Observation (Demand : Type v) (Output : Type w) where
  now : Nat
  request : Option (Demand × Nat) := none
  output : Option (OutputKind × Output) := none
  deriving Repr, BEq, DecidableEq

def requestedState (state : State Domain Demand Output) (event : Observation Demand Output) : State Domain Demand Output :=
  match event.request with | none => state | some (demand, delay) => issue state event.now demand delay

def issued (state : State Domain Demand Output) (event : Observation Demand Output) : List (Cause Domain Demand) :=
  match event.request with | none => [] | some (demand, delay) => [fresh state event.now demand delay]

def observe (state : State Domain Demand Output) (event : Observation Demand Output)
    (covers : Demand → Output → Bool) : Except Error (State Domain Demand Output) :=
  match checkTime state event.now with
  | .error reason => .error reason
  | .ok _ =>
    let next := requestedState state event
    match event.output with
    | none => .ok next
    | some (.response, output) => complete next event.now output covers
    | some (.independent, output) =>
      if next.pending.isEmpty then .ok next
      else if next.pending.all (fun cause => covers cause.demand output) then complete next event.now output covers
      else .ok next

theorem issue_domain (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat) :
    (issue state now demand delay).domain = state.domain := rfl

theorem issue_pending (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat) :
    (issue state now demand delay).pending = state.pending ++ [fresh state now demand delay] := rfl

theorem issue_completed (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat) :
    (issue state now demand delay).completed = state.completed := rfl

theorem issue_nextID (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat) :
    (issue state now demand delay).nextID = state.nextID + 1 := rfl

theorem issue_credit (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat) :
    credit (issue state now demand delay) = credit state + 1 := by simp [credit, issue]

theorem earliest_snoc (causes : List (Cause Domain Demand)) (cause : Cause Domain Demand) :
    earliest (causes ++ [cause]) = some (match earliest causes with | none => cause.due | some due => min due cause.due) := by
  induction causes with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.cons_append, earliest, ih]
    cases selected : earliest tail <;> simp [Nat.min_assoc]

theorem issue_due (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat) :
    pendingDue (issue state now demand delay) =
      some (match pendingDue state with | none => now + delay | some due => min due (now + delay)) :=
  earliest_snoc state.pending (fresh state now demand delay)

theorem issue_due_le (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay due : Nat)
    (pending : pendingDue state = some due) :
    pendingDue (issue state now demand delay) = some (min due (now + delay)) ∧ min due (now + delay) ≤ due := by
  rw [issue_due, pending]
  exact ⟨rfl, Nat.min_le_left _ _⟩

theorem checkTime_fields (state : State Domain Demand Output) (now : Nat) (checked : checkTime state now = .ok ()) :
    ∀ cause ∈ state.pending, cause.issuedAt ≤ now ∧ now ≤ cause.due := by
  unfold checkTime at checked
  split at checked
  · cases checked
  · rename_i earlier
    split at checked
    · cases checked
    · rename_i later
      intro cause member
      constructor
      · by_cases bound : cause.issuedAt ≤ now
        · exact bound
        · exact False.elim (earlier (List.any_eq_true.mpr ⟨cause, member, by simp only [decide_eq_true_eq]; omega⟩))
      · by_cases bound : now ≤ cause.due
        · exact bound
        · exact False.elim (later (List.any_eq_true.mpr ⟨cause, member, by simp only [decide_eq_true_eq]; omega⟩))

structure CompleteFacts (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output) : Prop where
  credit : state.pending ≠ []
  timed : ∀ cause ∈ state.pending, cause.issuedAt ≤ now ∧ now ≤ cause.due
  covered : ∀ cause ∈ state.pending, covers cause.demand output = true
  changed : after = completedState state now output

theorem complete_fields (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : complete state now output covers = .ok after) : CompleteFacts state now output covers after := by
  unfold complete at accepted
  split at accepted
  · cases accepted
  · rename_i nonempty
    cases checked : checkTime state now with
    | error reason => simp [checked] at accepted
    | ok value =>
      cases value
      simp only [checked] at accepted
      split at accepted
      · rename_i covered
        cases accepted
        refine ⟨?_, checkTime_fields state now checked, ?_, rfl⟩
        · intro empty
          simp [empty] at nonempty
        · exact List.all_eq_true.mp covered
      · cases accepted

theorem complete_pending (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : complete state now output covers = .ok after) : after.pending = [] := by
  rw [(complete_fields state now output covers after accepted).changed]
  rfl

theorem complete_credit (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : complete state now output covers = .ok after) : credit after = 0 := by
  simp only [credit, complete_pending state now output covers after accepted, List.length_nil]

theorem complete_completed (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : complete state now output covers = .ok after) :
    after.completed = state.completed ++ [⟨state.nextDischarge, state.domain, now, output, state.pending⟩] := by
  rw [(complete_fields state now output covers after accepted).changed]
  rfl

theorem complete_domain (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : complete state now output covers = .ok after) : after.domain = state.domain := by
  rw [(complete_fields state now output covers after accepted).changed]
  rfl

theorem complete_nextID (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : complete state now output covers = .ok after) : after.nextID = state.nextID := by
  rw [(complete_fields state now output covers after accepted).changed]
  rfl

def State.allCauses (state : State Domain Demand Output) : List (Cause Domain Demand) :=
  state.completed.flatMap (·.causes) ++ state.pending

def State.Valid (state : State Domain Demand Output) : Prop :=
  (state.allCauses.map (·.id)).Nodup ∧
    ∀ cause ∈ state.allCauses, cause.id < state.nextID ∧ cause.domain = state.domain ∧ cause.issuedAt ≤ cause.due

theorem initial_valid (domain : Domain) : (initial domain : State Domain Demand Output).Valid := by
  simp [State.Valid, State.allCauses, initial]

theorem issue_allCauses (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat) :
    (issue state now demand delay).allCauses = state.allCauses ++ [fresh state now demand delay] := by
  simp [State.allCauses, issue, List.append_assoc]

theorem issue_valid (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat)
    (valid : state.Valid) : (issue state now demand delay).Valid := by
  unfold State.Valid
  rw [issue_allCauses, List.map_append]
  constructor
  · apply List.nodup_append.mpr
    refine ⟨valid.1, by simp, ?_⟩
    intro old member new current same
    obtain ⟨cause, belongs, id⟩ := List.mem_map.mp member
    have bound := (valid.2 cause belongs).1
    have last : new = state.nextID := by simpa [fresh] using current
    have : cause.id = state.nextID := id.trans (same.trans last)
    omega
  · intro cause member
    rcases List.mem_append.mp member with old | new
    · have checked := valid.2 cause old
      exact ⟨by change cause.id < state.nextID + 1; omega, checked.2⟩
    · have same : cause = fresh state now demand delay := List.mem_singleton.mp new
      subst cause
      exact ⟨by change state.nextID < state.nextID + 1; omega, rfl, by change now ≤ now + delay; omega⟩

theorem completedState_allCauses (state : State Domain Demand Output) (now : Nat) (output : Output) :
    (completedState state now output).allCauses = state.allCauses := by
  simp [State.allCauses, completedState]

theorem complete_allCauses (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : complete state now output covers = .ok after) : after.allCauses = state.allCauses := by
  rw [(complete_fields state now output covers after accepted).changed]
  exact completedState_allCauses state now output

theorem complete_valid (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output) (valid : state.Valid)
    (accepted : complete state now output covers = .ok after) : after.Valid := by
  rw [(complete_fields state now output covers after accepted).changed]
  unfold State.Valid
  rw [completedState_allCauses]
  exact valid

theorem requestedState_pending (state : State Domain Demand Output) (event : Observation Demand Output) :
    (requestedState state event).pending = state.pending ++ issued state event := by
  cases request : event.request <;> simp [requestedState, issued, request, issue]

theorem requestedState_domain (state : State Domain Demand Output) (event : Observation Demand Output) :
    (requestedState state event).domain = state.domain := by
  cases request : event.request <;> simp [requestedState, request, issue]

theorem requestedState_completed (state : State Domain Demand Output) (event : Observation Demand Output) :
    (requestedState state event).completed = state.completed := by
  cases request : event.request <;> simp [requestedState, request, issue]

theorem requestedState_allCauses (state : State Domain Demand Output) (event : Observation Demand Output) :
    (requestedState state event).allCauses = state.allCauses ++ issued state event := by
  cases request : event.request with
  | none => simp [requestedState, issued, request]
  | some pair =>
    obtain ⟨demand, delay⟩ := pair
    simpa only [requestedState, issued, request] using issue_allCauses state event.now demand delay

theorem requestedState_valid (state : State Domain Demand Output) (event : Observation Demand Output)
    (valid : state.Valid) : (requestedState state event).Valid := by
  cases request : event.request with
  | none => simpa only [requestedState, request] using valid
  | some pair =>
    obtain ⟨demand, delay⟩ := pair
    simpa only [requestedState, request] using issue_valid state event.now demand delay valid

theorem observe_cases (state : State Domain Demand Output) (event : Observation Demand Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : observe state event covers = .ok after) :
    checkTime state event.now = .ok () ∧
      (after = requestedState state event ∨
        ∃ kind output, event.output = some (kind, output) ∧
          complete (requestedState state event) event.now output covers = .ok after) := by
  cases checked : checkTime state event.now with
  | error reason => simp [observe, checked] at accepted
  | ok value =>
    cases value
    refine ⟨rfl, ?_⟩
    cases present : event.output with
    | none =>
      simp only [observe, checked, present, Except.ok.injEq] at accepted
      exact .inl accepted.symm
    | some pair =>
      obtain ⟨kind, output⟩ := pair
      cases kind with
      | response => exact .inr ⟨.response, output, rfl, by simpa only [observe, checked, present] using accepted⟩
      | independent =>
        simp only [observe, checked, present] at accepted
        split at accepted
        · exact .inl (Except.ok.inj accepted).symm
        · split at accepted
          · exact .inr ⟨.independent, output, rfl, accepted⟩
          · exact .inl (Except.ok.inj accepted).symm

theorem observe_domain (state : State Domain Demand Output) (event : Observation Demand Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : observe state event covers = .ok after) : after.domain = state.domain := by
  rcases (observe_cases state event covers after accepted).2 with same | ⟨_, output, _, completed⟩
  · rw [same, requestedState_domain]
  · exact (complete_domain _ _ _ _ _ completed).trans (requestedState_domain state event)

theorem observe_allCauses (state : State Domain Demand Output) (event : Observation Demand Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : observe state event covers = .ok after) :
    after.allCauses = state.allCauses ++ issued state event := by
  rcases (observe_cases state event covers after accepted).2 with same | ⟨_, output, _, completed⟩
  · rw [same, requestedState_allCauses]
  · rw [complete_allCauses _ _ _ _ _ completed, requestedState_allCauses]

theorem observe_valid (state : State Domain Demand Output) (event : Observation Demand Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output) (valid : state.Valid)
    (accepted : observe state event covers = .ok after) : after.Valid := by
  rcases (observe_cases state event covers after accepted).2 with same | ⟨_, output, _, completed⟩
  · rw [same]
    exact requestedState_valid state event valid
  · exact complete_valid _ _ _ _ _ (requestedState_valid state event valid) completed

universe x y z

structure Adapter (Model : Type x) (Event : Type y) (Result : Type z)
    (Domain : Type u) (Demand : Type v) (Output : Type w) where
  execute : Model → Event → Result
  after : Result → Model
  reaction : Model → State Domain Demand Output
  now : Model → Nat
  request : Model → Event → Result → Option (Demand × Nat)
  output : Result → Option Output
  kind : Model → Event → Result → OutputKind
  covers : Demand → Output → Bool

variable {Model : Type x} {Event : Type y} {Result : Type z}
variable {Domain : Type u} {Demand : Type v} {Output : Type w}

def Adapter.observation (adapter : Adapter Model Event Result Domain Demand Output)
    (before : Model) (event : Event) (result : Result) : Observation Demand Output :=
  ⟨adapter.now (adapter.after result), adapter.request before event result,
    (adapter.output result).map (fun output => (adapter.kind before event result, output))⟩

structure CheckedStep (adapter : Adapter Model Event Result Domain Demand Output) where
  before : Model
  event : Event
  result : Result
  stamp : Nat
  computed : result = adapter.execute before event
  reflected : observe (adapter.reaction before) (adapter.observation before event result) adapter.covers =
    .ok (adapter.reaction (adapter.after result))

variable {adapter : Adapter Model Event Result Domain Demand Output}

def CheckedStep.after (step : CheckedStep adapter) : Model := adapter.after step.result
def CheckedStep.view (step : CheckedStep adapter) : Observation Demand Output := adapter.observation step.before step.event step.result
def CheckedStep.issued (step : CheckedStep adapter) : List (Cause Domain Demand) := TimedReaction.issued (adapter.reaction step.before) step.view

def IssuedAt (step : CheckedStep adapter) (cause : Cause Domain Demand) : Prop := cause ∈ step.issued

def DischargedAt (step : CheckedStep adapter) (completion : Discharge Domain Demand Output) : Prop :=
  ∃ kind output, step.view.output = some (kind, output) ∧
    complete (requestedState (adapter.reaction step.before) step.view) step.view.now output adapter.covers =
      .ok (adapter.reaction step.after) ∧
    completion = ⟨(requestedState (adapter.reaction step.before) step.view).nextDischarge,
      (requestedState (adapter.reaction step.before) step.view).domain, step.view.now, output,
      (requestedState (adapter.reaction step.before) step.view).pending⟩

theorem CheckedStep.completed (step : CheckedStep adapter) :
    (adapter.reaction step.after).completed = (adapter.reaction step.before).completed ∨
      ∃ completion, (adapter.reaction step.after).completed = (adapter.reaction step.before).completed ++ [completion] ∧
        DischargedAt step completion := by
  rcases (observe_cases _ _ _ _ step.reflected).2 with same | ⟨kind, output, present, accepted⟩
  · exact .inl ((congrArg State.completed same).trans (requestedState_completed _ _))
  · let completion : Discharge Domain Demand Output :=
      ⟨(requestedState (adapter.reaction step.before) step.view).nextDischarge,
        (requestedState (adapter.reaction step.before) step.view).domain, step.view.now, output,
        (requestedState (adapter.reaction step.before) step.view).pending⟩
    refine .inr ⟨completion, ?_, kind, output, present, accepted, rfl⟩
    exact (complete_completed _ _ _ _ _ accepted).trans (congrArg (· ++ [completion]) (requestedState_completed _ _))

theorem DischargedAt.output (step : CheckedStep adapter) (completion : Discharge Domain Demand Output)
    (discharged : DischargedAt step completion) : adapter.output step.result = some completion.output := by
  obtain ⟨kind, output, present, _, same⟩ := discharged
  rw [same]
  cases actual : adapter.output step.result with
  | none => simp [CheckedStep.view, Adapter.observation, actual] at present
  | some value =>
    have pair : (adapter.kind step.before step.event step.result, value) = (kind, output) := by
      simpa only [CheckedStep.view, Adapter.observation, actual, Option.map_some, Option.some.injEq] using present
    have selected := congrArg Prod.snd pair
    exact congrArg some selected

theorem DischargedAt.cause (step : CheckedStep adapter) (completion : Discharge Domain Demand Output)
    (discharged : DischargedAt step completion) (cause : Cause Domain Demand) (member : cause ∈ completion.causes) :
    cause ∈ (adapter.reaction step.before).pending ++ step.issued ∧
      cause.issuedAt ≤ completion.time ∧ completion.time ≤ cause.due ∧ adapter.covers cause.demand completion.output = true := by
  obtain ⟨kind, output, present, accepted, same⟩ := discharged
  rw [same] at member ⊢
  have facts := complete_fields _ _ _ _ _ accepted
  exact ⟨by simpa only [CheckedStep.issued, requestedState_pending] using member,
    (facts.timed cause member).1, (facts.timed cause member).2, facts.covered cause member⟩

inductive History (adapter : Adapter Model Event Result Domain Demand Output) :
    Model → List (CheckedStep adapter) → Model → Prop where
  | nil (state : Model) : History adapter state [] state
  | cons (head : CheckedStep adapter) (tail : History adapter head.after steps final) :
      History adapter head.before (head :: steps) final

namespace History

variable {initial final : Model} {steps : List (CheckedStep adapter)}

theorem valid (history : History adapter initial steps final) (valid : (adapter.reaction initial).Valid) :
    (adapter.reaction final).Valid := by
  induction history with
  | nil => exact valid
  | cons head tail ih => exact ih (observe_valid _ _ _ _ valid head.reflected)

theorem allCauses (history : History adapter initial steps final) :
    (adapter.reaction final).allCauses = (adapter.reaction initial).allCauses ++ steps.flatMap CheckedStep.issued := by
  induction history with
  | nil => simp
  | cons head tail ih =>
    rw [ih]
    have changed : (adapter.reaction head.after).allCauses = (adapter.reaction head.before).allCauses ++ head.issued :=
      observe_allCauses _ _ _ _ head.reflected
    rw [changed, List.flatMap_cons, List.append_assoc]

theorem issue_origin (history : History adapter initial steps final) (cause : Cause Domain Demand)
    (member : cause ∈ (adapter.reaction final).allCauses) :
    cause ∈ (adapter.reaction initial).allCauses ∨ ∃ step ∈ steps, IssuedAt step cause := by
  rw [history.allCauses] at member
  rcases List.mem_append.mp member with old | issued
  · exact .inl old
  · exact .inr (List.mem_flatMap.mp issued)

theorem discharge_origin (history : History adapter initial steps final) (completion : Discharge Domain Demand Output)
    (member : completion ∈ (adapter.reaction final).completed) :
    completion ∈ (adapter.reaction initial).completed ∨ ∃ step ∈ steps, DischargedAt step completion := by
  induction history with
  | nil => exact .inl member
  | @cons steps final head tail ih =>
    rcases ih member with prior | ⟨step, belongs, source⟩
    · rcases head.completed with unchanged | ⟨new, appended, origin⟩
      · exact .inl (unchanged ▸ prior)
      · rw [appended] at prior
        rcases List.mem_append.mp prior with old | newMember
        · exact .inl old
        · have same := List.mem_singleton.mp newMember
          subst completion
          exact .inr ⟨head, by simp, origin⟩
    · exact .inr ⟨step, by simp [belongs], source⟩

theorem split (history : History adapter initial steps final) (step : CheckedStep adapter) (member : step ∈ steps) :
    ∃ prior later, steps = prior ++ step :: later ∧ History adapter initial prior step.before ∧
      History adapter step.after later final := by
  induction history with
  | nil => simp at member
  | @cons steps final head tail ih =>
    rcases List.mem_cons.mp member with same | member
    · subst step
      exact ⟨[], steps, rfl, .nil _, tail⟩
    · obtain ⟨prior, later, same, preceding, following⟩ := ih member
      exact ⟨head :: prior, later, by simp [same], .cons head preceding, following⟩

end History

structure CausalWitness (adapter : Adapter Model Event Result Domain Demand Output)
    (steps : List (CheckedStep adapter)) (completion : Discharge Domain Demand Output) (cause : Cause Domain Demand) where
  issuer : CheckedStep adapter
  discharge : CheckedStep adapter
  prior : List (CheckedStep adapter)
  later : List (CheckedStep adapter)
  split : steps = prior ++ discharge :: later
  place : issuer ∈ prior ∨ issuer = discharge
  issued : IssuedAt issuer cause
  discharged : DischargedAt discharge completion
  actualOutput : adapter.output discharge.result = some completion.output
  domain : cause.domain = completion.domain
  issuedBefore : cause.issuedAt ≤ completion.time
  onTime : completion.time ≤ cause.due
  covered : adapter.covers cause.demand completion.output = true

theorem CausalWitness.ordinal (value : CausalWitness adapter steps completion cause)
    (ordered : steps.Pairwise (fun first second => first.stamp < second.stamp)) :
    value.issuer.stamp ≤ value.discharge.stamp := by
  rw [value.split] at ordered
  rcases value.place with prior | same
  · have before := (List.pairwise_append.mp ordered).2.2 value.issuer prior value.discharge (by simp)
    omega
  · rw [same]
    exact Nat.le_refl _

namespace History

variable {initial final : Model} {steps : List (CheckedStep adapter)}

theorem causal_witness (history : History adapter initial steps final) (domain : Domain)
    (empty : adapter.reaction initial = TimedReaction.initial domain)
    (completion : Discharge Domain Demand Output) (completed : completion ∈ (adapter.reaction final).completed)
    (cause : Cause Domain Demand) (member : cause ∈ completion.causes) :
    Nonempty (CausalWitness adapter steps completion cause) := by
  have firstValid : (adapter.reaction initial).Valid := by rw [empty]; exact initial_valid domain
  rcases history.discharge_origin completion completed with old | ⟨discharge, belongs, discharged⟩
  · simp [empty, TimedReaction.initial] at old
  · obtain ⟨prior, later, split, preceding, following⟩ := history.split discharge belongs
    have facts := discharged.cause discharge completion cause member
    have actual := discharged.output discharge completion
    have domainEq : cause.domain = completion.domain := by
      obtain ⟨_, output, _, accepted, same⟩ := discharged
      have present : cause ∈ (requestedState (adapter.reaction discharge.before) discharge.view).pending := by
        simpa only [same] using member
      have valid := requestedState_valid (adapter.reaction discharge.before) discharge.view (preceding.valid firstValid)
      have checked := valid.2 cause (List.mem_append_right _ present)
      exact checked.2.1.trans (congrArg Discharge.domain same).symm
    rcases List.mem_append.mp facts.1 with pending | issued
    · have earlier : cause ∈ (adapter.reaction discharge.before).allCauses := List.mem_append_right _ pending
      rcases preceding.issue_origin cause earlier with old | ⟨issuer, before, origin⟩
      · simp [empty, State.allCauses, TimedReaction.initial] at old
      · exact ⟨⟨issuer, discharge, prior, later, split, .inl before, origin, discharged, actual,
          domainEq, facts.2.1, facts.2.2.1, facts.2.2.2⟩⟩
    · exact ⟨⟨discharge, discharge, prior, later, split, .inr rfl, issued, discharged, actual,
        domainEq, facts.2.1, facts.2.2.1, facts.2.2.2⟩⟩

theorem closed_response (history : History adapter initial steps final) (domain : Domain)
    (empty : adapter.reaction initial = TimedReaction.initial domain)
    (closed : (adapter.reaction final).pending = [])
    (issuer : CheckedStep adapter) (belongs : issuer ∈ steps) (cause : Cause Domain Demand)
    (issued : IssuedAt issuer cause) :
    ∃ completion ∈ (adapter.reaction final).completed, cause ∈ completion.causes ∧
      Nonempty (CausalWitness adapter steps completion cause) := by
  have present : cause ∈ (adapter.reaction final).allCauses := by
    rw [history.allCauses]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨issuer, belongs, issued⟩)
  simp only [State.allCauses, closed, List.append_nil] at present
  obtain ⟨completion, completed, member⟩ := List.mem_flatMap.mp present
  exact ⟨completion, completed, member, history.causal_witness domain empty completion completed cause member⟩

end History

theorem complete_no_repeat (state : State Domain Demand Output) (now : Nat) (output : Output)
    (covers : Demand → Output → Bool) (after : State Domain Demand Output)
    (accepted : complete state now output covers = .ok after) (later : Nat) (next : Output) :
    complete after later next covers = .error .noCredit := by
  simp only [complete, complete_pending state now output covers after accepted, List.isEmpty_nil, ite_true]

theorem State.pending_not_completed (state : State Domain Demand Output) (valid : state.Valid)
    (completion : Discharge Domain Demand Output) (completed : completion ∈ state.completed)
    (cause : Cause Domain Demand) (member : cause ∈ completion.causes)
    (pending : Cause Domain Demand) (waiting : pending ∈ state.pending) : pending.id ≠ cause.id := by
  have unique := valid.1
  simp only [State.allCauses, List.map_append] at unique
  have disjoint := (List.nodup_append.mp unique).2.2
  intro same
  exact disjoint cause.id (List.mem_map.mpr ⟨cause, List.mem_flatMap.mpr ⟨completion, completed, member⟩, rfl⟩)
    pending.id (List.mem_map.mpr ⟨pending, waiting, rfl⟩) same.symm

end Netlib.Theory.TimedReaction
