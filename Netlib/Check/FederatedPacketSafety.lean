import Netlib.Check.FederatedPacketInvariant

/-!
# A common public history across native updates

Arrival extends the public history using the retained old send. Each public
vertex has an actual held-state occurrence in the same execution prefix.
-/

namespace Netlib.Federation.InFlight.Safety

variable {input : Input}

def publicPosition (context : Context input) (state : State input) : PublicRef :=
  match state.phase with
  | .held node => Control.project input state.current node
  | .flight stamp => Control.project input stamp.current stamp.source
  | .delivered _ => context.query.target

def upper (context : Context input) : Network PublicRef :=
  publicModel input.left.contract input.right.contract context.first context.second input.intent.borders false

def arrivalTarget (effect : Effect input) : Option PublicRef :=
  match effect with
  | .arrived stamp => some (Control.project input stamp.current stamp.target)
  | _ => none

def StepProjection (context : Context input) (before after : State input) (effect : Effect input) : Prop :=
  match arrivalTarget effect with
  | none => publicPosition context before = publicPosition context after
  | some target => publicPosition context after = target ∧
      (∃ node, after.phase = .held node ∧ Control.project input after.current node = target) ∧
      (publicPosition context before = target ∨ (upper context).link (publicPosition context before) target)

theorem position_relocate (context : Context input) (before : State input) (current : Cursors input) (clock : Nat)
    (coherent : Control.coherent input before.current current before.phase.key = true) :
    publicPosition context before = publicPosition context ⟨current, before.phase, clock⟩ := by
  cases phase : before.phase with
  | held node =>
    simpa only [publicPosition, phase] using
      (Control.coherent_spec before.current current (.held node) node rfl
        (by simpa only [phase, Phase.key] using coherent)).2.2
  | flight stamp => simp only [publicPosition, phase]
  | delivered index => simp only [publicPosition, phase]

theorem candidate_projection {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header)
    (accepted : context.first.selector.accepts header = true) (before : State input)
    (valid : before.Valid context header) (action : Action) (current : Cursors input)
    (observed : Execution.observationsMatch context header before action = true)
    (keyStep : Execution.KeyStep context header before action (Execution.candidate context header before action current).after) :
    StepProjection context before (Execution.candidate context header before action current).after
      (Execution.candidate context header before action current).effect := by
  cases action with
  | idle =>
    rw [Execution.candidate_idle] at keyStep ⊢
    have same : current = before.current := congrArg Key.current keyStep
    subst current
    rfl
  | send observation target =>
    cases phase : before.phase with
    | held source =>
      rw [Execution.candidate_send context header before observation source target current phase]
      simp only [StepProjection, arrivalTarget, publicPosition, phase]
    | flight stamp => simp [Execution.observationsMatch, phase] at observed
    | delivered index => simp [Execution.observationsMatch, phase] at observed
  | arrive observation index =>
    cases phase : before.phase with
    | held node => simp [Execution.observationsMatch, phase] at observed
    | flight stamp =>
      have flight : stamp.Valid context header before.current before.nextIndex := by
        simpa only [State.Valid, phase] using valid
      rw [Execution.candidate_arrive context header before observation index stamp current phase] at keyStep ⊢
      have currentEq : current = before.current :=
        (Execution.control_frame context header before.key _ .arrive keyStep).2.1 rfl
      have targetEq : Control.project input current stamp.target = Control.project input stamp.current stamp.target := by
        rw [currentEq]
        exact flight.projection
      have secondAccepted : context.second.selector.accepts header = true := by
        rw [← checked.matches.2.1]
        exact accepted
      have simulated := (Composition.upper deployment.compatible (deployment.left.nativeAt stamp.current.1)
        (deployment.right.nativeAt stamp.current.2) context.first context.second checked.first_mem checked.second_mem
        header accepted secondAccepted).simulate stamp.source stamp.target
          ((Control.nativeEdge_iff context header stamp.current stamp.source stamp.target).mp flight.native)
      change Control.project input stamp.current stamp.source = Control.project input stamp.current stamp.target ∨
        (upper context).link (Control.project input stamp.current stamp.source)
          (Control.project input stamp.current stamp.target) at simulated
      refine ⟨targetEq, ⟨stamp.target, rfl, targetEq⟩, ?_⟩
      simpa only [publicPosition, phase] using simulated
    | delivered receipt => simp [Execution.observationsMatch, phase] at observed
  | receive observation =>
    cases phase : before.phase with
    | held node =>
      rw [Execution.candidate_receive context header before observation node current phase] at keyStep ⊢
      simp only [Execution.KeyStep, Action.move?, Control.step, State.key, phase, Phase.key] at keyStep
      split at keyStep
      · rename_i guards
        have targetEq : node = context.targetNode := of_decide_eq_true (((Bool.and_eq_true _ _).mp guards).1)
        simp only [StepProjection, arrivalTarget, publicPosition, phase]
        rw [targetEq]
        exact checked.targetNode_project before.current
      · cases keyStep
    | flight stamp => simp [Execution.observationsMatch, phase] at observed
    | delivered index => simp [Execution.observationsMatch, phase] at observed
  | updateLeft index =>
    have coherent := (Execution.control_frame context header before.key _ (.updateLeft index) keyStep).2.2 rfl
    rw [Execution.candidate_updateLeft]
    exact position_relocate context before current _ coherent
  | updateRight index =>
    have coherent := (Execution.control_frame context header before.key _ (.updateRight index) keyStep).2.2 rfl
    rw [Execution.candidate_updateRight]
    exact position_relocate context before current _ coherent
  | updateBoth first second =>
    have coherent := (Execution.control_frame context header before.key _ (.updateBoth first second) keyStep).2.2 rfl
    rw [Execution.candidate_updateBoth]
    exact position_relocate context before current _ coherent

theorem step_projection {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header)
    (accepted : context.first.selector.accepts header = true) {before after : State input} {event : Event input}
    (valid : before.Valid context header) (step : (Execution.system context header).step before event after) :
    StepProjection context before after event.effect := by
  obtain ⟨outcome, facts, stateEq, effectEq⟩ := Execution.step_facts context header step
  have projection := candidate_projection checked header accepted before valid event.action outcome.after.current
    facts.observations (by rw [facts.candidateEq]; exact facts.keyStep)
  rw [facts.candidateEq, stateEq, effectEq] at projection
  exact projection

inductive StutteringWalk (network : Network PublicRef) : PublicRef → PublicRef → List PublicRef → Prop
  | nil (node) : StutteringWalk network node node [node]
  | cons {source next target vertices} : (source = next ∨ network.link source next) →
      StutteringWalk network next target vertices → StutteringWalk network source target (source :: vertices)

theorem StutteringWalk.snoc {network : Network PublicRef} {source target next : PublicRef} {vertices : List PublicRef}
    (walk : StutteringWalk network source target vertices) (edge : target = next ∨ network.link target next) :
    StutteringWalk network source next (vertices ++ [next]) := by
  induction walk with
  | nil node => exact .cons edge (.nil next)
  | cons first _ ih => exact .cons first (ih edge)

theorem StutteringWalk.compress {network : Network PublicRef} {source target : PublicRef} {vertices : List PublicRef}
    (walk : StutteringWalk network source target vertices) :
    ∃ compressed, Network.Walk network source target compressed ∧ ∀ node ∈ compressed, node ∈ vertices := by
  induction walk with
  | nil node => exact ⟨[node], .nil node, fun _ member => member⟩
  | @cons source next target vertices edge _ ih =>
    obtain ⟨compressed, actual, included⟩ := ih
    rcases edge with same | link
    · subst source
      exact ⟨compressed, actual, fun node member => List.mem_cons_of_mem _ (included node member)⟩
    · refine ⟨source :: compressed, .cons link actual, ?_⟩
      intro node member
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (included node member)

def publicHistory (context : Context input) (events : List (Event input)) : List PublicRef :=
  context.query.source :: events.filterMap (fun event => arrivalTarget event.effect)

theorem publicHistory_append (context : Context input) (events : List (Event input)) (event : Event input) :
    publicHistory context (events ++ [event]) = match arrivalTarget event.effect with
      | none => publicHistory context events
      | some target => publicHistory context events ++ [target] := by
  cases selected : arrivalTarget event.effect <;> simp [publicHistory, List.filterMap_append, selected]

def HeldWithin (context : Context input) (header : Packet.Header) (events : List (Event input))
    (after : State input) (reference : PublicRef) : Prop :=
  ∃ prior later state node, events = prior ++ later ∧
    (Execution.system context header).Trace (initialState context) prior state ∧
    (Execution.system context header).Trace state later after ∧ state.phase = .held node ∧
    Control.project input state.current node = reference

theorem HeldWithin.extend {context : Context input} {header : Packet.Header} {events : List (Event input)}
    {before after : State input} {reference : PublicRef} {event : Event input}
    (held : HeldWithin context header events before reference)
    (step : (Execution.system context header).step before event after) :
    HeldWithin context header (events ++ [event]) after reference := by
  obtain ⟨prior, later, state, node, same, first, rest, phase, visible⟩ := held
  exact ⟨prior, later ++ [event], state, node, by simp [same, List.append_assoc], first,
    rest.append (.cons step (.nil after)), phase, visible⟩

theorem HeldWithin.current {context : Context input} {header : Packet.Header} {events : List (Event input)}
    {after : State input} {reference : PublicRef} (trace : (Execution.system context header).Trace (initialState context) events after)
    (node : Node) (phase : after.phase = .held node) (visible : Control.project input after.current node = reference) :
    HeldWithin context header events after reference :=
  ⟨events, [], after, node, by simp, trace, .nil after, phase, visible⟩

theorem extend_history {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header)
    (accepted : context.first.selector.accepts header = true) {before after : State input}
    {events history : List (Event input)}
    (trace : (Execution.system context header).Trace before events after)
    (prior : (Execution.system context header).Trace (initialState context) history before)
    (walk : StutteringWalk (upper context) context.query.source (publicPosition context before) (publicHistory context history))
    (held : ∀ node ∈ publicHistory context history, HeldWithin context header history before node) :
    StutteringWalk (upper context) context.query.source (publicPosition context after) (publicHistory context (history ++ events)) ∧
      ∀ node ∈ publicHistory context (history ++ events), HeldWithin context header (history ++ events) after node := by
  induction trace generalizing history with
  | nil => simpa using And.intro walk held
  | @cons before middle after event events step tail ih =>
    have valid := Execution.trace_valid checked header prior
    have projection := step_projection checked header accepted valid step
    have nextPrior := prior.append (.cons step (.nil middle))
    have retained : ∀ node ∈ publicHistory context history, HeldWithin context header (history ++ [event]) middle node :=
      fun node member => (held node member).extend step
    cases targetEq : arrivalTarget event.effect with
    | none =>
      have same : publicPosition context before = publicPosition context middle := by
        simpa only [StepProjection, targetEq] using projection
      have nextWalk : StutteringWalk (upper context) context.query.source (publicPosition context middle)
          (publicHistory context (history ++ [event])) := by
        rw [publicHistory_append, targetEq]
        simpa only [← same] using walk
      have nextHeld : ∀ node ∈ publicHistory context (history ++ [event]),
          HeldWithin context header (history ++ [event]) middle node := by
        rw [publicHistory_append, targetEq]
        exact retained
      have result := ih nextPrior nextWalk nextHeld
      simpa only [List.append_assoc, List.singleton_append] using result
    | some target =>
      have facts : publicPosition context middle = target ∧
          (∃ node, middle.phase = .held node ∧ Control.project input middle.current node = target) ∧
          (publicPosition context before = target ∨ (upper context).link (publicPosition context before) target) := by
        simpa only [StepProjection, targetEq] using projection
      obtain ⟨native, phase, visible⟩ := facts.2.1
      have nextWalk : StutteringWalk (upper context) context.query.source (publicPosition context middle)
          (publicHistory context (history ++ [event])) := by
        rw [publicHistory_append, targetEq, facts.1]
        exact walk.snoc facts.2.2
      have nextHeld : ∀ node ∈ publicHistory context (history ++ [event]),
          HeldWithin context header (history ++ [event]) middle node := by
        rw [publicHistory_append, targetEq]
        intro node member
        rcases List.mem_append.mp member with earlier | current
        · exact retained node earlier
        · have same : node = target := List.mem_singleton.mp current
          subst node
          exact HeldWithin.current nextPrior native phase visible
      have result := ih nextPrior nextWalk nextHeld
      simpa only [List.append_assoc, List.singleton_append] using result

structure CommonHistory (context : Context input) (header : Packet.Header) (events : List (Event input))
    (after : State input) : Prop where
  stuttering : StutteringWalk (upper context) context.query.source (publicPosition context after) (publicHistory context events)
  held : ∀ node ∈ publicHistory context events, HeldWithin context header events after node

theorem common_history {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header)
    (accepted : context.first.selector.accepts header = true) {events : List (Event input)} {after : State input}
    (trace : (Execution.system context header).Trace (initialState context) events after) :
    CommonHistory context header events after := by
  have source : publicPosition context (initialState context) = context.query.source :=
    checked.sourceNode_project (Plan.jointInitial input.left input.right)
  have walk : StutteringWalk (upper context) context.query.source (publicPosition context (initialState context))
      (publicHistory context []) := by
    rw [source]
    exact .nil _
  have held : ∀ node ∈ publicHistory context [], HeldWithin context header [] (initialState context) node := by
    intro node member
    have same : node = context.query.source := List.mem_singleton.mp member
    subst node
    exact HeldWithin.current (.nil _) context.sourceNode rfl
      (checked.sourceNode_project (Plan.jointInitial input.left input.right))
  have facts := extend_history checked header accepted trace (.nil _) walk held
  exact ⟨by simpa only [List.nil_append] using facts.1, by simpa only [List.nil_append] using facts.2⟩

theorem CommonHistory.walk {context : Context input} {header : Packet.Header} {events : List (Event input)} {after : State input}
    (history : CommonHistory context header events after) :
    ∃ vertices, Network.Walk (upper context) context.query.source (publicPosition context after) vertices ∧
      ∀ node ∈ vertices, HeldWithin context header events after node := by
  obtain ⟨vertices, walk, included⟩ := history.stuttering.compress
  exact ⟨vertices, walk, fun node member => history.held node (included node member)⟩

theorem CommonHistory.reachable {context : Context input} {header : Packet.Header} {events : List (Event input)} {after : State input}
    (history : CommonHistory context header events after) :
    (upper context).Reachable context.query.source (publicPosition context after) := by
  obtain ⟨_, walk, _⟩ := history.walk
  exact walk.reachable

theorem prefix_history {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header)
    (accepted : context.first.selector.accepts header = true) {prior later : List (Event input)} {after : State input}
    (trace : (Execution.system context header).Trace (initialState context) (prior ++ later) after) :
    ∃ middle, (Execution.system context header).Trace (initialState context) prior middle ∧
      (Execution.system context header).Trace middle later after ∧ CommonHistory context header prior middle := by
  obtain ⟨middle, first, rest⟩ := trace.split
  exact ⟨middle, first, rest, common_history checked header accepted first⟩

theorem matching_cases {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (query : Query)
    (result : Queries.Result input.left.contract input.right.contract input.intent query)
    (sameCase : query.caseID = context.query.caseID) :
    result.first = context.first ∧ result.second = context.second := by
  have first : input.left.contract.case? context.query.caseID = some context.first := by
    rw [checked.firstEq]
    exact checked.result.firstFound
  have second : input.right.contract.case? context.query.caseID = some context.second := by
    rw [checked.secondEq]
    exact checked.result.secondFound
  have otherFirst := result.firstFound
  have otherSecond := result.secondFound
  rw [sameCase] at otherFirst otherSecond
  exact ⟨Option.some.inj (otherFirst.symm.trans first), Option.some.inj (otherSecond.symm.trans second)⟩

theorem isolate {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header)
    (accepted : context.first.selector.accepts header = true) {events : List (Event input)} {after : State input}
    (trace : (Execution.system context header).Trace (initialState context) events after)
    (query : Query) (member : query ∈ input.intent.queries) (kind : query.kind = .isolate)
    (sameCase : query.caseID = context.query.caseID) (sameSource : query.source = context.query.source) :
    publicPosition context after ≠ query.target := by
  obtain ⟨result, _⟩ := deployment.result_for query member
  have cases := matching_cases checked query result sameCase
  have secure : ¬(upper context).Reachable query.source query.target := by
    simpa only [Queries.Meaning, kind, cases.1, cases.2, upper] using result.correct
  intro reached
  apply secure
  simpa only [sameSource, reached] using (common_history checked header accepted trace).reachable

theorem mediated_held {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header)
    (accepted : context.first.selector.accepts header = true) {events : List (Event input)} {after : State input}
    (trace : (Execution.system context header).Trace (initialState context) events after)
    (query : Query) (member : query ∈ input.intent.queries) (kind : query.kind = .mediated)
    (sameCase : query.caseID = context.query.caseID) (sameSource : query.source = context.query.source)
    (reached : publicPosition context after = query.target) :
    ∃ reference ∈ query.gateways, HeldWithin context header events after reference := by
  obtain ⟨result, _⟩ := deployment.result_for query member
  have cases := matching_cases checked query result sameCase
  have secure : (upper context).Mediated (· = query.source) (· = query.target) (· ∈ query.gateways) := by
    simpa only [cases.1, cases.2, upper] using result.public_mediated kind
  obtain ⟨vertices, walk, held⟩ := (common_history checked header accepted trace).walk
  obtain ⟨reference, present, gateway⟩ := Network.mediated_iff_every_walk.mp secure
    context.query.source (publicPosition context after) vertices sameSource.symm reached walk
  exact ⟨reference, gateway, held reference present⟩

structure PEPVisit (context : Context input) (header : Packet.Header) (events : List (Event input))
    (after : State input) (query : Query) (side : Side) where
  prior : List (Event input)
  later : List (Event input)
  state : State input
  node : Node
  eventsEq : events = prior ++ later
  first : (Execution.system context header).Trace (initialState context) prior state
  rest : (Execution.system context header).Trace state later after
  held : state.phase = .held node
  known : Control.known input state.current node = true
  gateway : Control.project input state.current node ∈ query.gateways
  enforcement : Composition.EnforcementOn side (input.left.revisionAt state.current.1)
    (input.right.revisionAt state.current.2) node
  clock : state.nextIndex = prior.length

theorem mediated_on {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header)
    (accepted : context.first.selector.accepts header = true) {events : List (Event input)} {after : State input}
    (trace : (Execution.system context header).Trace (initialState context) events after)
    (query : Query) (member : query ∈ input.intent.queries) (kind : query.kind = .mediated)
    (sameCase : query.caseID = context.query.caseID) (sameSource : query.source = context.query.source)
    (reached : publicPosition context after = query.target) (side : Side)
    (checkedSide : query.gateways.all (fun gateway => decide (gateway.side = side)) = true) :
    Nonempty (PEPVisit context header events after query side) := by
  obtain ⟨reference, gateway, prior, later, state, node, eventsEq, first, rest, held, visible⟩ :=
    mediated_held checked header accepted trace query member kind sameCase sameSource reached
  have sameSide : ∀ gateway ∈ query.gateways, gateway.side = side := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using checkedSide
  obtain ⟨result, _⟩ := deployment.result_for query member
  have projected : Control.project input state.current node ∈ query.gateways := by rw [visible]; exact gateway
  have enforced := Composition.reflect_gateways_side (deployment.left.nativeAt state.current.1)
    (deployment.right.nativeAt state.current.2) query.gateways result.gateways_typed side sameSide node projected
  have valid := Execution.trace_valid checked header first
  have known : Control.known input state.current node = true := by simpa only [State.Valid, held] using valid
  exact ⟨⟨prior, later, state, node, eventsEq, first, rest, held, known, projected, enforced,
    Execution.initial_trace_index context header first⟩⟩

end Netlib.Federation.InFlight.Safety
