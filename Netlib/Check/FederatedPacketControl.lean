import Netlib.Model.FederatedPacket

/-!
# Finite packet control decisions

The control key retains the held node or pending receiver. Update guards
preserve that location and its public meaning without retaining old senders.
-/

namespace Netlib.Federation.InFlight.Control

variable {input : Input}

def known (input : Input) (current : Cursors input) : Node → Bool
  | .inl node => decide (node ∈ (input.left.revisionAt current.1).snapshot.intent.ids)
  | .inr node => decide (node ∈ (input.right.revisionAt current.2).snapshot.intent.ids)

def project (input : Input) (current : Cursors input) : Node → PublicRef :=
  Composition.project (input.left.revisionAt current.1) (input.right.revisionAt current.2)

def forward (left right : Revision) (borders : List Border) (caseID source target : String) : Bool :=
  borders.any fun border => match border.source, border.target with
    | ⟨.left, exit⟩, ⟨.right, entry⟩ =>
      border.cases.contains caseID && decide (source = left.anchor exit ∧ target = right.anchor entry)
    | _, _ => false

def backward (left right : Revision) (borders : List Border) (caseID source target : String) : Bool :=
  borders.any fun border => match border.source, border.target with
    | ⟨.right, exit⟩, ⟨.left, entry⟩ =>
      border.cases.contains caseID && decide (source = right.anchor exit ∧ target = left.anchor entry)
    | _, _ => false

theorem forward_iff (left right : Revision) (borders : List Border) (caseID source target : String) :
    forward left right borders caseID source target = true ↔
      Composition.nativeForward left right borders caseID source target := by
  constructor
  · intro checked
    obtain ⟨border, member, checked⟩ := List.any_eq_true.mp checked
    rcases sourceRef : border.source with ⟨sourceSide, exit⟩
    rcases targetRef : border.target with ⟨targetSide, entry⟩
    cases sourceSide <;> cases targetSide <;> simp only [sourceRef, targetRef] at checked
    · cases checked
    · simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at checked
      refine ⟨exit, entry, ?_, checked.2⟩
      exact List.any_eq_true.mpr ⟨border, member, by simp [sourceRef, targetRef, checked.1]⟩
    · cases checked
    · cases checked
  · rintro ⟨exit, entry, edge, sourceEq, targetEq⟩
    obtain ⟨border, member, sourceRef, targetRef, selected⟩ := Composition.border_witness borders caseID _ _ edge
    apply List.any_eq_true.mpr
    exact ⟨border, member, by simp [sourceRef, targetRef, selected, sourceEq, targetEq]⟩

theorem backward_iff (left right : Revision) (borders : List Border) (caseID source target : String) :
    backward left right borders caseID source target = true ↔
      Composition.nativeBackward left right borders caseID source target := by
  constructor
  · intro checked
    obtain ⟨border, member, checked⟩ := List.any_eq_true.mp checked
    rcases sourceRef : border.source with ⟨sourceSide, exit⟩
    rcases targetRef : border.target with ⟨targetSide, entry⟩
    cases sourceSide <;> cases targetSide <;> simp only [sourceRef, targetRef] at checked
    · cases checked
    · cases checked
    · simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at checked
      refine ⟨exit, entry, ?_, checked.2⟩
      exact List.any_eq_true.mpr ⟨border, member, by simp [sourceRef, targetRef, checked.1]⟩
    · cases checked
  · rintro ⟨exit, entry, edge, sourceEq, targetEq⟩
    obtain ⟨border, member, sourceRef, targetRef, selected⟩ := Composition.border_witness borders caseID _ _ edge
    apply List.any_eq_true.mpr
    exact ⟨border, member, by simp [sourceRef, targetRef, selected, sourceEq, targetEq]⟩

def nativeEdge (context : Context input) (header : Packet.Header) (current : Cursors input) : Node → Node → Bool
  | .inl source, .inl target =>
    let revision := input.left.revisionAt current.1
    decide (source ∈ revision.snapshot.intent.ids ∧ target ∈ revision.snapshot.intent.ids) &&
      revision.snapshot.nativeEdge header context.first.request source target
  | .inr source, .inr target =>
    let revision := input.right.revisionAt current.2
    decide (source ∈ revision.snapshot.intent.ids ∧ target ∈ revision.snapshot.intent.ids) &&
      revision.snapshot.nativeEdge header context.second.request source target
  | .inl source, .inr target =>
    forward (input.left.revisionAt current.1) (input.right.revisionAt current.2)
      input.intent.borders context.first.id source target
  | .inr source, .inl target =>
    backward (input.left.revisionAt current.1) (input.right.revisionAt current.2)
      input.intent.borders context.first.id source target

theorem nativeEdge_iff (context : Context input) (header : Packet.Header) (current : Cursors input)
    (source target : Node) : nativeEdge context header current source target = true ↔
    (Composition.nativeModel (input.left.revisionAt current.1) (input.right.revisionAt current.2)
      context.first context.second input.intent.borders header).link source target := by
  cases source <;> cases target
  · simp [nativeEdge, Composition.nativeModel, Network.interconnect, Revision.native,
      Import.LinuxDeployment.Snapshot.nativeModel, Certificate.finiteNetwork, and_assoc]
  · exact forward_iff _ _ _ _ _ _
  · exact backward_iff _ _ _ _ _ _
  · simp [nativeEdge, Composition.nativeModel, Network.interconnect, Revision.native,
      Import.LinuxDeployment.Snapshot.nativeModel, Certificate.finiteNetwork, and_assoc]

theorem nativeEdge_known (context : Context input) (checked : Deployment.Checked input)
    (header : Packet.Header) (current : Cursors input) (source target : Node)
    (edge : nativeEdge context header current source target = true) :
    known input current source = true ∧ known input current target = true := by
  have members := Composition.edge_known checked.compatible (checked.left.nativeAt current.1)
    (checked.right.nativeAt current.2) context.first context.second header source target
    ((nativeEdge_iff context header current source target).mp edge)
  constructor
  · cases source <;> exact decide_eq_true members.1
  · cases target <;> exact decide_eq_true members.2

def occupied : KeyPhase → Option Node
  | .held node | .flight node => some node
  | .delivered => none

def coherent (input : Input) (before after : Cursors input) (phase : KeyPhase) : Bool :=
  match occupied phase with
  | none => true
  | some node => known input before node && known input after node &&
      decide (project input before node = project input after node)

theorem coherent_spec (before after : Cursors input) (phase : KeyPhase) (node : Node)
    (location : occupied phase = some node) (checked : coherent input before after phase = true) :
    known input before node = true ∧ known input after node = true ∧ project input before node = project input after node := by
  simpa only [coherent, location, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked

def Valid (key : Key input) : Prop :=
  ∀ node, occupied key.phase = some node → known input key.current node = true

theorem coherent_valid (before after : Cursors input) (phase : KeyPhase)
    (checked : coherent input before after phase = true) : Valid (⟨after, phase⟩ : Key input) := by
  intro node location
  exact (coherent_spec before after phase node location checked).2.1

def fenceClear (fences : List (List String)) (index : Nat) (side : Side) (phase : KeyPhase) : Bool :=
  match fences[index]? with
  | none => false
  | some names => match occupied phase with
    | none => true
    | some (.inl node) => side != .left || !names.contains node
    | some (.inr node) => side != .right || !names.contains node

def nextCursor (plan : Plan) (before : plan.Cursor) (index : Nat) : Option plan.Cursor :=
  if available : before.val < plan.updates.length then
    if index = before.val then
      some ⟨before.val + 1, by simp only [Plan.versions, List.length_cons]; omega⟩
    else none
  else none

theorem nextCursor_index (plan : Plan) (before after : plan.Cursor) (index : Nat)
    (selected : nextCursor plan before index = some after) : index = before.val := by
  unfold nextCursor at selected
  split at selected
  · split at selected
    · assumption
    · cases selected
  · cases selected

theorem nextCursor_bound (plan : Plan) (before after : plan.Cursor) (index : Nat)
    (selected : nextCursor plan before index = some after) : index < plan.updates.length := by
  have same := nextCursor_index plan before after index selected
  subst index
  unfold nextCursor at selected
  split at selected
  · assumption
  · cases selected

theorem nextCursor_step (plan : Plan) (before after : plan.Cursor) (index : Nat)
    (selected : nextCursor plan before index = some after) :
    plan.transition.step before ⟨index, nextCursor_bound plan before after index selected⟩ after := by
  unfold nextCursor at selected
  split at selected
  · split at selected
    · cases selected
      exact ⟨by assumption, rfl⟩
    · cases selected
  · cases selected

def step (context : Context input) (header : Packet.Header) (key : Key input) : Move → Option (Key input)
  | .send target => match key.phase with
    | .held source =>
      if nativeEdge context header key.current source target && known input key.current source &&
          known input key.current target then some ⟨key.current, .flight target⟩ else none
    | _ => none
  | .arrive => match key.phase with
    | .flight receiver =>
      if known input key.current receiver then some ⟨key.current, .held receiver⟩ else none
    | _ => none
  | .receive => match key.phase with
    | .held node =>
      if decide (node = context.targetNode) && known input key.current node then some ⟨key.current, .delivered⟩ else none
    | _ => none
  | .updateLeft index => do
    let next ← nextCursor input.left key.current.1 index
    let current := (next, key.current.2)
    if coherent input key.current current key.phase &&
        fenceClear context.profile.leftFences index .left key.phase then some ⟨current, key.phase⟩ else none
  | .updateRight index => do
    let next ← nextCursor input.right key.current.2 index
    let current := (key.current.1, next)
    if coherent input key.current current key.phase &&
        fenceClear context.profile.rightFences index .right key.phase then some ⟨current, key.phase⟩ else none
  | .updateBoth leftIndex rightIndex => do
    let nextLeft ← nextCursor input.left key.current.1 leftIndex
    let nextRight ← nextCursor input.right key.current.2 rightIndex
    let current := (nextLeft, nextRight)
    if coherent input key.current current key.phase &&
        fenceClear context.profile.leftFences leftIndex .left key.phase &&
        fenceClear context.profile.rightFences rightIndex .right key.phase then some ⟨current, key.phase⟩ else none

def nodes (input : Input) : List Node :=
  ((input.left.versions.flatMap fun revision : Revision => revision.snapshot.intent.ids.map Sum.inl) ++
    (input.right.versions.flatMap fun revision : Revision => revision.snapshot.intent.ids.map Sum.inr)).eraseDups

theorem known_mem_nodes (current : Cursors input) (node : Node) (present : known input current node = true) :
    node ∈ nodes input := by
  apply List.mem_eraseDups.mpr
  cases node with
  | inl node =>
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨_, input.left.at_mem current.1,
      List.mem_map.mpr ⟨node, of_decide_eq_true present, rfl⟩⟩
  | inr node =>
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_, input.right.at_mem current.2,
      List.mem_map.mpr ⟨node, of_decide_eq_true present, rfl⟩⟩

def candidates (input : Input) (key : Key input) : List Move :=
  (nodes input).map Move.send ++ [.arrive, .receive,
    .updateLeft key.current.1.val, .updateRight key.current.2.val,
    .updateBoth key.current.1.val key.current.2.val]

def successors (context : Context input) (header : Packet.Header) (key : Key input) : List (Move × Key input) :=
  (candidates input key).filterMap fun move => (step context header key move).map (move, ·)

theorem step_send_known (context : Context input) (header : Packet.Header) (before after : Key input) (target : Node)
    (selected : step context header before (.send target) = some after) : known input before.current target = true := by
  cases phase : before.phase with
  | held source =>
    simp only [step, phase] at selected
    split at selected
    · rename_i checked
      exact ((Bool.and_eq_true _ _).mp checked).2
    · cases selected
  | flight receiver => simp [step, phase] at selected
  | delivered => simp [step, phase] at selected

theorem send_of_edge (context : Context input) (checked : Deployment.Checked input)
    (header : Packet.Header) (key : Key input) (source target : Node)
    (held : key.phase = .held source) (edge : nativeEdge context header key.current source target = true) :
    step context header key (.send target) = some ⟨key.current, .flight target⟩ := by
  have members := nativeEdge_known context checked header key.current source target edge
  simp [step, held, edge, members.1, members.2]

theorem step_left_index (context : Context input) (header : Packet.Header) (before after : Key input) (index : Nat)
    (selected : step context header before (.updateLeft index) = some after) : index = before.current.1.val := by
  cases next : nextCursor input.left before.current.1 index with
  | none => simp [step, next] at selected
  | some cursor => exact nextCursor_index _ _ _ _ next

theorem step_right_index (context : Context input) (header : Packet.Header) (before after : Key input) (index : Nat)
    (selected : step context header before (.updateRight index) = some after) : index = before.current.2.val := by
  cases next : nextCursor input.right before.current.2 index with
  | none => simp [step, next] at selected
  | some cursor => exact nextCursor_index _ _ _ _ next

theorem step_both_indices (context : Context input) (header : Packet.Header) (before after : Key input) (left right : Nat)
    (selected : step context header before (.updateBoth left right) = some after) :
    left = before.current.1.val ∧ right = before.current.2.val := by
  cases first : nextCursor input.left before.current.1 left with
  | none => simp [step, first] at selected
  | some nextLeft =>
    cases second : nextCursor input.right before.current.2 right with
    | none => simp [step, first, second] at selected
    | some nextRight => exact ⟨nextCursor_index _ _ _ _ first, nextCursor_index _ _ _ _ second⟩

theorem step_candidate (context : Context input) (header : Packet.Header) (before after : Key input) (move : Move)
    (selected : step context header before move = some after) : move ∈ candidates input before := by
  cases move with
  | send target =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨target, known_mem_nodes _ _ (step_send_known context header before after target selected), rfl⟩
  | arrive => simp [candidates]
  | receive => simp [candidates]
  | updateLeft index => simp [candidates, step_left_index context header before after index selected]
  | updateRight index => simp [candidates, step_right_index context header before after index selected]
  | updateBoth left right =>
    have indices := step_both_indices context header before after left right selected
    simp [candidates, indices.1, indices.2]

theorem mem_successors (context : Context input) (header : Packet.Header) (before after : Key input) (move : Move) :
    (move, after) ∈ successors context header before ↔ step context header before move = some after := by
  simp only [successors, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨candidate, _, next, selected, same⟩
    have parts := Prod.mk.inj same
    rcases parts with ⟨rfl, rfl⟩
    exact selected
  · intro selected
    exact ⟨move, step_candidate context header before after move selected, after, selected, rfl⟩

def phases (input : Input) : List KeyPhase :=
  (nodes input).map KeyPhase.held ++ (nodes input).map KeyPhase.flight ++ [.delivered]

private def pairs {α β : Type} (first : List α) (second : List β) : List (α × β) :=
  first.flatMap fun left => second.map (left, ·)

private theorem mem_pairs {α β : Type} (first : List α) (second : List β) (left : α) (right : β) :
    (left, right) ∈ pairs first second ↔ left ∈ first ∧ right ∈ second := by
  simp [pairs]

private theorem length_pairs {α β : Type} (first : List α) (second : List β) :
    (pairs first second).length = first.length * second.length := by
  induction first with
  | nil => simp [pairs]
  | cons left rest ih =>
    rw [pairs, List.flatMap_cons, List.length_append, List.length_map]
    change second.length + (pairs rest second).length = (left :: rest).length * second.length
    rw [ih]
    simp [Nat.add_mul, Nat.add_comm]

def cursorPairs (input : Input) : List (Cursors input) :=
  pairs (List.finRange input.left.versions.length) (List.finRange input.right.versions.length)

def allKeys (input : Input) : List (Key input) :=
  (pairs (cursorPairs input) (phases input)).map fun pair => ⟨pair.1, pair.2⟩

theorem allKeys_length (input : Input) :
    (allKeys input).length = input.left.versions.length * input.right.versions.length * (2 * (nodes input).length + 1) := by
  simp [allKeys, cursorPairs, phases, length_pairs, Nat.two_mul, Nat.add_assoc]

theorem mem_allKeys (key : Key input)
    (valid : ∀ node, occupied key.phase = some node → known input key.current node = true) :
    key ∈ allKeys input := by
  apply List.mem_map.mpr
  refine ⟨(key.current, key.phase), (mem_pairs _ _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · exact (mem_pairs _ _ _ _).mpr ⟨List.mem_finRange _, List.mem_finRange _⟩
  · cases phase : key.phase with
    | held node =>
      have member := known_mem_nodes key.current node (valid node (by simp [occupied, phase]))
      simp [phases, member]
    | flight node =>
      have member := known_mem_nodes key.current node (valid node (by simp [occupied, phase]))
      simp [phases, member]
    | delivered => simp [phases]
  · cases key
    rfl

theorem step_valid (context : Context input) (header : Packet.Header) (before after : Key input) (move : Move)
    (selected : step context header before move = some after) : Valid after := by
  cases move with
  | send target =>
    have present := step_send_known context header before after target selected
    cases phase : before.phase with
    | held source =>
      simp only [step, phase] at selected
      split at selected
      · cases selected
        intro node location
        have same : target = node := Option.some.inj location
        simpa only [same] using present
      · cases selected
    | flight receiver => simp [step, phase] at selected
    | delivered => simp [step, phase] at selected
  | arrive =>
    cases phase : before.phase with
    | held node => simp [step, phase] at selected
    | flight receiver =>
      simp only [step, phase] at selected
      split at selected
      · rename_i present
        cases selected
        intro node location
        have same : receiver = node := Option.some.inj location
        simpa only [same] using present
      · cases selected
    | delivered => simp [step, phase] at selected
  | receive =>
    cases phase : before.phase with
    | held node =>
      simp only [step, phase] at selected
      split at selected
      · cases selected
        intro node location
        cases location
      · cases selected
    | flight receiver => simp [step, phase] at selected
    | delivered => simp [step, phase] at selected
  | updateLeft index =>
    cases next : nextCursor input.left before.current.1 index with
    | none => simp [step, next] at selected
    | some cursor =>
      simp only [step, next] at selected
      change (if coherent input before.current (cursor, before.current.2) before.phase &&
        fenceClear context.profile.leftFences index .left before.phase then
        some ⟨(cursor, before.current.2), before.phase⟩ else none) = some after at selected
      split at selected
      · rename_i checks
        cases selected
        exact coherent_valid _ _ _ (((Bool.and_eq_true _ _).mp checks).1)
      · cases selected
  | updateRight index =>
    cases next : nextCursor input.right before.current.2 index with
    | none => simp [step, next] at selected
    | some cursor =>
      simp only [step, next] at selected
      change (if coherent input before.current (before.current.1, cursor) before.phase &&
        fenceClear context.profile.rightFences index .right before.phase then
        some ⟨(before.current.1, cursor), before.phase⟩ else none) = some after at selected
      split at selected
      · rename_i checks
        cases selected
        exact coherent_valid _ _ _ (((Bool.and_eq_true _ _).mp checks).1)
      · cases selected
  | updateBoth left right =>
    cases first : nextCursor input.left before.current.1 left with
    | none => simp [step, first] at selected
    | some nextLeft =>
      cases second : nextCursor input.right before.current.2 right with
      | none => simp [step, first, second] at selected
      | some nextRight =>
        simp only [step, first, second] at selected
        change (if coherent input before.current (nextLeft, nextRight) before.phase &&
          fenceClear context.profile.leftFences left .left before.phase &&
          fenceClear context.profile.rightFences right .right before.phase then
          some ⟨(nextLeft, nextRight), before.phase⟩ else none) = some after at selected
        split at selected
        · rename_i checks
          cases selected
          exact coherent_valid _ _ _ (((Bool.and_eq_true _ _).mp (((Bool.and_eq_true _ _).mp checks).1)).1)
        · cases selected

theorem successors_closed (context : Context input) (header : Packet.Header) (before after : Key input) (move : Move)
    (selected : (move, after) ∈ successors context header before) : after ∈ allKeys input :=
  mem_allKeys after (step_valid context header before after move ((mem_successors context header before after move).mp selected))

end Netlib.Federation.InFlight.Control
