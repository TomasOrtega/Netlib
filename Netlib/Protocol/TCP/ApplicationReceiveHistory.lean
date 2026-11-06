import Netlib.Protocol.TCP.ApplicationTraceCore
import Netlib.Protocol.TCP.ReceiveStoreHistory

/-!
# Actual receive allocations and ordered release

Each allocation is projected from one actual application operation.
Its carrier retains the original checked packet and local receipt time.
The ordered prefix uses released runs rather than packet arrival order.
-/

namespace Netlib.Protocol.TCP.Seq

theorem receive_epoch_position (origin : Seq) (current incoming : Nat)
    (currentBound : current < halfSpace) (incomingBound : incoming < halfSpace)
    (notOld : before (origin.add incoming) (origin.add current) = false) :
    current + distance (origin.add current) (origin.add incoming) = incoming := by
  have currentMod : current < modulus := by unfold halfSpace modulus at *; omega
  have incomingMod : incoming < modulus := by unfold halfSpace modulus at *; omega
  have currentDistance : distance origin (origin.add current) = current := by
    rw [distance_add, Nat.mod_eq_of_lt currentMod]
  have incomingDistance : distance origin (origin.add incoming) = incoming := by
    rw [distance_add, Nat.mod_eq_of_lt incomingMod]
  have forward := distance_triangle_mod origin (origin.add current) (origin.add incoming)
  have backward := distance_triangle_mod origin (origin.add incoming) (origin.add current)
  rw [currentDistance, incomingDistance] at forward backward
  have forwardBound := distance_lt (origin.add current) (origin.add incoming)
  have backwardBound := distance_lt (origin.add incoming) (origin.add current)
  have noBefore : ¬(0 < distance (origin.add incoming) (origin.add current) ∧
      distance (origin.add incoming) (origin.add current) < halfSpace) := by
    simpa only [before, decide_eq_false_iff_not, Before] using notOld
  unfold halfSpace modulus at *
  omega

end Netlib.Protocol.TCP.Seq

namespace Netlib.Protocol.TCP.ApplicationTrace

namespace H
export ReceiveStoreHistory (Accepted History StreamRange)
end H

structure ActualAllocation (operation : Step) where
  store : H.Accepted ReceiveReassembly.Receipt Step
  input : Input
  event : operation.event = .receive input
  carrier : store.carrier = operation
  before : store.before = operation.before.receiveStore
  after : store.after = operation.result.state.receiveStore
  position : store.position = ReceiveReassembly.position operation.before.core operation.before.receiveStore input.packet.segment
  payload : store.payload = input.packet.segment.payload
  metadata : store.metadata = ⟨input.packet.segment, input.packet.header, operation.before.now⟩
  edge : store.edge = operation.before.receiveStore.frontier + Endpoint.offeredWindow operation.before
  budget : store.budget = operation.before.core.window
  committed : (Endpoint.receiveEffect operation.before input).stored = some store.result
  runs : store.result.released = (Endpoint.receiveEffect operation.before input).runs
  released : ReceiveStore.bytes store.result.released = operation.releasedPayload
  notOld : Seq.before input.packet.segment.sequence operation.before.core.receiveNext = false

private theorem evaluate_no_receive_store (before : Model) (event : Event)
    (absent : ∀ input, event ≠ .receive input) : (evaluate before event).state.receiveStore = before.receiveStore := by
  cases event with
  | receive input => exact False.elim (absent input rfl)
  | write bytes =>
    simp only [evaluate]
    unfold Endpoint.write
    repeat' first | (solve | rfl) | split
  | read count =>
    simp only [evaluate]
    unfold Endpoint.read
    repeat' first | (solve | rfl) | split
  | send count policy =>
    simp only [evaluate]
    unfold Endpoint.send
    repeat' first
      | (solve | rfl)
      | (solve | rw [Endpoint.recoveryBlocked_state])
      | (solve | rw [Endpoint.ackBlocked_state])
      | split
  | emitAck policy =>
    simp only [evaluate]
    unfold Endpoint.emitAck Endpoint.pureAck
    repeat' first | (solve | rfl) | (solve | rw [Endpoint.ackBlocked_state]) | split
  | dispatchAck policy =>
    simp only [evaluate]
    unfold Endpoint.dispatchAck Endpoint.pureAck
    repeat' first | (solve | rfl) | (solve | rw [Endpoint.ackBlocked_state]) | split
  | enableRecovery =>
    simp only [evaluate]
    unfold Endpoint.enableRecovery
    repeat' first | (solve | rfl) | (solve | rw [Endpoint.recoveryBlocked_state]) | split
  | enableAck =>
    simp only [evaluate]
    unfold Endpoint.enableAck
    repeat' first
      | (solve | rfl)
      | (solve | rw [Endpoint.recoveryBlocked_state])
      | (solve | rw [Endpoint.ackBlocked_state])
      | split
  | advanceClock millis =>
    simp only [evaluate]
    unfold Endpoint.advanceClock
    repeat' first
      | (solve | rfl)
      | (solve | rw [Endpoint.recoveryBlocked_state])
      | (solve | rw [Endpoint.ackBlocked_state])
      | split
  | timeout policy =>
    simp only [evaluate]
    unfold Endpoint.timeout
    repeat' first
      | (solve | rfl)
      | (solve | rw [Endpoint.recoveryBlocked_state])
      | (solve | rw [Endpoint.ackBlocked_state])
      | split

inductive StoreTransition (operation : Step) where
  | stutter (state : operation.result.state.receiveStore = operation.before.receiveStore)
      (released : operation.releasedPayload = [])
  | accepted (allocation : ActualAllocation operation)

private def Step.receivedTransition (operation : Step) (input : Input) (event : operation.event = .receive input) :
    StoreTransition operation :=
  match selected : (Endpoint.receiveEffect operation.before input).stored with
  | none => .stutter (by
      have same := (Endpoint.receiveEffect_no_store operation.before input selected).state
      simpa only [operation.computed, event, evaluate, Endpoint.receive] using same) (by
      have same := (Endpoint.receiveEffect_no_store operation.before input selected).runs
      have effects := (Endpoint.receive_effects operation.before input).2.2.1
      simp only [Endpoint.receivedBytes, Endpoint.receiveRuns, same, ReceiveStore.bytes, List.flatMap_nil, List.append_nil] at effects
      simp only [Step.releasedPayload, ApplicationTrace.releasedPayload, event, operation.computed, evaluate, effects, List.drop_length])
  | some result =>
    let commit := Endpoint.receiveEffect_stored operation.before input result selected
    let store : H.Accepted ReceiveReassembly.Receipt Step := {
      before := operation.before.receiveStore
      position := ReceiveReassembly.position operation.before.core operation.before.receiveStore input.packet.segment
      payload := input.packet.segment.payload
      metadata := ⟨input.packet.segment, input.packet.header, operation.before.now⟩
      edge := operation.before.receiveStore.frontier + Endpoint.offeredWindow operation.before
      budget := operation.before.core.window
      result := result
      carrier := operation
      checked := by
        obtain ⟨_, _, _, checked⟩ := ReceiveReassembly.prepare_data _ _ _ _ _ _ commit.prepared
        exact checked }
    .accepted {
      store := store
      input := input
      event := event
      carrier := rfl
      before := rfl
      after := by
        change result.state = operation.result.state.receiveStore
        simpa only [operation.computed, event, evaluate, Endpoint.receive] using commit.state.symm
      position := rfl
      payload := rfl
      metadata := rfl
      edge := rfl
      budget := rfl
      committed := selected
      runs := commit.runs.symm
      released := by
        have effects := (Endpoint.receive_effects operation.before input).2.2.1
        simp only [Step.releasedPayload, ApplicationTrace.releasedPayload, event, operation.computed, evaluate, effects, List.drop_left]
        change ReceiveStore.bytes result.released = ReceiveStore.bytes (Endpoint.receiveEffect operation.before input).runs
        rw [commit.runs]
      notOld := Endpoint.prepare_data_not_old operation.before input result commit.prepared }

private def Step.otherTransition (operation : Step) (absent : ∀ input, operation.event ≠ .receive input) :
    StoreTransition operation := .stutter (by
      rw [operation.computed]
      exact evaluate_no_receive_store operation.before operation.event absent) (by
      cases event : operation.event with
      | receive input => exact False.elim (absent input event)
      | write _ | send _ _ | read _ | emitAck _ | enableRecovery | advanceClock _ | timeout _ | enableAck | dispatchAck _ =>
        simp only [Step.releasedPayload, ApplicationTrace.releasedPayload, event])

def Step.storeTransition (operation : Step) : StoreTransition operation := by
  cases event : operation.event
  case receive input => exact operation.receivedTransition input event
  all_goals exact operation.otherTransition (by intro input received; rw [event] at received; cases received)

def Step.allocation (operation : Step) : Option (ActualAllocation operation) :=
  match operation.storeTransition with | .stutter .. => none | .accepted allocation => some allocation

def receiveAllocations (operations : List Step) : List (H.Accepted ReceiveReassembly.Receipt Step) :=
  operations.filterMap (fun operation => operation.allocation.map (·.store))

theorem Chain.receive_history (chain : Chain initial operations final) :
    H.History initial.receiveStore (receiveAllocations operations) final.receiveStore := by
  induction chain with
  | nil state => exact .nil state.receiveStore
  | cons head tail ih =>
    cases transition : head.storeTransition with
    | stutter same empty =>
      simp only [receiveAllocations, List.filterMap_cons, Step.allocation, transition, Option.map_none]
      rw [same] at ih
      exact ih
    | accepted allocation =>
      simp only [receiveAllocations, List.filterMap_cons, Step.allocation, transition, Option.map_some]
      rw [← allocation.before]
      apply ReceiveStoreHistory.History.cons allocation.store
      rw [allocation.after]
      exact ih

theorem receiveAllocations_released (operations : List Step) :
    (receiveAllocations operations).flatMap (fun allocation => ReceiveStore.bytes allocation.result.released) =
      operations.flatMap Step.releasedPayload := by
  induction operations with
  | nil => rfl
  | cons head tail ih =>
    cases transition : head.storeTransition with
    | stutter same empty =>
      simp only [receiveAllocations, List.filterMap_cons, Step.allocation, transition, Option.map_none,
        List.flatMap_cons, empty, List.nil_append]
      exact ih
    | accepted allocation =>
      simp only [receiveAllocations, List.filterMap_cons, Step.allocation, transition, Option.map_some,
        List.flatMap_cons, allocation.released]
      exact congrArg (head.releasedPayload ++ ·) ih

theorem receiveAllocations_origin (operations : List Step) (allocation : H.Accepted ReceiveReassembly.Receipt Step)
    (member : allocation ∈ receiveAllocations operations) :
    ∃ operation ∈ operations, ∃ actual : ActualAllocation operation,
      operation.allocation = some actual ∧ actual.store = allocation := by
  obtain ⟨operation, belongs, selected⟩ := List.mem_filterMap.mp member
  cases found : operation.allocation with
  | none => simp only [found, Option.map_none] at selected; cases selected
  | some actual =>
    simp only [found, Option.map_some, Option.some.injEq] at selected
    exact ⟨operation, belongs, actual, found, selected⟩

theorem ActualAllocation.streamRange (actual : ActualAllocation operation)
    (sourceChain : Chain sourceInitial sourceSteps sourceFinal) (emptySent : sourceInitial.core.sent = [])
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace)
    (base : Nat) (accumulated : List UInt8) (prior : accumulated <+: sourceSteps.flatMap Step.emitted)
    (cursor : operation.before.core.receiveNext = sourceInitial.core.sendNext.add accumulated.length)
    (frontier : operation.before.receiveStore.frontier = base + accumulated.length)
    (delivered : Delivered sourceSteps operation) :
    H.StreamRange base (sourceSteps.flatMap Step.emitted) actual.store.allocated := by
  obtain ⟨source, _, path⟩ := delivered actual.input actual.event
  obtain ⟨prefixBytes, rangePrefix, sequence⟩ := source.range sourceChain emptySent
  have ranged := rangePrefix.trans source.scope_prefix
  have sourcePrefix : prefixBytes <+: sourceSteps.flatMap Step.emitted :=
    (List.prefix_append _ _).trans ranged
  have currentBound : accumulated.length < Seq.halfSpace := Nat.lt_of_le_of_lt prior.length_le epoch
  have incomingBound : prefixBytes.length < Seq.halfSpace := Nat.lt_of_le_of_lt sourcePrefix.length_le epoch
  have incoming : actual.input.packet.segment.sequence = sourceInitial.core.sendNext.add prefixBytes.length :=
    path.fields.2.trans sequence
  have position := Seq.receive_epoch_position sourceInitial.core.sendNext accumulated.length prefixBytes.length
    currentBound incomingBound (by simpa only [← incoming, ← cursor] using actual.notOld)
  refine ⟨prefixBytes, ?_, ?_⟩
  · change base + prefixBytes.length = actual.store.position
    rw [actual.position, ReceiveReassembly.position, frontier, cursor, incoming]
    omega
  · change prefixBytes ++ actual.store.payload <+: sourceSteps.flatMap Step.emitted
    rw [actual.payload, path.fields.1]
    exact ranged

private theorem released_prefix_aux (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (emptySent : sourceInitial.core.sent = [])
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace)
    (base : Nat) (targetChain : Chain targetInitial targetSteps targetFinal) :
    ∀ accumulated : List UInt8,
      accumulated <+: sourceSteps.flatMap Step.emitted →
      targetInitial.core.receiveNext = sourceInitial.core.sendNext.add accumulated.length →
      targetInitial.receiveStore.frontier = base + accumulated.length →
      (∀ run ∈ targetInitial.receiveStore.held, H.StreamRange base (sourceSteps.flatMap Step.emitted) run) →
      (∀ operation ∈ targetSteps, Delivered sourceSteps operation) →
      accumulated ++ targetSteps.flatMap Step.releasedPayload <+: sourceSteps.flatMap Step.emitted := by
  induction targetChain with
  | nil state => intro accumulated prior _ _ _ _; simpa using prior
  | cons head tail ih =>
    intro accumulated prior cursor frontier held delivered
    cases transition : head.storeTransition with
    | stutter same empty =>
      have nextCursor : head.result.state.core.receiveNext = sourceInitial.core.sendNext.add accumulated.length := by
        rw [head.receiveNext_balance, empty, List.length_nil, Seq.add_zero]
        exact cursor
      have nextFrontier : head.result.state.receiveStore.frontier = base + accumulated.length := by
        rw [same]
        exact frontier
      have nextHeld : ∀ run ∈ head.result.state.receiveStore.held, H.StreamRange base (sourceSteps.flatMap Step.emitted) run := by
        rw [same]
        exact held
      have rest := ih accumulated prior nextCursor nextFrontier nextHeld
        (fun operation member => delivered operation (by simp [member]))
      simpa only [List.flatMap_cons, empty, List.nil_append] using rest
    | accepted allocation =>
      have incoming := allocation.streamRange sourceChain emptySent epoch base accumulated prior cursor frontier
        (delivered head (by simp))
      have added := allocation.store.prefix_step base (sourceSteps.flatMap Step.emitted) accumulated
        (by rw [allocation.before]; exact frontier) prior
        (by rw [allocation.before]; exact held) incoming
      have nextPrefix : accumulated ++ head.releasedPayload <+: sourceSteps.flatMap Step.emitted := by
        simpa only [allocation.released] using added.1
      have nextCursor : head.result.state.core.receiveNext =
          sourceInitial.core.sendNext.add (accumulated ++ head.releasedPayload).length := by
        rw [head.receiveNext_balance, cursor, Seq.add_add, List.length_append]
      have nextFrontier : head.result.state.receiveStore.frontier = base + (accumulated ++ head.releasedPayload).length := by
        rw [← allocation.after, allocation.store.frontier, allocation.before, allocation.released, frontier, List.length_append]
        omega
      have nextHeld : ∀ run ∈ head.result.state.receiveStore.held, H.StreamRange base (sourceSteps.flatMap Step.emitted) run := by
        rw [← allocation.after]
        exact added.2
      have rest := ih (accumulated ++ head.releasedPayload) nextPrefix nextCursor nextFrontier nextHeld
        (fun operation member => delivered operation (by simp [member]))
      simpa only [List.flatMap_cons, List.append_assoc] using rest

theorem released_prefix_emitted (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (emptySent : sourceInitial.core.sent = [])
    (targetChain : Chain targetInitial targetSteps targetFinal)
    (history : DeliveryHistory sourceSteps targetSteps)
    (emptyHeld : targetInitial.receiveStore.held = [])
    (cursors : targetInitial.core.receiveNext = sourceInitial.core.sendNext)
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace) :
    targetSteps.flatMap Step.releasedPayload <+: sourceSteps.flatMap Step.emitted := by
  have result := released_prefix_aux sourceChain emptySent epoch targetInitial.receiveStore.frontier targetChain []
    (by simp) (by simpa only [List.length_nil, Seq.add_zero] using cursors) (by simp)
    (by intro run member; simp only [emptyHeld, List.not_mem_nil] at member) history.delivered
  simpa only [List.nil_append] using result

def Step.releasedRuns (operation : Step) : List ReceiveReassembly.Run :=
  match operation.allocation with | none => [] | some actual => actual.store.result.released

theorem Step.releasedPayload_runs (operation : Step) :
    operation.releasedPayload = ReceiveStore.bytes operation.releasedRuns := by
  cases transition : operation.storeTransition with
  | stutter state empty =>
    simp only [Step.releasedRuns, Step.allocation, transition, empty, ReceiveStore.bytes, List.flatMap_nil]
  | accepted actual =>
    simp only [Step.releasedRuns, Step.allocation, transition]
    exact actual.released.symm

theorem ActualAllocation.accepted (actual : ActualAllocation operation) :
    ∃ count, operation.result.decision = .accepted (.receive count actual.store.result.novel) := by
  have selected := (Endpoint.receiveEffect_stored operation.before actual.input actual.store.result actual.committed).accepted
  simpa only [operation.computed, actual.event, evaluate, Endpoint.receive] using selected

structure RunReceiptOrigin (operations : List Step) (run : ReceiveReassembly.Run) where
  issuer : Step
  allocation : ActualAllocation issuer
  selected : issuer.allocation = some allocation
  member : issuer ∈ operations
  allocated : run = allocation.store.allocated

theorem Chain.held_run_origin (chain : Chain initial operations final) (empty : initial.receiveStore.held = [])
    (run : ReceiveReassembly.Run) (held : run ∈ final.receiveStore.held) :
    Nonempty (RunReceiptOrigin operations run) := by
  obtain ⟨issuer, belongs, allocated⟩ := chain.receive_history.held_origin empty run held
  obtain ⟨operation, member, source, selected, same⟩ := receiveAllocations_origin operations issuer belongs
  exact ⟨⟨operation, source, selected, member,
    allocated.trans (congrArg ReceiveStoreHistory.Accepted.allocated same.symm)⟩⟩

theorem RunReceiptOrigin.fields (value : RunReceiptOrigin operations run) :
    run.bytes = value.allocation.input.packet.segment.payload ∧
      run.metadata = ⟨value.allocation.input.packet.segment, value.allocation.input.packet.header, value.issuer.before.now⟩ ∧
      run.receipt = value.issuer.before.receiveStore.nextID ∧
      run.position = ReceiveReassembly.position value.issuer.before.core value.issuer.before.receiveStore
        value.allocation.input.packet.segment := by
  have bytes := congrArg ReceiveStore.Run.bytes value.allocated
  have metadata := congrArg ReceiveStore.Run.metadata value.allocated
  have receipt := congrArg ReceiveStore.Run.receipt value.allocated
  have position := congrArg ReceiveStore.Run.position value.allocated
  exact ⟨bytes.trans value.allocation.payload, metadata.trans value.allocation.metadata,
    receipt.trans (congrArg (·.nextID) value.allocation.before), position.trans value.allocation.position⟩

theorem receiveAllocations_selected (operation : Step) (member : operation ∈ operations)
    (actual : ActualAllocation operation) (selected : operation.allocation = some actual) :
    actual.store ∈ receiveAllocations operations := by
  apply List.mem_filterMap.mpr
  exact ⟨operation, member, by rw [selected]; rfl⟩

theorem ActualAllocation.unique (chain : Chain initial operations final)
    (first : ActualAllocation firstStep) (second : ActualAllocation secondStep)
    (firstMember : firstStep ∈ operations) (secondMember : secondStep ∈ operations)
    (firstSelected : firstStep.allocation = some first) (secondSelected : secondStep.allocation = some second)
    (identity : firstStep.before.receiveStore.nextID = secondStep.before.receiveStore.nextID) : firstStep = secondStep := by
  have same := chain.receive_history.allocation_unique first.store second.store
    (receiveAllocations_selected firstStep firstMember first firstSelected)
    (receiveAllocations_selected secondStep secondMember second secondSelected)
    (by rw [first.before, second.before]; exact identity)
  exact first.carrier.symm.trans ((congrArg ReceiveStoreHistory.Accepted.carrier same).trans second.carrier)

structure ReceiptAt (operations : List Step) (id : Nat) where
  prior : List Step
  issuer : Step
  later : List Step
  split : operations = prior ++ issuer :: later
  allocation : ActualAllocation issuer
  selected : issuer.allocation = some allocation
  identity : issuer.before.receiveStore.nextID = id

def findReceipt : (operations : List Step) → (id : Nat) → Except String (ReceiptAt operations id)
  | [], _ => .error "The actual receive allocation is absent from this history."
  | head :: tail, id =>
    match selected : head.allocation with
    | none => do
      let rest ← findReceipt tail id
      return ⟨head :: rest.prior, rest.issuer, rest.later,
        by simp only [rest.split, List.cons_append], rest.allocation, rest.selected, rest.identity⟩
    | some actual => do
      if identity : head.before.receiveStore.nextID = id then
        return ⟨[], head, tail, rfl, actual, selected, identity⟩
      else
        let rest ← findReceipt tail id
        return ⟨head :: rest.prior, rest.issuer, rest.later,
          by simp only [rest.split, List.cons_append], rest.allocation, rest.selected, rest.identity⟩

theorem ReceiptAt.member {id : Nat} (value : ReceiptAt operations id) : value.issuer ∈ operations := by
  have belongs : value.issuer ∈ value.prior ++ value.issuer :: value.later := by simp
  exact Eq.mpr (congrArg (fun list => value.issuer ∈ list) value.split) belongs

structure ReleasedRunOrigin (operations : List Step) (release : Step) (run : ReceiveReassembly.Run) where
  prior : List Step
  later : List Step
  split : operations = prior ++ release :: later
  issuer : Step
  allocation : ActualAllocation issuer
  selected : issuer.allocation = some allocation
  place : issuer ∈ prior ∨ issuer = release
  allocated : run = allocation.store.allocated

theorem released_run_origin (chain : Chain initial operations final) (empty : initial.receiveStore.held = [])
    (release : Step) (member : release ∈ operations) (run : ReceiveReassembly.Run)
    (released : run ∈ release.releasedRuns) : Nonempty (ReleasedRunOrigin operations release run) := by
  obtain ⟨prior, later, split, preceding, _⟩ := chain.split release member
  cases transition : release.storeTransition with
  | stutter state emptyRelease =>
    simp only [Step.releasedRuns, Step.allocation, transition, List.not_mem_nil] at released
  | accepted actual =>
    have present : run ∈ actual.store.result.released := by
      simpa only [Step.releasedRuns, Step.allocation, transition] using released
    rcases actual.store.source run (.inl present) with held | current
    · have inHeld : run ∈ release.before.receiveStore.held := by simpa only [actual.before] using held
      obtain ⟨issuer, belongs, allocated⟩ := preceding.receive_history.held_origin empty run inHeld
      obtain ⟨operation, earlier, source, selected, same⟩ := receiveAllocations_origin prior issuer belongs
      exact ⟨⟨prior, later, split, operation, source, selected, .inl earlier,
        allocated.trans (congrArg ReceiveStoreHistory.Accepted.allocated same.symm)⟩⟩
    · exact ⟨⟨prior, later, split, release, actual,
        by simp only [Step.allocation, transition], .inr rfl, current⟩⟩

theorem ReleasedRunOrigin.issuer_member (value : ReleasedRunOrigin operations release run) : value.issuer ∈ operations := by
  have belongs : value.issuer ∈ value.prior ++ release :: value.later := by
    rcases value.place with earlier | same
    · exact List.mem_append_left _ earlier
    · simp only [same, List.mem_append, List.mem_cons, true_or, or_true]
  exact Eq.mpr (congrArg (fun list => value.issuer ∈ list) value.split) belongs

def ReleasedRunOrigin.receiptOrigin (value : ReleasedRunOrigin operations release run) : RunReceiptOrigin operations run :=
  ⟨value.issuer, value.allocation, value.selected, value.issuer_member, value.allocated⟩

theorem ReleasedRunOrigin.fields (value : ReleasedRunOrigin operations release run) :
    run.bytes = value.allocation.input.packet.segment.payload ∧
      run.metadata = ⟨value.allocation.input.packet.segment, value.allocation.input.packet.header, value.issuer.before.now⟩ ∧
      run.receipt = value.issuer.before.receiveStore.nextID ∧
      run.position = ReceiveReassembly.position value.issuer.before.core value.issuer.before.receiveStore
        value.allocation.input.packet.segment := by
  have bytes := congrArg ReceiveStore.Run.bytes value.allocated
  have metadata := congrArg ReceiveStore.Run.metadata value.allocated
  have receipt := congrArg ReceiveStore.Run.receipt value.allocated
  have position := congrArg ReceiveStore.Run.position value.allocated
  exact ⟨bytes.trans value.allocation.payload, metadata.trans value.allocation.metadata,
    receipt.trans (congrArg (·.nextID) value.allocation.before), position.trans value.allocation.position⟩

theorem ReleasedRunOrigin.no_later (value : ReleasedRunOrigin operations release run) (ordered : Chronological operations) :
    value.issuer.stamp ≤ release.stamp := by
  rcases value.place with earlier | same
  · have pair := ordered
    unfold Chronological at pair
    rw [value.split] at pair
    have strict := (List.pairwise_append.mp pair).2.2 value.issuer earlier release (by simp)
    omega
  · rw [same]
    exact Nat.le_refl _

theorem ReleasedRunOrigin.held_earlier (value : ReleasedRunOrigin operations release run)
    (ordered : Chronological operations) (held : run ∈ release.before.receiveStore.held)
    (actual : ActualAllocation release) : value.issuer.stamp < release.stamp := by
  rcases value.place with earlier | same
  · have pair := ordered
    unfold Chronological at pair
    rw [value.split] at pair
    exact (List.pairwise_append.mp pair).2.2 value.issuer earlier release (by simp)
  · have old : run.receipt < release.before.receiveStore.nextID := by
      rw [← actual.before] at held ⊢
      exact actual.store.held_before run held
    have identity := value.fields.2.2.1
    rw [same] at identity
    omega

theorem RunReceiptOrigin.unique (value other : RunReceiptOrigin operations run)
    (chain : Chain initial operations final) : value.issuer = other.issuer :=
  value.allocation.unique chain other.allocation value.member other.member value.selected other.selected
    (value.fields.2.2.1.symm.trans other.fields.2.2.1)

theorem RunReceiptOrigin.no_later (value : RunReceiptOrigin operations run)
    (chain : Chain initial operations final) (empty : initial.receiveStore.held = [])
    (release : Step) (member : release ∈ operations) (released : run ∈ release.releasedRuns)
    (ordered : Chronological operations) : value.issuer.stamp ≤ release.stamp := by
  obtain ⟨origin⟩ := released_run_origin chain empty release member run released
  have same := value.unique origin.receiptOrigin chain
  change value.issuer = origin.issuer at same
  rw [same]
  exact origin.no_later ordered

theorem RunReceiptOrigin.held_earlier (value : RunReceiptOrigin operations run)
    (chain : Chain initial operations final) (empty : initial.receiveStore.held = [])
    (release : Step) (member : release ∈ operations) (released : run ∈ release.releasedRuns)
    (held : run ∈ release.before.receiveStore.held) (ordered : Chronological operations) :
    value.issuer.stamp < release.stamp := by
  obtain ⟨origin⟩ := released_run_origin chain empty release member run released
  have same := value.unique origin.receiptOrigin chain
  change value.issuer = origin.issuer at same
  rw [same]
  cases transition : release.storeTransition with
  | stutter state noRelease =>
    simp only [Step.releasedRuns, Step.allocation, transition, List.not_mem_nil] at released
  | accepted actual => exact origin.held_earlier ordered held actual

structure ActualReleasedByteOrigin (operations : List Step) (release : Step) (index : Nat) (byte : UInt8) where
  prior : List ReceiveReassembly.Run
  run : ReceiveReassembly.Run
  later : List ReceiveReassembly.Run
  split : release.releasedRuns = prior ++ run :: later
  localIndex : Nat
  position : index = ReceiveStore.size prior + localIndex
  selected : run.bytes[localIndex]? = some byte
  origin : ReleasedRunOrigin operations release run
  coordinate : run.position + localIndex = release.before.receiveStore.frontier + index

theorem released_byte_origin (chain : Chain initial operations final) (empty : initial.receiveStore.held = [])
    (release : Step) (member : release ∈ operations) (index : Nat) (byte : UInt8)
    (selected : release.releasedPayload[index]? = some byte) :
    Nonempty (ActualReleasedByteOrigin operations release index byte) := by
  rw [release.releasedPayload_runs] at selected
  obtain ⟨prior, run, later, localIndex, split, position, present⟩ :=
    ReceiveStoreHistory.bytes_location _ index byte selected
  have belongs : run ∈ release.releasedRuns := by rw [split]; simp
  obtain ⟨origin⟩ := released_run_origin chain empty release member run belongs
  have aligned : ReceiveStore.Contiguous release.before.receiveStore.frontier release.releasedRuns := by
    cases transition : release.storeTransition with
    | stutter state empty =>
      simp only [Step.releasedRuns, Step.allocation, transition, ReceiveStore.Contiguous]
    | accepted actual =>
      simpa only [Step.releasedRuns, Step.allocation, transition, actual.before] using actual.store.contiguous
  have coordinate := ReceiveStoreHistory.contiguous_position _ _ prior later run aligned split
  exact ⟨⟨prior, run, later, split, localIndex, position, present, origin, by omega⟩⟩

theorem ActualReleasedByteOrigin.input_byte (value : ActualReleasedByteOrigin operations release index byte) :
    value.origin.allocation.input.packet.segment.payload[value.localIndex]? = some byte := by
  rw [← value.origin.fields.1]
  exact value.selected

theorem ActualReleasedByteOrigin.input_position (value : ActualReleasedByteOrigin operations release index byte) :
    value.origin.allocation.store.position + value.localIndex = release.before.receiveStore.frontier + index := by
  have same := congrArg ReceiveStore.Run.position value.origin.allocated
  change value.run.position = value.origin.allocation.store.position at same
  have coordinate := value.coordinate
  omega

private def checkedReceiptOrigin (chain : Chain initial operations final) (run : ReceiveReassembly.Run)
    (valid : Nonempty (RunReceiptOrigin operations run)) : Except String (RunReceiptOrigin operations run) := do
  let issuer ← findReceipt operations run.receipt
  have allocated : run = issuer.allocation.store.allocated := by
    obtain ⟨origin⟩ := valid
    have same := chain.receive_history.allocation_unique origin.allocation.store issuer.allocation.store
      (receiveAllocations_selected origin.issuer origin.member origin.allocation origin.selected)
      (receiveAllocations_selected issuer.issuer issuer.member issuer.allocation issuer.selected)
      (by rw [origin.allocation.before, issuer.allocation.before]; exact origin.fields.2.2.1.symm.trans issuer.identity.symm)
    exact origin.allocated.trans (congrArg ReceiveStoreHistory.Accepted.allocated same)
  return ⟨issuer.issuer, issuer.allocation, issuer.selected, issuer.member, allocated⟩

def heldRunOrigin (chain : Chain initial operations final) (empty : initial.receiveStore.held = [])
    (run : ReceiveReassembly.Run) (held : run ∈ final.receiveStore.held) :
    Except String (RunReceiptOrigin operations run) :=
  checkedReceiptOrigin chain run (chain.held_run_origin empty run held)

def releasedReceiptOrigin (chain : Chain initial operations final) (empty : initial.receiveStore.held = [])
    (release : Step) (member : release ∈ operations) (run : ReceiveReassembly.Run)
    (released : run ∈ release.releasedRuns) : Except String (RunReceiptOrigin operations run) :=
  checkedReceiptOrigin chain run (by
    obtain ⟨origin⟩ := released_run_origin chain empty release member run released
    exact ⟨origin.receiptOrigin⟩)

end Netlib.Protocol.TCP.ApplicationTrace
