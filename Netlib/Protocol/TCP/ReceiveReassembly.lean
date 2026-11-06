import Netlib.Protocol.TCP.ReceiveStore
import Netlib.Protocol.TCP.EstablishedReceive

/-!
# Actual packet receipts and bounded receive plans

The plan retains the whole original segment and its local arrival time.
It releases every contiguous run before the endpoint generates one ACK cause.
ACK and window effects of held data are deferred until release.
-/

namespace Netlib.Protocol.TCP.ReceiveReassembly

namespace E
export EstablishedReceive (State Input Block AckRequest)
end E

structure Receipt where
  segment : Segment
  header : Packet.Header
  receivedAt : Nat
  deriving Repr, BEq, DecidableEq

abbrev Run := ReceiveStore.Run Receipt
abbrev Store := ReceiveStore.State Receipt

inductive Plan where
  | blocked (reason : E.Block) (ack : Option E.AckRequest)
  | acknowledgment (count : Nat)
  | data (stored : ReceiveStore.Result Receipt)
  deriving Repr, BEq, DecidableEq

def storeBlock : ReceiveStore.Stop → E.Block
  | .invalid | .empty => .reject .invalidSeed
  | .left | .right => .unsupported .trimming
  | .overlap => .unsupported .overlap
  | .conflict => .unsupported .conflict
  | .capacity => .unsupported .receiveCapacity

def request (state : E.State) (window : Nat) (kind : EstablishedReceive.AckKind) : E.AckRequest :=
  { EstablishedReceive.request state kind with window }

def position (state : E.State) (store : Store) (segment : Segment) : Nat :=
  store.frontier + Seq.distance state.receiveNext segment.sequence

def initialGate (state : E.State) (input : E.Input) (window : Nat) : EstablishedReceive.Gate :=
  if ¬state.Valid then .blocked (.reject .invalidSeed) none
  else if input.packet.header ≠ state.inbound then .blocked (.reject .tuple) none
  else if let some reason := EstablishedReceive.control input.packet.segment then .blocked (.unsupported reason) none
  else if !ReceiveWindow.acceptsSegment state.receiveNext window input.packet.segment then
    .blocked (.reject .sequence) (some .sequence)
  else .next 0

def prepare (state : E.State) (store : Store) (input : E.Input) (window now : Nat) : Plan :=
  match initialGate state input window with
  | .blocked reason kind => .blocked reason (kind.map (request state window))
  | .next _ =>
    if input.packet.segment.payload.isEmpty then
      match EstablishedReceive.gateWithWindow state input.packet.header input.packet.segment window with
      | .blocked reason kind => .blocked reason (kind.map (request state window))
      | .next count => .acknowledgment count
    else if Seq.before input.packet.segment.sequence state.receiveNext then .blocked (.unsupported .trimming) none
    else match ReceiveStore.accept store (position state store input.packet.segment)
        input.packet.segment.payload ⟨input.packet.segment, input.packet.header, now⟩ (store.frontier + window) state.window with
      | .error reason => .blocked (storeBlock reason) none
      | .ok stored => .data stored

def Plan.released : Plan → List Run
  | .data stored => stored.released
  | _ => []

def Plan.releasedBytes (plan : Plan) : List UInt8 := ReceiveStore.bytes plan.released

def immediate (state : E.State) (store : Store) (input : E.Input) : Bool :=
  decide (input.packet.segment.sequence ≠ state.receiveNext) || !store.held.isEmpty

theorem prepare_data (state : E.State) (store : Store) (input : E.Input) (window now : Nat)
    (stored : ReceiveStore.Result Receipt) (selected : prepare state store input window now = .data stored) :
    ∃ count, initialGate state input window = .next count ∧
      input.packet.segment.payload.isEmpty = false ∧
      ReceiveStore.accept store (position state store input.packet.segment) input.packet.segment.payload
        ⟨input.packet.segment, input.packet.header, now⟩ (store.frontier + window) state.window = .ok stored := by
  unfold prepare at selected
  cases gated : initialGate state input window with
  | blocked reason kind => simp only [gated] at selected; cases selected
  | next count =>
    simp only [gated] at selected
    split at selected
    · cases checked : EstablishedReceive.gateWithWindow state input.packet.header input.packet.segment window with
      | blocked reason kind => simp only [checked] at selected; cases selected
      | next amount => simp only [checked] at selected; cases selected
    · rename_i nonempty
      split at selected
      · cases selected
      · cases accepted : ReceiveStore.accept store (position state store input.packet.segment)
          input.packet.segment.payload ⟨input.packet.segment, input.packet.header, now⟩ (store.frontier + window) state.window with
        | error reason => simp only [accepted] at selected; cases selected
        | ok result =>
          simp only [accepted, Plan.data.injEq] at selected
          subst result
          exact ⟨count, rfl, by cases empty : input.packet.segment.payload.isEmpty <;> simp_all, rfl⟩

theorem prepare_source (state : E.State) (store : Store) (input : E.Input) (window now : Nat)
    (stored : ReceiveStore.Result Receipt) (selected : prepare state store input window now = .data stored)
    (run : Run) (member : run ∈ stored.released ∨ run ∈ stored.state.held) :
    run ∈ store.held ∨ run = ReceiveStore.current store (position state store input.packet.segment)
      input.packet.segment.payload ⟨input.packet.segment, input.packet.header, now⟩ := by
  obtain ⟨_, _, _, accepted⟩ := prepare_data state store input window now stored selected
  exact ReceiveStore.accept_source store _ _ _ _ _ stored accepted run member

theorem prepare_frontier (state : E.State) (store : Store) (input : E.Input) (window now : Nat)
    (stored : ReceiveStore.Result Receipt) (selected : prepare state store input window now = .data stored) :
    stored.state.frontier = store.frontier + (ReceiveStore.bytes stored.released).length := by
  obtain ⟨_, _, _, accepted⟩ := prepare_data state store input window now stored selected
  rw [ReceiveStore.size_bytes]
  exact ReceiveStore.accept_frontier store _ _ _ _ _ stored accepted

structure HeaderEffect where
  before : E.State
  run : Run
  acknowledged : Nat
  after : E.State
  deriving Repr, BEq, DecidableEq

structure HeaderFailure where
  before : E.State
  run : Run
  reason : E.Block
  deriving Repr, BEq, DecidableEq

def applyRun (state : E.State) (run : Run) : Except HeaderFailure HeaderEffect :=
  if run.metadata.segment.payload ≠ run.bytes then .error ⟨state, run, .unsupported .queuedHeader⟩
  else
    let result := EstablishedReceive.evaluate state run.metadata.header run.metadata.segment
    match result.decision with
    | .blocked reason => .error ⟨state, run, reason⟩
    | .accepted count _ => .ok ⟨state, run, count, result.state⟩

structure Applied where
  state : E.State
  acknowledged : Nat
  headers : List HeaderEffect
  deriving Repr, BEq, DecidableEq

def applyRuns (state : E.State) : List Run → Except HeaderFailure Applied
  | [] => .ok ⟨state, 0, []⟩
  | head :: tail => do
    let first ← applyRun state head
    let rest ← applyRuns first.after tail
    return ⟨rest.state, first.acknowledged + rest.acknowledged, first :: rest.headers⟩

theorem applyRun_fields (state : E.State) (run : Run) (effect : HeaderEffect)
    (accepted : applyRun state run = .ok effect) :
    effect.before = state ∧ effect.run = run ∧
      EstablishedReceive.acknowledgedCount state run.metadata.segment.acknowledgment = some effect.acknowledged ∧
      effect.acknowledged ≤ state.sent.length ∧ run.bytes.length ≤ state.window ∧
      effect.after = EstablishedReceive.commit state run.bytes effect.acknowledged := by
  unfold applyRun at accepted
  split at accepted
  · cases accepted
  · rename_i matching
    have payload : run.metadata.segment.payload = run.bytes := Decidable.not_not.mp matching
    cases decision : (EstablishedReceive.evaluate state run.metadata.header run.metadata.segment).decision with
    | blocked reason => simp only [decision] at accepted; cases accepted
    | accepted count size =>
      simp only [decision, Except.ok.injEq] at accepted
      subst effect
      have effects := EstablishedReceive.evaluate_effects state run.metadata.header run.metadata.segment
      simp only [EstablishedReceive.Effects, decision] at effects
      obtain ⟨counted, bounded, _, fits, result⟩ := effects
      exact ⟨rfl, rfl, counted, bounded, by simpa only [payload] using fits,
        by simpa only [payload] using result⟩

theorem applyRun_failure (state : E.State) (run : Run) (failure : HeaderFailure)
    (blocked : applyRun state run = .error failure) : failure.before = state ∧ failure.run = run := by
  unfold applyRun at blocked
  split at blocked
  · cases blocked
    exact ⟨rfl, rfl⟩
  · cases decision : (EstablishedReceive.evaluate state run.metadata.header run.metadata.segment).decision with
    | blocked reason =>
      simp only [decision, Except.error.injEq] at blocked
      subst failure
      exact ⟨rfl, rfl⟩
    | accepted count size => simp only [decision] at blocked; cases blocked

theorem applyRun_valid (state : E.State) (run : Run) (effect : HeaderEffect) (valid : state.Valid)
    (accepted : applyRun state run = .ok effect) : effect.after.Valid := by
  obtain ⟨_, _, _, count, room, same⟩ := applyRun_fields state run effect accepted
  rw [same]
  exact EstablishedReceive.commit_valid state run.bytes effect.acknowledged valid room count

theorem applyRuns_cons (state : E.State) (head : Run) (tail : List Run) (result : Applied)
    (accepted : applyRuns state (head :: tail) = .ok result) :
    ∃ first rest, applyRun state head = .ok first ∧ applyRuns first.after tail = .ok rest ∧
      result = ⟨rest.state, first.acknowledged + rest.acknowledged, first :: rest.headers⟩ := by
  unfold applyRuns at accepted
  cases first : applyRun state head with
  | error reason => simp [first, bind, Except.bind] at accepted
  | ok effect =>
    cases rest : applyRuns effect.after tail with
    | error reason => simp [first, rest, bind, Except.bind] at accepted
    | ok applied =>
      simp only [first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      exact ⟨effect, applied, rfl, rest, accepted.symm⟩

theorem applyRuns_valid (state : E.State) (runs : List Run) (result : Applied) (valid : state.Valid)
    (accepted : applyRuns state runs = .ok result) : result.state.Valid := by
  induction runs generalizing state result with
  | nil =>
    simp only [applyRuns, Except.ok.injEq] at accepted
    subst result
    exact valid
  | cons head tail ih =>
    obtain ⟨first, rest, firstEq, restEq, same⟩ := applyRuns_cons state head tail result accepted
    rw [same]
    exact ih first.after rest (applyRun_valid state head first valid firstEq) restEq

theorem applyRuns_failure_source (state : E.State) (runs : List Run) (failure : HeaderFailure)
    (blocked : applyRuns state runs = .error failure) : failure.run ∈ runs := by
  induction runs generalizing state with
  | nil => simp [applyRuns] at blocked
  | cons head tail ih =>
    unfold applyRuns at blocked
    cases first : applyRun state head with
    | error reason =>
      simp only [first, bind, Except.bind, Except.error.injEq] at blocked
      subst failure
      have same := (applyRun_failure state head reason first).2
      exact List.mem_cons.mpr (.inl same)
    | ok effect =>
      cases rest : applyRuns effect.after tail with
      | error reason =>
        simp only [first, rest, bind, Except.bind, Except.error.injEq] at blocked
        subst failure
        exact List.mem_cons.mpr (.inr (ih effect.after rest))
      | ok result => simp only [first, rest, bind, Except.bind, pure, Except.pure] at blocked; cases blocked

theorem applyRuns_effects (state : E.State) (runs : List Run) (result : Applied)
    (accepted : applyRuns state runs = .ok result) :
    result.state.received = state.received ++ ReceiveStore.bytes runs ∧
      result.state.receiveNext = state.receiveNext.add (ReceiveStore.size runs) ∧
      result.state.sent = state.sent.drop result.acknowledged ∧
      result.state.sendUna = state.sendUna.add result.acknowledged ∧
      result.state.sendNext = state.sendNext ∧ result.state.capacity = state.capacity ∧
      result.state.inbound = state.inbound ∧ result.acknowledged ≤ state.sent.length := by
  induction runs generalizing state result with
  | nil =>
    simp only [applyRuns, Except.ok.injEq] at accepted
    subst result
    simp [ReceiveStore.bytes, ReceiveStore.size]
  | cons head tail ih =>
    obtain ⟨first, rest, firstEq, restEq, same⟩ := applyRuns_cons state head tail result accepted
    obtain ⟨_, _, _, count, _, firstState⟩ := applyRun_fields state head first firstEq
    obtain ⟨received, cursor, sent, una, next, capacity, header, bound⟩ := ih first.after rest restEq
    rw [same]
    simp only [firstState, EstablishedReceive.commit] at received cursor sent una next capacity header bound
    refine ⟨?_, ?_, ?_, ?_, next, capacity, header, ?_⟩
    · simpa only [ReceiveStore.bytes, List.flatMap_cons, List.append_assoc] using received
    · simpa only [ReceiveStore.size, List.map_cons, List.sum_cons, Seq.add_add] using cursor
    · simpa only [List.drop_drop] using sent
    · simpa only [Seq.add_add] using una
    · simp only [List.length_drop] at bound
      change first.acknowledged + rest.acknowledged ≤ state.sent.length
      omega

end Netlib.Protocol.TCP.ReceiveReassembly
