import Netlib.Check.TCPHandshakeRecoveryEvaluate

/-!
# Histories from actual startup recovery operations

The trace stores each checked operation once.
Every received source remains an earlier actual emission.
Occurrence indices are event stamps, not campus output or custody indices.
-/

namespace Netlib.Check.TCPHandshakeRecovery

variable {active passive : Protocol.TCP.Handshake.Local}
variable {before state : State active passive} {effect : Effect active passive}
variable {actual : Step active passive} {output : Emission} {receipt : Receipt} {index source : Nat}

private theorem pairwise_option (position : α → Nat) (ordered : values.Pairwise (fun a b => position a < position b))
    (fresh : ∀ old ∈ values, ∀ value, selected = some value → position old < position value) :
    (values ++ selected.toList).Pairwise (fun a b => position a < position b) := by
  cases selected with
  | none => simpa only [Option.toList_none, List.append_nil] using ordered
  | some value =>
    apply List.pairwise_append.mpr
    refine ⟨ordered, by simp, ?_⟩
    intro old member next selected
    have same : next = value := List.mem_singleton.mp selected
    subst next
    exact fresh old member value rfl

theorem Records.retain_source (records : Records before index effect) (found : before.source source = some output) :
    effect.state.source source = some output := by
  unfold State.source at found ⊢
  rw [records.emissions, List.find?_append, found]
  rfl

structure History (state : State active passive) : Prop where
  emissionOrder : state.emissions.Pairwise (fun first second => first.index < second.index)
  receiptOrder : state.receipts.Pairwise (fun first second => first.index < second.index)
  emissionPast : ∀ output ∈ state.emissions, ∃ index, state.last = some index ∧ output.index ≤ index
  receiptPast : ∀ receipt ∈ state.receipts, ∃ index, state.last = some index ∧ receipt.index ≤ index
  source : ∀ receipt ∈ state.receipts, state.source receipt.source.index = some receipt.source

theorem History.initial : History (State.initial (active := active) (passive := passive)) := by
  refine ⟨.nil, .nil, ?_, ?_, ?_⟩
  all_goals intro value member; cases member

theorem History.step (actual : Step active passive) (history : History actual.before) : History actual.result.state := by
  have records := actual.records
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [records.emissions]
    apply pairwise_option Emission.index history.emissionOrder
    intro old member output selected
    obtain ⟨prior, last, before⟩ := history.emissionPast old member
    have newer := actual.after_prior last
    rw [records.outputIndex output selected]
    omega
  · rw [records.receipts]
    apply pairwise_option Receipt.index history.receiptOrder
    intro old member receipt selected
    obtain ⟨prior, last, before⟩ := history.receiptPast old member
    have newer := actual.after_prior last
    rw [records.receiptIndex receipt selected]
    omega
  · intro output member
    refine ⟨actual.index, actual.last, ?_⟩
    rw [records.emissions] at member
    rcases List.mem_append.mp member with old | emitted
    · obtain ⟨prior, last, before⟩ := history.emissionPast output old
      have newer := actual.after_prior last
      omega
    · have present : actual.result.output = some output := by simpa only [Option.mem_toList] using emitted
      exact Nat.le_of_eq (records.outputIndex output present)
  · intro receipt member
    refine ⟨actual.index, actual.last, ?_⟩
    rw [records.receipts] at member
    rcases List.mem_append.mp member with old | received
    · obtain ⟨prior, last, before⟩ := history.receiptPast receipt old
      have newer := actual.after_prior last
      omega
    · have present : actual.result.receipt = some receipt := by simpa only [Option.mem_toList] using received
      exact Nat.le_of_eq (records.receiptIndex receipt present)
  · intro receipt member
    rw [records.receipts] at member
    apply records.retain_source
    rcases List.mem_append.mp member with old | received
    · exact history.source receipt old
    · have present : actual.result.receipt = some receipt := by simpa only [Option.mem_toList] using received
      exact records.source receipt present

theorem History.emission_indices (history : History state) :
    (state.emissions.map Emission.index).Pairwise (· < ·) := List.pairwise_map.mpr history.emissionOrder

theorem History.emission_indices_nodup (history : History state) : (state.emissions.map Emission.index).Nodup := by
  change List.Pairwise (fun a b : Nat => a ≠ b) _
  exact history.emission_indices.imp (fun {a b} before same => by
    subst b
    exact Nat.lt_irrefl _ before)

theorem History.receipt_indices (history : History state) :
    (state.receipts.map Receipt.index).Pairwise (· < ·) := List.pairwise_map.mpr history.receiptOrder

theorem History.source_member (history : History state) (receipt : Receipt) (member : receipt ∈ state.receipts) :
    receipt.source ∈ state.emissions := List.mem_of_find?_eq_some (history.source receipt member)

inductive Trace : State active passive → List Event → List (Step active passive) → State active passive → Prop where
  | done (state : State active passive) : Trace state [] [] state
  | next (actual : Step active passive) (tail : Trace actual.result.state events steps final) :
      Trace actual.before (actual.event :: events) (actual :: steps) final

variable {initial final : State active passive} {events : List Event} {steps : List (Step active passive)}

theorem Trace.covered (trace : Trace initial events steps final) : steps.map (·.event) = events := by
  induction trace with
  | done => rfl
  | next actual tail ih => simp only [List.map_cons, ih]

theorem Trace.history (trace : Trace initial events steps final) (history : History initial) : History final := by
  induction trace with
  | done => exact history
  | next actual tail ih => exact ih (History.step actual history)

theorem Trace.emissions (trace : Trace initial events steps final) :
    final.emissions = initial.emissions ++ steps.filterMap (·.result.output) := by
  induction trace with
  | done => simp
  | next actual tail ih =>
    rw [ih, actual.records.emissions]
    cases present : actual.result.output <;> simp [present, List.append_assoc]

theorem Trace.receipts (trace : Trace initial events steps final) :
    final.receipts = initial.receipts ++ steps.filterMap (·.result.receipt) := by
  induction trace with
  | done => simp
  | next actual tail ih =>
    rw [ih, actual.records.receipts]
    cases present : actual.result.receipt <;> simp [present, List.append_assoc]

theorem Trace.append (first : Trace initial events steps middle) (later : Trace middle more rest final) :
    Trace initial (events ++ more) (steps ++ rest) final := by
  induction first with
  | done => exact later
  | next actual tail ih => exact .next actual (ih later)

theorem Trace.snoc (trace : Trace initial events steps actual.before) :
    Trace initial (events ++ [actual.event]) (steps ++ [actual]) actual.result.state :=
  trace.append (.next actual (.done actual.result.state))

theorem Trace.cut (trace : Trace initial events steps final) (actual : Step active passive) (member : actual ∈ steps) :
    ∃ prior later, steps = prior ++ actual :: later ∧
      Trace initial (prior.map (·.event)) prior actual.before ∧
        Trace actual.result.state (later.map (·.event)) later final := by
  induction trace with
  | done => cases member
  | next head tail ih =>
    rcases List.mem_cons.mp member with same | retained
    · subst actual
      refine ⟨[], _, rfl, .done head.before, ?_⟩
      rw [tail.covered]
      exact tail
    · obtain ⟨prior, later, same, preceding, following⟩ := ih retained
      exact ⟨head :: prior, later, by rw [same]; rfl, .next head preceding, following⟩

theorem Trace.after_last (trace : Trace initial events steps final) (prior : initial.last = some index) :
    ∀ actual ∈ steps, index < actual.index := by
  induction trace generalizing index with
  | done => intro actual member; cases member
  | next head tail ih =>
    intro actual member
    rcases List.mem_cons.mp member with same | later
    · subst actual; exact head.after_prior prior
    · exact Nat.lt_trans (head.after_prior prior) (ih head.last actual later)

theorem Trace.index_order (trace : Trace initial events steps final) : steps.Pairwise (fun a b => a.index < b.index) := by
  induction trace with
  | done => exact .nil
  | next actual tail ih => exact .cons (tail.after_last actual.last) ih

structure Reachable (state : State active passive) where
  events : List Event
  steps : List (Step active passive)
  trace : Trace .initial events steps state

theorem Reachable.history (value : Reachable state) : History state := value.trace.history History.initial

theorem Trace.emission_origin (trace : Trace (State.initial (active := active) (passive := passive)) events steps final)
    (member : output ∈ final.emissions) :
    ∃ actual ∈ steps, actual.result.output = some output ∧ output.index = actual.index := by
  rw [trace.emissions] at member
  change output ∈ ([] ++ steps.filterMap (·.result.output)) at member
  obtain ⟨actual, retained, selected⟩ := List.mem_filterMap.mp member
  exact ⟨actual, retained, selected, actual.records.outputIndex output selected⟩

structure EmissionOrigin (steps : List (Step active passive)) (output : Emission) where
  prior : List (Step active passive)
  actual : Step active passive
  later : List (Step active passive)
  history : steps = prior ++ actual :: later
  recorded : actual.result.output = some output
  index : output.index = actual.index

theorem Trace.output_origin (trace : Trace (State.initial (active := active) (passive := passive)) events steps final)
    (member : output ∈ final.emissions) : Nonempty (EmissionOrigin steps output) := by
  obtain ⟨actual, retained, recorded, index⟩ := trace.emission_origin member
  obtain ⟨prior, later, history, _, _⟩ := trace.cut actual retained
  exact ⟨⟨prior, actual, later, history, recorded, index⟩⟩

theorem EmissionOrigin.fields (origin : EmissionOrigin steps output) :
    origin.actual.result.output.map Emission.actor = some output.actor ∧
      origin.actual.result.output.map Emission.kind = some output.kind ∧
      origin.actual.result.output.map Emission.cause = some output.cause := by
  rw [origin.recorded]
  exact ⟨rfl, rfl, rfl⟩

structure ReceiptOrigin (steps : List (Step active passive)) (receipt : Receipt) where
  prior : List (Step active passive)
  actual : Step active passive
  later : List (Step active passive)
  history : steps = prior ++ actual :: later
  recorded : actual.result.receipt = some receipt
  index : receipt.index = actual.index
  producer : Step active passive
  earlier : producer ∈ prior
  produced : producer.result.output = some receipt.source
  sourceIndex : receipt.source.index = producer.index

theorem Trace.receipt_origin (trace : Trace (State.initial (active := active) (passive := passive)) events steps final)
    (member : receipt ∈ final.receipts) : Nonempty (ReceiptOrigin steps receipt) := by
  rw [trace.receipts] at member
  change receipt ∈ ([] ++ steps.filterMap (·.result.receipt)) at member
  obtain ⟨actual, retained, selected⟩ := List.mem_filterMap.mp member
  obtain ⟨prior, later, history, preceding, following⟩ := trace.cut actual retained
  have sourceMember : receipt.source ∈ actual.before.emissions :=
    List.mem_of_find?_eq_some (actual.records.source receipt selected)
  obtain ⟨producer, earlier, produced, sourceIndex⟩ := preceding.emission_origin sourceMember
  exact ⟨⟨prior, actual, later, history, selected, actual.records.receiptIndex receipt selected,
    producer, earlier, produced, sourceIndex⟩⟩

theorem Reachable.receipt_origin (value : Reachable state) (member : receipt ∈ state.receipts) :
    Nonempty (ReceiptOrigin value.steps receipt) := value.trace.receipt_origin member

theorem ReceiptOrigin.source_earlier (origin : ReceiptOrigin steps receipt) : origin.producer.index < origin.actual.index := by
  rw [← origin.sourceIndex, ← origin.index]
  exact receipt.earlier

theorem application_origin (member : (actor, operation) ∈ steps.filterMap (·.result.application)) :
    ∃ actual ∈ steps, actual.result.application = some (actor, operation) ∧ operation.stamp = actual.index := by
  obtain ⟨actual, retained, recorded⟩ := List.mem_filterMap.mp member
  exact ⟨actual, retained, recorded, actual.records.applicationIndex actor operation recorded⟩

end Netlib.Check.TCPHandshakeRecovery
