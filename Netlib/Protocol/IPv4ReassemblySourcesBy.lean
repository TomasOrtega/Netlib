import Netlib.Protocol.IPv4ReassemblyFacts

/-! Fragment provenance retains the actual defragmentation user and L3-master domain. -/

namespace Netlib.Protocol.IPv4Reassembly

open Packet

def Queue.SourcesBy (queue : Queue) (source : Domain → IPv4Fragment.Decoded → Prop) : Prop :=
  ∀ piece ∈ queue.pieces, source queue.key.domain piece.fragment

def State.SourcesBy (state : State) (source : Domain → IPv4Fragment.Decoded → Prop) : Prop :=
  ∀ queue ∈ state.queues, queue.SourcesBy source

theorem State.initial_sourcesBy (source : Domain → IPv4Fragment.Decoded → Prop) :
    State.initial.SourcesBy source := by simp [State.SourcesBy, State.initial]

theorem Queue.sourcesBy_mono (queue : Queue) (source target : Domain → IPv4Fragment.Decoded → Prop)
    (sources : queue.SourcesBy source) (included : ∀ domain fragment, source domain fragment → target domain fragment) :
    queue.SourcesBy target := by
  intro piece member
  exact included _ _ (sources piece member)

theorem State.sourcesBy_mono (state : State) (source target : Domain → IPv4Fragment.Decoded → Prop)
    (sources : state.SourcesBy source) (included : ∀ domain fragment, source domain fragment → target domain fragment) :
    state.SourcesBy target := by
  intro queue member
  exact queue.sourcesBy_mono source target (sources queue member) included

theorem State.age_sourcesBy (state : State) (now : Nat) (source : Domain → IPv4Fragment.Decoded → Prop)
    (sources : state.SourcesBy source) : (state.age now).SourcesBy source := by
  intro queue member
  exact sources queue ((State.age_member _ _ _).mp member).1

theorem State.erase_sourcesBy (state : State) (wanted : Key) (source : Domain → IPv4Fragment.Decoded → Prop)
    (sources : state.SourcesBy source) : (state.erase wanted).SourcesBy source := by
  intro queue member
  exact sources queue ((State.erase_member _ _ _).mp member).1

theorem State.put_sourcesBy (state : State) (queue : Queue) (source : Domain → IPv4Fragment.Decoded → Prop)
    (sources : state.SourcesBy source) (inserted : queue.SourcesBy source) : (state.put queue).SourcesBy source := by
  intro value member
  rcases (State.put_member _ _ _).mp member with rfl | previous
  · exact inserted
  · exact sources value previous.1

theorem store_sourcesBy (queue : Queue) (piece : Piece) (source : Domain → IPv4Fragment.Decoded → Prop)
    (sources : queue.SourcesBy source) (current : source queue.key.domain piece.fragment) :
    (store queue piece).SourcesBy source := by
  intro value member
  change source queue.key.domain value.fragment
  rcases (store_piece_member _ _ _).mp member with rfl | previous
  · exact current
  · exact sources value previous

theorem queuedLength_sourcesBy (queue next : Queue) (piece : Piece)
    (source : Domain → IPv4Fragment.Decoded → Prop) (updated : queuedLength queue piece = some next)
    (sources : queue.SourcesBy source) : next.SourcesBy source := by
  intro value member
  have fields := queuedLength_fields _ _ _ updated
  change source next.key.domain value.fragment
  rw [fields.1]
  apply sources value
  change value ∈ next.runs.flatMap Run.pieces at member
  rw [fields.2.2.1] at member
  exact member

theorem accept_sourcesBy (state : State) (queue : Queue) (piece : Piece)
    (source : Domain → IPv4Fragment.Decoded → Prop) (sources : state.SourcesBy source)
    (previous : queue.SourcesBy source) (current : source queue.key.domain piece.fragment) :
    (accept state queue piece).state.SourcesBy source := by
  unfold accept
  split
  · exact state.erase_sourcesBy _ _ sources
  · split
    · exact state.put_sourcesBy _ _ sources previous
    · split
      · exact state.erase_sourcesBy _ _ sources
      · have stored := store_sourcesBy queue piece source previous current
        dsimp only
        cases done : (store queue piece).complete with
        | waiting => exact state.put_sourcesBy _ _ sources stored
        | rejected reason => exact state.erase_sourcesBy _ _ sources
        | accepted output => exact state.erase_sourcesBy _ _ sources

theorem process_sourcesBy (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (source : Domain → IPv4Fragment.Decoded → Prop)
    (sources : before.SourcesBy source) (current : source domain fragment) :
    (process policy before now domain fragment).state.SourcesBy source := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have stateSources : state.SourcesBy source := before.age_sourcesBy now source sources
  have oldSources : old.SourcesBy source := by
    cases found : state.lookup wanted with
    | none => simp [old, found, Queue.SourcesBy, Queue.pieces]
    | some queue => simpa only [old, found, Option.getD_some] using stateSources queue (state.lookup_member _ _ found)
  have oldKey : old.key = wanted := by
    cases found : state.lookup wanted with
    | none => simp [old, found]
    | some queue => simpa only [old, found, Option.getD_some] using state.lookup_key _ _ found
  unfold process
  split
  · exact stateSources
  · dsimp only
    split
    · exact state.erase_sourcesBy _ _ stateSources
    · rename_i queue updated
      have queueSources := queuedLength_sourcesBy _ _ _ source updated oldSources
      have queueKey : queue.key = wanted := (queuedLength_fields _ _ _ updated).1.trans oldKey
      have queueCurrent : source queue.key.domain (normalize fragment).fragment := by
        simpa only [queueKey, wanted, key, normalize] using current
      exact accept_sourcesBy _ _ _ _ stateSources queueSources queueCurrent

theorem arrive_sourcesBy (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result) (source : Domain → IPv4Fragment.Decoded → Prop)
    (accepted : arrive policy before now domain fragment = .ok result)
    (sources : before.SourcesBy source) (current : source domain fragment) : result.state.SourcesBy source := by
  obtain ⟨processed, _, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed]
  exact process_sourcesBy _ _ _ _ _ _ sources current

theorem accept_output_sourcesBy (state : State) (queue : Queue) (piece : Piece) (output : Output)
    (source : Domain → IPv4Fragment.Decoded → Prop) (previous : queue.SourcesBy source)
    (current : source queue.key.domain piece.fragment) (emitted : (accept state queue piece).output = some output) :
    ∀ value ∈ output.pieces, source queue.key.domain value.fragment := by
  intro value member
  rcases accept_output_piece _ _ _ _ _ emitted member with rfl | old
  · exact current
  · exact previous value old

theorem process_output_sourcesBy (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (output : Output) (source : Domain → IPv4Fragment.Decoded → Prop)
    (sources : before.SourcesBy source) (current : source domain fragment)
    (emitted : (process policy before now domain fragment).output = some output) :
    ∀ piece ∈ output.pieces, source domain piece.fragment := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have stateSources : state.SourcesBy source := before.age_sourcesBy now source sources
  have oldSources : old.SourcesBy source := by
    cases found : state.lookup wanted with
    | none => simp [old, found, Queue.SourcesBy, Queue.pieces]
    | some queue => simpa only [old, found, Option.getD_some] using stateSources queue (state.lookup_member _ _ found)
  have oldKey : old.key = wanted := by
    cases found : state.lookup wanted with
    | none => simp [old, found]
    | some queue => simpa only [old, found, Option.getD_some] using state.lookup_key _ _ found
  unfold process at emitted
  split at emitted
  · cases Option.some.inj emitted
    intro piece member
    have same : piece = ⟨fragment, fragment.packet.payload⟩ := List.mem_singleton.mp member
    cases same
    exact current
  · dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i queue updated
      have queueSources := queuedLength_sourcesBy _ _ _ source updated oldSources
      have queueKey : queue.key = wanted := (queuedLength_fields _ _ _ updated).1.trans oldKey
      have queueCurrent : source queue.key.domain (normalize fragment).fragment := by
        simpa only [queueKey, wanted, key, normalize] using current
      have outputSources := accept_output_sourcesBy _ _ _ _ source queueSources queueCurrent emitted
      simpa only [queueKey, wanted, key] using outputSources

theorem arrive_output_sourcesBy (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result) (output : Output)
    (source : Domain → IPv4Fragment.Decoded → Prop)
    (accepted : arrive policy before now domain fragment = .ok result) (emitted : result.output = some output)
    (sources : before.SourcesBy source) (current : source domain fragment) :
    ∀ piece ∈ output.pieces, source domain piece.fragment := by
  obtain ⟨processed, _, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed] at emitted
  exact process_output_sourcesBy _ _ _ _ _ _ _ sources current emitted

end Netlib.Protocol.IPv4Reassembly
