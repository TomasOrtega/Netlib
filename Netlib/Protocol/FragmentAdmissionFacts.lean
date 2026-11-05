import Netlib.Protocol.FragmentAdmission

namespace Netlib.Protocol.FragmentAdmission

open Packet IPv4Reassembly

private theorem accept_piece_key (state : IPv4Reassembly.State) (queue : Queue) (input : Piece) (output : Output)
    (valid : queue.Valid) (same : key queue.key.domain input.fragment = queue.key)
    (emitted : (accept state queue input).output = some output) :
    ∀ piece ∈ output.pieces, key queue.key.domain piece.fragment = queue.key := by
  have completed := (accept_output state queue input output emitted).2.2
  have pieces := (Queue.complete_pieces _ _ completed).1
  intro piece member
  rw [pieces] at member
  rcases (store_piece_member queue input piece).mp member with rfl | previous
  · exact same
  · exact valid.fragmentKey piece previous

theorem process_piece_key (policy : Policy) (before : IPv4Reassembly.State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (output : Output) (valid : before.Valid)
    (emitted : (process policy before now domain fragment).output = some output) :
    ∀ piece ∈ output.pieces, key domain piece.fragment = key domain fragment := by
  let state : IPv4Reassembly.State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have stateValid : state.Valid := before.age_valid now valid
  have oldValid : old.Valid := by
    cases found : state.lookup wanted with
    | none => simpa only [old, found, Option.getD_none] using Queue.fresh_valid wanted (now + policy.timeout)
    | some queue => simpa only [old, found, Option.getD_some] using stateValid queue (state.lookup_member _ _ found)
  have oldKey : old.key = wanted := by
    cases found : state.lookup wanted with
    | none => simp [old, found]
    | some queue => simpa only [old, found, Option.getD_some] using state.lookup_key _ _ found
  change (if !fragment.packet.moreFragments && decide (fragment.packet.offset.val = 0) then
      (⟨state, .whole, some ⟨fragment.packet.toPacket, [⟨fragment, fragment.packet.payload⟩], 0, 0, false⟩⟩ : IPv4Reassembly.Result)
    else match queuedLength old (normalize fragment) with
      | none => ⟨state.erase wanted, .inconsistentLength, none⟩
      | some queue => accept state queue (normalize fragment)).output = some output at emitted
  split at emitted
  · cases Option.some.inj emitted
    intro piece member
    have selected : piece = ⟨fragment, fragment.packet.payload⟩ := List.mem_singleton.mp member
    cases selected
    rfl
  · split at emitted
    · cases emitted
    · rename_i queue updated
      have queueKey : queue.key = wanted := (queuedLength_fields _ _ _ updated).1.trans oldKey
      have queueValid := queuedLength_valid _ _ _ updated oldValid
      have current : key queue.key.domain (normalize fragment).fragment = queue.key := by rw [queueKey]; rfl
      have keys := accept_piece_key state queue (normalize fragment) output queueValid current emitted
      simpa only [queueKey, wanted, key] using keys

theorem Accepted.output_piece_key (accepted : Accepted pipeline policy before input current early fine)
    (output : Output) (emitted : accepted.result.output = some output) (piece : Piece) (member : piece ∈ output.pieces) :
    key input.domain piece.fragment = key input.domain input.fragment := by
  have processed := (arrive_processed _ _ _ _ _ _ accepted.arrived).1
  rw [processed] at emitted
  exact process_piece_key _ _ _ _ _ _ before.fragmentsValid emitted piece member

theorem Accepted.output_piece_envelope (accepted : Accepted pipeline policy before input current early fine)
    (output : Output) (emitted : accepted.result.output = some output) (piece : Piece) (member : piece ∈ output.pieces) :
    IPv4Envelope.ofFragment piece.fragment = IPv4Envelope.ofPacket output.packet := by
  have pieceKey := accepted.output_piece_key output emitted piece member
  have packetKey := (arrive_output_valid _ _ _ _ _ _ _ accepted.arrived emitted before.fragmentsValid).sameKey
  exact congrArg (fun selected : Key => (⟨selected.source, selected.destination, selected.protocol⟩ : IPv4Envelope))
    (pieceKey.trans packetKey.symm)

theorem Accepted.output_receipt_envelope (accepted : Accepted pipeline policy before input current early fine)
    (output : Output) (emitted : accepted.result.output = some output) (piece : Piece) (member : piece ∈ output.pieces) :
    ∃ receipt ∈ accepted.state.history, receipt.fragment = piece.fragment ∧
      receipt.input.envelope = IPv4Envelope.ofPacket output.packet ∧ receipt.guard.allows receipt.input = true := by
  obtain ⟨receipt, stored, same, allowed⟩ := accepted.output_early_admitted output emitted piece member
  refine ⟨receipt, stored, same, ?_, allowed⟩
  have selected := accepted.output_piece_envelope output emitted piece member
  change IPv4Envelope.ofFragment receipt.fragment = _
  rw [same]
  exact selected

theorem Accepted.output_bound_receipt (accepted : Accepted pipeline policy before input current early fine)
    (output : Output) (emitted : accepted.result.output = some output) (piece : Piece) (member : piece ∈ output.pieces) :
    ∃ receipt ∈ accepted.state.history, receipt.fragment = piece.fragment ∧ receipt.input.domain = input.domain ∧
      receipt.input.ingress.ns = before.ns ∧ receipt.input.now ≤ input.now ∧
      receipt.input.envelope = IPv4Envelope.ofPacket output.packet ∧ receipt.guard.allows receipt.input = true := by
  obtain ⟨receipt, stored, same, domainEq, earlier, allowed⟩ := accepted.output_domain_source output emitted piece member
  have namespaceEq : accepted.state.ns = before.ns := by
    change (accepted.completion.state _).ns = _
    rw [Completion.namespace_eq]
    rfl
  refine ⟨receipt, stored, same, domainEq, (accepted.state.namespaces receipt stored).trans namespaceEq, earlier, ?_, allowed⟩
  change IPv4Envelope.ofFragment receipt.fragment = _
  rw [same]
  exact accepted.output_piece_envelope output emitted piece member

theorem Residency.fresh_empty (before after : Residency) (ns : IngressAttachment.NamespaceRef)
    (created : before.fresh ns = .ok after) :
    ∃ state, after.active = some state ∧ state.fragments = IPv4Reassembly.State.initial ∧
      state.conntrack = ConntrackLifecycle.State.initial ∧ state.history = [] ∧ state.ns = ns := by
  have initialized := (Residency.fresh_state before after ns created).1
  exact ⟨State.initial ns, initialized, rfl, rfl, rfl, rfl⟩

end Netlib.Protocol.FragmentAdmission
