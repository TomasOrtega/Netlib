import Netlib.Packet.Rewrite

/-!
# Bidirectional flow-tuple projection

The original and reply tuples describe a complete connection boundary.
Both direction keys include their effective zone in one implicit namespace.
Remaining timeout seconds are evidence, including zero. This model does not evolve time.
Tuple pairs alone do not establish native NAT status, firewall permission, or kernel rewriting.
-/

namespace Netlib.Protocol.FlowNAT

open Packet

inductive Direction where
  | original
  | reply
  deriving Repr, BEq, DecidableEq

structure Entry where
  original : Header
  reply : Header
  originalZone : Nat
  replyZone : Nat
  remainingTTL : Nat
  deriving Repr, BEq, DecidableEq

namespace Entry

def zone (entry : Entry) : Direction → Nat
  | .original => entry.originalZone
  | .reply => entry.replyZone

def input (entry : Entry) : Direction → Header
  | .original => entry.original
  | .reply => entry.reply

def output (entry : Entry) : Direction → Header
  | .original => entry.reply.reverse
  | .reply => entry.original.reverse

def key (entry : Entry) (direction : Direction) : Nat × Header :=
  (entry.zone direction, entry.input direction)

def WellFormed (entry : Entry) : Prop :=
  entry.original.protocol = entry.reply.protocol ∧
  (entry.original.protocol = Protocol.tcp ∨ entry.original.protocol = Protocol.udp) ∧
  entry.originalZone < 65536 ∧ entry.replyZone < 65536 ∧ entry.remainingTTL < 4294967296 ∧
  entry.key .original ≠ entry.key .reply

instance (entry : Entry) : Decidable entry.WellFormed := by
  unfold WellFormed
  infer_instance

def check (entry : Entry) : Bool := decide entry.WellFormed

@[simp] theorem check_correct (entry : Entry) : entry.check = true ↔ entry.WellFormed := by
  simp [check]

/-- Only endpoint fields change; the protocol remains unchanged. -/
def rewrite (entry : Entry) (direction : Direction) : Rewrite :=
  let target := entry.output direction
  { source := some target.source, destination := some target.destination,
    sourcePort := some target.sourcePort, destinationPort := some target.destinationPort }

theorem output_protocol (entry : Entry) (wellFormed : entry.WellFormed) (direction : Direction) :
    (entry.output direction).protocol = (entry.input direction).protocol := by
  cases direction
  · exact wellFormed.1.symm
  · exact wellFormed.1

theorem rewrite_correct (entry : Entry) (wellFormed : entry.WellFormed) (direction : Direction) :
    (entry.rewrite direction).apply (entry.input direction) = entry.output direction := by
  have same := entry.output_protocol wellFormed direction
  cases before : entry.input direction
  cases after : entry.output direction
  simp only [before, after] at same
  simp [rewrite, Rewrite.apply, after, same]

theorem original_output_reverse (entry : Entry) :
    (entry.output .original).reverse = entry.input .reply := Header.reverse_reverse _

theorem reply_output_reverse (entry : Entry) :
    (entry.output .reply).reverse = entry.input .original := Header.reverse_reverse _

def sourceOnly (entry : Entry) : Prop := entry.reply.reverse.destinationEndpoint = entry.original.destinationEndpoint
def destinationOnly (entry : Entry) : Prop := entry.reply.reverse.sourceEndpoint = entry.original.sourceEndpoint

theorem sourceOnly_original (entry : Entry) (sourceOnly : entry.sourceOnly) :
    (entry.output .original).destinationEndpoint = entry.original.destinationEndpoint := sourceOnly

theorem sourceOnly_reply (entry : Entry) (sourceOnly : entry.sourceOnly) :
    (entry.output .reply).sourceEndpoint = entry.reply.sourceEndpoint := sourceOnly.symm

theorem destinationOnly_original (entry : Entry) (destinationOnly : entry.destinationOnly) :
    (entry.output .original).sourceEndpoint = entry.original.sourceEndpoint := destinationOnly

theorem destinationOnly_reply (entry : Entry) (destinationOnly : entry.destinationOnly) :
    (entry.output .reply).destinationEndpoint = entry.reply.destinationEndpoint := destinationOnly.symm

end Entry

structure Hit where
  entry : Entry
  direction : Direction
  deriving Repr, BEq, DecidableEq

def Hit.key (hit : Hit) : Nat × Header := hit.entry.key hit.direction
def Hit.output (hit : Hit) : Header := hit.entry.output hit.direction

structure Snapshot where
  entries : List Entry
  deriving Repr, BEq, DecidableEq

namespace Snapshot

def slots (snapshot : Snapshot) : List Hit :=
  snapshot.entries.flatMap fun entry => [⟨entry, .original⟩, ⟨entry, .reply⟩]

def keys (snapshot : Snapshot) : List (Nat × Header) := snapshot.slots.map Hit.key

/-- This describes supported visible rows, not every transient native conntrack object. -/
def Valid (snapshot : Snapshot) : Prop :=
  (∀ entry ∈ snapshot.entries, entry.WellFormed) ∧ snapshot.keys.Nodup

def check (snapshot : Snapshot) : Bool :=
  snapshot.entries.all Entry.check && decide snapshot.keys.Nodup

theorem check_correct (snapshot : Snapshot) : snapshot.check = true ↔ snapshot.Valid := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, Entry.check_correct, decide_eq_true_eq, Valid]

def validate (snapshot : Snapshot) : Except String Unit :=
  if snapshot.check then .ok ()
  else .error "Unsupported flow tuple, zone, timeout range, or ambiguous bidirectional lookup key."

theorem validate_ok_iff (snapshot : Snapshot) : snapshot.validate = .ok () ↔ snapshot.Valid := by
  rw [← check_correct]
  cases accepted : snapshot.check <;> simp [validate, accepted]

theorem mem_slots (snapshot : Snapshot) (hit : Hit) : hit ∈ snapshot.slots ↔ hit.entry ∈ snapshot.entries := by
  rcases hit with ⟨entry, direction⟩
  cases direction <;> simp [slots, List.mem_flatMap]

/-- A miss means that the frozen table has no association; it is not a firewall denial. -/
def lookup (snapshot : Snapshot) (zone : Nat) (packet : Header) : Option Hit :=
  snapshot.slots.find? (fun hit => decide (hit.key = (zone, packet)))

def translate (snapshot : Snapshot) (zone : Nat) (packet : Header) : Option Header :=
  (snapshot.lookup zone packet).map Hit.output

theorem lookup_sound (snapshot : Snapshot) (zone : Nat) (packet : Header) (hit : Hit)
    (found : snapshot.lookup zone packet = some hit) :
    hit.entry ∈ snapshot.entries ∧ hit.key = (zone, packet) := by
  refine ⟨(mem_slots _ _).mp (List.mem_of_find?_eq_some found), ?_⟩
  exact of_decide_eq_true (List.find?_some
    (p := fun candidate : Hit => decide (candidate.key = (zone, packet))) (a := hit) found)

private theorem key_injective {hits : List Hit} (unique : (hits.map Hit.key).Nodup)
    {left right : Hit} (leftMember : left ∈ hits) (rightMember : right ∈ hits)
    (same : left.key = right.key) : left = right := by
  induction hits generalizing left right with
  | nil => simp at leftMember
  | cons head tail ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · rfl
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨right, rightTail, same.symm⟩))
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨left, leftTail, same⟩))
      · exact ih distinct.2 leftTail rightTail same

theorem lookup_unique (snapshot : Snapshot) (valid : snapshot.Valid) (left right : Hit)
    (leftMember : left.entry ∈ snapshot.entries) (rightMember : right.entry ∈ snapshot.entries)
    (same : left.key = right.key) : left = right :=
  key_injective valid.2 ((mem_slots _ _).mpr leftMember) ((mem_slots _ _).mpr rightMember) same

theorem lookup_complete (snapshot : Snapshot) (valid : snapshot.Valid) (hit : Hit)
    (member : hit.entry ∈ snapshot.entries) : snapshot.lookup hit.key.1 hit.key.2 = some hit := by
  cases found : snapshot.lookup hit.key.1 hit.key.2 with
  | none =>
    have absent := List.find?_eq_none.mp found
    exact False.elim (absent hit ((mem_slots _ _).mpr member) (by simp))
  | some other =>
    obtain ⟨otherMember, same⟩ := lookup_sound _ _ _ _ found
    have equal := lookup_unique snapshot valid other hit otherMember member same
    subst other
    rfl

theorem translate_entry (snapshot : Snapshot) (valid : snapshot.Valid) (entry : Entry)
    (member : entry ∈ snapshot.entries) (direction : Direction) :
    snapshot.translate (entry.zone direction) (entry.input direction) = some (entry.output direction) := by
  have found := lookup_complete snapshot valid ⟨entry, direction⟩ member
  simpa only [translate, Hit.key, Hit.output, Entry.key, Option.map_some] using congrArg (Option.map Hit.output) found

theorem translate_sound (snapshot : Snapshot) (zone : Nat) (packet output : Header)
    (accepted : snapshot.translate zone packet = some output) :
    ∃ hit : Hit, hit.entry ∈ snapshot.entries ∧ hit.key = (zone, packet) ∧ output = hit.output := by
  unfold translate at accepted
  cases found : snapshot.lookup zone packet with
  | none => simp [found] at accepted
  | some hit =>
    simp only [found, Option.map_some, Option.some.injEq] at accepted
    obtain ⟨member, key⟩ := lookup_sound snapshot zone packet hit found
    exact ⟨hit, member, key, accepted.symm⟩

theorem rewrite_agreement (snapshot : Snapshot) (valid : snapshot.Valid) (zone : Nat)
    (packet : Header) (hit : Hit) (found : snapshot.lookup zone packet = some hit) :
    (hit.entry.rewrite hit.direction).apply packet = hit.output := by
  obtain ⟨member, key⟩ := lookup_sound snapshot zone packet hit found
  have input : hit.entry.input hit.direction = packet := congrArg Prod.snd key
  rw [← input]
  exact hit.entry.rewrite_correct (valid.1 _ member) hit.direction

theorem roundtrip (snapshot : Snapshot) (valid : snapshot.Valid) (entry : Entry)
    (member : entry ∈ snapshot.entries) :
    (snapshot.translate entry.originalZone entry.original).bind
      (fun wire => snapshot.translate entry.replyZone wire.reverse) = some entry.original.reverse := by
  have first := translate_entry snapshot valid entry member .original
  simp only [Entry.zone, Entry.input, Entry.output] at first
  rw [first]
  simp only [Option.bind_some, Header.reverse_reverse]
  exact translate_entry snapshot valid entry member .reply

theorem reverse_roundtrip (snapshot : Snapshot) (valid : snapshot.Valid) (entry : Entry)
    (member : entry ∈ snapshot.entries) :
    (snapshot.translate entry.replyZone entry.reply).bind
      (fun restored => snapshot.translate entry.originalZone restored.reverse) = some entry.reply.reverse := by
  have first := translate_entry snapshot valid entry member .reply
  simp only [Entry.zone, Entry.input, Entry.output] at first
  rw [first]
  simp only [Option.bind_some, Header.reverse_reverse]
  exact translate_entry snapshot valid entry member .original

end Snapshot
end Netlib.Protocol.FlowNAT
