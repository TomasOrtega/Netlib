import Netlib.Check.CampusTCPModel

/-!
# Actual recovery jobs at their current queue stages

Custody IDs, work IDs, output indices, and service indices stay separate.
Selecting by a stored key does not prefer a newly emitted retry.
-/

namespace Netlib.Check.CampusTCPStartupJobs

open CampusTCPModel

namespace C
export TCPHandshakeRecovery (Step Emission Side Kind)
end C

inductive Stage where
  | ingress | ticket | link
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

inductive Key where
  | ingress (custodyID : Nat)
  | ticket (workID : Nat)
  | link (custodyID : Nat)
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

structure Source (input : Input) where
  actual : C.Step input.active input.passive
  occurrence : C.Emission
  emitted : actual.result.output = some occurrence

def Source.produced (source : Source input) : Produced input.active input.passive :=
  .recovery source.actual source.occurrence source.emitted

abbrev PacketItem (input : Input) := Theory.PacketCustody.Item (Transit input)
abbrev TicketItem (input : Input) := Work.Item (Ticket input.active input.passive)

inductive Job (input : Input) where
  | ingress (item : PacketItem input) (outputIndex : Nat) (source : Source input)
      (payload : item.value.payload = .ingress outputIndex source.produced)
  | ticket (item : TicketItem input) (source : Source input)
      (production : item.value.produced = source.produced)
  | link (item : PacketItem input) (serviceIndex : Nat) (served : Served input)
      (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
      (source : Source input) (production : served.ticket.value.produced = source.produced)
      (payload : item.value.payload = .link serviceIndex served emission emitted)

def Job.key : Job input → Key
  | .ingress item .. => .ingress item.id
  | .ticket item .. => .ticket item.id
  | .link item .. => .link item.id

def Job.stage : Job input → Stage
  | .ingress .. => .ingress
  | .ticket .. => .ticket
  | .link .. => .link

def Job.source : Job input → Source input
  | .ingress _ _ source _ | .ticket _ source _ | .link _ _ _ _ _ source _ _ => source

def Job.actor (job : Job input) : Actor := Actor.ofRecovery job.source.occurrence.actor

def Job.kind (job : Job input) : C.Kind := job.source.occurrence.kind

def Job.stamp (job : Job input) : Nat := job.source.occurrence.index

def Job.outputIndex : Job input → Nat
  | .ingress _ index .. => index
  | .ticket item .. => item.value.outputIndex
  | .link _ _ served .. => served.ticket.value.outputIndex

def Job.serviceIndex : Job input → Option Nat
  | .link _ index .. => some index
  | _ => none

def Job.packet : Job input → Option (PacketItem input)
  | .ingress item .. | .link item .. => some item
  | .ticket .. => none

def Job.work : Job input → Option (TicketItem input)
  | .ticket item .. => some item
  | _ => none

def Job.Pending (state : State input) : Job input → Prop
  | .ingress item .. | .link item .. => item ∈ state.custody.pending
  | .ticket item .. => item ∈ state.work.pending

def packetJob (item : PacketItem input) : Option (Job input) :=
  match payload : item.value.payload with
  | .ingress index produced =>
    match production : produced with
    | .recovery actual occurrence emitted =>
      some (.ingress item index ⟨actual, occurrence, emitted⟩ (by simpa only [production, Source.produced] using payload))
    | _ => none
  | .link index served emission emitted =>
    match production : served.ticket.value.produced with
    | .recovery actual occurrence present =>
      some (.link item index served emission emitted ⟨actual, occurrence, present⟩ production payload)
    | _ => none

def ticketJob (item : TicketItem input) : Option (Job input) :=
  match production : item.value.produced with
  | .recovery actual occurrence emitted => some (.ticket item ⟨actual, occurrence, emitted⟩ production)
  | _ => none

def inventory (state : State input) : List (Job input) :=
  state.custody.pending.filterMap packetJob ++ state.work.pending.filterMap ticketJob

def selected (state : State input) (key : Key) : Option (Job input) :=
  (inventory state).find? (fun job => job.key == key)

def stageWeight (kind : C.Kind) (stage : Stage) : Nat :=
  match kind, stage with
  | .syn, .ingress | .synAck, .ingress => 6
  | .syn, .ticket | .synAck, .ticket => 5
  | .syn, .link | .synAck, .link => 4
  | .finalAck, .ingress | .synReplyAck, .ingress => 3
  | .finalAck, .ticket | .synReplyAck, .ticket => 2
  | .finalAck, .link | .synReplyAck, .link => 1

def Job.weight (job : Job input) : Nat := stageWeight job.kind job.stage

def potential (state : State input) : Nat := ((inventory state).map Job.weight).sum

variable {input : Input} {state : State input} {job : Job input} {key : Key}

theorem Job.weight_positive (job : Job input) : 0 < job.weight := by
  unfold Job.weight
  cases job.kind <;> cases job.stage <;> decide

theorem packetJob_exists (item : PacketItem input) :
    (∃ job, packetJob item = some job) ↔ item.value.payload.isRecovery = true := by
  rcases item with ⟨id, payload, parent⟩
  cases payload with
  | ingress index produced => cases produced <;> simp [packetJob, Transit.isRecovery, Produced.isRecovery]
  | link index served emission emitted =>
    rcases served with ⟨time, ⟨ticketID, ⟨outputIndex, produced, ingress, gateway, epoch⟩⟩,
      before, mode, evidence, computed, observed⟩
    cases produced <;> simp [packetJob, Transit.isRecovery, Produced.isRecovery]

theorem ticketJob_exists (item : TicketItem input) :
    (∃ job, ticketJob item = some job) ↔ item.value.produced.isRecovery = true := by
  rcases item with ⟨id, outputIndex, produced, ingress, gateway, epoch⟩
  cases produced <;> simp [ticketJob, Produced.isRecovery]

theorem inventory_member : job ∈ inventory state ↔
    (∃ item ∈ state.custody.pending, packetJob item = some job) ∨
      (∃ item ∈ state.work.pending, ticketJob item = some job) := by
  simp only [inventory, List.mem_append, List.mem_filterMap]

theorem packetJob_packet (item : PacketItem input) (found : packetJob item = some job) : job.packet = some item := by
  unfold packetJob at found
  split at found
  · split at found <;> cases found <;> rfl
  · split at found <;> cases found <;> rfl

theorem ticketJob_work (item : TicketItem input) (found : ticketJob item = some job) : job.work = some item := by
  unfold ticketJob at found
  split at found <;> cases found <;> rfl

theorem inventory_pending (member : job ∈ inventory state) : job.Pending state := by
  rcases inventory_member.mp member with ⟨item, present, found⟩ | ⟨item, present, found⟩
  · have same := packetJob_packet item found
    cases job <;> simp only [Job.packet, Option.some.injEq, reduceCtorEq] at same
    all_goals cases same; exact present
  · have same := ticketJob_work item found
    cases job <;> simp only [Job.work, Option.some.injEq, reduceCtorEq] at same
    cases same
    exact present

theorem selected_member (found : selected state key = some job) : job ∈ inventory state :=
  List.mem_of_find?_eq_some found

theorem selected_key (found : selected state key = some job) : job.key = key := by
  simpa only [beq_iff_eq] using List.find?_some found

theorem selected_pending (found : selected state key = some job) : job.Pending state :=
  inventory_pending (selected_member found)

theorem selected_exists : (∃ job, selected state key = some job) ↔ ∃ job ∈ inventory state, job.key = key := by
  constructor
  · rintro ⟨job, found⟩
    exact ⟨job, selected_member found, selected_key found⟩
  · rintro ⟨job, member, same⟩
    cases found : selected state key with
    | none =>
      have absent := List.find?_eq_none.mp found job member
      exact False.elim (absent (by simp only [same, beq_self_eq_true]))
    | some value => exact ⟨value, rfl⟩

theorem inventory_empty_iff : inventory state = [] ↔
    (state.custody.pending.any (fun item => item.value.payload.isRecovery) = false ∧
      state.work.pending.any (fun item => item.value.produced.isRecovery) = false) := by
  constructor
  · intro empty
    constructor
    · apply List.any_eq_false.mpr
      intro item member recovery
      obtain ⟨job, found⟩ := (packetJob_exists item).mpr recovery
      have inside : job ∈ inventory state := inventory_member.mpr (Or.inl ⟨item, member, found⟩)
      rw [empty] at inside
      cases inside
    · apply List.any_eq_false.mpr
      intro item member recovery
      obtain ⟨job, found⟩ := (ticketJob_exists item).mpr recovery
      have inside : job ∈ inventory state := inventory_member.mpr (Or.inr ⟨item, member, found⟩)
      rw [empty] at inside
      cases inside
  · rintro ⟨packets, tickets⟩
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro job member
    rcases inventory_member.mp member with ⟨item, present, found⟩ | ⟨item, present, found⟩
    · exact List.any_eq_false.mp packets item present ((packetJob_exists item).mp ⟨job, found⟩)
    · exact List.any_eq_false.mp tickets item present ((ticketJob_exists item).mp ⟨job, found⟩)

theorem queues_empty (empty : inventory state = [])
    (packets : ∀ item ∈ state.custody.pending, item.value.payload.isRecovery = true)
    (tickets : ∀ item ∈ state.work.pending, item.value.produced.isRecovery = true) :
    state.custody.pending = [] ∧ state.work.pending = [] := by
  obtain ⟨noPackets, noTickets⟩ := inventory_empty_iff.mp empty
  constructor
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro item member
    exact List.any_eq_false.mp noPackets item member (packets item member)
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro item member
    exact List.any_eq_false.mp noTickets item member (tickets item member)

theorem Job.weight_le_six (job : Job input) : job.weight ≤ 6 := by
  unfold Job.weight
  cases job.kind <;> cases job.stage <;> decide

theorem potential_zero_iff : potential state = 0 ↔ inventory state = [] := by
  unfold potential
  cases jobs : inventory state with
  | nil => simp only [List.map_nil, List.sum_nil]
  | cons head tail =>
    have positive := Job.weight_positive head
    constructor
    · intro zero
      simp only [List.map_cons, List.sum_cons] at zero
      omega
    · intro impossible
      cases impossible

theorem inventory_length_le_potential : (inventory state).length ≤ potential state := by
  unfold potential
  generalize inventory state = jobs
  induction jobs with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    have positive := Job.weight_positive head
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem potential_le_six_length : potential state ≤ 6 * (inventory state).length := by
  unfold potential
  generalize inventory state = jobs
  induction jobs with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    have bounded := Job.weight_le_six head
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem inventory_same {before after : State input}
    (packets : after.custody.pending = before.custody.pending) (tickets : after.work.pending = before.work.pending) :
    inventory after = inventory before := by rw [inventory, inventory, packets, tickets]

theorem selected_same {before after : State input}
    (packets : after.custody.pending = before.custody.pending) (tickets : after.work.pending = before.work.pending) :
    selected after key = selected before key := by rw [selected, selected, inventory_same packets tickets]

end Netlib.Check.CampusTCPStartupJobs
