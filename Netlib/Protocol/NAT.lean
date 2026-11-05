import Netlib.Protocol.Conntrack

/-!
# Timed source NAPT

Mapping uses the internal endpoint and protocol, independently of the remote peer.
Filtering separately requires a live grant for the exact reversed five-tuple.
RFC 3022 describes NAPT. RFC 4787 separates mapping and filtering behavior.
The model excludes checksums, fragmentation, hairpinning, and transport handshakes.
-/

namespace Netlib.Protocol.NAT

open Packet

def mappingSource : String := "https://www.rfc-editor.org/rfc/rfc3022.html#section-2.2"
def behaviorSource : String := "https://www.rfc-editor.org/rfc/rfc4787.html#section-4.1"
def filteringSource : String := "https://www.rfc-editor.org/rfc/rfc4787.html#section-5"

structure Binding where
  inside : Endpoint
  outside : Endpoint
  protocol : Protocol
  expiresAt : Nat
  deriving Repr, DecidableEq

def Binding.internalKey (binding : Binding) : Endpoint × Protocol := (binding.inside, binding.protocol)
def Binding.publicKey (binding : Binding) : Endpoint × Protocol := (binding.outside, binding.protocol)

structure State where
  tracking : Conntrack.State := {}
  bindings : List Binding := []
  deriving Repr, DecidableEq

def State.initial : State := {}

structure State.Safe (state : State) : Prop where
  tracking : state.tracking.Safe
  live : ∀ binding ∈ state.bindings, state.tracking.now < binding.expiresAt
  internalUnique : (state.bindings.map Binding.internalKey).Nodup
  publicUnique : (state.bindings.map Binding.publicKey).Nodup

theorem initial_safe : State.initial.Safe := by
  constructor <;> simp [State.initial, Conntrack.State.Safe]

def mapping? (state : State) (packet : Header) : Option Binding :=
  state.bindings.find? (fun binding => decide (binding.internalKey = (packet.sourceEndpoint, packet.protocol)))

theorem mapping_independent_of_remote (state : State) (left right : Header)
    (source : left.sourceEndpoint = right.sourceEndpoint) (protocol : left.protocol = right.protocol) :
    mapping? state left = mapping? state right := by simp only [mapping?, source, protocol]

def collisionFree (state : State) (packet : Header) (allocation : Endpoint) : Bool :=
  state.bindings.all (fun binding => decide
    (binding.internalKey = (packet.sourceEndpoint, packet.protocol) ∨
      binding.publicKey ≠ (allocation, packet.protocol)))

def allocationAllowed (state : State) (packet : Header) (allocation : Endpoint) : Bool :=
  (match mapping? state packet with
    | none => true
    | some binding => decide (binding.outside = allocation)) && collisionFree state packet allocation

def newBinding (state : State) (packet : Header) (allocation : Endpoint) (expiresAt : Nat) : Binding :=
  ⟨packet.sourceEndpoint, allocation, packet.protocol,
    max (((mapping? state packet).map Binding.expiresAt).getD expiresAt) expiresAt⟩

def outboundState (state : State) (packet : Header) (allocation : Endpoint) (expiresAt : Nat) : State :=
  ⟨Conntrack.install state.tracking packet expiresAt,
    newBinding state packet allocation expiresAt ::
      state.bindings.filter (fun binding => decide
        (binding.internalKey ≠ (packet.sourceEndpoint, packet.protocol)))⟩

private theorem filtered_unique {bindings : List Binding} (key : Binding → α)
    (predicate : Binding → Bool) (unique : (bindings.map key).Nodup) :
    ((bindings.filter predicate).map key).Nodup :=
  unique.sublist (List.filter_sublist.map key)

theorem outboundState_safe (state : State) (packet : Header) (allocation : Endpoint) (expiresAt : Nat)
    (safe : state.Safe) (future : state.tracking.now < expiresAt)
    (free : collisionFree state packet allocation = true) :
    (outboundState state packet allocation expiresAt).Safe := by
  constructor
  · exact Conntrack.install_safe state.tracking packet expiresAt safe.tracking future
  · intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.lt_of_lt_of_le future (Nat.le_max_right _ _)
    · exact safe.live binding (List.mem_filter.mp member).1
  · apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨binding, belongs, same⟩ := List.mem_map.mp member
      have different := of_decide_eq_true (List.mem_filter.mp belongs).2
      exact different same
    · exact filtered_unique _ _ safe.internalUnique
  · apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨binding, belongs, same⟩ := List.mem_map.mp member
      have retained := List.mem_filter.mp belongs
      have different := of_decide_eq_true retained.2
      have condition := of_decide_eq_true (List.all_eq_true.mp free binding retained.1)
      rcases condition with sameInside | differentOutside
      · exact different sameInside
      · exact differentOutside same
    · exact filtered_unique _ _ safe.publicUnique

def inbound (state : State) (packet : Header) : Option Header :=
  match state.bindings.find? (fun binding => decide
      (binding.publicKey = (packet.destinationEndpoint, packet.protocol))) with
  | none => none
  | some binding =>
    let restored := (Rewrite.destinationEndpoint binding.inside).apply packet
    if state.tracking.now < binding.expiresAt && Conntrack.permitsReply state.tracking restored then
      some restored
    else none

theorem inbound_sound (state : State) (packet restored : Header) (accepted : inbound state packet = some restored) :
    ∃ binding ∈ state.bindings,
      binding.publicKey = (packet.destinationEndpoint, packet.protocol) ∧
      state.tracking.now < binding.expiresAt ∧
      restored = (Rewrite.destinationEndpoint binding.inside).apply packet ∧
      ∃ entry ∈ state.tracking.entries, state.tracking.now < entry.expiresAt ∧ entry.flow.reverse = restored := by
  unfold inbound at accepted
  cases found : state.bindings.find? (fun binding => decide
      (binding.publicKey = (packet.destinationEndpoint, packet.protocol))) with
  | none => simp [found] at accepted
  | some binding =>
    simp only [found] at accepted
    split at accepted
    next guard =>
      cases accepted
      have conditions := (Bool.and_eq_true _ _).mp guard
      refine ⟨binding, List.mem_of_find?_eq_some found, ?_, of_decide_eq_true conditions.1, rfl, ?_⟩
      · exact of_decide_eq_true (List.find?_some
          (p := fun entry : Binding => decide (entry.publicKey = (packet.destinationEndpoint, packet.protocol)))
          (a := binding) found)
      · exact (Conntrack.permitsReply_iff _ _).mp conditions.2
    next _ => cases accepted

def advance (state : State) (now : Nat) : State :=
  let tracking := Conntrack.advance state.tracking now
  ⟨tracking, state.bindings.filter (fun binding => decide (tracking.now < binding.expiresAt))⟩

theorem advance_safe (state : State) (now : Nat) (safe : state.Safe) : (advance state now).Safe := by
  constructor
  · exact Conntrack.advance_safe _ _
  · intro binding member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · exact filtered_unique _ _ safe.internalUnique
  · exact filtered_unique _ _ safe.publicUnique

def close (state : State) (packet : Header) : State :=
  { state with tracking := Conntrack.close state.tracking packet }

def flush (state : State) : State := ⟨Conntrack.flush state.tracking, []⟩

inductive Event where
  | outbound (packet : Header) (allocation : Endpoint) (authorized : Bool) (expiresAt : Nat)
  | inbound (packet : Header)
  | advance (now : Nat)
  | close (packet : Header)
  | flush
  deriving Repr, DecidableEq

structure Outcome where
  state : State
  output : Option Header
  deriving Repr, DecidableEq

def step (state : State) : Event → Outcome
  | .outbound packet allocation authorized expiresAt =>
    if Conntrack.canOpen state.tracking packet authorized expiresAt && allocationAllowed state packet allocation then
      ⟨outboundState state packet allocation expiresAt, some ((Rewrite.sourceEndpoint allocation).apply packet)⟩
    else ⟨state, none⟩
  | .inbound packet => ⟨state, inbound state packet⟩
  | .advance now => ⟨advance state now, none⟩
  | .close packet => ⟨close state packet, none⟩
  | .flush => ⟨flush state, none⟩

theorem step_safe (state : State) (event : Event) (safe : state.Safe) : (step state event).state.Safe := by
  cases event with
  | outbound packet allocation authorized expiresAt =>
    simp only [step]
    split
    next guard =>
      have guards := (Bool.and_eq_true _ _).mp guard
      have future := of_decide_eq_true ((Bool.and_eq_true _ _).mp guards.1).2
      exact outboundState_safe state packet allocation expiresAt safe future
        ((Bool.and_eq_true _ _).mp guards.2).2
    next _ => exact safe
  | inbound => exact safe
  | advance now => exact advance_safe state now safe
  | close packet =>
    exact ⟨Conntrack.close_safe _ _ safe.tracking, safe.live, safe.internalUnique, safe.publicUnique⟩
  | flush => exact ⟨by simp [Conntrack.State.Safe, step, flush, Conntrack.flush], by simp [step, flush],
      by simp [step, flush], by simp [step, flush]⟩

theorem clock_mono (state : State) (event : Event) :
    state.tracking.now ≤ (step state event).state.tracking.now := by
  cases event <;> simp [step, outboundState, Conntrack.install, advance, Conntrack.advance,
    close, Conntrack.close, flush, Conntrack.flush, Nat.le_max_left]
  split <;> exact Nat.le_refl _

theorem denied_unchanged (state : State) (packet : Header) (allocation : Endpoint) (expiresAt : Nat) :
    step state (.outbound packet allocation false expiresAt) = ⟨state, none⟩ := by
  simp [step, Conntrack.canOpen]

theorem inbound_unchanged (state : State) (packet : Header) :
    (step state (.inbound packet)).state = state := rfl

theorem allocation_denied (state : State) (packet : Header) (allocation : Endpoint)
    (authorized : Bool) (expiresAt : Nat) (denied : allocationAllowed state packet allocation = false) :
    step state (.outbound packet allocation authorized expiresAt) = ⟨state, none⟩ := by
  simp [step, denied]

theorem outbound_authorized (state : State) (packet output : Header) (allocation : Endpoint)
    (authorized : Bool) (expiresAt : Nat)
    (accepted : (step state (.outbound packet allocation authorized expiresAt)).output = some output) :
    authorized = true ∧ Conntrack.transport packet = true ∧ state.tracking.now < expiresAt ∧
      allocationAllowed state packet allocation = true := by
  simp only [step] at accepted
  split at accepted
  next guard =>
    have guards := (Bool.and_eq_true _ _).mp guard
    have authorizedGuard := (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp guards.1).1
    exact ⟨authorizedGuard.1, authorizedGuard.2,
      of_decide_eq_true ((Bool.and_eq_true _ _).mp guards.1).2, guards.2⟩
  next _ => cases accepted

theorem installed_roundtrip (state : State) (packet : Header) (allocation : Endpoint) (expiresAt : Nat)
    (future : state.tracking.now < expiresAt) :
    inbound (outboundState state packet allocation expiresAt)
      ((Rewrite.sourceEndpoint allocation).apply packet).reverse = some packet.reverse := by
  have lifetime : state.tracking.now < (newBinding state packet allocation expiresAt).expiresAt :=
    Nat.lt_of_lt_of_le future (Nat.le_max_right _ _)
  have restored := Rewrite.source_reply_roundtrip packet.sourceEndpoint allocation packet rfl
  simp only [inbound, outboundState, List.find?_cons]
  have key : (newBinding state packet allocation expiresAt).publicKey =
      (((Rewrite.sourceEndpoint allocation).apply packet).reverse.destinationEndpoint,
        ((Rewrite.sourceEndpoint allocation).apply packet).reverse.protocol) := rfl
  simp only [key, decide_true]
  change (if state.tracking.now < (newBinding state packet allocation expiresAt).expiresAt &&
    Conntrack.permitsReply (Conntrack.install state.tracking packet expiresAt)
      ((Rewrite.destinationEndpoint packet.sourceEndpoint).apply
        ((Rewrite.sourceEndpoint allocation).apply packet).reverse) then _ else _) = _
  rw [restored]
  simp [lifetime, Conntrack.installed_reply _ _ _ future]
  exact restored

theorem accepted_roundtrip (state : State) (packet output : Header) (allocation : Endpoint)
    (authorized : Bool) (expiresAt : Nat)
    (accepted : (step state (.outbound packet allocation authorized expiresAt)).output = some output) :
    (step (step state (.outbound packet allocation authorized expiresAt)).state (.inbound output.reverse)).output =
      some packet.reverse := by
  simp only [step] at accepted ⊢
  split at accepted
  next guard =>
    simp only [guard, ite_true]
    cases accepted
    exact installed_roundtrip state packet allocation expiresAt
      (of_decide_eq_true ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp guard).1).2)
  next _ => cases accepted

def run (state : State) (events : List Event) : State :=
  events.foldl (fun current event => (step current event).state) state

theorem step_entry_origin (state : State) (event : Event) (entry : Conntrack.Entry)
    (member : entry ∈ (step state event).state.tracking.entries) :
    entry ∈ state.tracking.entries ∨
      ∃ allocation expiresAt, event = .outbound entry.flow allocation true expiresAt := by
  cases event with
  | outbound packet allocation authorized expiresAt =>
    simp only [step] at member
    split at member
    next accepted =>
      have authorizedTrue : authorized = true :=
        ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp accepted).1).1).1
      rcases List.mem_cons.mp member with rfl | member
      · exact .inr ⟨allocation, expiresAt, by subst authorized; rfl⟩
      · exact .inl (List.mem_filter.mp member).1
    next _ => exact .inl member
  | inbound => exact .inl member
  | advance => exact .inl (List.mem_filter.mp member).1
  | close => exact .inl (List.mem_filter.mp member).1
  | flush => cases member

theorem run_entry_origin (state : State) (events : List Event) (entry : Conntrack.Entry)
    (member : entry ∈ (run state events).tracking.entries) :
    entry ∈ state.tracking.entries ∨
      ∃ allocation expiresAt, .outbound entry.flow allocation true expiresAt ∈ events := by
  induction events generalizing state with
  | nil => exact .inl member
  | cons event events ih =>
    rcases ih (step state event).state member with earlier | authorized
    · rcases step_entry_origin state event entry earlier with original | ⟨allocation, expiresAt, same⟩
      · exact .inl original
      · exact .inr ⟨allocation, expiresAt, by simp [same]⟩
    · obtain ⟨allocation, expiresAt, belongs⟩ := authorized
      exact .inr ⟨allocation, expiresAt, by simp [belongs]⟩

/-- Every retained grant from the initial state has an authorized outbound source event. -/
theorem authorized_origin (events : List Event) (entry : Conntrack.Entry)
    (member : entry ∈ (run State.initial events).tracking.entries) :
    ∃ allocation expiresAt, .outbound entry.flow allocation true expiresAt ∈ events := by
  rcases run_entry_origin State.initial events entry member with initial | authorized
  · cases initial
  · exact authorized

theorem trace_reply_origin (events : List Event) (packet restored : Header)
    (accepted : inbound (run State.initial events) packet = some restored) :
    ∃ flow allocation expiresAt, .outbound flow allocation true expiresAt ∈ events ∧ flow.reverse = restored := by
  obtain ⟨_, _, _, _, _, entry, member, _, reverse⟩ :=
    inbound_sound (run State.initial events) packet restored accepted
  obtain ⟨allocation, expiresAt, origin⟩ := authorized_origin events entry member
  exact ⟨entry.flow, allocation, expiresAt, origin, reverse⟩

theorem run_safe (state : State) (events : List Event) (safe : state.Safe) : (run state events).Safe := by
  induction events generalizing state with
  | nil => exact safe
  | cons event events ih => exact ih _ (step_safe state event safe)

def transition : Transition State Event := Transition.ofFunction (fun state event => (step state event).state)

theorem transition_safe : transition.Invariant State.Safe := by
  intro before event after safe changed
  change (step before event).state = after at changed
  subst after
  exact step_safe before event safe

end Netlib.Protocol.NAT
