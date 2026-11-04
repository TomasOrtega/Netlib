import Netlib.Packet.Rewrite
import Netlib.Protocol.Transition

/-!
# Timed flow authorization

A grant authorizes one outbound five-tuple and its exact reverse reply.
The model excludes transport handshakes and packet flags.
-/

namespace Netlib.Protocol.Conntrack

open Packet

structure Entry where
  flow : Header
  expiresAt : Nat
  deriving Repr, DecidableEq

structure State where
  now : Nat := 0
  entries : List Entry := []
  deriving Repr, DecidableEq

def State.Safe (state : State) : Prop := ∀ entry ∈ state.entries, state.now < entry.expiresAt

def transport (packet : Header) : Bool :=
  decide (packet.protocol = Protocol.tcp ∨ packet.protocol = Protocol.udp)

def canOpen (state : State) (packet : Header) (authorized : Bool) (expiresAt : Nat) : Bool :=
  authorized && transport packet && decide (state.now < expiresAt)

def permitsReply (state : State) (packet : Header) : Bool :=
  state.entries.any (fun entry => decide (state.now < entry.expiresAt) && decide (entry.flow.reverse = packet))

theorem permitsReply_iff (state : State) (packet : Header) :
    permitsReply state packet = true ↔
      ∃ entry ∈ state.entries, state.now < entry.expiresAt ∧ entry.flow.reverse = packet := by
  simp [permitsReply, List.any_eq_true]

def install (state : State) (packet : Header) (expiresAt : Nat) : State :=
  ⟨state.now, ⟨packet, expiresAt⟩ :: state.entries.filter (fun entry => decide (entry.flow ≠ packet))⟩

theorem install_safe (state : State) (packet : Header) (expiresAt : Nat)
    (safe : state.Safe) (future : state.now < expiresAt) : (install state packet expiresAt).Safe := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | member
  · exact future
  · exact safe entry (List.mem_filter.mp member).1

theorem installed_reply (state : State) (packet : Header) (expiresAt : Nat)
    (future : state.now < expiresAt) : permitsReply (install state packet expiresAt) packet.reverse = true := by
  apply (permitsReply_iff _ _).mpr
  exact ⟨⟨packet, expiresAt⟩, by simp [install], future, rfl⟩

def advance (state : State) (now : Nat) : State :=
  let clock := max state.now now
  ⟨clock, state.entries.filter (fun entry => decide (clock < entry.expiresAt))⟩

theorem advance_safe (state : State) (now : Nat) : (advance state now).Safe := by
  intro entry member
  exact of_decide_eq_true (List.mem_filter.mp member).2

def close (state : State) (packet : Header) : State :=
  { state with entries := state.entries.filter (fun entry => decide (entry.flow ≠ packet)) }

theorem close_safe (state : State) (packet : Header) (safe : state.Safe) : (close state packet).Safe :=
  fun entry member => safe entry (List.mem_filter.mp member).1

theorem closed_reply_denied (state : State) (packet : Header) :
    permitsReply (close state packet) packet.reverse = false := by
  apply Bool.eq_false_iff.mpr
  intro admitted
  obtain ⟨entry, member, _, equal⟩ := (permitsReply_iff _ _).mp admitted
  have different := of_decide_eq_true (List.mem_filter.mp member).2
  have same := congrArg Header.reverse equal
  simp only [Header.reverse_reverse] at same
  exact different same

def flush (state : State) : State := { state with entries := [] }

inductive Event where
  | outbound (packet : Header) (authorized : Bool) (expiresAt : Nat)
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
  | .outbound packet authorized expiresAt =>
    if canOpen state packet authorized expiresAt then ⟨install state packet expiresAt, some packet⟩
    else ⟨state, none⟩
  | .inbound packet => ⟨state, if permitsReply state packet then some packet else none⟩
  | .advance now => ⟨advance state now, none⟩
  | .close packet => ⟨close state packet, none⟩
  | .flush => ⟨flush state, none⟩

theorem step_safe (state : State) (event : Event) (safe : state.Safe) : (step state event).state.Safe := by
  cases event with
  | outbound packet authorized expiresAt =>
    simp only [step]
    split
    next accepted =>
      have future : state.now < expiresAt := by simpa [canOpen] using ((Bool.and_eq_true _ _).mp accepted).2
      exact install_safe state packet expiresAt safe future
    next _ => exact safe
  | inbound => exact safe
  | advance now => exact advance_safe state now
  | close packet => exact close_safe state packet safe
  | flush => simp [step, flush, State.Safe]

theorem clock_mono (state : State) (event : Event) : state.now ≤ (step state event).state.now := by
  cases event <;> simp [step, install, advance, close, flush, Nat.le_max_left]
  split <;> exact Nat.le_refl _

theorem denied_unchanged (state : State) (packet : Header) (expiresAt : Nat) :
    step state (.outbound packet false expiresAt) = ⟨state, none⟩ := by simp [step, canOpen]

def run (state : State) (events : List Event) : State :=
  events.foldl (fun current event => (step current event).state) state

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

end Netlib.Protocol.Conntrack
