import Netlib.Protocol.ICMP
import Netlib.Protocol.IPv4Fragmentation

/-!
# Host path-MTU state

The selected connected UDP host uses a stable route and a monotonic clock.
Updates model the Linux floor, locking, refresh threshold, and exception expiry.
Allocation failure, route replacement, and clock wrap remain outside this model.
-/

namespace Netlib.Protocol.PMTU

open Packet InternetChecksum
abbrev MTU := IPv4Fragmentation.MTU

structure Policy where
  minimum : MTU
  lifetime : Nat
  deriving Repr, BEq, DecidableEq

structure Route where
  mtu : MTU
  locked : Bool := false
  deriving Repr, BEq, DecidableEq

structure Entry where
  mtu : MTU
  locked : Bool
  expires : Nat
  deriving Repr, BEq, DecidableEq

structure State where
  exception : Option Entry := none
  deriving Repr, BEq, DecidableEq

def State.Valid (state : State) (route : Route) : Prop :=
  ∀ entry, state.exception = some entry → entry.mtu.val ≤ route.mtu.val

def State.age (state : State) (now : Nat) : State :=
  ⟨state.exception.filter (fun entry => decide (now < entry.expires))⟩

def State.current (state : State) (route : Route) (now : Nat) : MTU :=
  (((state.age now).exception).map (·.mtu)).getD route.mtu

theorem State.age_valid (state : State) (route : Route) (valid : state.Valid route) (now : Nat) :
    (state.age now).Valid route := by
  intro entry found
  unfold age at found
  cases previous : state.exception with
  | none => simp [previous] at found
  | some old =>
    simp only [previous, Option.filter_some] at found
    split at found
    · cases found; exact valid _ previous
    · cases found

theorem State.current_le_route (state : State) (route : Route) (valid : state.Valid route) (now : Nat) :
    (state.current route now).val ≤ route.mtu.val := by
  unfold current
  cases active : (state.age now).exception with
  | none => simp
  | some entry => exact state.age_valid route valid now entry active

def reduced (old floor : MTU) (advertised : Word) : MTU :=
  if below : advertised.val < floor.val then
    ⟨min old.val floor.val, by have := old.property; have := floor.property; omega⟩
  else ⟨advertised.val, by have := floor.property.1; have := advertised.isLt; omega⟩

theorem reduced_le_old (old floor : MTU) (advertised : Word) (notIncrease : advertised.val ≤ old.val) :
    (reduced old floor advertised).val ≤ old.val := by
  unfold reduced
  split <;> dsimp only
  · exact Nat.min_le_left _ _
  · exact notIncrease

inductive Disposition where
  | locked | increase | unchanged | updated
  deriving Repr, BEq, DecidableEq

structure Result where
  state : State
  disposition : Disposition
  deriving Repr, BEq, DecidableEq

def update (policy : Policy) (route : Route) (before : State) (now : Nat) (advertised : Word) : Result :=
  let state := before.age now
  let old := state.current route now
  if route.locked || (state.exception.map (·.locked)).getD false then ⟨state, .locked⟩
  else if old.val < advertised.val then ⟨state, .increase⟩
  else
    let below := decide (advertised.val < policy.minimum.val)
    let target := reduced old policy.minimum advertised
    if (state.exception.map fun entry =>
        entry.mtu == target && !below && decide (now < entry.expires - policy.lifetime / 2)).getD false then
      ⟨state, .unchanged⟩
    else ⟨⟨some ⟨target, below, now + policy.lifetime⟩⟩, .updated⟩

structure Feedback where
  kind : ICMP.Kind
  quoted : Header
  reporter : Address
  deriving Repr, BEq, DecidableEq

def feedback (policy : Policy) (route : Route) (socket : Header) (before : State) (now : Nat)
    (message : Feedback) : Option Result :=
  if message.quoted = socket then
    match message.kind with
    | .fragmentationNeeded mtu => some (update policy route before now mtu)
    | .timeExceeded => none
  else none

theorem feedback_unrelated (policy : Policy) (route : Route) (socket : Header) (before : State) (now : Nat)
    (message : Feedback) (unrelated : message.quoted ≠ socket) :
    feedback policy route socket before now message = none := by simp [feedback, unrelated]

theorem feedback_reporter_independent (policy : Policy) (route : Route) (socket : Header) (before : State)
    (now : Nat) (message : Feedback) (reporter : Address) :
    feedback policy route socket before now { message with reporter } =
      feedback policy route socket before now message := rfl

inductive Send where
  | accepted | messageSize | invalidLength
  deriving Repr, BEq, DecidableEq

def send (route : Route) (state : State) (now : Nat) (df : Bool) (payloadLength : Nat) : Send :=
  if 65535 < payloadLength + 28 then .invalidLength
  else if df && decide ((state.current route now).val < payloadLength + 28) then .messageSize
  else .accepted

theorem send_accepted_iff (route : Route) (state : State) (now : Nat) (df : Bool) (payloadLength : Nat) :
    send route state now df payloadLength = .accepted ↔
      payloadLength + 28 ≤ 65535 ∧ (df = true → payloadLength + 28 ≤ (state.current route now).val) := by
  by_cases tooLarge : 65535 < payloadLength + 28
  · simp [send, tooLarge]
    omega
  · cases df <;> simp [send, tooLarge] <;> omega

end Netlib.Protocol.PMTU
