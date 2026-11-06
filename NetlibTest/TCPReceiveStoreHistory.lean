import Netlib.Protocol.TCP.ReceiveStoreHistory

namespace NetlibTest.TCPReceiveStoreHistory

open Netlib.Protocol.TCP
namespace H
export ReceiveStoreHistory (Accepted History ReleasedOrigin StreamRange releasedOrigin)
end H

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

structure Recorded (before : ReceiveStore.State Nat) (position : Nat) (payload : List UInt8) (metadata : Nat) where
  result : ReceiveStore.Result Nat
  checked : ReceiveStore.accept before position payload metadata 8 8 = .ok result

def Recorded.step (value : Recorded before position payload metadata) (carrier : String) : H.Accepted Nat String :=
  ⟨before, position, payload, metadata, 8, 8, value.result, carrier, value.checked⟩

private def record (before : ReceiveStore.State Nat) (position : Nat) (payload : List UInt8) (metadata : Nat) :
    Except String (Recorded before position payload metadata) :=
  match checked : ReceiveStore.accept before position payload metadata 8 8 with
  | .error _ => .error "The selected actual store operation did not succeed."
  | .ok result => .ok ⟨result, checked⟩

def run : IO Unit := do
  let initial : ReceiveStore.State Nat := ReceiveStore.initial
  let suffix ← load (record initial 2 [30, 40] 57)
  let duplicate ← load (record suffix.result.state 2 [30, 40] 91)
  let gap ← load (record duplicate.result.state 0 [10, 20] 36)
  let first := suffix.step "suffix"
  let second := duplicate.step "duplicate"
  let third := gap.step "gap"
  let steps := [first, second, third]
  have history : H.History initial steps gap.result.state :=
    .cons first (.cons second (.cons third (.nil _)))
  have origins : ∀ run ∈ gap.result.released, Nonempty (H.ReleasedOrigin steps third run) :=
    history.released_origin rfl third (by simp [steps])
  have byteOrigins : ∀ index byte, (ReceiveStore.bytes gap.result.released)[index]? = some byte →
      Nonempty (ReceiveStoreHistory.ReleasedByteOrigin steps third index byte) :=
    history.released_byte_origin rfl third (by simp [steps])
  have sources : ∀ step ∈ steps, H.StreamRange initial.frontier [10, 20, 30, 40] step.allocated := by
    intro step member
    simp only [steps, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨[10, 20], rfl, ⟨[], rfl⟩⟩
    · exact ⟨[10, 20], rfl, ⟨[], rfl⟩⟩
    · exact ⟨[], rfl, ⟨[30, 40], rfl⟩⟩
  have prefixResult := history.released_prefix rfl [10, 20, 30, 40] sources
  let _ := origins
  let _ := byteOrigins
  let _ := prefixResult
  ensure (suffix.result.released.isEmpty && suffix.result.novel == 2 && suffix.result.state.frontier == 0)
    "A future span must stay held without advancing the ordered frontier."
  ensure (duplicate.result.duplicate && duplicate.result.novel == 0 && duplicate.result.state.nextID == 2 &&
      duplicate.result.state.held == suffix.result.state.held)
    "An exact duplicate must keep the first bytes and metadata while allocating its own receipt identity."
  ensure (ReceiveStore.bytes gap.result.released == [10, 20, 30, 40] && gap.result.state.frontier == 4 &&
      gap.result.state.held.isEmpty)
    "The gap receipt must release the exact ordered prefix from both actual inputs."
  ensure (gap.result.released.map (·.receipt) == [2, 0] && gap.result.released.map (·.metadata) == [36, 57])
    "Release must retain each original receipt and its first metadata."
  ensure (gap.result.state.nextID == 3 && gap.result.novel == 2 && ReceiveStore.size gap.result.released == 4)
    "New input bytes and released bytes must have separate counts."
  for selected in gap.result.released.attach do
    let origin ← load (H.releasedOrigin history rfl third (by simp [steps]) selected.val selected.property)
    ensure ((origin.issuer.carrier == "gap" && selected.val.receipt == 2) ||
        (origin.issuer.carrier == "suffix" && selected.val.receipt == 0))
      "The origin lookup must select the actual original operation, including held data."
  IO.println "Checked receive-store history tests passed."

end NetlibTest.TCPReceiveStoreHistory
