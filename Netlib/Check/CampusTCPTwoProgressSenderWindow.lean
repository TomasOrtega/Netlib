import Netlib.Check.CampusTCPTwoProgressState

/-!
# Current sender window space across ACK retirement

The reserve comes from the current endpoint window.
It supplies the tail-head space before a partial ACK is processed.
-/

namespace Netlib.Check.CampusTCPTwoProgressSenderWindow

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSender

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {state after : Endpoint.State} {stage next : Stage initial} {count : Nat}

def Reserved (initial : TwoWriteInitial cut sender gateway lower upper) (state : Endpoint.State) (stage : Stage initial) : Prop :=
  lower.length + upper.length ≤ stage.retiredBytes + state.sendWindow

theorem initial_reserved (initial : TwoWriteInitial cut sender gateway lower upper) :
    Reserved initial (source initial) .written := by
  simpa only [Reserved, Stage.retiredBytes, Nat.zero_add, source] using initial.senderState.window

theorem congr (space : Reserved initial state stage) (window : after.sendWindow = state.sendWindow)
    (retired : stage.retiredBytes ≤ next.retiredBytes) : Reserved initial after next := by
  unfold Reserved at *
  rw [window]
  omega

theorem clock (space : Reserved initial state stage) (frame : Endpoint.ClockFrame state after) :
    Reserved initial after stage := congr space frame.sendWindow (Nat.le_refl _)

theorem retirement_monotone (retiring : Retires stage count next) : stage.retiredBytes ≤ next.retiredBytes := by
  cases retiring <;> simp only [Stage.retiredBytes] <;> omega

theorem old_head_space (space : Reserved initial state stage) (retiring : Retires stage count next)
    (head : Recovery.Outstanding) (present : next.ledger.head? = some head) : head.count ≤ state.sendWindow := by
  cases retiring with
  | lower first second old =>
    have same : second.entry = head := Option.some.inj present
    subst head
    change lower.length + upper.length ≤ 0 + state.sendWindow at space
    change upper.length ≤ state.sendWindow
    omega
  | both first second old => cases present
  | tail first second old => cases present

theorem incoming_head_space (retiring : Retires stage count next) (window : Nat)
    (space : lower.length + upper.length ≤ next.retiredBytes + window)
    (head : Recovery.Outstanding) (present : next.ledger.head? = some head) : head.count ≤ window := by
  cases retiring with
  | lower first second old =>
    have same : second.entry = head := Option.some.inj present
    subst head
    change lower.length + upper.length ≤ lower.length + window at space
    change upper.length ≤ window
    omega
  | both first second old => cases present
  | tail first second old => cases present

theorem advancing_ack (space : Reserved initial state stage) (retiring : Retires stage count next)
    (received : Endpoint.AdvancingAck state packet recovery after)
    (incoming : lower.length + upper.length ≤ next.retiredBytes + packet.packet.segment.window.val) :
    Reserved initial after next := by
  have monotone := retirement_monotone retiring
  unfold Reserved at *
  rw [received.afterEq]
  unfold Endpoint.advancingAckState Endpoint.inOrderReceivedWith Endpoint.windowState
  split
  · exact incoming
  · dsimp only
    omega

theorem zero_ack (space : Reserved initial state stage) (received : Endpoint.ZeroAck state packet recovery after)
    (incoming : lower.length + upper.length ≤ stage.retiredBytes + packet.packet.segment.window.val) :
    Reserved initial after stage := by
  unfold Reserved at *
  rw [received.afterEq]
  unfold Endpoint.zeroAckState Endpoint.windowState
  split
  · exact incoming
  · exact space

end Netlib.Check.CampusTCPTwoProgressSenderWindow
