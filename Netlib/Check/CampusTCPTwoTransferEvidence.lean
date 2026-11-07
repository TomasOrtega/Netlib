import Netlib.Check.CampusTCPTwoTransferRecorded
import Netlib.Check.CampusTCPTwoTransferControlProgress
import Netlib.Check.CampusTCPTwoTransferDrainProgress
import Netlib.Check.CampusTCPTwoTransferPhaseClock
import Netlib.Check.CampusTCPTwoTransferPreparationActive
import Netlib.Check.CampusTCPTwoTransferLocatedReadOrigins

/-!
# Current forward evidence on one actual transfer trace

Protocol state, transfer controls, and action checks share the original cut.
The recorded prefix keeps the actual moves and endpoint clock bounds.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferRecorded (Recorded)
open CampusTCPTwoTransferScope (TransferScope)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe Control controlDemand drainTicket)
end W
namespace C
export CampusTCPTwoTransferControlState (Phase)
end C
namespace P
export CampusTCPTwoTransferPreparationState (Written PendingUpper)
end P
namespace A
export CampusTCPTwoTransferPhaseState (Active)
end A
namespace S
export CampusTCPTwoProgressSender (Stage Original)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {actual : Step input} {actor : Actor} {millis : Nat}

inductive Forward (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (current : Cut input complete) (monitor : W.Monitor) (location : Gateway) :
    {sent : S.Stage initial} → {received : R.Stage} →
      Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received → Type where
  | written (state : P.Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location) :
      Forward initial checks routing quantum allowance reverseLower reverseUpper current monitor location state.core
  | pending {first : S.Original initial .lower}
      (state : P.PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first) :
      Forward initial checks routing quantum allowance reverseLower reverseUpper current monitor location state.core
  | active {sent : S.Stage initial} {received : R.Stage}
      {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
      (state : A.Active core) : Forward initial checks routing quantum allowance reverseLower reverseUpper current monitor location core
  | readable {first : S.Original initial .lower} {second : S.Original initial .upper}
      (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location (.retired first second) .allReleased)
      (exchange : monitor.exchange.mode = .forward) (mode : monitor.exchange.forward.mode = .needRead)
      (sources : CampusTCPTwoProgressReceiptSources.History initial current)
      (senderDuplicate : core.live.senderFlight.recovery.duplicateAcks = 0)
      (mainAck : (core.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
        initial.geometry.«prefix» + (lower ++ upper).length) :
      Forward initial checks routing quantum allowance reverseLower reverseUpper current monitor location core

variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

theorem Forward.exchange (state : Forward initial checks routing quantum allowance reverseLower reverseUpper current monitor location core) :
    monitor.exchange.mode = .forward := by
  cases state with
  | written state => exact state.exchange
  | pending state => exact state.exchange
  | active state => exact state.exchange
  | readable _ exchange _ _ _ _ => exact exchange

theorem Forward.not_done (state : Forward initial checks routing quantum allowance reverseLower reverseUpper current monitor location core) :
    monitor.exchange.forward.mode ≠ .done := by
  cases state with
  | written state => rw [state.mode]; decide
  | pending state => rw [state.mode]; decide
  | active state => rcases state.mode with mode | mode <;> rw [mode] <;> decide
  | readable _ _ mode _ _ _ => rw [mode]; decide

def Scoped (monitor : W.Monitor) : Prop :=
  monitor.mode ≠ .armed → monitor.mode ≠ .finished → TransferScope monitor

structure Evidence (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (current : Cut input complete) (monitor : W.Monitor) (location : Gateway) where
  sent : S.Stage initial
  received : R.Stage
  core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received
  forward : Forward initial checks routing quantum allowance reverseLower reverseUpper current monitor location core
  controls : C.Phase current.report.final monitor.mode location
  scope : Scoped monitor
  armed : monitor.mode = .armed → monitor.exchange.forward.mode = .originals
  recorded : Recorded cut (config initial checks routing quantum allowance reverseLower reverseUpper) current monitor

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def Evidence.ofInitial (initial : TwoWriteInitial cut sender .primary lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut .primary)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (primaryEmpty : cut.report.final.outstanding .primary = 0)
    (targetEmpty : cut.report.final.standby.transport = Checkpoint.Gateway.initial)
    (targetNS : cut.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS) :
    Evidence initial checks routing quantum allowance reverseLower reverseUpper cut .initial .primary :=
  { sent := .written
    received := .empty
    core := (CampusTCPTwoTransferPreparationState.Written.ofInitial initial checks routing quantum allowance reverseLower reverseUpper primaryEmpty).core
    forward := .written (CampusTCPTwoTransferPreparationState.Written.ofInitial initial checks routing quantum allowance reverseLower reverseUpper primaryEmpty)
    controls := CampusTCPTwoTransferControlState.of_initial routing targetEmpty targetNS
    scope := by intro impossible; exact False.elim (impossible rfl)
    armed := fun _ => rfl
    recorded := Recorded.empty cut _ }

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

include evidence in
theorem Evidence.healthy : monitor.mode ≠ .invalid := by
  have phase := evidence.controls
  intro invalid
  rw [invalid] at phase
  cases phase

theorem Evidence.loss_suffix : evidence.recorded.suffix = evidence.core.losses.suffix :=
  evidence.recorded.loss_suffix evidence.core.losses

theorem Evidence.now_le (selected : Actor) :
    (endpoint current.endpoints selected).now ≤
      (endpoint cut.endpoints selected).now + evidence.core.losses.suffix.length * quantum := by
  have bound := evidence.recorded.now_le selected
  rw [evidence.loss_suffix] at bound
  exact bound

include evidence in
theorem Evidence.nonoriginal_finished
    (mode : monitor.exchange.forward.mode ≠ .originals) : monitor.mode = .finished := by
  by_cases finished : monitor.mode = .finished
  · exact finished
  · by_cases armed : monitor.mode = .armed
    · exact False.elim (mode (evidence.armed armed))
    · exact False.elim (mode (evidence.scope armed finished).mode)

include evidence in
theorem Evidence.readable_finished
    (mode : monitor.exchange.forward.mode = .needRead) : monitor.mode = .finished :=
  evidence.nonoriginal_finished (by rw [mode]; decide)

include evidence in
theorem Evidence.recovery_finished
    (mode : monitor.exchange.forward.mode = .recovery) : monitor.mode = .finished :=
  evidence.nonoriginal_finished (by rw [mode]; decide)

structure Advanced (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (actual : Step input) where
  move : Move current actual
  location : Gateway
  next : Evidence initial checks routing quantum allowance reverseLower reverseUpper move.after
    (W.observe cfg monitor actual) location

theorem Advanced.suffix (advance : Advanced evidence actual) :
    advance.next.recorded.suffix = evidence.recorded.suffix ++ [actual] := by
  apply List.append_cancel_left
  rw [← advance.next.recorded.history, advance.move.history, evidence.recorded.history, List.append_assoc]

def Forward.clock
    (state : Forward initial checks routing quantum allowance reverseLower reverseUpper current monitor location core)
    (clocked : CampusTCPTwoTransferLocatedClock.Clocked core actor millis actual) :
    Forward initial checks routing quantum allowance reverseLower reverseUpper clocked.move.after
      (W.observe cfg monitor actual) location clocked.next := by
  cases state with
  | written state => exact .written (state.clock clocked)
  | pending state => exact .pending (state.clock clocked)
  | active state => exact .active (state.clock clocked)
  | readable core exchange mode sources senderDuplicate mainAck =>
    exact .readable clocked.next (by rw [clocked.observed]; exact exchange)
      (by rw [clocked.observed]; exact mode) (sources.non_delivery clocked.move (by rw [clocked.event]; trivial))
      (by rw [CampusTCPTwoTransferPhaseState.clock_sender_recovery clocked]; exact senderDuplicate)
      (by rw [CampusTCPTwoTransferPhaseState.clock_session clocked]; exact mainAck)

theorem Evidence.clock_step (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .advanceClock actor millis)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced evidence actual) := by
  obtain ⟨clocked⟩ := CampusTCPTwoTransferLocatedClock.Step.clock evidence.core evidence.forward.exchange
    evidence.forward.not_done actual before event (by simpa only [event] using allowed)
  have nextMode : (W.observe cfg monitor actual).mode = monitor.mode := by rw [clocked.observed]
  have controls : C.Phase clocked.move.after.report.final (W.observe cfg monitor actual).mode location := by
    rw [nextMode]
    exact evidence.controls.clock clocked.placement
  exact ⟨{
    move := clocked.move, location
    next := {
      sent := evidence.sent, received := evidence.received, core := clocked.next
      forward := evidence.forward.clock clocked, controls
      scope := by
        intro unarmed unfinished
        have scope := evidence.scope (by rw [← nextMode]; exact unarmed) (by rw [← nextMode]; exact unfinished)
        exact scope.clock clocked
      armed := by rw [nextMode]; intro armed; rw [clocked.observed]; exact evidence.armed armed
      recorded := evidence.recorded.snoc clocked.move allowed } }⟩

end Netlib.Check.CampusTCPTwoTransferEvidence
