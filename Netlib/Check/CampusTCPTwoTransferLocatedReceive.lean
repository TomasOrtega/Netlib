import Netlib.Check.CampusTCPTwoTransferState
import Netlib.Check.CampusTCPTwoTransferPaths
import Netlib.Check.CampusTCPTwoProgressReceiveState
import Netlib.Check.CampusTCPTwoProgressReceiptSources

/-!
# Actual data delivery at the current gateway location

The existing endpoint receive proofs use the same stored serviced link.
The located task retains its source gateway view and application history.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedReceive

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferPaths (DataLink)
open CampusTCPTwoProgressReadWriter (SelectedOutput)

namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace D
export CampusTCPTwoProgressReceive (Received)
end D

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper chunk : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {sent : S.Stage initial} {timeouts : Nat} {beforeStage afterStage : R.Stage}
variable {part : S.Part} {lane : CampusTCPTwoProgressMonitor.Lane}
variable {index : Nat} {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

def joint (value : D.Received initial current beforeStage afterStage chunk index served emission emitted)
    (live : LiveAt initial current location sent timeouts beforeStage) :
    LiveAt initial value.move.after location sent timeouts afterStage := by
  have flight : CampusTCPTwoProgressSender.Flight initial (endpoint value.move.after.endpoints sender) sent timeouts := by
    rw [value.peer]
    exact live.senderFlight
  have stream : beforeStage.bytes lower upper ++ value.delivery.localStep.releasedPayload = afterStage.bytes lower upper := by
    rw [value.localRelease]
    exact value.stream
  have within : beforeStage.bytes lower upper ++ value.delivery.localStep.releasedPayload <+: lower ++ upper := by
    rw [stream]
    exact CampusTCPTwoProgressPhaseBase.stage_prefix afterStage
  have history := live.history.release value.delivery.localStep value.selectedSteps within value.localRead
  exact {
    anchor := {
      retained := live.anchor.retained.trans value.move.retained
      policy := fun selected => (live.anchor.policy selected).trans
        (CampusTCPRoundEnvironment.service_environment _ _ value.environment selected)
      guards := CampusTCPTwoProgressState.endpoint_guards flight value.receiver }
    senderFlight := flight
    receiverFacts := value.receiver
    gatewayState := live.gatewayState.reframe (value.gateway location)
    gatewayWindow := live.gatewayWindow
    history := stream ▸ history }

structure Delivered (live : LiveAt initial current location sent timeouts beforeStage)
    (path : DataLink initial current part lane) (afterStage : R.Stage) (chunk : List UInt8) where
  value : D.Received initial current beforeStage afterStage chunk path.index path.served path.emission path.emitted
  next : LiveAt initial value.move.after location sent timeouts afterStage
  gateway : next.gatewayState = live.gatewayState.reframe (value.gateway location)

private def finish (live : LiveAt initial current location sent timeouts beforeStage)
    (path : DataLink initial current part lane)
    (value : D.Received initial current beforeStage afterStage chunk path.index path.served path.emission path.emitted) :
    Delivered live path afterStage chunk := ⟨value, joint value live, rfl⟩

theorem lower_at (live : LiveAt initial current location sent timeouts .empty)
    (path : DataLink initial current .lower lane) : Nonempty (Delivered live path .lowerReleased lower) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.lower_at live.receiverFacts path.receive_link
  exact ⟨finish live path value⟩

theorem hold_at (live : LiveAt initial current location sent timeouts .empty)
    (path : DataLink initial current .upper lane) : Nonempty (Delivered live path .upperHeld []) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.hold_at live.receiverFacts path.receive_link
  exact ⟨finish live path value⟩

theorem upper_at (live : LiveAt initial current location sent timeouts .lowerReleased)
    (path : DataLink initial current .upper lane) : Nonempty (Delivered live path .allReleased upper) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.upper_at live.receiverFacts path.receive_link
  exact ⟨finish live path value⟩

theorem gap_at (live : LiveAt initial current location sent timeouts .upperHeld)
    (path : DataLink initial current .lower lane) : Nonempty (Delivered live path .allReleased (lower ++ upper)) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.gap_at live.receiverFacts path.receive_link
  exact ⟨finish live path value⟩

theorem old_at (live : LiveAt initial current location sent timeouts beforeStage)
    (path : DataLink initial current part lane)
    (old : part.offset lower + (part.bytes lower upper).length ≤ (beforeStage.bytes lower upper).length) :
    Nonempty (Delivered live path beforeStage []) := by
  have nonempty : part.bytes lower upper ≠ [] := by cases part; exact initial.lowerNonempty; exact initial.upperNonempty
  obtain ⟨value⟩ := CampusTCPTwoProgressReceive.old_at live.receiverFacts path.receive_link nonempty old
  exact ⟨finish live path value⟩

variable {live : LiveAt initial current location sent timeouts beforeStage} {path : DataLink initial current part lane}

theorem Delivered.step_eq (delivered : Delivered live path afterStage chunk) (actual : Step input)
    (before : actual.before = current.report.final) (event : actual.event = .deliver path.index path.emission.bytes true) :
    delivered.value.delivery.step = actual := delivered.value.step_eq actual before event

theorem Delivered.sender_recovery (delivered : Delivered live path afterStage chunk) :
    delivered.next.senderFlight.recovery = live.senderFlight.recovery := by
  have same := congrArg Endpoint.State.recovery delivered.value.peer
  exact Option.some.inj (delivered.next.senderFlight.runtime.symm.trans (same.trans live.senderFlight.runtime))

theorem Delivered.stream (delivered : Delivered live path afterStage chunk) :
    beforeStage.bytes lower upper ++ chunk = afterStage.bytes lower upper := delivered.value.stream

def Delivered.sources (delivered : Delivered live path afterStage chunk)
    (history : CampusTCPTwoProgressReceiptSources.History initial current)
    (source : SelectedOutput initial current path.served.ticket.value.produced) :
    CampusTCPTwoProgressReceiptSources.History initial delivered.value.move.after :=
  history.data path source delivered.value

def Delivered.source (delivered : Delivered live path afterStage chunk)
    (source : SelectedOutput initial current path.served.ticket.value.produced) :
    SelectedOutput initial delivered.value.move.after path.served.ticket.value.produced :=
  source.retain_steps delivered.value.move.retained

end Netlib.Check.CampusTCPTwoTransferLocatedReceive
