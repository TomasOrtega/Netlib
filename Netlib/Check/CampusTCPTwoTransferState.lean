import Netlib.Check.CampusTCPTwoProgressGatewayAt
import Netlib.Check.CampusTCPTwoProgressState
import Netlib.Check.CampusTCPTwoProgressGatewayPeerSettled

/-!
# Retained task state during gateway transfer

Policy inputs stay fixed at both deployments.
Ownership and transfer controls can change.
-/

namespace Netlib.Check.CampusTCPTwoTransferState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundGuards
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressGatewayAt (ViewAt)

namespace S
export CampusTCPTwoProgressSender (Stage Flight)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage Facts)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway location target : Gateway}
variable {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

structure Retained (initial current : Cut input complete) : Prop where
  retained : initial.report.steps <+: current.report.steps
  policy : ∀ gateway, (beforeService input initial.report.final gateway).environment =
    (beforeService input current.report.final gateway).environment

theorem Retained.refl (cut : Cut input complete) : Retained cut cut :=
  ⟨List.prefix_refl _, fun _ => rfl⟩

theorem Retained.trans (first : Retained cut current) (second : Retained current next) : Retained cut next :=
  ⟨first.retained.trans second.retained, fun gateway => (first.policy gateway).trans (second.policy gateway)⟩

structure AnchorAt (initial current : Cut input complete) : Prop extends Retained initial current where
  guards : Guards current.endpoints

theorem AnchorAt.ofAnchor (value : CampusTCPGapProgressPhaseBase.Anchor cut current) : AnchorAt cut current :=
  ⟨⟨value.retained, CampusTCPRoundEnvironment.service_environment _ _ value.environment⟩, value.guards⟩

theorem AnchorAt.refl (cut : Cut input complete) (guards : Guards cut.endpoints) : AnchorAt cut cut :=
  ⟨Retained.refl cut, guards⟩

def Reserved (view : ViewAt initial current location) : Prop :=
  initial.geometry.«prefix» + lower.length + upper.length ≤
    (view.gateway.session.lane sender.direction).acknowledged +
      (view.gateway.session.lane sender.direction).peerWindow.val

def PeerReserved (view : ViewAt initial current location) : Prop :=
  CampusTCPTwoProgressGatewayPeerWindow.floor initial ≤ (view.gateway.session.peer sender.direction).peerWindow.val

def Settled (view : ViewAt initial current location) : Prop :=
  (view.ranges.lowerRun.isSome = true ∨ view.ranges.upperRun.isSome = true) →
    (view.gateway.session.peer sender.direction).acknowledged = (view.gateway.session.peer sender.direction).observed

theorem reserved_relocate (view : ViewAt initial current location) (space : Reserved view)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    Reserved (view.relocate copied) := space

theorem peer_reserved_relocate (view : ViewAt initial current location) (space : PeerReserved view)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    PeerReserved (view.relocate copied) := space

theorem settled_relocate (view : ViewAt initial current location) (settled : Settled view)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    Settled (view.relocate copied) := settled

structure LiveAt (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (location : Gateway) (sent : S.Stage initial) (timeouts : Nat) (received : R.Stage) where
  anchor : AnchorAt cut current
  senderFlight : S.Flight initial (endpoint current.endpoints sender) sent timeouts
  receiverFacts : R.Facts initial (endpoint current.endpoints sender.other) received
  gatewayState : ViewAt initial current location
  gatewayWindow : Reserved gatewayState
  history : CampusTCPTwoProgressHistory.History cut current sender.other (lower ++ upper) (received.bytes lower upper)

variable {sent : S.Stage initial} {timeouts : Nat} {received : R.Stage}

def LiveAt.ofLive (value : CampusTCPTwoProgressState.Live initial current sent timeouts received) :
    LiveAt initial current gateway sent timeouts received :=
  ⟨AnchorAt.ofAnchor value.anchor, value.senderFlight, value.receiverFacts, ViewAt.ofView value.gatewayState,
    value.gatewayWindow, value.history⟩

def LiveAt.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper) : LiveAt initial cut gateway .written 0 .empty :=
  LiveAt.ofLive (CampusTCPTwoProgressState.Live.ofInitial initial)

def LiveAt.reindex (value : LiveAt initial current location sent timeouts received)
    (retained : current.report.steps <+: next.report.steps)
    (policy : ∀ selected, (beforeService input current.report.final selected).environment =
      (beforeService input next.report.final selected).environment)
    (endpoints : ∀ actor, endpoint next.endpoints actor = endpoint current.endpoints actor)
    (operations : applicationSteps next.endpoints sender.other = applicationSteps current.endpoints sender.other)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    LiveAt initial next target sent timeouts received := by
  let flight : S.Flight initial (endpoint next.endpoints sender) sent timeouts := by
    rw [endpoints sender]
    exact value.senderFlight
  let receiver : R.Facts initial (endpoint next.endpoints sender.other) received := by
    rw [endpoints sender.other]
    exact value.receiverFacts
  exact ⟨⟨⟨value.anchor.retained.trans retained, fun selected => (value.anchor.policy selected).trans (policy selected)⟩,
    CampusTCPTwoProgressState.endpoint_guards flight receiver⟩, flight, receiver,
    value.gatewayState.relocate copied, value.gatewayWindow, value.history.same operations⟩

theorem install_endpoints (move : Move current actual) (executionNS : IngressAttachment.NamespaceRef)
    (event : actual.event = .installCheckpoint executionNS) (installation : InstalledCheckpoint)
    (present : actual.result.installation = some installation) : move.after.endpoints = current.endpoints := by
  have source := CampusTCPTransferFacts.installation_origin actual executionNS event installation present
  have connected : move.after.report.final.connection = current.report.final.connection := by
    rw [move.final, source.connection, move.beforeEq]
  rw [move.after.connection, current.connection] at connected
  exact eq_of_heq (Connection.application.inj connected).2

def LiveAt.after_install (value : LiveAt initial current .primary sent timeouts received) (move : Move current actual)
    (executionNS : IngressAttachment.NamespaceRef) (event : actual.event = .installCheckpoint executionNS)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation)
    (policy : ∀ selected, (beforeService input current.report.final selected).environment =
      (beforeService input move.after.report.final selected).environment) :
    LiveAt initial move.after .standby sent timeouts received := by
  have endpoints := install_endpoints move executionNS event installation present
  exact value.reindex move.retained policy (fun actor => congrArg (fun updated => endpoint updated actor) endpoints)
    (congrArg (fun updated => applicationSteps updated sender.other) endpoints)
    (CampusTCPTwoProgressGatewayAt.install_transport move executionNS event installation present)

theorem LiveAt.after_install_gateway (value : LiveAt initial current .primary sent timeouts received) (move : Move current actual)
    (executionNS : IngressAttachment.NamespaceRef) (event : actual.event = .installCheckpoint executionNS)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation)
    (policy : ∀ selected, (beforeService input current.report.final selected).environment =
      (beforeService input move.after.report.final selected).environment) :
    (value.after_install move executionNS event installation present policy).gatewayState =
      value.gatewayState.after_install move executionNS event installation present := rfl

def LiveAt.clock (value : LiveAt initial current location sent timeouts received)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (senderTimely : Endpoint.AckTimeReady (endpoint current.endpoints sender) (endpoint next.endpoints sender).now)
    (receiverTimely : Endpoint.AckTimeReady (endpoint current.endpoints sender.other) (endpoint next.endpoints sender.other).now) :
    LiveAt initial next location sent timeouts received := by
  let flight := value.senderFlight.clock (placement.frame.endpointFrame sender) senderTimely
  let receiver := value.receiverFacts.clock (placement.frame.endpointFrame sender.other) receiverTimely
  exact ⟨⟨⟨value.anchor.retained.trans placement.retained, fun selected => (value.anchor.policy selected).trans
    (congrArg CampusTCPService.Before.environment (placement.frame.beforeService selected)).symm⟩,
    CampusTCPTwoProgressState.endpoint_guards flight receiver⟩, flight, receiver,
    value.gatewayState.reframe (placement.frame.beforeService location), value.gatewayWindow, value.history.clock placement⟩

end Netlib.Check.CampusTCPTwoTransferState
