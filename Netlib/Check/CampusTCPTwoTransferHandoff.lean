import Netlib.Check.CampusTCPTransferEnabled
import Netlib.Check.CampusTCPTwoTransferNative
import Netlib.Check.CampusTCPTransferSequence

/-!
# Actual controls preserve the original TCP task

Current endpoint and gateway facts provide the capture guard.
Every control extends the same cut and retains its endpoint histories.
-/

namespace Netlib.Check.CampusTCPTwoTransferHandoff

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressGatewayAt (ViewAt)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferNative (Checks Routing)

namespace T
export CampusTCPTransferEnabled (Control Ready CaptureReady)
end T

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {timeouts : Nat}
variable {received : CampusTCPTwoProgressReceiver.Stage}

theorem entry_tcp (initial : TwoWriteInitial cut sender gateway lower upper) :
    initial.gatewayState.session.entry.flow.original.protocol = .tcp := by
  have tuple := congrArg Packet.Header.protocol (initial.input_tuple .client)
  exact tuple.symm.trans (endpoint_valid cut.endpoints .client).1.1

theorem capture_ready (view : ViewAt initial current .primary) :
    T.CaptureReady current.report.final.primary.transport := by
  refine ⟨⟨view.gateway.session, view.gateway.record, view.gateway.phase, view.gateway.member,
    view.gateway.entry, ?_⟩⟩
  rw [view.gateway.entry, view.gateway.identity.entry]
  exact entry_tcp initial

theorem transfer_ready (live : LiveAt initial current .primary sent timeouts received)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing current .primary)
    (drained : current.report.final.outstanding .primary = 0)
    (empty : current.report.final.standby.transport = Checkpoint.Gateway.initial)
    (namespaceEq : current.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS) :
    T.Ready current.report.final := by
  obtain ⟨unsealed, unfenced⟩ := routing.primary rfl
  exact ⟨⟨checks.configured .standby, routing.unpaused, unsealed, unfenced⟩,
    capture_ready live.gatewayState, drained, namespaceEq, empty⟩

theorem control_transport (value : T.Control current event actual)
    (ordinary : ∀ ns, event ≠ .installCheckpoint ns) (location : Gateway) :
    (value.move.after.report.final.resident location).transport =
      (current.report.final.resident location).transport := by
  cases location
  · exact congrArg Local.transport value.frame.primary
  · exact congrArg Local.transport (value.frame.standby ordinary)

def control_live (live : LiveAt initial current location sent timeouts received)
    (value : T.Control current event actual) (ordinary : ∀ ns, event ≠ .installCheckpoint ns) :
    LiveAt initial value.move.after location sent timeouts received :=
  live.reindex value.move.retained (fun selected => (value.frame.policy selected).symm)
    (fun actor => congrArg (fun endpoints => endpoint endpoints actor) value.endpoints)
    (congrArg (fun endpoints => applicationSteps endpoints sender.other) value.endpoints)
    (control_transport value ordinary location)

def install_live (live : LiveAt initial current .primary sent timeouts received)
    (value : T.Control current (.installCheckpoint executionNS) actual)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    LiveAt initial value.move.after .standby sent timeouts received :=
  live.after_install value.move executionNS value.eventEq installation present
    (fun selected => (value.frame.policy selected).symm)

theorem install_live_session (live : LiveAt initial current .primary sent timeouts received)
    (value : T.Control current (.installCheckpoint executionNS) actual)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    (install_live live value installation present).gatewayState.gateway.session = live.gatewayState.gateway.session := rfl

theorem install_live_recovery (live : LiveAt initial current .primary sent timeouts received)
    (value : T.Control current (.installCheckpoint executionNS) actual)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    (install_live live value installation present).senderFlight.recovery = live.senderFlight.recovery := by
  have runtime := (install_live live value installation present).senderFlight.runtime
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
  exact Option.some.inj (runtime.symm.trans (same.trans live.senderFlight.runtime))

def sequence_live (live : LiveAt initial current .primary sent timeouts received)
    (value : CampusTCPTransferSequence.Seven current) :
    LiveAt initial value.final .standby sent timeouts received :=
  live.reindex value.retained (fun selected => (value.policy selected).symm)
    (fun actor => congrArg (fun endpoints => endpoint endpoints actor) value.endpoints)
    (congrArg (fun endpoints => applicationSteps endpoints sender.other) value.endpoints) value.target

theorem sequence_session (live : LiveAt initial current .primary sent timeouts received)
    (value : CampusTCPTransferSequence.Seven current) :
    (sequence_live live value).gatewayState.gateway.session = live.gatewayState.gateway.session := rfl

theorem sequence_recovery (live : LiveAt initial current .primary sent timeouts received)
    (value : CampusTCPTransferSequence.Seven current) :
    (sequence_live live value).senderFlight.recovery = live.senderFlight.recovery := by
  have runtime := (sequence_live live value).senderFlight.runtime
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
  exact Option.some.inj (runtime.symm.trans (same.trans live.senderFlight.runtime))

theorem sequence_routing (value : CampusTCPTransferSequence.Seven current) : Routing value.final .standby := by
  refine ⟨?_, value.final_unpaused, ?_, ?_⟩
  · intro actor
    cases actor
    · exact value.owners.1
    · exact value.owners.2
  · intro impossible
    cases impossible
  · intro _
    exact ⟨value.installation, value.final_installation, value.final_sealed, value.final_fenced⟩

def sequence_native (live : LiveAt initial current .primary sent timeouts received)
    (checks : Checks cut initial.gatewayState.session.entry) (value : CampusTCPTransferSequence.Seven current) :
    NativeEnv value.final .standby initial.gatewayState.session.entry :=
  checks.native_env (sequence_live live value).anchor.toRetained (sequence_routing value)

theorem sequence_ingress (live : LiveAt initial current .primary sent timeouts received)
    (checks : Checks cut initial.gatewayState.session.entry) (value : CampusTCPTransferSequence.Seven current) :
    (sequence_native live checks value).ingress = checks.ingress .standby := rfl

theorem transfer_at (live : LiveAt initial current .primary sent timeouts received)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing current .primary)
    (drained : current.report.final.outstanding .primary = 0)
    (empty : current.report.final.standby.transport = Checkpoint.Gateway.initial)
    (namespaceEq : current.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS) :
    ∃ value : CampusTCPTransferSequence.Seven current,
      Nonempty (LiveAt initial value.final .standby sent timeouts received) ∧
        Nonempty (NativeEnv value.final .standby initial.gatewayState.session.entry) := by
  obtain ⟨value⟩ := CampusTCPTransferSequence.of_ready (transfer_ready live checks routing drained empty namespaceEq)
  exact ⟨value, ⟨sequence_live live value⟩, ⟨sequence_native live checks value⟩⟩

def paused_live (live : LiveAt initial current .primary sent timeouts received)
    (value : CampusTCPTransferSequence.Six current) :
    LiveAt initial value.final .standby sent timeouts received :=
  live.reindex value.retained (fun selected => (value.policy selected).symm)
    (fun actor => congrArg (fun endpoints => endpoint endpoints actor) value.endpoints)
    (congrArg (fun endpoints => applicationSteps endpoints sender.other) value.endpoints) value.target

theorem paused_session (live : LiveAt initial current .primary sent timeouts received)
    (value : CampusTCPTransferSequence.Six current) :
    (paused_live live value).gatewayState.gateway.session = live.gatewayState.gateway.session := rfl

theorem paused_recovery (live : LiveAt initial current .primary sent timeouts received)
    (value : CampusTCPTransferSequence.Six current) :
    (paused_live live value).senderFlight.recovery = live.senderFlight.recovery := by
  have runtime := (paused_live live value).senderFlight.runtime
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
  exact Option.some.inj (runtime.symm.trans (same.trans live.senderFlight.runtime))

theorem paused_routing (value : CampusTCPTransferSequence.Six current) : Routing value.final .standby := by
  refine ⟨?_, value.final_unpaused, ?_, ?_⟩
  · intro actor
    cases actor
    · exact value.owners.1
    · exact value.owners.2
  · intro impossible
    cases impossible
  · intro _
    exact ⟨value.installation, value.final_installation, value.final_sealed, value.final_fenced⟩

def paused_native (live : LiveAt initial current .primary sent timeouts received)
    (checks : Checks cut initial.gatewayState.session.entry) (value : CampusTCPTransferSequence.Six current) :
    NativeEnv value.final .standby initial.gatewayState.session.entry :=
  checks.native_env (paused_live live value).anchor.toRetained (paused_routing value)

theorem paused_transfer_at (live : LiveAt initial current .primary sent timeouts received)
    (checks : Checks cut initial.gatewayState.session.entry)
    (paused : current.report.final.assignmentPaused = true)
    (unsealed : current.report.final.primarySealed = false) (unfenced : current.report.final.primaryFenced = false)
    (drained : current.report.final.outstanding .primary = 0)
    (empty : current.report.final.standby.transport = Checkpoint.Gateway.initial)
    (namespaceEq : current.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS) :
    ∃ value : CampusTCPTransferSequence.Six current,
      Nonempty (LiveAt initial value.final .standby sent timeouts received) ∧
        Nonempty (NativeEnv value.final .standby initial.gatewayState.session.entry) := by
  have ready : CampusTCPTransferSequence.PausedReady current.report.final :=
    ⟨⟨checks.configured .standby, unsealed, unfenced, capture_ready live.gatewayState⟩,
      paused, drained, namespaceEq, empty⟩
  obtain ⟨value⟩ := CampusTCPTransferSequence.of_paused_ready ready
  exact ⟨value, ⟨paused_live live value⟩, ⟨paused_native live checks value⟩⟩

end Netlib.Check.CampusTCPTwoTransferHandoff
