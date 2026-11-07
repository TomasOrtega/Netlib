import Netlib.Check.CampusTCPRecoveryStartupLinkInput
import Netlib.Check.CampusTCPDeliveryEnabled

/-!
# Actual campus delivery from current startup receive conditions

The control step and campus receipt retain the same source and gateway bytes.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupDeliveryEnabled

open Protocol.TCP CampusTCPModel

namespace J
export CampusTCPStartupJobs (Source PacketItem)
end J

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : C.State input.active input.passive}

def ControlOutput (control : C.Step input.active input.passive)
    (output : Option (Produced input.active input.passive)) : Prop :=
  match present : control.result.output with
  | none => output = none
  | some occurrence => output = some (.recovery control occurrence present)

theorem ControlOutput.none {control : C.Step input.active input.passive}
    (actual : ControlOutput control output) (absent : control.result.output = none) :
    output = none := by
  unfold ControlOutput at actual
  split at actual
  · exact actual
  · rename_i occurrence present
    rw [absent] at present
    cases present

theorem ControlOutput.some {control : C.Step input.active input.passive}
    (actual : ControlOutput control output) (present : control.result.output = some occurrence) :
    output = some (.recovery control occurrence present) := by
  unfold ControlOutput at actual
  split at actual
  · rename_i absent
    rw [absent] at present
    cases present
  · rename_i emitted emittedAt
    have same : emitted = occurrence := Option.some.inj (emittedAt.symm.trans present)
    subst emitted
    exact actual

private theorem run_control (control : C.Step input.active input.passive)
    (connected : before.connection = .recovering control.before) (stamp : control.index = before.time) :
    ∃ effect, runRecovery input before control.event = .ok effect ∧
      effect.recovery = some control ∧ effect.supported = true ∧ effect.passed = true ∧
      effect.state.connection = .recovering control.result.state ∧ effect.state.work = before.work ∧
      effect.service = none ∧ ControlOutput control effect.output := by
  cases control with
  | mk state index event result computed =>
    dsimp only at connected stamp ⊢
    subst index
    simp only [runRecovery, connected]
    split
    · rename_i reason failed
      rw [computed] at failed
      cases failed
    · rename_i actual actualAt
      have same : actual = result := Except.ok.inj (actualAt.symm.trans computed)
      subst actual
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure]
        all_goals exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem deliver_core (before : State input) (index : Nat) (served : Served input)
    (found : before.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : J.Source input) (production : served.ticket.value.produced = source.produced)
    (effect : Effect input)
    (received : runRecovery input before (.receive source.occurrence.index emission.bytes .rewrite true) = .ok effect) :
    ∃ result receipt, processCore input before (.deliver index emission.bytes true) = .ok result ∧
      result.supported = effect.supported ∧ result.passed = effect.passed ∧
      result.recovery = effect.recovery ∧ result.output = effect.output ∧
      result.receipt = some receipt ∧ receipt.served = served ∧ receipt.received = emission.asInput ∧
      receipt.recovery = effect.recovery.bind (fun control => control.result.receipt) ∧
      result.state.connection = effect.state.connection ∧ result.state.work = effect.state.work ∧
      result.service = effect.service := by
  simp only [processCore, CampusTCPModel.get, found, bind, Except.bind]
  split
  · rename_i missing
    rw [emitted] at missing
    cases missing
  · rename_i actual actualEmitted
    have same : actual = emission := Option.some.inj (actualEmitted.symm.trans emitted)
    subst actual
    have parsedInput : EstablishedReceive.input emission.bytes = .ok emission.asInput :=
      EstablishedReceive.input_roundtrip emission.asInput
    have bytes : emission.asInput.bytes = emission.bytes := rfl
    simp only [pure, Except.pure, parsedInput, parsed, Except.mapError, bytes, dite_true,
      production, CampusTCPStartupJobs.Source.produced, received]
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure Delivery (report : Report input events)
    (value : TCPHandshakeRecovery.ReceiveInput current report.final.time .rewrite)
    (index : Nat) (served : Served input) (emission : W.Emission served.ticket.value.source.packet)
    (actual : Step input) where
  before : actual.before = report.final
  event : actual.event = .deliver index emission.bytes true
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  control : C.Step input.active input.passive
  controlBefore : control.before = current
  controlIndex : control.index = report.final.time
  controlEvent : control.event = value.event
  recorded : actual.result.recovery = some control
  output : ControlOutput control actual.result.output
  controlReceipt : control.result.receipt = some value.receipt
  phase : TCPHandshakeRecovery.phaseLevel control.result.state.phase =
    TCPHandshakeRecovery.receiveLevel (TCPHandshakeRecovery.phaseLevel current.phase) value.source.kind
  response : TCPHandshakeRecovery.ResponseKind
    (TCPHandshakeRecovery.receiveResponse current.phase value.source.kind) control.result.output
  receipt : Receipt input
  received : actual.result.receipt = some receipt
  servedEq : receipt.served = served
  packet : receipt.received = emission.asInput
  recovery : receipt.recovery = some value.receipt
  connection : actual.result.state.connection = .recovering control.result.state
  work : actual.result.state.work = report.final.work
  service : actual.result.service = none

theorem deliver_input (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (item : J.PacketItem input) (index : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : J.Source input) (production : served.ticket.value.produced = source.produced)
    (payload : item.value.payload = .link index served emission emitted)
    (pending : item ∈ report.final.custody.pending)
    (value : TCPHandshakeRecovery.ReceiveInput current report.final.time .rewrite)
    (sourceEq : value.source = source.occurrence) (packetEq : value.packet = emission.asInput)
    (ordered : TCPHandshakeRecovery.ReceiveIndex current report.final.time)
    (fields : TCPHandshakeRecovery.ReceiveFields current value.receipt) :
    ∃ actual, Nonempty (Delivery report value index served emission actual) := by
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected
  obtain ⟨result, computed, phase, response, received⟩ :=
    TCPHandshakeRecovery.evaluate_receive_enabled reachable.invariant.phase value ordered fields
  let control : C.Step input.active input.passive := ⟨current, report.final.time, value.event, result, computed⟩
  obtain ⟨effect, runComputed, recorded, supported, passed, connection, work, service, output⟩ :=
    run_control (before := report.final) control connected rfl
  have event : value.event = .receive source.occurrence.index emission.bytes .rewrite true := by
    simp only [TCPHandshakeRecovery.ReceiveInput.event, sourceEq, packetEq]
    rfl
  change runRecovery input report.final value.event = .ok effect at runComputed
  rw [event] at runComputed
  have found := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ pending)
  rw [payload] at found
  obtain ⟨core, receipt, coreComputed, coreSupport, corePassed, coreRecovery, coreOutput, coreReceipt,
      receiptServed, receiptPacket, receiptRecovery, coreConnection, coreWork, coreService⟩ :=
    deliver_core report.final index served found emission emitted source production effect runComputed
  have linkPending : CampusTCPDeliveryEnabled.LinkPending report.final index := by
    refine ⟨item, pending, ?_⟩
    rw [payload]
    simp only [Transit.linkAt, beq_self_eq_true]
  obtain ⟨custody, prepared⟩ := CampusTCPDeliveryEnabled.prepare_deliver_exists report.final index served found
    emission emitted linkPending (CampusTCPCustodyFacts.Report.history report)
    (CampusTCPCustodyFacts.Report.sources report)
  let finalEffect : Effect input := { core with state := { core.state with
    custody := finishCustody report.final core custody, time := report.final.time + 1 } }
  have finalComputed : step input report.final (.deliver index emission.bytes true) = .ok finalEffect := by
    simp only [step, process, coreComputed, prepared, bind, Except.bind, pure, Except.pure]
    rfl
  let actual : Step input := ⟨report.final, .deliver index emission.bytes true, finalEffect, finalComputed⟩
  refine ⟨actual, ⟨⟨rfl, rfl, coreSupport.trans supported, corePassed.trans passed, control, rfl, rfl, rfl,
    coreRecovery.trans recorded, ?_, received, phase, response, receipt, coreReceipt, receiptServed, receiptPacket,
    ?_, coreConnection.trans connection, coreWork.trans work, coreService.trans service⟩⟩⟩
  · change ControlOutput control core.output
    rw [coreOutput]
    exact output
  · exact receiptRecovery.trans
      (show effect.recovery.bind (fun selected => selected.result.receipt) = some value.receipt by
        rw [recorded]
        exact received)

def Delivery.on_step (value : Delivery report receivedInput index served emission actual) (supplied : Step input)
    (before : supplied.before = report.final) (event : supplied.event = .deliver index emission.bytes true) :
    Delivery report receivedInput index served emission supplied := by
  have computed := actual.computed
  rw [value.before.trans before.symm, value.event.trans event.symm, supplied.computed] at computed
  have result : actual.result = supplied.result := (Except.ok.inj computed).symm
  have beforeEq := value.before.trans before.symm
  have eventEq := value.event.trans event.symm
  have same : actual = supplied := by
    cases actual
    cases supplied
    simp_all only
  exact same ▸ value

end Netlib.Check.CampusTCPRecoveryStartupDeliveryEnabled
