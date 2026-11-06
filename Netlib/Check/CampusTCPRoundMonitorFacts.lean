import Netlib.Check.CampusTCPRoundMonitor
import Netlib.Check.CampusTCPRoundAssignment

/-!
# Monitor updates from actual round records

The observation laws read the stored operation and packet identities.
They do not run endpoint or gateway processing.
-/

namespace Netlib.Check.CampusTCPRoundMonitorFacts

open CampusTCPModel
namespace M
export CampusTCPRoundMonitor
  (Config Phase References Monitor observeOutput observeAssignment observeService observeReceipt advance)
end M

variable {input : Input} {id : Nat}

theorem action_clock (before : State input) (action : CampusTCPRoundMonitor.Action) :
    CampusTCPRoundMonitor.sameClock before action.event = false := by
  cases connection : before.connection <;> cases action <;>
    simp only [CampusTCPRoundMonitor.sameClock, CampusTCPRoundMonitor.Action.event, connection]

theorem observe_action (config : M.Config) (monitor : M.Monitor) (actual : Step input)
    (action : CampusTCPRoundMonitor.Action) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true)
    (next : CampusTCPRoundMonitor.nextAction config actual.before monitor = some action)
    (event : actual.event = action.event) :
    CampusTCPRoundMonitor.observe config monitor actual = M.advance config monitor actual := by
  apply CampusTCPRoundMonitor.observe_selected config monitor actual action supported passed
  · rw [event]
    exact action_clock actual.before action
  · exact next
  · rw [event]
    exact CampusTCPRoundMonitor.Action.actionOf_event action

theorem observeOutput_eq (monitor : M.Monitor) (actual : Step input) (actor : Actor) (next : M.Phase)
    (produced : Produced input.active input.passive) (output : actual.result.output = some produced)
    (sender : produced.actor = actor)
    (pending : actual.result.state.custody.pendingID (Transit.ingressAt actual.before.outputs.length) = some id) :
    M.observeOutput monitor actual actor next =
      match actor with
      | .client => { phase := next, refs := { monitor.refs with
          dataOutput := some actual.before.outputs.length, dataIngressPacket := some id } }
      | .server => { phase := next, refs := { monitor.refs with
          ackOutput := some actual.before.outputs.length, ackIngressPacket := some id } } := by
  simp only [M.observeOutput, output, sender, pending]
  cases actor <;> rfl

theorem observeAssignment_eq (monitor : M.Monitor) (actual : Step input) (actor : Actor) (next : M.Phase)
    (ticket : Theory.Outstanding.Item (Ticket input.active input.passive))
    (found : actual.result.state.work.pending.find? (fun item => item.id == actual.before.work.nextID) = some ticket) :
    M.observeAssignment monitor actual actor next =
      match actor with
      | .client => { phase := next, refs := { monitor.refs with dataTicket := some ticket.id } }
      | .server => { phase := next, refs := { monitor.refs with ackTicket := some ticket.id } } := by
  simp only [M.observeAssignment, found]
  cases actor <;> rfl

theorem observeService_eq (monitor : M.Monitor) (actual : Step input) (actor : Actor) (next : M.Phase)
    (served : Served input) (recorded : actual.result.service = some served)
    (emission : Protocol.TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission)
    (pending : actual.result.state.custody.pendingID (Transit.linkAt actual.before.services.length) = some id) :
    M.observeService monitor actual actor next =
      match actor with
      | .client => { phase := next, refs := { monitor.refs with
          dataService := some actual.before.services.length, dataLinkPacket := some id } }
      | .server => { phase := next, refs := { monitor.refs with
          ackService := some actual.before.services.length, ackLinkPacket := some id } } := by
  simp only [M.observeService, recorded, emitted, pending]
  cases actor <;> rfl

theorem observeReceipt_eq (monitor : M.Monitor) (actual : Step input) (actor : Actor) (next : M.Phase)
    (receipt : Receipt input) (recorded : actual.result.receipt = some receipt) (receiver : receipt.actor = actor)
    (operation : T.Step) (application : actual.result.application = some (actor, operation)) :
    M.observeReceipt monitor actual actor next =
      match actor with
      | .server => { phase := next, refs := { monitor.refs with
          dataReceipt := some actual.before.receipts.length, dataReceiveStamp := some operation.stamp } }
      | .client => { phase := next, refs := { monitor.refs with
          ackReceipt := some actual.before.receipts.length, ackReceiveStamp := some operation.stamp } } := by
  simp only [M.observeReceipt, recorded, application, receiver, Bool.and_self]
  cases actor <;> rfl

theorem advanceRead_eq (config : M.Config) (monitor : M.Monitor) (phase : monitor.phase = .needRead)
    (actual : Step input) (operation : T.Step) (application : actual.result.application = some (.server, operation))
    (read : actual.result.read = config.bytes) :
    M.advance config monitor actual = { phase := .done, refs := { monitor.refs with
      readStamp := some operation.stamp, readBytes := config.bytes } } := by
  simp only [M.advance, phase, application, read, beq_self_eq_true, ite_true]

theorem output_pending (actual : Step input) (produced : Produced input.active input.passive)
    (output : actual.result.output = some produced) :
    ∃ id, actual.result.state.custody.pendingID (Transit.ingressAt actual.before.outputs.length) = some id := by
  obtain ⟨packet, member, _, payload⟩ := CampusTCPCustodyFacts.Step.output_packet actual produced output
  apply actual.result.state.custody.pendingID_exists (Transit.ingressAt actual.before.outputs.length)
  exact ⟨packet, member, by simp only [payload, Transit.ingressAt, beq_self_eq_true]⟩

theorem service_pending (actual : Step input) (served : Served input) (recorded : actual.result.service = some served)
    (emission : Protocol.TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) :
    ∃ id, actual.result.state.custody.pendingID (Transit.linkAt actual.before.services.length) = some id := by
  obtain ⟨packet, member, _, payload, _⟩ := CampusTCPCustodyFacts.Step.emission_packet actual served recorded emission emitted
  apply actual.result.state.custody.pendingID_exists (Transit.linkAt actual.before.services.length)
  exact ⟨packet, member, by simp only [payload, Transit.linkAt, beq_self_eq_true]⟩

theorem AssignmentFacts.find_new {before : State input} {index : Nat} {ingress : I.InterfaceRef}
    {produced : Produced input.active input.passive} {actual : Step input}
    (facts : CampusTCPRoundAssignment.AssignmentFacts before index ingress produced actual) :
    actual.result.state.work.pending.find? (fun item => item.id == actual.before.work.nextID) =
      some (CampusTCPRoundAssignment.ticket before index ingress produced) := by
  have unique := facts.workValid.1
  rw [facts.work] at unique
  have expanded :
      (Theory.Outstanding.enqueue before.work (CampusTCPRoundAssignment.ticketValue before index ingress produced)).ids =
        before.work.ids ++ [before.work.nextID] := by
    simp only [Theory.Outstanding.State.ids, Theory.Outstanding.enqueue, Theory.Outstanding.newItem,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  rw [expanded] at unique
  have disjoint := (List.nodup_append.mp unique).2.2
  have absent : before.work.pending.find? (fun item => item.id == before.work.nextID) = none := by
    apply List.find?_eq_none.mpr
    intro item member selected
    have same : item.id = before.work.nextID := beq_iff_eq.mp selected
    have belongs : item.id ∈ before.work.ids :=
      List.mem_map.mpr ⟨item, List.mem_append_right _ member, rfl⟩
    exact disjoint item.id belongs before.work.nextID (by simp) same
  rw [facts.beforeEq, facts.work]
  simp only [Theory.Outstanding.enqueue, List.find?_append, absent,
    List.find?_cons, Theory.Outstanding.newItem, beq_self_eq_true, CampusTCPRoundAssignment.ticket]
  rfl

end Netlib.Check.CampusTCPRoundMonitorFacts
