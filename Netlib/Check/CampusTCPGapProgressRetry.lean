import Netlib.Check.CampusTCPGapTimeout
import Netlib.Check.CampusTCPGapProgressDemand

namespace Netlib.Check.CampusTCPGapProgressRetry

open Packet Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressPhaseBase (Move)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressState (Live gateway_reframe endpoint_guards)
open CampusTCPGapProgressWire (Geometry DataFields)
open CampusTCPGapProgressSetup (config)

namespace E
export CampusTCPGapProgressEvidence (DropLog dropID FirstReceipt DataOutput DataIngress Waiting)
end E
namespace M
export CampusTCPGapProgressMonitor (Monitor observe observeOutput nextDemand)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current after : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper} {retries : Nat} {released : Bool} {actual : Step input}

structure Retry (live : Live initial current retries released) (actual : Step input)
    extends CampusTCPGapTimeout.TimeoutMove current sender live.senderFlight.recovery live.senderFlight.head [initial.flight.tail] actual where
  next : Live initial move.after (retries + 1) released
  encoded : Endpoint.emitAt (endpoint current.endpoints sender) (endpoint current.endpoints sender).core.sendUna lower = .ok facts.packet
  fields : DataFields initial facts.produced
  source : move.after.report.final.outputs[actual.before.outputs.length]? = some facts.produced
  pending : IngressPending move.after.report.final actual.before.outputs.length
  minted : ∃ item ∈ move.after.report.final.custody.pending,
    item.value.parent = none ∧ item.value.payload = .ingress actual.before.outputs.length facts.produced
  packetID : Nat
  custody : move.after.report.final.custody.pendingID (Transit.ingressAt actual.before.outputs.length) = some packetID
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  first : next.history.streams.first = live.history.streams.first

theorem retry_at (wire : Geometry initial) (live : Live initial current retries released)
    (credit : retries < 2) (due : live.senderFlight.head.lastAt + live.senderFlight.recovery.rto ≤ live.senderFlight.recovery.now) :
    ∃ actual, Nonempty (Retry live actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPGapTimeout.timeout_at current sender live.senderFlight.recovery live.senderFlight.head
    [initial.flight.tail] (live.senderFlight.head.lastAt + live.senderFlight.recovery.rto)
    (live.senderFlight.timeout_ready credit due) live.senderFlight.storage
  have flight : CampusTCPGapProgressSender.Flight initial.flight (endpoint value.move.after.endpoints sender) (retries + 1) := by
    rw [value.selected]
    exact live.senderFlight.retry credit due
  have receiver : CampusTCPGapProgressReceiver.Facts initial (endpoint value.move.after.endpoints sender.other) released := by
    rw [value.peer]
    exact live.receiverFacts
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment value.move.after.report.final := by
    rw [value.move.final]
    exact value.facts.environment
  have gateway (selected : Gateway) :
      beforeService input value.move.after.report.final selected = beforeService input current.report.final selected := by
    rw [value.move.final, CampusTCPRoundLocal.step_service_nonservice actual
      (by rw [value.facts.event]; trivial), value.facts.beforeEq]
  let next : Live initial value.move.after (retries + 1) released := {
    anchor := ⟨endpoint_guards flight receiver, live.anchor.retained.trans value.move.retained,
      live.anchor.environment.trans environment⟩
    senderFlight := flight, receiverFacts := receiver, gateway := gateway_reframe live.gateway (gateway .standby)
    history := live.history.same value.peerSteps }
  have encoded : Endpoint.emitAt (endpoint current.endpoints sender) (endpoint current.endpoints sender).core.sendUna lower =
      .ok value.facts.packet := by simpa only [live.senderFlight.payload] using value.facts.encoded
  have fields : DataFields initial value.facts.produced := by
    rw [value.facts.production]
    apply CampusTCPGapProgressWire.retry_fields wire value.facts.localStep value.facts.packet value.facts.origin
      (value.facts.localBefore.symm ▸ live.senderFlight)
    rw [value.facts.localBefore]
    exact encoded
  have source : value.move.after.report.final.outputs[actual.before.outputs.length]? = some value.facts.produced := by
    rw [value.move.final, value.facts.beforeEq]
    exact value.facts.source
  obtain ⟨id, pendingID⟩ := CampusTCPRoundMonitorFacts.output_pending actual value.facts.produced value.facts.output
  refine ⟨actual, ⟨{
    toTimeoutMove := value, next, encoded, fields, source, pending := ?_, minted := ?_, packetID := id
    custody := ?_, gateway, environment, first := rfl }⟩⟩
  · rw [value.move.final, value.facts.beforeEq]
    exact value.facts.pending
  · rw [value.move.final, value.facts.beforeEq]
    exact value.facts.minted
  · rw [value.move.final]
    exact pendingID

variable {live : Live initial current retries released}

def Retry.output (value : Retry live actual) : E.DataOutput initial value.move.after where
  index := actual.before.outputs.length
  produced := value.facts.produced
  stored := value.source
  actor := by rw [value.facts.production]; rfl
  application := by rw [value.facts.production]; trivial
  fields := value.fields

theorem Retry.observe (value : Retry live actual) (native : NativeEnv cut initial.gateway.seed.entry)
    (quantum allowance : Nat) (monitor : M.Monitor) (waiting : monitor.waiting = true) :
    M.observe (config initial native quantum allowance) monitor actual =
      { monitor with
        phase := .dataIngress
        refs := { monitor.refs with dataOutput := some actual.before.outputs.length, dataIngressPacket := some value.packetID }
        waiting := false
        retries := monitor.retries + 1 } := by
  have actor : value.facts.produced.actor = sender := by rw [value.facts.production]; rfl
  have pending : actual.result.state.custody.pendingID (Transit.ingressAt actual.before.outputs.length) = some value.packetID := by
    rw [← value.move.final]
    exact value.custody
  rw [CampusTCPGapProgressMonitorFacts.observe_timeout _ _ _ value.facts.supported value.facts.passed waiting value.facts.event]
  simp only [M.observeOutput, value.facts.output, ite_true, actor,
    show (config initial native quantum allowance).sender = sender from rfl, pending]
  cases sender <;> rfl

theorem Step.retry (actual : Step input) (wire : Geometry initial) (live : Live initial current retries released)
    (credit : retries < 2) (due : live.senderFlight.head.lastAt + live.senderFlight.recovery.rto ≤ live.senderFlight.recovery.now)
    (before : actual.before = current.report.final) (event : actual.event = .timeout sender true) :
    Nonempty (Retry live actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := retry_at wire live credit due
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.move.beforeEq.trans before.symm) (value.facts.event.trans event.symm)
  subst enabled
  exact ⟨value⟩

private def retainFirst (first : Option (E.FirstReceipt initial current))
    (retained : current.report.final.receipts <+: after.report.final.receipts) : Option (E.FirstReceipt initial after) :=
  first.map fun receipt => receipt.reframe (by
    obtain ⟨extra, history⟩ := retained
    rw [← history, List.getElem?_append_left (List.getElem?_eq_some_iff.mp receipt.stored).1]
    exact receipt.stored)

private theorem retainFirst_index (first : Option (E.FirstReceipt initial current))
    (retained : current.report.final.receipts <+: after.report.final.receipts) :
    (retainFirst first retained).map (·.index) = first.map (·.index) := by cases first <;> rfl

private theorem retainFirst_operation (first : Option (E.FirstReceipt initial current))
    (retained : current.report.final.receipts <+: after.report.final.receipts) :
    (retainFirst first retained).map (·.operation) = first.map (·.operation) := by cases first <;> rfl

theorem Waiting.retry_at (wire : Geometry initial) (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (record : E.Waiting initial allowance current monitor retries released) (budget : allowance ≤ 2)
    (due : record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto ≤ record.live.senderFlight.recovery.now) :
    ∃ actual, ∃ move : Move current actual, actual.event = .timeout sender true ∧
      Nonempty (E.DataIngress initial allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) (retries + 1) released) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPGapProgressRetry.retry_at wire record.live (record.credit budget) due
  have observed := value.observe native quantum allowance monitor record.waiting
  have receipts : value.move.after.report.final.receipts = current.report.final.receipts := by
    rw [value.move.final]
    exact value.facts.receipts
  have retained : current.report.final.receipts <+: value.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_refl _
  have drops : E.DropLog cut value.move.after monitor.drops := by
    have log := record.drops.append value.move
    simpa only [E.dropID, value.facts.event, Option.toList_none, List.append_nil] using log
  refine ⟨actual, value.move, value.facts.event, ⟨{
    live := value.next, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, bound := record.bound, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation := ?_
    output := value.output, packetID := value.packetID, custody := value.custody, outputRef := ?_, packetRef := ?_ }⟩⟩
  · rw [observed]
  · rw [observed]
  · rw [observed, record.retryCount]
  · rw [observed]
    exact record.dropCount
  · rw [observed]
    exact drops
  · rw [observed, retainFirst_index]
    exact record.firstRef
  · rw [value.first, retainFirst_operation]
    exact record.firstOperation
  · rw [observed]
    rfl
  · rw [observed]

end Netlib.Check.CampusTCPGapProgressRetry
