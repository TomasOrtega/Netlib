import Netlib.Check.CampusTCPTwoProgressPhaseBase
import Netlib.Check.CampusTCPTwoProgressPathsFrames

/-!
# Actual original sends from the joint phase

Each send extends the same writer and loss histories.
The second send also permits an already dropped lower packet.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseSend

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core OriginalTimes emitted)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane Allowed observe observeSend nextDemand)
end M
namespace F
export CampusTCPTwoProgressMonitorFacts
  (allowed_iff serves_operation observe_action observe_send_lower observe_send_upper phase_beq_false phase_beq_self)
end F
namespace S
export CampusTCPTwoProgressSender (Original Stage Flight Part)
end S
namespace Send
export CampusTCPTwoProgressSend (SendFacts FirstSent SecondSent)
end Send

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {actual : Step input}

def ingressLane (lane : M.Lane) (index packetID : Nat) : M.Lane :=
  ⟨.dataIngress, { lane.refs with dataOutput := some index, dataIngressPacket := some packetID }⟩

private theorem lower_allowed (mode : monitor.mode = .originals) (pending : monitor.lower.phase = .needSend) :
    M.Allowed (config initial native quantum allowance) current.report.final monitor (.send sender lower.length true) := by
  apply (F.allowed_iff _ _ _ _).mpr
  refine ⟨by rw [mode]; decide, .inl ⟨.single (.operation (.send sender lower.length true)), ?_, ?_⟩, rfl⟩
  · simp only [M.nextDemand, mode, pending, CampusTCPTwoProgressMonitorFacts.phase_beq_self, ite_true]
    rfl
  · exact (F.serves_operation _ _).mpr rfl

private theorem upper_allowed (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (pending : monitor.upper.phase = .needSend) :
    M.Allowed (config initial native quantum allowance) current.report.final monitor (.send sender upper.length true) := by
  apply (F.allowed_iff _ _ _ _).mpr
  refine ⟨by rw [mode]; decide, .inl ⟨.single (.operation (.send sender upper.length true)), ?_, ?_⟩, rfl⟩
  · simp only [M.nextDemand, mode, (F.phase_beq_false _ _).mpr first, Bool.false_eq_true, ite_false,
      pending, CampusTCPTwoProgressMonitorFacts.phase_beq_self, ite_true]
    rfl
  · exact (F.serves_operation _ _).mpr rfl

private theorem output_lane (facts : Send.SendFacts current sender count actual)
    (actor : facts.produced.actor = sender) (lane : M.Lane) :
    CampusTCPTwoProgressMonitor.Lane.ofGap (CampusTCPGapProgressMonitor.observeOutput (config initial native quantum allowance).toConfig
      lane.toGap actual true .dataIngress) = ingressLane lane current.report.final.outputs.length facts.packetID := by
  have custody := facts.custody
  rw [facts.move.final] at custody
  have self : (sender == sender) = true := by cases sender <;> rfl
  simp only [CampusTCPGapProgressMonitor.observeOutput, facts.output, actor, config,
    ite_true, self, facts.move.beforeEq, custody,
    CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap, ingressLane]

private theorem send_recovery (facts : Send.SendFacts current sender count actual)
    (before : S.Flight initial (endpoint current.endpoints sender) sent timeouts)
    (after : S.Flight initial (endpoint facts.move.after.endpoints sender) next timeouts) :
    after.recovery = Recovery.sent before.recovery count := by
  have runtime := after.runtime.symm.trans (congrArg (fun state : Endpoint.State => state.recovery) facts.sendState)
  change some after.recovery =
    (endpoint current.endpoints sender).recovery.map (fun recovery => Recovery.sent recovery count) at runtime
  rw [before.runtime, Option.map_some] at runtime
  exact Option.some.inj runtime

private theorem duplicate_send (facts : Send.SendFacts current sender count actual)
    (before : S.Flight initial (endpoint current.endpoints sender) sent timeouts)
    (after : S.Flight initial (endpoint facts.move.after.endpoints sender) next timeouts) :
    after.recovery.duplicateAcks = before.recovery.duplicateAcks := by
  rw [send_recovery facts before after]
  rfl

private theorem gateway_session (facts : Send.SendFacts current sender count actual)
    (before : CampusTCPTwoProgressState.Live initial current sent timeouts received)
    (after : CampusTCPTwoProgressState.Live initial facts.move.after next timeouts received) :
    after.gatewayState.gateway.session = before.gatewayState.gateway.session := by
  have phase := after.gatewayState.gateway.phase
  rw [facts.serviceFrame gateway, before.gatewayState.gateway.phase] at phase
  exact (Admission.Phase.data.inj phase).symm

private def ingress (facts : Send.SendFacts current sender (part.bytes lower upper).length actual)
    (actor : facts.produced.actor = sender) (application : CampusTCPDeliveryEnabled.ApplicationSource facts.produced)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) facts.produced)
    (lane : M.Lane) :
    CampusTCPTwoProgressPaths.DataIngress initial facts.move.after part
      (ingressLane lane current.report.final.outputs.length facts.packetID) where
  output := ⟨current.report.final.outputs.length, facts.produced, facts.source, actor, application, fields⟩
  packetID := facts.packetID
  custody := facts.custody
  phase := rfl
  outputRef := rfl
  packetRef := rfl

private theorem core_cast_book (core : Core initial native quantum allowance current before sent received)
    (same : before = after) : (same ▸ core).losses.book = core.losses.book := by cases same; rfl

private theorem history_cast_book
    (history : CampusTCPTwoProgressLossHistory.History initial (config initial native quantum allowance) current before)
    (same : before = after) : (same ▸ history).book = history.book := by cases same; rfl

structure First (core : Core initial native quantum allowance current monitor .written .empty) (actual : Step input) where
  value : Send.FirstSent core.live actual
  allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event
  observed : M.observe (config initial native quantum allowance) monitor actual =
    { monitor with lower := ingressLane monitor.lower current.report.final.outputs.length value.facts.packetID }
  next : Core initial native quantum allowance value.facts.move.after
    (M.observe (config initial native quantum allowance) monitor actual) (.lower value.original) .empty
  book : next.losses.book = core.losses.book
  path : CampusTCPTwoProgressPaths.DataIngress initial value.facts.move.after .lower
    (M.observe (config initial native quantum allowance) monitor actual).lower

structure Second {first : S.Original initial .lower}
    (core : Core initial native quantum allowance current monitor (.lower first) .empty) (actual : Step input) where
  value : Send.SecondSent core.live actual
  allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event
  observed : M.observe (config initial native quantum allowance) monitor actual =
    { monitor with upper := ingressLane monitor.upper current.report.final.outputs.length value.facts.packetID }
  next : Core initial native quantum allowance value.facts.move.after
    (M.observe (config initial native quantum allowance) monitor actual) (.both first value.original first.entry) .empty
  book : next.losses.book = core.losses.book
  path : CampusTCPTwoProgressPaths.DataIngress initial value.facts.move.after .upper
    (M.observe (config initial native quantum allowance) monitor actual).upper

theorem first_at (core : Core initial native quantum allowance current monitor .written .empty)
    (mode : monitor.mode = .originals) (pending : monitor.lower.phase = .needSend) :
    ∃ actual, Nonempty (First core actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressSend.first_at core.live core.senderWindow
  have allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event := by
    rw [value.facts.event]
    exact lower_allowed mode pending
  have observed : M.observe (config initial native quantum allowance) monitor actual =
      { monitor with lower := ingressLane monitor.lower current.report.final.outputs.length value.facts.packetID } := by
    rw [F.observe_action _ _ _ value.facts.move.supported value.facts.move.passed
      (by rw [value.facts.move.beforeEq]; exact allowed) (.send sender lower.length true) value.facts.event,
      F.observe_send_lower _ _ _ mode pending]
    have output := output_lane (initial := initial) (native := native) (quantum := quantum) (allowance := allowance)
      value.facts (by rw [value.production]; rfl) monitor.lower
    simp only [M.observeSend, output, ingressLane]
    rfl
  have payload : value.facts.packet.packet.segment.payload = lower := by
    have packet : value.facts.packet = value.original.packet := congrArg Produced.output (value.facts.production.symm.trans value.production)
    rw [packet]
    exact value.original.payload
  have duplicate := duplicate_send value.facts core.live.senderFlight value.next.senderFlight
  let healthy : Core initial native quantum allowance value.facts.move.after
      { monitor with lower := ingressLane monitor.lower current.report.final.outputs.length value.facts.packetID }
      (.lower value.original) .empty := {
    live := value.next, senderWindow := value.reserve
    originals := CampusTCPTwoProgressSourceHistory.Originals.first value core.writer
    originalTimes := by
      change (endpoint cut.endpoints sender).now ≤ value.original.operation.before.now
      rw [value.sameStep, value.facts.localBefore]
      exact core.live.senderFlight.monotone
    writer := by simpa only [emitted, List.nil_append] using core.writer.send value.facts payload
    losses := observed ▸ core.losses.append value.facts.move
      (by rw [CampusTCPTwoProgressLossHistory.isDrop, value.facts.event])
      (by rw [CampusTCPTwoProgressLossHistory.isTimeout, value.facts.event])
      (by rw [observed]) (by rw [observed])
    lossBound := core.lossBound
    retired := Nat.le_refl _
    gatewayAck := by rw [gateway_session value.facts core.live value.next]; exact core.gatewayAck
    covered := by intro part impossible; cases part <;> cases impossible
    duplicates := duplicate ▸ core.duplicates
    emptyDuplicate := fun _ => duplicate ▸ core.emptyDuplicate rfl
    deadline := by
      rw [send_recovery value.facts core.live.senderFlight value.next.senderFlight]
      exact RecoveryDeadline.sent _ _ core.deadline
    estimatorBeforeRetire := fun _ => by
      rw [send_recovery value.facts core.live.senderFlight value.next.senderFlight]
      exact core.estimatorBeforeRetire rfl
    rtoBeforeRetire := fun _ => by
      rw [send_recovery value.facts core.live.senderFlight value.next.senderFlight]
      exact core.rtoBeforeRetire rfl
    rtoPending := fun _ => RTOEnvelope.of_power (by
      rw [send_recovery value.facts core.live.senderFlight value.next.senderFlight]
      exact core.rtoBeforeRetire rfl) }
  have path := ingress (part := (.lower : S.Part)) value.facts (by rw [value.production]; rfl)
    (by rw [value.production]; trivial) value.fields monitor.lower
  have book : (observed.symm ▸ healthy).losses.book = core.losses.book := by
    rw [core_cast_book]
    exact history_cast_book _ observed
  exact ⟨actual, ⟨⟨value, allowed, observed, observed.symm ▸ healthy, book, by rw [observed]; exact path⟩⟩⟩

theorem second_at {first : S.Original initial .lower}
    (core : Core initial native quantum allowance current monitor (.lower first) .empty)
    (mode : monitor.mode = .originals)
    (lowerPhase : monitor.lower.phase = .dataIngress ∨ monitor.lower.phase = .done)
    (pending : monitor.upper.phase = .needSend) :
    ∃ actual, Nonempty (Second core actual) := by
  have lowerPending : monitor.lower.phase ≠ .needSend := by rcases lowerPhase with lowerPhase | lowerPhase <;> rw [lowerPhase] <;> decide
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressSend.second_at core.live core.senderWindow
  have allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event := by
    rw [value.facts.event]
    exact upper_allowed mode lowerPending pending
  have observed : M.observe (config initial native quantum allowance) monitor actual =
      { monitor with upper := ingressLane monitor.upper current.report.final.outputs.length value.facts.packetID } := by
    rw [F.observe_action _ _ _ value.facts.move.supported value.facts.move.passed
      (by rw [value.facts.move.beforeEq]; exact allowed) (.send sender upper.length true) value.facts.event,
      F.observe_send_upper _ _ _ mode lowerPending pending]
    have output := output_lane (initial := initial) (native := native) (quantum := quantum) (allowance := allowance)
      value.facts (by rw [value.production]; rfl) monitor.upper
    simp only [M.observeSend, output, ingressLane]
    rfl
  have payload : value.facts.packet.packet.segment.payload = upper := by
    have packet : value.facts.packet = value.original.packet := congrArg Produced.output (value.facts.production.symm.trans value.production)
    rw [packet]
    exact value.original.payload
  have duplicate := duplicate_send value.facts core.live.senderFlight value.next.senderFlight
  let healthy : Core initial native quantum allowance value.facts.move.after
      { monitor with upper := ingressLane monitor.upper current.report.final.outputs.length value.facts.packetID }
      (.both first value.original first.entry) .empty := {
    live := value.next, senderWindow := value.reserve
    originals := core.originals.second value core.writer
    originalTimes := ⟨core.originalTimes, by
      rw [value.sameStep, value.facts.localBefore]
      exact core.live.senderFlight.monotone⟩
    writer := core.writer.send value.facts payload
    losses := observed ▸ core.losses.append value.facts.move
      (by rw [CampusTCPTwoProgressLossHistory.isDrop, value.facts.event])
      (by rw [CampusTCPTwoProgressLossHistory.isTimeout, value.facts.event])
      (by rw [observed]) (by rw [observed])
    lossBound := core.lossBound
    retired := Nat.le_refl _
    gatewayAck := by rw [gateway_session value.facts core.live value.next]; exact core.gatewayAck
    covered := by intro part impossible; cases part <;> cases impossible
    duplicates := duplicate ▸ core.duplicates
    emptyDuplicate := fun _ => duplicate ▸ core.emptyDuplicate rfl
    deadline := by
      rw [send_recovery value.facts core.live.senderFlight value.next.senderFlight]
      exact RecoveryDeadline.sent _ _ core.deadline
    estimatorBeforeRetire := fun _ => by
      rw [send_recovery value.facts core.live.senderFlight value.next.senderFlight]
      exact core.estimatorBeforeRetire rfl
    rtoBeforeRetire := fun _ => by
      rw [send_recovery value.facts core.live.senderFlight value.next.senderFlight]
      exact core.rtoBeforeRetire rfl
    rtoPending := fun _ => RTOEnvelope.of_power (by
      rw [send_recovery value.facts core.live.senderFlight value.next.senderFlight]
      exact core.rtoBeforeRetire rfl) }
  have path := ingress (part := (.upper : S.Part)) value.facts (by rw [value.production]; rfl)
    (by rw [value.production]; trivial) value.fields monitor.upper
  have book : (observed.symm ▸ healthy).losses.book = core.losses.book := by
    rw [core_cast_book]
    exact history_cast_book _ observed
  exact ⟨actual, ⟨⟨value, allowed, observed, observed.symm ▸ healthy, book, by rw [observed]; exact path⟩⟩⟩

theorem First.upper_frame {core : Core initial native quantum allowance current monitor .written .empty} (record : First core actual) :
    (M.observe (config initial native quantum allowance) monitor actual).upper = monitor.upper := by rw [record.observed]

theorem Second.lower_frame {first : S.Original initial .lower}
    {core : Core initial native quantum allowance current monitor (.lower first) .empty} (record : Second core actual) :
    (M.observe (config initial native quantum allowance) monitor actual).lower = monitor.lower := by rw [record.observed]

theorem SendFacts.custody_mint (facts : Send.SendFacts current sender count actual) :
    facts.move.after.report.final.custody = Theory.PacketCustody.mint current.report.final.custody
      (.ingress current.report.final.outputs.length facts.produced) := by
  have noService : actual.result.service = none := by
    cases present : actual.result.service with
    | none => rfl
    | some served =>
      obtain ⟨id, observed, completed, event, _⟩ := CampusTCPOrigins.service_origin actual served present
      rw [facts.event] at event
      cases event
  obtain ⟨effect, custody, _, prepared, result⟩ := actual.transaction
  have preparedEq : actual.before.custody = custody := by
    simpa only [facts.event, prepareCustody, pure, Except.pure, Except.ok.injEq] using prepared
  have output : effect.output = some facts.produced := by simpa only [result] using facts.output
  have service : effect.service = none := by simpa only [result] using noService
  rw [facts.move.final, result, ← preparedEq]
  change finishCustody actual.before effect actual.before.custody = _
  rw [finishCustody, output, service, facts.move.beforeEq]

theorem SendFacts.fresh_packet_id (facts : Send.SendFacts current sender count actual) :
    facts.packetID = current.report.final.custody.nextID := by
  have absent : current.report.final.custody.pending.find?
      (fun item => Transit.ingressAt current.report.final.outputs.length item.value.payload) = none := by
    apply List.find?_eq_none.mpr
    intro item member selected
    obtain ⟨produced, payload⟩ := CampusTCPCustodyFacts.ingress_stage _ _ selected
    have source := CampusTCPCustodyFacts.Report.sources current.report item (List.mem_append_right _ member)
    rw [payload] at source
    change current.report.final.outputs[current.report.final.outputs.length]? = some produced at source
    exact (Nat.lt_irrefl _) (List.getElem?_eq_some_iff.mp source).1
  have selected := facts.custody
  rw [SendFacts.custody_mint facts, Theory.PacketCustody.State.pendingID,
    Theory.PacketCustody.mint_pending, List.find?_append, absent] at selected
  simpa [Transit.ingressAt] using selected.symm

private theorem pending_mint {α : Type} {predicate : α → Bool} {id : Nat}
    (before : Theory.PacketCustody.State α) (payload : α)
    (selected : before.pendingID predicate = some id) :
    (Theory.PacketCustody.mint before payload).pendingID predicate = some id := by
  unfold Theory.PacketCustody.State.pendingID at selected ⊢
  rw [Theory.PacketCustody.mint_pending, List.find?_append]
  cases found : before.pending.find? (fun item => predicate item.value.payload) with
  | none => simp only [found, Option.map_none, reduceCtorEq] at selected
  | some item => rw [found] at selected; exact selected

def SendFacts.retain_ingress (facts : Send.SendFacts current sender count actual)
    (path : CampusTCPTwoProgressPaths.DataIngress initial current part lane) :
    CampusTCPTwoProgressPaths.DataIngress initial facts.move.after part lane := by
  apply path.retain
  · rw [facts.move.final, CampusTCPOrigins.output_history actual, facts.output, facts.move.beforeEq]
    exact List.prefix_append _ _
  · rw [SendFacts.custody_mint facts]
    exact pending_mint _ _ path.custody

def Second.retain_lower {first : S.Original initial .lower}
    {core : Core initial native quantum allowance current monitor (.lower first) .empty} (record : Second core actual)
    (path : CampusTCPTwoProgressPaths.DataIngress initial current .lower monitor.lower) :
    CampusTCPTwoProgressPaths.DataIngress initial record.value.facts.move.after .lower
      (M.observe (config initial native quantum allowance) monitor actual).lower :=
  (SendFacts.retain_ingress record.value.facts path).reindex record.lower_frame

end Netlib.Check.CampusTCPTwoProgressPhaseSend
