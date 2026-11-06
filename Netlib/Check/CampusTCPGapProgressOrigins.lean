import Netlib.Check.CampusTCPGapProgressEvidence
import Netlib.Check.CampusTCPRecoveryRoundOrigins
import Netlib.Check.CampusTCPGapProgressRetry

/-!
# Actual packet sources for a held-gap read

Selected old outputs keep their exact original source.
A later lower output keeps its actual head retry and preceding sender flight.
-/

namespace Netlib.Check.CampusTCPGapProgressOrigins

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPGapProgressStart
open CampusTCPGapProgressMonitor (Monitor)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current next : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper} {monitor updated : Monitor}

structure RetriedSource (initial : GapInitial cut sender lower upper) (produced : Produced input.active input.passive) where
  prior : Cut input complete
  actual : Step input
  move : Move prior actual
  retained : cut.report.steps <+: prior.report.steps
  retries : Nat
  flight : CampusTCPGapProgressSender.Flight initial.flight (endpoint prior.endpoints sender) retries
  operation : T.Step
  recorded : actual.result.application = some (sender, operation)
  localBefore : operation.before = endpoint prior.endpoints sender
  localEvent : operation.event = .timeout true
  packet : EstablishedReceive.Input
  origin : T.OutputOrigin operation packet
  production : produced = .application sender operation packet origin
  output : actual.result.output = some produced
  encoded : Endpoint.emitAt (endpoint prior.endpoints sender) (endpoint prior.endpoints sender).core.sendUna lower = .ok packet

inductive LowerSource (initial : GapInitial cut sender lower upper) (produced : Produced input.active input.passive) : Type where
  | original (same : produced = initial.lowerSource.produced)
  | retry (source : RetriedSource initial produced)

structure SourceHistory (initial : GapInitial cut sender lower upper) (current : Cut input complete) (monitor : Monitor) : Prop where
  output : ∀ index, monitor.refs.dataOutput = some index → ∃ produced,
    current.report.final.outputs[index]? = some produced ∧ Nonempty (LowerSource initial produced)
  service : ∀ index, monitor.refs.dataService = some index → ∃ served,
    current.report.final.services[index]? = some served ∧ Nonempty (LowerSource initial served.ticket.value.produced)
  first : ∀ index, monitor.firstDataReceipt = some index → ∃ receipt,
    current.report.final.receipts[index]? = some receipt ∧ Nonempty (LowerSource initial receipt.served.ticket.value.produced)

private theorem prefix_lookup {α : Type} {before after : List α} {index : Nat} {value : α}
    (retained : before <+: after) (stored : before[index]? = some value) : after[index]? = some value := by
  obtain ⟨extra, history⟩ := retained
  rw [← history, List.getElem?_append_left (List.getElem?_eq_some_iff.mp stored).1]
  exact stored

theorem SourceHistory.ofInitial (initial : GapInitial cut sender lower upper) :
    SourceHistory initial cut (CampusTCPGapProgressSetup.initialMonitor initial) := by
  constructor
  · intro index selected
    have same : initial.lowerSource.index = index := Option.some.inj selected
    subst index
    exact ⟨_, initial.lowerSource.stored, ⟨.original rfl⟩⟩
  · intro index selected
    have same : initial.selected.serviceIndex = index := Option.some.inj selected
    subst index
    exact ⟨_, initial.selected.stored, ⟨.original initial.selected.source⟩⟩
  · intro index selected
    cases selected

theorem SourceHistory.output_source (history : SourceHistory initial current monitor)
    (reference : monitor.refs.dataOutput = some index) (stored : current.report.final.outputs[index]? = some produced) :
    Nonempty (LowerSource initial produced) := by
  obtain ⟨actual, found, source⟩ := history.output index reference
  have same : actual = produced := Option.some.inj (found.symm.trans stored)
  exact same ▸ source

theorem SourceHistory.service_source (history : SourceHistory initial current monitor)
    (reference : monitor.refs.dataService = some index) (stored : current.report.final.services[index]? = some served) :
    Nonempty (LowerSource initial served.ticket.value.produced) := by
  obtain ⟨actual, found, source⟩ := history.service index reference
  have same : actual = served := Option.some.inj (found.symm.trans stored)
  exact same ▸ source

theorem SourceHistory.first_source (history : SourceHistory initial current monitor)
    (reference : monitor.firstDataReceipt = some index) (stored : current.report.final.receipts[index]? = some receipt) :
    Nonempty (LowerSource initial receipt.served.ticket.value.produced) := by
  obtain ⟨actual, found, source⟩ := history.first index reference
  have same : actual = receipt := Option.some.inj (found.symm.trans stored)
  exact same ▸ source

theorem SourceHistory.retain (history : SourceHistory initial current monitor)
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (services : current.report.final.services <+: next.report.final.services)
    (receipts : current.report.final.receipts <+: next.report.final.receipts)
    (outputRef : updated.refs.dataOutput = monitor.refs.dataOutput)
    (serviceRef : updated.refs.dataService = monitor.refs.dataService)
    (firstRef : updated.firstDataReceipt = monitor.firstDataReceipt) : SourceHistory initial next updated := by
  constructor
  · intro index selected
    obtain ⟨produced, stored, source⟩ := history.output index (outputRef.symm.trans selected)
    exact ⟨produced, prefix_lookup outputs stored, source⟩
  · intro index selected
    obtain ⟨served, stored, source⟩ := history.service index (serviceRef.symm.trans selected)
    exact ⟨served, prefix_lookup services stored, source⟩
  · intro index selected
    obtain ⟨receipt, stored, source⟩ := history.first index (firstRef.symm.trans selected)
    exact ⟨receipt, prefix_lookup receipts stored, source⟩

theorem SourceHistory.reframe (history : SourceHistory initial current monitor)
    (same : current.report.final = next.report.final) : SourceHistory initial next monitor := by
  apply history.retain
  · rw [same]; exact List.prefix_refl _
  · rw [same]; exact List.prefix_refl _
  · rw [same]; exact List.prefix_refl _
  · rfl
  · rfl
  · rfl

theorem SourceHistory.clock (history : SourceHistory initial current monitor)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : SourceHistory initial next monitor := by
  apply history.retain
  · rw [placement.frame.outputs]; exact List.prefix_refl _
  · rw [placement.frame.services]; exact List.prefix_refl _
  · rw [placement.frame.receipts]; exact List.prefix_refl _
  · rfl
  · rfl
  · rfl

theorem SourceHistory.update_output (history : SourceHistory initial current monitor)
    (produced : Produced input.active input.passive) (stored : next.report.final.outputs[index]? = some produced)
    (source : Nonempty (LowerSource initial produced))
    (services : current.report.final.services <+: next.report.final.services)
    (receipts : current.report.final.receipts <+: next.report.final.receipts)
    (outputRef : updated.refs.dataOutput = some index)
    (serviceRef : updated.refs.dataService = monitor.refs.dataService)
    (firstRef : updated.firstDataReceipt = monitor.firstDataReceipt) : SourceHistory initial next updated := by
  constructor
  · intro selected reference
    have same : index = selected := Option.some.inj (outputRef.symm.trans reference)
    subst selected
    exact ⟨produced, stored, source⟩
  · intro selected reference
    obtain ⟨served, found, origin⟩ := history.service selected (serviceRef.symm.trans reference)
    exact ⟨served, prefix_lookup services found, origin⟩
  · intro selected reference
    obtain ⟨receipt, found, origin⟩ := history.first selected (firstRef.symm.trans reference)
    exact ⟨receipt, prefix_lookup receipts found, origin⟩

theorem SourceHistory.update_service (history : SourceHistory initial current monitor)
    (served : Served input) (stored : next.report.final.services[index]? = some served)
    (source : Nonempty (LowerSource initial served.ticket.value.produced))
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (receipts : current.report.final.receipts <+: next.report.final.receipts)
    (outputRef : updated.refs.dataOutput = monitor.refs.dataOutput)
    (serviceRef : updated.refs.dataService = some index)
    (firstRef : updated.firstDataReceipt = monitor.firstDataReceipt) : SourceHistory initial next updated := by
  constructor
  · intro selected reference
    obtain ⟨produced, found, origin⟩ := history.output selected (outputRef.symm.trans reference)
    exact ⟨produced, prefix_lookup outputs found, origin⟩
  · intro selected reference
    have same : index = selected := Option.some.inj (serviceRef.symm.trans reference)
    subst selected
    exact ⟨served, stored, source⟩
  · intro selected reference
    obtain ⟨receipt, found, origin⟩ := history.first selected (firstRef.symm.trans reference)
    exact ⟨receipt, prefix_lookup receipts found, origin⟩

theorem SourceHistory.update_first (history : SourceHistory initial current monitor)
    (receipt : Receipt input) (stored : next.report.final.receipts[index]? = some receipt)
    (source : Nonempty (LowerSource initial receipt.served.ticket.value.produced))
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (services : current.report.final.services <+: next.report.final.services)
    (outputRef : updated.refs.dataOutput = monitor.refs.dataOutput)
    (serviceRef : updated.refs.dataService = monitor.refs.dataService)
    (firstRef : updated.firstDataReceipt = some index) : SourceHistory initial next updated := by
  constructor
  · intro selected reference
    obtain ⟨produced, found, origin⟩ := history.output selected (outputRef.symm.trans reference)
    exact ⟨produced, prefix_lookup outputs found, origin⟩
  · intro selected reference
    obtain ⟨served, found, origin⟩ := history.service selected (serviceRef.symm.trans reference)
    exact ⟨served, prefix_lookup services found, origin⟩
  · intro selected reference
    have same : index = selected := Option.some.inj (firstRef.symm.trans reference)
    subst selected
    exact ⟨receipt, stored, source⟩


variable {retries : Nat} {actual : Step input} {released : Bool}

def RetriedSource.ofRetry {live : CampusTCPGapProgressState.Live initial current retries released}
    (value : CampusTCPGapProgressRetry.Retry live actual) : RetriedSource initial value.facts.produced where
  prior := current
  actual
  move := value.move
  retained := live.anchor.retained
  retries
  flight := live.senderFlight
  operation := value.facts.localStep
  recorded := value.facts.application
  localBefore := value.facts.localBefore
  localEvent := value.facts.localEvent
  packet := value.facts.packet
  origin := value.facts.origin
  production := value.facts.production
  output := value.facts.output
  encoded := value.encoded

theorem seed_empty_unread (complete : H.Completed input.active input.passive) (actor : Actor) :
    (seed complete actor).core.received = [] := by
  cases actor
  · exact complete.certificate.empty.2.2.1
  · exact complete.certificate.empty.2.2.2.2.2

theorem seed_empty_pending (complete : H.Completed input.active input.passive) (actor : Actor) :
    (seed complete actor).pending = [] := by
  cases actor
  · exact complete.certificate.empty.1
  · exact complete.certificate.empty.2.2.2.1

theorem seed_empty_sent (complete : H.Completed input.active input.passive) (actor : Actor) :
    (seed complete actor).core.sent = [] := by
  cases actor
  · exact complete.certificate.empty.2.1
  · exact complete.certificate.empty.2.2.2.2.1

theorem endpoint_order (current : Cut input complete) (actor : Actor) :
    ApplicationTrace.Chronological (applicationSteps current.endpoints actor) := by
  cases actor
  · exact current.endpoints.client.ordered
  · exact current.endpoints.server.ordered

theorem Completed.receives (_done : CampusTCPGapProgressRetire.Completed initial current retries) :
    Nonempty (CampusTCPFacts.Receives current.report (applicationSteps current.endpoints sender) sender.other
      (applicationSteps current.endpoints sender.other)) := by
  have actual := CampusTCPRecoveryRoundOrigins.Report.receives current.report complete current.endpoints current.connection sender.other
  cases sender <;> exact actual

theorem Completed.read_origin (done : CampusTCPGapProgressRetire.Completed initial current retries)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    Nonempty (CampusTCPGapFacts.ReadOrigin current.report (seed complete sender)
      (applicationSteps current.endpoints sender) sender.other (applicationSteps current.endpoints sender.other)
      done.operation index byte) := by
  obtain ⟨receives⟩ := Completed.receives done
  have history : ApplicationTrace.DeliveryHistory (applicationSteps current.endpoints sender)
      (applicationSteps current.endpoints sender.other) :=
    ⟨endpoint_order current sender, endpoint_order current sender.other, receives.delivered⟩
  obtain ⟨member, _, event, read⟩ := done.history.exact_read
  apply CampusTCPGapFacts.read_origin (endpoint_chain current sender.other) (endpoint_chain current sender) history receives
    (seed_empty_unread complete sender.other) (seed_empty_held complete sender.other)
    (seed_empty_sent complete sender) (seed_empty_pending complete sender)
    done.operation member (lower ++ upper).length event index byte
  rw [read]
  exact selected

theorem Completed.compliant (_done : CampusTCPGapProgressRetire.Completed initial current retries)
    (prior : cut.report.compliant = true) (suffix : List (Step input))
    (history : current.report.steps = cut.report.steps ++ suffix)
    (passed : ∀ actual ∈ suffix, actual.result.passed = true) : current.report.compliant = true :=
  CampusTCPRecoveryRoundOrigins.compliant_of_suffix cut.report current.report current.supported prior suffix history passed

theorem Completed.read_permissions (done : CampusTCPGapProgressRetire.Completed initial current retries)
    (prior : cut.report.compliant = true) (suffix : List (Step input))
    (history : current.report.steps = cut.report.steps ++ suffix)
    (passed : ∀ actual ∈ suffix, actual.result.passed = true)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : CampusTCPGapFacts.ReadOrigin current.report (seed complete sender)
      (applicationSteps current.endpoints sender) sender.other (applicationSteps current.endpoints sender.other)
      done.operation index byte,
      CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served := by
  obtain ⟨origin⟩ := Completed.read_origin done index byte selected
  refine ⟨origin, ?_⟩
  exact CampusTCPRoundOrigins.service_permissions current.report (Completed.compliant done prior suffix history passed)
    origin.delivery.service.joint.step origin.delivery.service.joint.member origin.delivery.receive.receipt.served
    origin.delivery.service.present origin.delivery.receive.receipt.emission origin.delivery.receive.receipt.emitted


private theorem original_accepted (original : Original cut sender lower) :
    original.attempt.step.result.decision = .accepted (.send lower.length) := by
  cases original.attempt.origin with
  | send count policy event accepted actual =>
    have same := Netlib.Protocol.TCP.ApplicationTrace.Event.send.inj (event.symm.trans original.event)
    simpa only [same.1] using accepted
  | retry count policy event accepted actual => rw [original.event] at event; cases event
  | ack policy event accepted actual => rw [original.event] at event; cases event
  | dispatchAck policy event accepted actual => rw [original.event] at event; cases event

private theorem batch_prior_balance (initial : GapInitial cut sender lower upper) :
    initial.write.prior.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.written = initial.write.prior.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.emitted := by
  have chain := endpoint_chain cut sender
  rw [initial.lowerSource.attempt.same] at chain
  have preceding := chain.cut.1
  rw [initial.write.lowerSplit] at preceding
  have balance := preceding.cut.1.pending
  simpa only [seed_empty_pending complete sender, initial.write.emptyPending, List.nil_append, List.append_nil] using balance

structure SelectedWriteOrigin (initial : GapInitial cut sender lower upper) (attempt : T.OutputAt steps)
    (index : Nat) (byte : UInt8) where
  origin : ApplicationTrace.AttemptByteOrigin (seed complete sender) steps attempt index byte
  writer : origin.writer = initial.write.writer
  bytes : origin.bytes = lower ++ upper

private def selected_original_origin (initial : GapInitial cut sender lower upper)
    (original : Original cut sender payload) (writerLater : List T.Step)
    (split : original.attempt.prior = initial.write.prior ++ initial.write.writer :: writerLater)
    (writerIndex index : Nat) (byte : UInt8)
    (selected : payload[index]? = some byte) (writerByte : (lower ++ upper)[writerIndex]? = some byte)
    (position : (original.attempt.prior.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.emitted).length + index =
      (initial.write.prior.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.written).length + writerIndex) :
    SelectedWriteOrigin initial original.attempt index byte := by
  have noRetry : ApplicationTrace.NoRetry original.attempt.step := by
    intro policy timeout
    rw [original.event] at timeout
    cases timeout
  let provenance : ApplicationTrace.AttemptByteOrigin (seed complete sender) (applicationSteps cut.endpoints sender)
      original.attempt index byte := {
    prefixBytes := original.attempt.prior.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.emitted
    rangePrefix := by
      rw [original.payload, List.flatMap_append, List.flatMap_cons, original.emitted, List.flatMap_nil, List.append_nil]
      exact List.prefix_refl _
    sequence := original.attempt.coordinate (endpoint_chain cut sender) noRetry
    original := original.attempt
    originalIndex := index, count := payload.length, policy := true, originalEvent := original.event
    originalAccepted := original_accepted original
    originalByte := by rw [original.payload]; exact selected
    originalPosition := rfl
    noLater := Nat.le_refl _
    retryEarlier := by intro policy timeout; exact False.elim (noRetry policy timeout)
    writerPrior := initial.write.prior, writer := initial.write.writer, writerLater, writerSplit := split
    bytes := lower ++ upper, writtenCount := lower.length + upper.length, writerIndex
    writerEvent := initial.write.event, writerAccepted := initial.write.accepted, writerByte, writerPosition := position
    writerEarlier := original.attempt.prior_before (endpoint_order cut sender) initial.write.writer (by rw [split]; simp) }
  exact ⟨provenance, rfl, rfl⟩

def lower_write_origin (initial : GapInitial cut sender lower upper) (index : Nat) (byte : UInt8)
    (selected : lower[index]? = some byte) : SelectedWriteOrigin initial initial.lowerSource.attempt index byte := by
  apply selected_original_origin initial initial.lowerSource initial.write.toLower initial.write.lowerSplit index index byte selected
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp selected).1]
    exact selected
  · rw [initial.write.lower_coordinate, batch_prior_balance]

def upper_write_origin (initial : GapInitial cut sender lower upper) (index : Nat) (byte : UInt8)
    (selected : upper[index]? = some byte) : SelectedWriteOrigin initial initial.upperSource.attempt index byte := by
  apply selected_original_origin initial initial.upperSource
    (initial.write.toLower ++ initial.lowerSource.attempt.step :: initial.write.toUpper) initial.write.upperSplit
    (lower.length + index) index byte selected
  · rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact selected
  · rw [initial.write.upper_coordinate, batch_prior_balance]
    omega

theorem Step.receipt_service (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .deliver index bytes policy)
    (stored : current.report.final.services[index]? = some served)
    (present : actual.result.receipt = some receipt) : receipt.served = served := by
  have found := (CampusTCPFacts.deliver_origin actual index bytes policy event receipt present).2.2
  rw [before] at found
  exact Option.some.inj (found.symm.trans stored)

theorem SourceHistory.output_actual (history : SourceHistory initial current monitor)
    (reference : monitor.refs.dataOutput = some index) (stored : current.report.final.outputs[index]? = some produced) :
    Nonempty (LowerSource initial produced) ∧ ∃ actual ∈ current.report.steps, actual.result.output = some produced := by
  refine ⟨history.output_source reference stored, ?_⟩
  obtain ⟨actual, member, output, _, _⟩ := CampusTCPOrigins.Report.outputs_origin current.report produced (List.mem_of_getElem? stored)
  exact ⟨actual, member, output⟩


theorem application_retained (retained : cut.report.steps <+: current.report.steps) (actor : Actor) :
    applicationSteps cut.endpoints actor <+: applicationSteps current.endpoints actor := by
  obtain ⟨extra, history⟩ := retained
  have trace := CampusTCPRoundReport.Report.suffix cut.report current.report current.supported current.finished history.symm
  have retainedSteps := CampusTCPRecoveryRoundOrigins.Trace.application_prefix trace actor
  simpa only [cut.connection, current.connection, CampusTCPRoundPhaseHistory.connectionSteps] using retainedSteps

private def extend_output (value : ApplicationTrace.OutputAt before) (retained : before <+: after) :
    ApplicationTrace.OutputAt after where
  prior := value.prior
  step := value.step
  later := value.later ++ after.drop before.length
  same := by
    obtain ⟨extra, history⟩ := retained
    rw [← history, List.drop_left]
    exact (congrArg (fun steps => steps ++ extra) value.same).trans (by simp only [List.append_assoc, List.cons_append])
  output := value.output
  origin := value.origin

private theorem prefix_before {past prior later : List ApplicationTrace.Step} {operation : ApplicationTrace.Step}
    (retained : past <+: prior ++ operation :: later)
    (earlier : ∀ old ∈ past, old.stamp < operation.stamp) : past <+: prior := by
  apply List.prefix_of_prefix_length_le retained (List.prefix_append _ _)
  apply Nat.le_of_not_lt
  intro short
  have found : (prior ++ operation :: later)[prior.length]? = some operation := by simp
  obtain ⟨extra, history⟩ := retained
  rw [← history, List.getElem?_append_left short] at found
  have impossible := earlier operation (List.mem_of_getElem? found)
  omega

theorem RetriedSource.earlier (source : RetriedSource initial produced) :
    ∀ old ∈ applicationSteps cut.endpoints sender, old.stamp < source.operation.stamp := by
  have updates := CampusTCPRecoveryRoundOrigins.Step.application_history source.actual sender
  rw [← source.move.final, source.move.after.connection, source.move.beforeEq, source.prior.connection] at updates
  simp only [CampusTCPRoundPhaseHistory.connectionSteps, source.recorded, CampusTCPRecoveryRoundOrigins.localSteps, ite_true] at updates
  have ordered := endpoint_order source.move.after sender
  rw [updates] at ordered
  intro old member
  exact (List.pairwise_append.mp ordered).2.2 old ((application_retained source.retained sender).subset member)
    source.operation (by simp)

def RetriedSource.write_origin (source : RetriedSource initial produced)
    (retained : cut.report.steps <+: current.report.steps)
    (attempt : ApplicationTrace.OutputAt (applicationSteps current.endpoints sender))
    (step : attempt.step = source.operation) (packet : attempt.output = source.packet)
    (index : Nat) (byte : UInt8) (selected : lower[index]? = some byte) :
    SelectedWriteOrigin initial attempt index byte := by
  let base := (lower_write_origin initial index byte selected).origin
  let original := extend_output base.original (application_retained retained sender)
  have past : applicationSteps cut.endpoints sender <+: attempt.prior := by
    have retainedSteps := application_retained retained sender
    rw [attempt.same] at retainedSteps
    apply prefix_before retainedSteps
    intro old member
    rw [step]
    exact source.earlier old member
  have range : base.prefixBytes ++ source.packet.packet.segment.payload <+:
      (attempt.prior ++ [attempt.step]).flatMap ApplicationTrace.Step.emitted := by
    have payload := Endpoint.emitAt_payload _ _ _ _ source.encoded
    rw [payload]
    have retainedSteps := initial.lowerSource.attempt.emitted_prefix (by
      intro policy timeout
      rw [initial.lowerSource.event] at timeout
      cases timeout)
    rw [initial.lowerSource.payload] at retainedSteps
    have whole := past.trans (List.prefix_append attempt.prior [attempt.step])
    have mapped : (applicationSteps cut.endpoints sender).flatMap ApplicationTrace.Step.emitted <+:
        (attempt.prior ++ [attempt.step]).flatMap ApplicationTrace.Step.emitted := by
      obtain ⟨extra, history⟩ := whole
      exact ⟨extra.flatMap ApplicationTrace.Step.emitted, by rw [← history, List.flatMap_append]⟩
    exact retainedSteps.trans mapped
  have before : initial.lowerSource.attempt.step.stamp < attempt.step.stamp := by
    rw [step]
    exact source.earlier _ initial.lowerSource.attempt.member
  have fields := Endpoint.emitAt_transport _ _ _ _ source.encoded
  let provenance : ApplicationTrace.AttemptByteOrigin (seed complete sender) (applicationSteps current.endpoints sender)
      attempt index byte := {
    prefixBytes := base.prefixBytes
    rangePrefix := by rw [packet]; exact range
    sequence := by
      rw [packet, fields.2.1, source.flight.headSequence]
      exact base.sequence
    original
    originalIndex := base.originalIndex, count := base.count, policy := base.policy
    originalEvent := base.originalEvent, originalAccepted := base.originalAccepted, originalByte := base.originalByte
    originalPosition := base.originalPosition
    noLater := Nat.le_of_lt before
    retryEarlier := by intro _ _; exact before
    writerPrior := base.writerPrior, writer := base.writer, writerLater := base.writerLater
    writerSplit := base.writerSplit, bytes := base.bytes, writtenCount := base.writtenCount, writerIndex := base.writerIndex
    writerEvent := base.writerEvent, writerAccepted := base.writerAccepted, writerByte := base.writerByte
    writerPosition := base.writerPosition, writerEarlier := base.writerEarlier }
  exact ⟨provenance, rfl, rfl⟩


private def extend_origin (origin : ApplicationTrace.AttemptByteOrigin state before attempt index byte)
    (retained : before <+: after) : ApplicationTrace.AttemptByteOrigin state after (extend_output attempt retained) index byte where
  prefixBytes := origin.prefixBytes
  rangePrefix := origin.rangePrefix
  sequence := origin.sequence
  original := extend_output origin.original retained
  originalIndex := origin.originalIndex
  count := origin.count
  policy := origin.policy
  originalEvent := origin.originalEvent
  originalAccepted := origin.originalAccepted
  originalByte := origin.originalByte
  originalPosition := origin.originalPosition
  noLater := origin.noLater
  retryEarlier := origin.retryEarlier
  writerPrior := origin.writerPrior
  writer := origin.writer
  writerLater := origin.writerLater
  writerSplit := origin.writerSplit
  bytes := origin.bytes
  writtenCount := origin.writtenCount
  writerIndex := origin.writerIndex
  writerEvent := origin.writerEvent
  writerAccepted := origin.writerAccepted
  writerByte := origin.writerByte
  writerPosition := origin.writerPosition
  writerEarlier := origin.writerEarlier

private theorem output_prior_eq (left right : ApplicationTrace.OutputAt steps)
    (ordered : ApplicationTrace.Chronological steps) (same : left.step = right.step) : left.prior = right.prior := by
  have unique : steps.Nodup := ordered.imp (fun {a b} before equal => by cases equal; exact Nat.lt_irrefl _ before)
  have first : steps[left.prior.length]? = some left.step := by exact (congrArg (fun list => list[left.prior.length]?) left.same).trans (by simp)
  have second : steps[right.prior.length]? = some right.step := by exact (congrArg (fun list => list[right.prior.length]?) right.same).trans (by simp)
  have length : left.prior.length = right.prior.length := unique.eq_of_getElem?_eq
    (List.getElem?_eq_some_iff.mp first).1 (by rw [first, second, same])
  have leftPrefix : left.prior <+: steps := ⟨_, left.same.symm⟩
  have rightPrefix : right.prior <+: steps := ⟨_, right.same.symm⟩
  rw [List.prefix_iff_eq_take.mp leftPrefix, List.prefix_iff_eq_take.mp rightPrefix, length]

private theorem output_eq (left right : ApplicationTrace.OutputAt steps)
    (ordered : ApplicationTrace.Chronological steps) (same : left.step = right.step) (packet : left.output = right.output) :
    left = right := by
  have prior := output_prior_eq left right ordered same
  cases left with
  | mk p s l h o r =>
    cases right with
    | mk q t m k v w =>
      dsimp only at same packet prior
      cases prior
      cases same
      cases packet
      have tail : l = m := by
        have equality := congrArg (fun steps => steps.drop p.length) (h.symm.trans k)
        simpa only [List.drop_left, List.cons.injEq, true_and] using equality
      cases tail
      rfl

private def produced_step : Produced input.active input.passive → Option T.Step
  | .application _ operation _ _ => some operation
  | .startup .. => none

theorem LowerSource.write_origin (source : LowerSource initial produced)
    (retained : cut.report.steps <+: current.report.steps)
    (attempt : ApplicationTrace.OutputAt (applicationSteps current.endpoints sender))
    (production : produced = .application sender attempt.step attempt.output attempt.origin)
    (member : produced ∈ current.report.final.outputs)
    (index : Nat) (byte : UInt8) (selected : lower[index]? = some byte) :
    ∃ actual ∈ current.report.steps, actual.result.output = some produced ∧ Nonempty (SelectedWriteOrigin initial attempt index byte) := by
  obtain ⟨actual, inside, output, _, _⟩ := CampusTCPOrigins.Report.outputs_origin current.report produced member
  refine ⟨actual, inside, output, ?_⟩
  cases source with
  | original same =>
    have equal := production.symm.trans (same.trans initial.lowerSource.application)
    have step : attempt.step = initial.lowerSource.attempt.step := Option.some.inj (congrArg produced_step equal)
    have packet : attempt.output = initial.lowerSource.attempt.output := congrArg Produced.output equal
    let retainedSteps := application_retained retained sender
    let base := lower_write_origin initial index byte selected
    let extended : SelectedWriteOrigin initial (extend_output initial.lowerSource.attempt retainedSteps) index byte :=
      ⟨extend_origin base.origin retainedSteps, base.writer, base.bytes⟩
    have sameAttempt := output_eq attempt (extend_output initial.lowerSource.attempt retainedSteps) (endpoint_order current sender) step packet
    exact ⟨sameAttempt.symm ▸ extended⟩
  | retry source =>
    have equal := production.symm.trans source.production
    have step : attempt.step = source.operation := Option.some.inj (congrArg produced_step equal)
    have packet : attempt.output = source.packet := congrArg Produced.output equal
    exact ⟨source.write_origin retained attempt step packet index byte selected⟩

theorem upper_current_write_origin (initial : GapInitial cut sender lower upper)
    (retained : cut.report.steps <+: current.report.steps)
    (attempt : ApplicationTrace.OutputAt (applicationSteps current.endpoints sender))
    (step : attempt.step = initial.upperSource.attempt.step) (packet : attempt.output = initial.upperSource.attempt.output)
    (index : Nat) (byte : UInt8) (selected : upper[index]? = some byte) :
    Nonempty (SelectedWriteOrigin initial attempt index byte) := by
  let retainedSteps := application_retained retained sender
  let base := upper_write_origin initial index byte selected
  let extended : SelectedWriteOrigin initial (extend_output initial.upperSource.attempt retainedSteps) index byte :=
    ⟨extend_origin base.origin retainedSteps, base.writer, base.bytes⟩
  have sameAttempt := output_eq attempt (extend_output initial.upperSource.attempt retainedSteps) (endpoint_order current sender) step packet
  exact ⟨sameAttempt.symm ▸ extended⟩


private theorem initial_releases_empty (initial : GapInitial cut sender lower upper) :
    (applicationSteps cut.endpoints sender.other).filter CampusTCPRecoveryRoundHistory.nonemptyRelease = [] := by
  have frontier := (endpoint_chain cut sender.other).receive_history.frontier
  rw [initial.receiver.frontier, ApplicationTrace.receiveAllocations_released] at frontier
  have zero : ((applicationSteps cut.endpoints sender.other).flatMap ApplicationTrace.Step.releasedPayload).length = 0 := by omega
  have empty := List.length_eq_zero_iff.mp zero
  apply List.filter_eq_nil_iff.mpr
  intro operation member
  have quiet := (List.flatMap_eq_nil_iff.mp empty) operation member
  simp only [CampusTCPRecoveryRoundHistory.nonemptyRelease, quiet, List.isEmpty_nil,
    Bool.not_true, Bool.false_eq_true, not_false_eq_true]

theorem read_release_first (done : CampusTCPGapProgressEvidence.Done initial allowance current monitor retries)
    (first : CampusTCPGapProgressEvidence.FirstReceipt initial current) (same : done.first = some first)
    (origin : CampusTCPGapFacts.ReadOrigin current.report (seed complete sender)
      (applicationSteps current.endpoints sender) sender.other (applicationSteps current.endpoints sender.other)
      done.completed.operation index byte) : origin.read.release = first.operation := by
  have selected : done.completed.history.streams.first = some first.operation := by
    rw [done.firstOperation, same]
    rfl
  have releases : (applicationSteps current.endpoints sender.other).filter CampusTCPRecoveryRoundHistory.nonemptyRelease =
      [first.operation] := by
    rw [done.completed.history.steps, List.filter_append, initial_releases_empty initial,
      List.nil_append, done.completed.history.streams.releases, selected]
    rfl
  have prior : origin.read.release ∈ origin.read.prior := by
    rw [origin.read.releaseSplit]
    simp
  have member : origin.read.release ∈ applicationSteps current.endpoints sender.other := by
    have inside : origin.read.release ∈ origin.read.prior ++ done.completed.operation :: origin.read.later :=
      List.mem_append_left _ prior
    exact Eq.mpr (congrArg (fun list => origin.read.release ∈ list) origin.read.split) inside
  have nonempty : origin.read.release.releasedPayload ≠ [] := by
    intro empty
    have chosen := origin.read.releaseByte
    rw [empty] at chosen
    cases chosen
  have chosen : origin.read.release ∈
      (applicationSteps current.endpoints sender.other).filter CampusTCPRecoveryRoundHistory.nonemptyRelease := by
    apply List.mem_filter.mpr
    exact ⟨member, by
      simp only [CampusTCPRecoveryRoundHistory.nonemptyRelease,
        List.isEmpty_eq_false_iff.mpr nonempty, Bool.not_false]⟩
  rw [releases] at chosen
  exact List.mem_singleton.mp chosen



private theorem Trace.outputs_prefix (trace : Trace input before events steps after remaining) : before.outputs <+: after.outputs := by
  induction trace with
  | done state => exact List.prefix_refl _
  | stop actual blocked rest =>
    rw [CampusTCPOrigins.output_history actual]
    exact List.prefix_append _ _
  | next actual supported rest ih =>
    apply List.IsPrefix.trans _ ih
    rw [CampusTCPOrigins.output_history actual]
    exact List.prefix_append _ _

private theorem Trace.output_member (trace : Trace input before events steps after remaining)
    (actual : Step input) (member : actual ∈ steps) (output : actual.result.output = some produced) : produced ∈ after.outputs := by
  induction trace with
  | done state => cases member
  | stop head blocked rest =>
    have same := List.mem_singleton.mp member
    subst actual
    rw [CampusTCPOrigins.output_history head, output]
    simp
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst actual
      apply (Trace.outputs_prefix rest).subset
      rw [CampusTCPOrigins.output_history head, output]
      simp
    · exact ih member

private theorem delivery_production
    (delivery : CampusTCPFacts.ApplicationDelivery current.report (applicationSteps current.endpoints sender) sender.other operation) :
    delivery.receive.receipt.served.ticket.value.produced =
      .application sender delivery.source.step delivery.source.output delivery.source.origin := by
  obtain ⟨actor, source, packet, origin, production, other, step, output⟩ := delivery.applicationSource
  have actorEq : actor = sender := by cases sender <;> exact other
  rw [actorEq] at production
  subst source
  subst packet
  exact production

private theorem delivery_source_member
    (delivery : CampusTCPFacts.ApplicationDelivery current.report (applicationSteps current.endpoints sender) sender.other operation) :
    delivery.receive.receipt.served.ticket.value.produced ∈ current.report.final.outputs := by
  obtain ⟨actual, _, _, _, member, _, output, _⟩ := delivery.lineage
  exact Trace.output_member current.report.trace actual member output

structure SelectedReadOrigin (initial : GapInitial cut sender lower upper) (current : Cut input complete)
    (reader : T.Step) (index : Nat) (byte : UInt8) where
  read : CampusTCPGapFacts.ReadOrigin current.report (seed complete sender)
    (applicationSteps current.endpoints sender) sender.other (applicationSteps current.endpoints sender.other) reader index byte
  selected : SelectedWriteOrigin initial read.attempt read.read.origin.localIndex byte
  producer : Step input
  member : producer ∈ current.report.steps
  output : producer.result.output = some read.delivery.receive.receipt.served.ticket.value.produced


private theorem member_before_reader (ordered : ApplicationTrace.Chronological operations)
    (split : operations = prior ++ reader :: later) (member : operation ∈ operations)
    (earlier : operation.stamp < reader.stamp) : operation ∈ prior := by
  rw [split] at member ordered
  rcases List.mem_append.mp member with before | after
  · exact before
  · rcases List.mem_cons.mp after with same | laterMember
    · rw [same] at earlier
      omega
    · have pairs := (List.pairwise_append.mp ordered).2.1
      have opposite := (List.pairwise_cons.mp pairs).1 operation laterMember
      omega

private theorem nonempty_allocation (operation : ApplicationTrace.Step) (nonempty : operation.releasedPayload ≠ []) :
    ∃ allocation : ApplicationTrace.ActualAllocation operation, operation.allocation = some allocation := by
  cases transition : operation.storeTransition with
  | stutter state empty => exact False.elim (nonempty empty)
  | accepted allocation => exact ⟨allocation, by simp only [ApplicationTrace.Step.allocation, transition]⟩

theorem read_issuer_cases (done : CampusTCPGapProgressEvidence.Done initial allowance current monitor retries)
    (first : CampusTCPGapProgressEvidence.FirstReceipt initial current) (same : done.first = some first)
    (origin : CampusTCPGapFacts.ReadOrigin current.report (seed complete sender)
      (applicationSteps current.endpoints sender) sender.other (applicationSteps current.endpoints sender.other)
      done.completed.operation index byte) :
    origin.read.origin.origin.issuer = first.operation ∨
      origin.read.origin.origin.issuer = initial.receiver.source.origin.issuer := by
  have releaseEq := read_release_first done first same origin
  have chain := endpoint_chain current sender.other
  have order := endpoint_order current sender.other
  have originMember := origin.read.origin.origin.issuer_member
  have issuerEarlier : origin.read.origin.origin.issuer.stamp < done.completed.operation.stamp := by
    have before := origin.receiptBeforeRelease
    have reader := origin.read.earlier
    omega
  have issuerPrior := member_before_reader order origin.read.split originMember issuerEarlier
  have firstPrior : first.operation ∈ origin.read.prior := by
    rw [← releaseEq, origin.read.releaseSplit]
    simp
  have firstMember : first.operation ∈ applicationSteps current.endpoints sender.other := by
    rw [origin.read.split]
    exact List.mem_append_left _ firstPrior
  have upperMember : initial.receiver.source.origin.issuer ∈ applicationSteps current.endpoints sender.other := by
    have oldMember : initial.receiver.source.origin.issuer ∈
        CampusTCPRoundPhaseHistory.connectionSteps cut.report.final.connection sender.other := by
      simpa only [cut.connection, CampusTCPRoundPhaseHistory.connectionSteps] using initial.receiver.source.origin.member
    obtain ⟨actual, member, recorded⟩ := CampusTCPRecoveryRoundOrigins.Report.application_origin cut.report sender.other
      initial.receiver.source.origin.issuer oldMember
    have stored := CampusTCPRecoveryRoundOrigins.Report.application_member current.report actual
      (done.completed.anchor.member member) sender.other initial.receiver.source.origin.issuer recorded
    simpa only [current.connection, CampusTCPRoundPhaseHistory.connectionSteps] using stored
  have beforeReader := chain
  rw [origin.read.split] at beforeReader
  have preceding := beforeReader.cut.1
  have readerCounter : done.completed.operation.before.receiveStore.nextID = 2 := by
    simpa only [ite_true] using done.completed.readerFacts.nextID
  have issuerBound : origin.read.origin.origin.issuer.before.receiveStore.nextID < 2 := by
    have bound := preceding.receive_history.counter_upper origin.read.origin.origin.allocation.store
      (ApplicationTrace.receiveAllocations_selected _ issuerPrior _ origin.read.origin.origin.selected)
    rw [origin.read.origin.origin.allocation.before, readerCounter] at bound
    exact bound
  have firstNonempty : first.operation.releasedPayload ≠ [] := by
    rw [first.released]
    exact List.append_ne_nil_of_left_ne_nil initial.lowerNonempty upper
  obtain ⟨firstAllocation, firstSelected⟩ := nonempty_allocation first.operation firstNonempty
  have firstBound : first.operation.before.receiveStore.nextID < 2 := by
    have bound := preceding.receive_history.counter_upper firstAllocation.store
      (ApplicationTrace.receiveAllocations_selected _ firstPrior _ firstSelected)
    rw [firstAllocation.before, readerCounter] at bound
    exact bound
  have upperCounter : initial.receiver.source.origin.issuer.before.receiveStore.nextID = 0 :=
    initial.receiver.source.origin.fields.2.2.1.symm.trans initial.receiver.receipt
  have firstCounter : first.operation.before.receiveStore.nextID = 1 := by
    by_cases one : first.operation.before.receiveStore.nextID = 1
    · exact one
    · have zero : first.operation.before.receiveStore.nextID = 0 := by omega
      have equal := ApplicationTrace.ActualAllocation.unique chain firstAllocation initial.receiver.source.origin.allocation
        firstMember upperMember firstSelected initial.receiver.source.origin.selected (zero.trans upperCounter.symm)
      have absent := List.filter_eq_nil_iff.mp (initial_releases_empty initial)
        initial.receiver.source.origin.issuer initial.receiver.source.origin.member
      apply False.elim
      apply absent
      rw [← equal]
      simp only [CampusTCPRecoveryRoundHistory.nonemptyRelease, List.isEmpty_eq_false_iff.mpr firstNonempty, Bool.not_false]
  by_cases zero : origin.read.origin.origin.issuer.before.receiveStore.nextID = 0
  · right
    exact ApplicationTrace.ActualAllocation.unique chain origin.read.origin.origin.allocation initial.receiver.source.origin.allocation
      originMember upperMember origin.read.origin.origin.selected initial.receiver.source.origin.selected (zero.trans upperCounter.symm)
  · left
    have one : origin.read.origin.origin.issuer.before.receiveStore.nextID = 1 := by omega
    exact ApplicationTrace.ActualAllocation.unique chain origin.read.origin.origin.allocation firstAllocation
      originMember firstMember origin.read.origin.origin.selected firstSelected (one.trans firstCounter.symm)



theorem LowerSource.payload (source : LowerSource initial produced) : produced.source.packet.segment.payload = lower := by
  cases source with
  | original same =>
    rw [same, initial.lowerSource.application]
    exact initial.lowerSource.payload
  | retry source =>
    rw [source.production]
    exact Endpoint.emitAt_payload _ _ _ _ source.encoded

private def selected_read (origin : CampusTCPGapFacts.ReadOrigin current.report (seed complete sender)
    (applicationSteps current.endpoints sender) sender.other (applicationSteps current.endpoints sender.other) reader index byte)
    (selected : SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte)
    (actual : Step input) (member : actual ∈ current.report.steps)
    (output : actual.result.output = some origin.delivery.receive.receipt.served.ticket.value.produced) :
    SelectedReadOrigin initial current reader index byte where
  read := { origin with provenance := ⟨selected.origin⟩ }
  selected
  producer := actual
  member
  output


theorem FirstReceipt.delivery_same
    (first : CampusTCPGapProgressEvidence.FirstReceipt initial current)
    (delivery : CampusTCPFacts.ApplicationDelivery current.report (applicationSteps current.endpoints sender) sender.other operation)
    (same : operation = first.operation) :
    delivery.receive.receipt = first.receipt := by
  have nonempty : first.operation.releasedPayload ≠ [] := by
    rw [first.released]
    intro empty
    exact initial.lowerNonempty (List.append_eq_nil_iff.mp empty).1
  obtain ⟨packet, received⟩ : ∃ packet, first.operation.event = .receive packet := by
    cases event : first.operation.event
    all_goals first
      | exact ⟨_, rfl⟩
      | simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, event,
          ne_eq, not_true_eq_false] at nonempty
  obtain ⟨actual, member, present⟩ := CampusTCPRecoveryRoundOrigins.Report.receipt_origin current.report first.receipt
    (List.mem_of_getElem? first.stored)
  have mapped := ((CampusTCPRecoveryRoundOrigins.Step.receipt_application actual first.receipt present).2).symm.trans first.application
  obtain ⟨actor, recorded⟩ : ∃ actor, actual.result.application = some (actor, first.operation) := by
    cases selected : actual.result.application with
    | none => simp only [selected, Option.map_none, reduceCtorEq] at mapped
    | some pair =>
      rcases pair with ⟨actor, operation⟩
      have same : operation = first.operation := by simpa only [selected, Option.map_some, Option.some.injEq] using mapped
      exact ⟨actor, by simp only [same]⟩
  obtain ⟨_, _, _, _, _, _, _, _, stamp, _, _⟩ := CampusTCPRecoveryRoundOrigins.Step.receive_origin
    actual actor first.operation recorded packet received
  let actualAt : CampusTCPFacts.At current.report operation.stamp :=
    ⟨actual, member, stamp.symm.trans (congrArg ApplicationTrace.Step.stamp same).symm⟩
  have unique : delivery.receive.joint.step = actual := CampusTCPFacts.At.unique delivery.receive.joint actualAt
  have received : actual.result.receipt = some delivery.receive.receipt := by
    simpa only [unique] using delivery.receive.recorded
  exact Option.some.inj (received.symm.trans present)


theorem held_delivery_source (retained : cut.report.steps <+: current.report.steps)
    (geometry : CampusTCPGapProgressReceiver.Geometry initial)
    (delivery : CampusTCPFacts.ApplicationDelivery current.report (applicationSteps current.endpoints sender)
      sender.other operation) (same : operation = initial.receiver.source.origin.issuer) :
    delivery.source.step = initial.upperSource.attempt.step ∧ delivery.source.output = initial.upperSource.attempt.output := by
  let old := initial.receiver.source.delivery
  let actual : CampusTCPFacts.At current.report operation.stamp :=
    ⟨old.receive.joint.step, retained.subset old.receive.joint.member,
      old.receive.joint.time.trans (congrArg ApplicationTrace.Step.stamp same).symm⟩
  have jointEq := delivery.receive.joint.unique actual
  have receiptEq : delivery.receive.receipt = old.receive.receipt := by
    apply Option.some.inj
    exact delivery.receive.recorded.symm.trans (by rw [jointEq]; exact old.receive.recorded)
  obtain ⟨newActor, newStep, newPacket, newOrigin, newProduction, _, newStepEq, _⟩ := delivery.applicationSource
  obtain ⟨oldActor, oldStep, oldPacket, oldOrigin, oldProduction, _, oldStepEq, _⟩ := old.applicationSource
  have produced : Produced.application (active := input.active) (passive := input.passive) newActor newStep newPacket newOrigin =
      Produced.application oldActor oldStep oldPacket oldOrigin := by
    rw [← newProduction, receiptEq]
    exact oldProduction
  have stepEq : newStep = oldStep := (Produced.application.inj produced).2.1
  have sourceEq : delivery.source.step = initial.upperSource.attempt.step :=
    newStepEq.trans (stepEq.trans (oldStepEq.symm.trans geometry.upperSource))
  refine ⟨sourceEq, ?_⟩
  have newOutput := delivery.source.origin.actual
  rw [sourceEq] at newOutput
  exact Option.some.inj (newOutput.symm.trans initial.upperSource.attempt.origin.actual)


theorem Done.read_origin_selected
    (done : CampusTCPGapProgressEvidence.Done initial allowance current monitor retries)
    (sources : SourceHistory initial current monitor)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    Nonempty (SelectedReadOrigin initial current done.completed.operation index byte) := by
  obtain ⟨first, firstEq⟩ : ∃ first, done.first = some first := by
    have present := done.completed.history.streams.present
    rw [done.firstOperation] at present
    cases found : done.first with
    | none => simp only [found, Option.map_none, Option.isSome_none, Bool.false_eq_true] at present
    | some first => exact ⟨first, rfl⟩
  obtain ⟨origin⟩ := Completed.read_origin done.completed index byte selected
  have sourceByte : origin.attempt.output.packet.segment.payload[origin.read.origin.localIndex]? = some byte := by
    rw [← origin.path.fields.1]
    exact origin.read.origin.input_byte
  rcases read_issuer_cases done first firstEq origin with lowerSource | upperSource
  · have receiptEq : origin.delivery.receive.receipt = first.receipt := by
      exact FirstReceipt.delivery_same first origin.delivery lowerSource
    have reference : monitor.firstDataReceipt = some first.index := by rw [done.firstRef, firstEq]; rfl
    obtain ⟨source⟩ := sources.first_source reference first.stored
    rw [← receiptEq] at source
    have production := delivery_production origin.delivery
    rw [← origin.actualSource] at production
    have payload := source.payload
    rw [production] at payload
    change origin.attempt.output.packet.segment.payload = lower at payload
    rw [payload] at sourceByte
    obtain ⟨actual, member, output, ⟨written⟩⟩ := source.write_origin done.completed.anchor.retained origin.attempt production
      (delivery_source_member origin.delivery) origin.read.origin.localIndex byte sourceByte
    exact ⟨selected_read origin written actual member output⟩
  · have source : origin.attempt.step = initial.upperSource.attempt.step ∧
        origin.attempt.output = initial.upperSource.attempt.output := by
      rw [origin.actualSource]
      exact held_delivery_source done.completed.anchor.retained done.completed.readerFacts.geometry origin.delivery upperSource
    rw [source.2, initial.upperSource.payload] at sourceByte
    obtain ⟨written⟩ := upper_current_write_origin initial done.completed.anchor.retained origin.attempt source.1 source.2
      origin.read.origin.localIndex byte sourceByte
    obtain ⟨actual, member, output, _, _⟩ := CampusTCPOrigins.Report.outputs_origin current.report
      origin.delivery.receive.receipt.served.ticket.value.produced (delivery_source_member origin.delivery)
    exact ⟨selected_read origin written actual member output⟩

end Netlib.Check.CampusTCPGapProgressOrigins
