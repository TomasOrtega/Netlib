import Netlib.Check.CampusTCPStartupJobDrainComplete
import Netlib.Check.CampusTCPRecoveryStartupCurrentSources

/-!
# Completed-startup delivery decreases the live job weight

The consumed link and any ACK response come from the same actual receipt.
-/

namespace Netlib.Check.CampusTCPStartupJobDrainDelivery

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs CampusTCPStartupJobDrain

namespace C
export TCPHandshakeRecovery (State Step Reachable Emission)
end C

variable {input : Input}

private structure DeliveryFields (before : State input) (current : C.State input.active input.passive)
    (source : Source input) (index : Nat) (bytes : List UInt8) (policy : Bool) (effect : Effect input) where
  actual : C.Step input.active input.passive
  beforeEq : actual.before = current
  event : actual.event = .receive source.occurrence.index bytes .rewrite policy
  recorded : effect.recovery = some actual
  work : effect.state.work = before.work
  service : effect.service = none
  output : ∀ produced, effect.output = some produced →
    ∃ emission, ∃ present : actual.result.output = some emission, produced = .recovery actual emission present

private theorem recovery_fields (connection : before.connection = .recovering current)
    (computed : runRecovery input before (.receive source.occurrence.index bytes .rewrite policy) = .ok result) :
    Nonempty (DeliveryFields before current source index bytes policy result) := by
  simp only [runRecovery, connection] at computed
  split at computed
  · cases computed
  · rename_i effect evaluatedAt
    cases effect with
    | mk state decision output receipt application =>
      cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
      all_goals
        subst result
        refine ⟨⟨_, rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
        intro produced present
        cases present <;> exact ⟨_, rfl, rfl⟩

private theorem delivery_fields (connection : before.connection = .recovering current)
    (selected : before.services[index]? = some served)
    (production : served.ticket.value.produced = source.produced)
    (computed : processCore input before (.deliver index bytes policy) = .ok effect) :
    Nonempty (DeliveryFields before current source index bytes policy effect) := by
  simp only [processCore, CampusTCPModel.get, selected, production,
    Source.produced, bind, Except.bind, pure, Except.pure] at computed
  repeat' first
    | (solve | cases computed)
    | (solve |
      have fields := recovery_fields (index := index) connection (by assumption)
      cases computed
      obtain ⟨fields⟩ := fields
      exact ⟨⟨fields.actual, fields.beforeEq, fields.event, fields.recorded,
        fields.work, fields.service, fields.output⟩⟩)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

def outputWeight (output : Option (Produced input.active input.passive)) : Nat :=
  (output.map (sourceWeight .ingress)).getD 0

private theorem delivery_delta (actual : Step input)
    (event : actual.event = .deliver index bytes policy)
    (history : Theory.PacketCustody.History actual.before.custody)
    (work : actual.result.state.work = actual.before.work) (service : actual.result.service = none) :
    ∃ id, ∃ resolved : Theory.PacketCustody.Resolved actual.before.custody id .delivered,
      actual.before.custody.pendingID (Transit.linkAt index) = some id ∧
      Theory.PacketCustody.resolve actual.before.custody id .delivered = .ok resolved ∧
      Transit.linkAt index resolved.item.value.payload = true ∧
      potential actual.result.state + packetWeight resolved.item =
        potential actual.before + outputWeight actual.result.output := by
  obtain ⟨id, resolved, selected, computed, link, bytesEq, _⟩ :=
    CampusTCPCustodyFacts.Step.deliver actual index bytes policy event history
  obtain ⟨effect, custody, core, prepared, final⟩ := actual.transaction
  rw [event] at prepared
  simp only [prepareCustody, selected, computed, Except.mapError, bind, Except.bind,
    bytesEq, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at prepared
  subst custody
  have finalService : effect.service = none := by simpa only [final] using service
  have custody : actual.result.state.custody =
      match actual.result.output with
      | none => resolved.state
      | some produced => Theory.PacketCustody.mint resolved.state (.ingress actual.before.outputs.length produced) := by
    rw [final]
    simp only [finishCustody, finalService]
    rfl
  have removed := resolved_weight (input := input) resolved
  refine ⟨id, resolved, selected, computed, link, ?_⟩
  rw [potential_rows, potential_rows, work, custody]
  cases produced : actual.result.output with
  | none =>
    simp only [outputWeight, Option.map_none, Option.getD_none]
    omega
  | some output =>
    have newWeight : packetWeight (Theory.PacketCustody.newItem resolved.state
        (.ingress actual.before.outputs.length output)) = sourceWeight .ingress output := rfl
    simp only [Theory.PacketCustody.mint_pending, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      newWeight, outputWeight, Option.map_some, Option.getD_some]
    omega

theorem Step.complete_delivery (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (connection : report.final.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (packets : ∀ item ∈ report.final.custody.pending, item.value.payload.isRecovery = true)
    (event : actual.event = .deliver index bytes policy) :
    ∃ id, ∃ resolved : Theory.PacketCustody.Resolved actual.before.custody id .delivered,
      Theory.PacketCustody.resolve actual.before.custody id .delivered = .ok resolved ∧
      actual.result.state.work = actual.before.work ∧ actual.result.service = none ∧
      potential actual.result.state + packetWeight resolved.item =
        potential actual.before + outputWeight actual.result.output ∧
      outputWeight actual.result.output < packetWeight resolved.item := by
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [before]
    exact CampusTCPCustodyFacts.Report.history report
  obtain ⟨id, resolved, selected, resolvedAt, link, bytesEq, _⟩ :=
    CampusTCPCustodyFacts.Step.deliver actual index bytes policy event history
  obtain ⟨served, emission, emitted, payload⟩ := CampusTCPCustodyFacts.link_stage _ _ link
  have recovery : served.ticket.value.produced.isRecovery = true := by
    have pending : resolved.item ∈ report.final.custody.pending := by rw [← before]; exact resolved.member
    have current := packets resolved.item pending
    simpa only [payload, Transit.isRecovery] using current
  obtain ⟨source, production⟩ : ∃ source : Source input, served.ticket.value.produced = source.produced := by
    cases production : served.ticket.value.produced with
    | startup => simp only [production, Produced.isRecovery, Bool.false_eq_true] at recovery
    | application => simp only [production, Produced.isRecovery, Bool.false_eq_true] at recovery
    | recovery step occurrence present => exact ⟨⟨step, occurrence, present⟩, rfl⟩
  let job : Job input := .link resolved.item index served emission emitted source production payload
  have pending : job.Pending report.final := by
    change resolved.item ∈ report.final.custody.pending
    rw [← before]
    exact resolved.member
  have occurrence := CampusTCPRecoveryStartupCurrentSources.Job.recovering_member report job pending connection
  change source.occurrence ∈ current.emissions at occurrence
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connection
  have sourceAt := reachable.history.source_of_member occurrence
  have serviceAt : actual.before.services[index]? = some served := by
    have sourced := CampusTCPCustodyFacts.Report.sources report resolved.item
      (List.mem_append_right _ (by rw [← before]; exact resolved.member))
    rw [payload] at sourced
    simpa only [CampusTCPCustodyFacts.Sourced, before] using sourced
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  rw [event] at computed
  obtain ⟨fields⟩ := delivery_fields (before := actual.before)
    (by rw [before]; exact connection) serviceAt production computed
  have work : actual.result.state.work = actual.before.work := by simpa only [final] using fields.work
  have service : actual.result.service = none := by simpa only [final] using fields.service
  obtain ⟨otherID, chosen, chosenSelected, chosenAt, _, delta⟩ := delivery_delta actual event history work service
  have sameID : otherID = id := Option.some.inj (chosenSelected.symm.trans selected)
  subst otherID
  have chosenEq : chosen = resolved := Except.ok.inj (chosenAt.symm.trans resolvedAt)
  subst chosen
  refine ⟨id, resolved, resolvedAt, work, service, delta, ?_⟩
  cases output : actual.result.output with
  | none =>
    have positive := packetWeight_positive resolved.item (by
      rw [payload, Transit.isRecovery, production]
      rfl)
    simpa only [outputWeight, output, Option.map_none, Option.getD_none] using positive
  | some produced =>
    have producedAt : effect.output = some produced := by simpa only [final] using output
    obtain ⟨response, present, productionEq⟩ := fields.output produced producedAt
    have recorded : actual.result.recovery = some fields.actual := by simpa only [final] using fields.recorded
    have actualOutput : actual.result.output = some (.recovery fields.actual response present) := output.trans (congrArg some productionEq)
    have connected : actual.before.connection = .recovering current := by rw [before]; exact connection
    obtain ⟨receipt, received, kind⟩ := CampusTCPStartupJobDrainComplete.Step.complete_response actual connected phase event
      fields.actual response present actualOutput
    obtain ⟨selectedReceipt, receivedAt, selectedAt, _, _, _⟩ := fields.actual.receive_receipt fields.event
    have receiptEq : selectedReceipt = receipt := Option.some.inj (receivedAt.symm.trans received)
    subst selectedReceipt
    have selectedSource : fields.actual.before.source source.occurrence.index = some source.occurrence := by
      rw [fields.beforeEq]
      exact sourceAt
    have sourceEq : receipt.source = source.occurrence := Option.some.inj (selectedAt.symm.trans selectedSource)
    rw [sourceEq] at kind
    rw [outputWeight, Option.map_some, Option.getD_some, productionEq, sourceWeight,
      packetWeight, payload]
    change stageWeight response.kind .ingress < sourceWeight .link served.ticket.value.produced
    rw [production]
    change stageWeight response.kind .ingress < stageWeight source.occurrence.kind .link
    rcases kind with ⟨originalKind, responseKind⟩ | ⟨originalKind, responseKind⟩
    · rw [originalKind, responseKind]
      decide
    · rw [originalKind, responseKind]
      decide

theorem Step.complete_delivery_strict (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (connection : report.final.connection = .recovering current)
    (phase : current.phase = .complete complete client server)
    (packets : ∀ item ∈ report.final.custody.pending, item.value.payload.isRecovery = true)
    (event : actual.event = .deliver index bytes policy) :
    potential actual.result.state < potential actual.before := by
  obtain ⟨_, _, _, _, _, delta, decreased⟩ := Step.complete_delivery actual report before connection phase packets event
  omega

end Netlib.Check.CampusTCPStartupJobDrainDelivery
