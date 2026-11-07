import Netlib.Check.CampusTCPOrigins

/-!
# Packet custody in the checked campus history

Each packet comes from an actual output or gateway emission.
Only an explicit drop consumes the link-loss count.
Pending packets do not establish loss or eventual delivery.
-/

namespace Netlib.Check.CampusTCPCustodyFacts

namespace M
export CampusTCPModel (Input State Step Trace Report Event Transit Custody)
end M
namespace C
export Netlib.Theory.PacketCustody (History Item State mint copy resolve)
end C

open CampusTCPModel

private theorem mapError_ok (value : Except ε α) (map : ε → ε') (output : α)
    (computed : value.mapError map = .ok output) : value = .ok output := by
  cases value <;> simp_all [Except.mapError]

private theorem prepare_history (before : M.State input) (event : M.Event) (after : M.Custody input)
    (computed : prepareCustody before event = .ok after) (history : C.History before.custody) : C.History after := by
  cases event <;> simp only [prepareCustody] at computed
  all_goals repeat' first
    | (solve | cases computed; exact history)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
    | (solve | cases computed; exact .copy history _ (mapError_ok _ _ _ (by assumption)))
    | (solve | cases computed; exact .resolve history _ (mapError_ok _ _ _ (by assumption)))

private theorem finish_history (before : M.State input) (effect : Effect input) (custody : M.Custody input)
    (history : C.History custody) : C.History (finishCustody before effect custody) := by
  unfold finishCustody
  cases effect.output <;> cases effect.service <;> simp only
  · exact history
  · split
    · exact history
    · exact .mint history _
  · exact .mint history _
  · split
    · exact .mint history _
    · exact .mint (.mint history _) _

theorem Step.history (step : M.Step input) (prior : C.History step.before.custody) :
    C.History step.result.state.custody := by
  obtain ⟨effect, custody, _, prepared, result⟩ := step.transaction
  rw [result]
  exact finish_history _ _ _ (prepare_history _ _ _ prepared prior)

theorem Trace.history (trace : M.Trace input initial events steps final remaining)
    (prior : C.History initial.custody) : C.History final.custody := by
  induction trace with
  | done state => exact prior
  | stop head _ _ => exact Step.history head prior
  | next head _ _ ih => exact ih (Step.history head prior)

theorem Report.history (report : M.Report input events) : C.History report.final.custody :=
  Trace.history report.trace .initial

theorem Trace.each_history (trace : M.Trace input initial events steps final remaining)
    (prior : C.History initial.custody) : ∀ step ∈ steps, C.History step.before.custody := by
  induction trace with
  | done state => simp
  | stop head _ _ => intro step member; simpa only [List.mem_singleton.mp member] using prior
  | next head _ _ ih =>
    intro step member
    rcases List.mem_cons.mp member with same | tail
    · simpa only [same] using prior
    · exact ih (Step.history head prior) step tail

theorem Report.each_history (report : M.Report input events) (step : M.Step input) (member : step ∈ report.steps) :
    C.History step.before.custody := Trace.each_history report.trace .initial step member

theorem Report.valid (report : M.Report input events) : report.final.custody.Valid :=
  (Report.history report).valid

theorem Report.accounted (report : M.Report input events) :
    report.final.custody.pending.length + report.final.custody.resolutions.length = report.final.custody.nextID :=
  (Report.history report).accounted

def dropEvent : M.Event → Bool
  | .dropPacket _ => true
  | _ => false

private theorem prepare_drop_count (before : M.State input) (event : M.Event) (after : M.Custody input)
    (computed : prepareCustody before event = .ok after) :
    after.dropped = before.custody.dropped + if dropEvent event then 1 else 0 := by
  cases event <;> simp only [prepareCustody] at computed
  all_goals repeat' first
    | (solve | cases computed; simp [dropEvent])
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
    | (solve | cases computed; simp [dropEvent, Theory.PacketCustody.State.dropped,
        Theory.PacketCustody.Resolved.count])

private theorem finish_drop_count (before : M.State input) (effect : Effect input) (custody : M.Custody input) :
    (finishCustody before effect custody).dropped = custody.dropped := by
  cases effect.output <;> cases effect.service <;> simp only [finishCustody]
  all_goals repeat' first
    | (solve | rfl)
    | (split)
    | (simp only [Theory.PacketCustody.State.dropped, Theory.PacketCustody.mint_count])

theorem Step.drop_count (step : M.Step input) :
    step.result.state.custody.dropped = step.before.custody.dropped + if dropEvent step.event then 1 else 0 := by
  obtain ⟨effect, custody, _, prepared, result⟩ := step.transaction
  rw [result]
  exact (finish_drop_count _ _ _).trans (prepare_drop_count _ _ _ prepared)

theorem Trace.drop_count (trace : M.Trace input initial events steps final remaining) :
    final.custody.dropped = initial.custody.dropped + steps.countP (fun step => dropEvent step.event) := by
  induction trace with
  | done state => simp
  | stop head _ _ => simpa only [List.countP_cons, List.countP_nil, Nat.zero_add] using Step.drop_count head
  | next head _ _ ih =>
    have current := Step.drop_count head
    simp only [List.countP_cons]
    omega

theorem Report.drop_count (report : M.Report input events) :
    report.final.custody.dropped = report.steps.countP (fun step => dropEvent step.event) := by
  simpa only [Input.initial, Theory.PacketCustody.State.initial, Theory.PacketCustody.State.dropped,
    Theory.PacketCustody.State.count, List.countP_nil, Nat.zero_add] using Trace.drop_count report.trace

theorem Step.drop (step : M.Step input) (id : Nat) (event : step.event = .dropPacket id) :
    ∃ result : Theory.PacketCustody.Resolved step.before.custody id .dropped,
      C.resolve step.before.custody id .dropped = .ok result ∧ step.result.state.custody = result.state := by
  obtain ⟨effect, custody, core, prepared, result⟩ := step.transaction
  rw [event] at core prepared
  simp only [processCore, pure, Except.pure, Except.ok.injEq] at core
  subst effect
  simp only [prepareCustody] at prepared
  cases resolved : C.resolve step.before.custody id .dropped with
  | error reason => simp [resolved, Except.mapError, bind, Except.bind] at prepared
  | ok chosen =>
    simp only [resolved, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at prepared
    subst custody
    exact ⟨chosen, rfl, by rw [result]; rfl⟩

theorem Step.copy (step : M.Step input) (id : Nat) (event : step.event = .copyPacket id) :
    ∃ result : Theory.PacketCustody.Copied step.before.custody id,
      C.copy step.before.custody id = .ok result ∧ step.result.state.custody = result.state := by
  obtain ⟨effect, custody, core, prepared, result⟩ := step.transaction
  rw [event] at core prepared
  simp only [processCore, pure, Except.pure, Except.ok.injEq] at core
  subst effect
  simp only [prepareCustody] at prepared
  cases copied : C.copy step.before.custody id with
  | error reason => simp [copied, Except.mapError, bind, Except.bind] at prepared
  | ok chosen =>
    simp only [copied, Except.mapError, bind, Except.bind, pure, Except.pure] at prepared
    split at prepared
    · cases prepared
    · simp only [Except.ok.injEq] at prepared
      subst custody
      exact ⟨chosen, rfl, by rw [result]; rfl⟩

theorem Step.drop_not_repeat (step : M.Step input) (id : Nat) (event : step.event = .dropPacket id)
    (prior : C.History step.before.custody) : C.resolve step.result.state.custody id .dropped = .error .notPending := by
  obtain ⟨result, _, state⟩ := Step.drop step id event
  rw [state]
  exact result.no_repeat prior.valid .dropped

private theorem finish_output (before : M.State input) (effect : Effect input) (custody : M.Custody input)
    (produced : Produced input.active input.passive) (present : effect.output = some produced) :
    ∃ item ∈ (finishCustody before effect custody).pending,
      item.id = custody.nextID ∧ item.value.parent = none ∧
      item.value.payload = .ingress before.outputs.length produced := by
  let item := Theory.PacketCustody.newItem custody (.ingress before.outputs.length produced)
  have member : item ∈ (C.mint custody (.ingress before.outputs.length produced)).pending := by
    rw [Theory.PacketCustody.mint_pending]
    exact List.mem_append_right _ (by simp [item])
  refine ⟨item, ?_, rfl, rfl, rfl⟩
  unfold finishCustody
  simp only [present]
  cases effect.service <;> simp only
  · exact member
  · split
    · exact member
    · rw [Theory.PacketCustody.mint_pending]
      exact List.mem_append_left _ member

theorem Step.output_packet (step : M.Step input) (produced : Produced input.active input.passive)
    (present : step.result.output = some produced) :
    ∃ item ∈ step.result.state.custody.pending,
      item.value.parent = none ∧ item.value.payload = .ingress step.before.outputs.length produced := by
  obtain ⟨effect, custody, _, _, result⟩ := step.transaction
  have output : effect.output = some produced := by simpa only [result] using present
  obtain ⟨item, member, _, parent, payload⟩ := finish_output step.before effect custody produced output
  exact ⟨item, by simpa only [result] using member, parent, payload⟩

private theorem finish_emission (before : M.State input) (effect : Effect input) (custody : M.Custody input)
    (served : Served input) (present : effect.service = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission) :
    ∃ item ∈ (finishCustody before effect custody).pending,
      item.id = custody.nextID + effect.output.toList.length ∧ item.value.parent = none ∧
      item.value.payload = .link before.services.length served emission emitted := by
  have minted (state : M.Custody input) :
      ∃ item ∈ (C.mint state (.link before.services.length served emission emitted)).pending,
        item.id = state.nextID ∧ item.value.parent = none ∧
        item.value.payload = .link before.services.length served emission emitted := by
    refine ⟨Theory.PacketCustody.newItem state _, ?_, rfl, rfl, rfl⟩
    rw [Theory.PacketCustody.mint_pending]
    exact List.mem_append_right _ (by simp)
  unfold finishCustody
  cases output : effect.output <;> simp only [present]
  all_goals
    split
    · rename_i missing
      rw [emitted] at missing
      contradiction
    · rename_i packet found
      have same : packet = emission := Option.some.inj (found.symm.trans emitted)
      subst packet
      simpa only [output, Option.toList_none, Option.toList_some, List.length_nil,
        List.length_cons, Nat.add_zero, Theory.PacketCustody.mint_nextID] using
        minted (match effect.output with
          | none => custody
          | some produced => C.mint custody (.ingress before.outputs.length produced))

theorem Step.emission_packet (step : M.Step input) (served : Served input) (present : step.result.service = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission) :
    ∃ item ∈ step.result.state.custody.pending,
      item.value.parent = none ∧ item.value.payload = .link step.before.services.length served emission emitted ∧
      item.value.payload.bytes = emission.bytes := by
  obtain ⟨effect, custody, _, _, result⟩ := step.transaction
  have service : effect.service = some served := by simpa only [result] using present
  obtain ⟨item, member, _, parent, payload⟩ := finish_emission step.before effect custody served service emission emitted
  exact ⟨item, by simpa only [result] using member, parent, payload, by rw [payload]; rfl⟩

def Sourced (state : M.State input) : M.Transit input → Prop
  | .ingress index produced => state.outputs[index]? = some produced
  | .link index served _ _ => state.services[index]? = some served

def Sources (state : M.State input) : Prop :=
  ∀ item ∈ state.custody.items, Sourced state item.value.payload

private theorem append_lookup (values extra : List α) (index : Nat) (value : α)
    (found : values[index]? = some value) : (values ++ extra)[index]? = some value := by
  have bound : index < values.length := List.getElem?_eq_some_iff.mp found |>.1
  rw [List.getElem?_append_left bound, found]

private theorem sourced_mono (before after : M.State input) (packet : M.Transit input)
    (outputs : ∃ extra, after.outputs = before.outputs ++ extra)
    (services : ∃ extra, after.services = before.services ++ extra)
    (prior : Sourced before packet) : Sourced after packet := by
  obtain ⟨moreOutputs, outputs⟩ := outputs
  obtain ⟨moreServices, services⟩ := services
  cases packet with
  | ingress index produced =>
    change after.outputs[index]? = some produced
    rw [outputs]
    exact append_lookup _ _ _ _ prior
  | link index served emission emitted =>
    change after.services[index]? = some served
    rw [services]
    exact append_lookup _ _ _ _ prior

private theorem prepare_sources (before : M.State input) (event : M.Event) (after : M.Custody input)
    (computed : prepareCustody before event = .ok after) (prior : Sources before) :
    ∀ item ∈ after.items, Sourced before item.value.payload := by
  cases event <;> simp only [prepareCustody] at computed
  all_goals repeat' first
    | (solve | cases computed; exact prior)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
    | (solve | cases computed; intro item member; exact prior item ((by assumption : Theory.PacketCustody.Resolved _ _ _).items_perm.mem_iff.mpr member))
  all_goals
    cases computed
    rename_i result _ _
    intro item member
    rw [result.items] at member
    rcases List.mem_append.mp member with old | fresh
    · exact prior item old
    · have same := List.mem_singleton.mp fresh
      subst item
      exact prior result.source result.member

private theorem finish_sources (before after : M.State input) (effect : Effect input) (custody : M.Custody input)
    (outputs : after.outputs = before.outputs ++ effect.output.toList)
    (services : after.services = before.services ++ effect.service.toList)
    (prior : ∀ item ∈ custody.items, Sourced after item.value.payload) :
    ∀ item ∈ (finishCustody before effect custody).items, Sourced after item.value.payload := by
  have extend (state : M.Custody input) (packet : M.Transit input)
      (old : ∀ item ∈ state.items, Sourced after item.value.payload) (source : Sourced after packet) :
      ∀ item ∈ (C.mint state packet).items, Sourced after item.value.payload := by
    intro item member
    rw [Theory.PacketCustody.mint_items] at member
    rcases List.mem_append.mp member with member | member
    · exact old item member
    · have same := List.mem_singleton.mp member
      subst item
      exact source
  have endpoint : ∀ produced, effect.output = some produced →
      Sourced after (.ingress before.outputs.length produced) := by
    intro produced present
    change after.outputs[before.outputs.length]? = some produced
    rw [outputs, present]
    simp
  have gateway : ∀ served, effect.service = some served → ∀ emission emitted,
      Sourced after (.link before.services.length served emission emitted) := by
    intro served present emission emitted
    change after.services[before.services.length]? = some served
    rw [services, present]
    simp
  unfold finishCustody
  cases produced : effect.output <;> cases served : effect.service <;> simp only
  · exact prior
  · split
    · exact prior
    · exact extend _ _ prior (gateway _ served _ _)
  · exact extend _ _ prior (endpoint _ produced)
  · split
    · exact extend _ _ prior (endpoint _ produced)
    · exact extend _ _ (extend _ _ prior (endpoint _ produced)) (gateway _ served _ _)

theorem Step.sources (step : M.Step input) (prior : Sources step.before) : Sources step.result.state := by
  obtain ⟨effect, custody, _, prepared, result⟩ := step.transaction
  have outputs := CampusTCPOrigins.output_history step
  have services := CampusTCPOrigins.service_history step
  have old := prepare_sources _ _ _ prepared prior
  have monotone : ∀ item ∈ custody.items, Sourced step.result.state item.value.payload := by
    intro item member
    exact sourced_mono _ _ _ ⟨step.result.output.toList, outputs⟩
      ⟨step.result.service.toList, services⟩ (old item member)
  have finalOutputs : step.result.state.outputs = step.before.outputs ++ effect.output.toList := by
    simpa only [result] using outputs
  have finalServices : step.result.state.services = step.before.services ++ effect.service.toList := by
    simpa only [result] using services
  have final := finish_sources _ _ _ _ finalOutputs finalServices monotone
  simpa only [result, Sources] using final

theorem Trace.sources (trace : M.Trace input initial events steps final remaining) (prior : Sources initial) : Sources final := by
  induction trace with
  | done state => exact prior
  | stop head _ _ => exact Step.sources head prior
  | next head _ _ ih => exact ih (Step.sources head prior)

theorem Report.sources (report : M.Report input events) : Sources report.final :=
  Trace.sources report.trace (by simp [Sources, Theory.PacketCustody.State.items,
    Theory.PacketCustody.State.pending, Theory.PacketCustody.State.initial, Theory.Outstanding.State.initial, Input.initial])

theorem Trace.each_sources (trace : M.Trace input initial events steps final remaining)
    (prior : Sources initial) : ∀ step ∈ steps, Sources step.before := by
  induction trace with
  | done state => simp
  | stop head _ _ => intro step member; simpa only [List.mem_singleton.mp member] using prior
  | next head _ _ ih =>
    intro step member
    rcases List.mem_cons.mp member with same | tail
    · simpa only [same] using prior
    · exact ih (Step.sources head prior) step tail

theorem Report.each_sources (report : M.Report input events) (step : M.Step input) (member : step ∈ report.steps) :
    Sources step.before :=
  Trace.each_sources report.trace (by simp [Sources, Theory.PacketCustody.State.items,
    Theory.PacketCustody.State.pending, Theory.PacketCustody.State.initial, Theory.Outstanding.State.initial, Input.initial]) step member


private theorem prepare_assign (before : M.State input) (index : Nat) (ingress : I.InterfaceRef)
    (after : M.Custody input) (computed : prepareCustody before (.assign index ingress) = .ok after) :
    ∃ id, ∃ result : Theory.PacketCustody.Resolved before.custody id .assigned,
      before.custody.pendingID (Transit.ingressAt index) = some id ∧
      C.resolve before.custody id .assigned = .ok result ∧ after = result.state := by
  simp only [prepareCustody] at computed
  cases selected : before.custody.pendingID (Transit.ingressAt index) with
  | none => simp [selected, throw, throwThe, MonadExceptOf.throw] at computed
  | some id =>
    simp only [selected] at computed
    cases resolved : C.resolve before.custody id .assigned with
    | error reason => simp [resolved, Except.mapError, bind, Except.bind] at computed
    | ok result =>
      simp only [resolved, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
      exact ⟨id, result, rfl, resolved, computed.symm⟩

private theorem prepare_deliver (before : M.State input) (index : Nat) (bytes : List UInt8) (policy : Bool)
    (after : M.Custody input) (computed : prepareCustody before (.deliver index bytes policy) = .ok after) :
    ∃ id, ∃ result : Theory.PacketCustody.Resolved before.custody id .delivered,
      before.custody.pendingID (Transit.linkAt index) = some id ∧
      C.resolve before.custody id .delivered = .ok result ∧ after = result.state ∧
      bytes = result.item.value.payload.bytes := by
  simp only [prepareCustody] at computed
  cases selected : before.custody.pendingID (Transit.linkAt index) with
  | none => simp [selected, throw, throwThe, MonadExceptOf.throw] at computed
  | some id =>
    simp only [selected] at computed
    cases resolved : C.resolve before.custody id .delivered with
    | error reason => simp [resolved, Except.mapError, bind, Except.bind] at computed
    | ok result =>
      simp only [resolved, Except.mapError, bind, Except.bind] at computed
      split at computed
      · rename_i same
        simp only [pure, Except.pure, Except.ok.injEq] at computed
        exact ⟨id, result, rfl, resolved, computed.symm, same⟩
      · cases computed

private theorem mint_absent (before : M.Custody input) (payload : M.Transit input) (id : Nat)
    (bounded : id < before.nextID) (absent : ∀ item ∈ before.pending, item.id ≠ id) :
    ∀ item ∈ (C.mint before payload).pending, item.id ≠ id := by
  intro item member
  rw [Theory.PacketCustody.mint_pending] at member
  rcases List.mem_append.mp member with old | current
  · exact absent item old
  · have same := List.mem_singleton.mp current
    rw [same, Theory.PacketCustody.newItem_id]
    omega

private theorem finish_absent (before : M.State input) (effect : Effect input) (custody : M.Custody input) (id : Nat)
    (bounded : id < custody.nextID) (absent : ∀ item ∈ custody.pending, item.id ≠ id) :
    ∀ item ∈ (finishCustody before effect custody).pending, item.id ≠ id := by
  unfold finishCustody
  cases effect.output <;> cases effect.service <;> simp only
  · exact absent
  · split
    · exact absent
    · exact mint_absent _ _ _ bounded absent
  · exact mint_absent _ _ _ bounded absent
  · split
    · exact mint_absent _ _ _ bounded absent
    · apply mint_absent
      · simpa only [Theory.PacketCustody.mint_nextID] using Nat.lt_trans bounded (Nat.lt_succ_self _)
      · exact mint_absent _ _ _ bounded absent

private theorem selected_predicate (before : M.Custody input) (predicate : M.Transit input → Bool)
    (id : Nat) (result : Theory.PacketCustody.Resolved before id disposition) (valid : before.Valid)
    (selected : before.pendingID predicate = some id) : predicate result.item.value.payload = true := by
  obtain ⟨item, member, same, property⟩ := before.pendingID_source predicate id selected
  rw [result.item_eq valid item member same]
  exact property

private theorem resolved_finish_absent (before : M.State input) (effect : Effect input) (id : Nat)
    (result : Theory.PacketCustody.Resolved before.custody id disposition) (valid : before.custody.Valid) :
    ∀ item ∈ (finishCustody before effect result.state).pending, item.id ≠ id := by
  apply finish_absent
  · have member : result.item.id ∈ before.custody.work.ids :=
      List.mem_map.mpr ⟨result.item, List.mem_append_right _ result.member, rfl⟩
    have bounded := valid.1.2 result.item.id member
    rw [result.nextID, ← result.selected]
    exact bounded
  · exact result.completed.no_pending_id valid.1

theorem Step.assign (step : M.Step input) (index : Nat) (ingress : I.InterfaceRef)
    (event : step.event = .assign index ingress) (prior : C.History step.before.custody) :
    ∃ id, ∃ result : Theory.PacketCustody.Resolved step.before.custody id .assigned,
      step.before.custody.pendingID (Transit.ingressAt index) = some id ∧
      C.resolve step.before.custody id .assigned = .ok result ∧
      Transit.ingressAt index result.item.value.payload = true ∧
      ∀ item ∈ step.result.state.custody.pending, item.id ≠ id := by
  obtain ⟨effect, custody, _, prepared, final⟩ := step.transaction
  rw [event] at prepared
  obtain ⟨id, result, selected, resolved, state⟩ := prepare_assign _ _ _ _ prepared
  refine ⟨id, result, selected, resolved, selected_predicate _ _ _ _ prior.valid selected, ?_⟩
  rw [final, state]
  exact resolved_finish_absent _ _ _ _ prior.valid

theorem Step.deliver (step : M.Step input) (index : Nat) (bytes : List UInt8) (policy : Bool)
    (event : step.event = .deliver index bytes policy) (prior : C.History step.before.custody) :
    ∃ id, ∃ result : Theory.PacketCustody.Resolved step.before.custody id .delivered,
      step.before.custody.pendingID (Transit.linkAt index) = some id ∧
      C.resolve step.before.custody id .delivered = .ok result ∧
      Transit.linkAt index result.item.value.payload = true ∧ bytes = result.item.value.payload.bytes ∧
      ∀ item ∈ step.result.state.custody.pending, item.id ≠ id := by
  obtain ⟨effect, custody, _, prepared, final⟩ := step.transaction
  rw [event] at prepared
  obtain ⟨id, result, selected, resolved, state, same⟩ := prepare_deliver _ _ _ _ _ prepared
  refine ⟨id, result, selected, resolved, selected_predicate _ _ _ _ prior.valid selected, same, ?_⟩
  rw [final, state]
  exact resolved_finish_absent _ _ _ _ prior.valid

theorem ingress_stage (packet : M.Transit input) (index : Nat) (selected : Transit.ingressAt index packet = true) :
    ∃ produced, packet = .ingress index produced := by
  cases packet with
  | ingress source produced =>
    have same : source = index := by simpa only [Transit.ingressAt, beq_iff_eq] using selected
    exact ⟨produced, by rw [same]⟩
  | link source served emission emitted => simp [Transit.ingressAt] at selected

theorem link_stage (packet : M.Transit input) (index : Nat) (selected : Transit.linkAt index packet = true) :
    ∃ served, ∃ emission, ∃ emitted, packet = .link index served emission emitted := by
  cases packet with
  | ingress source produced => simp [Transit.linkAt] at selected
  | link source served emission emitted =>
    have same : source = index := by simpa only [Transit.linkAt, beq_iff_eq] using selected
    exact ⟨served, emission, emitted, by rw [same]⟩

theorem Report.assignment_source (report : M.Report input events) (step : M.Step input) (member : step ∈ report.steps)
    (index : Nat) (ingress : I.InterfaceRef) (event : step.event = .assign index ingress) :
    ∃ id, ∃ result : Theory.PacketCustody.Resolved step.before.custody id .assigned, ∃ produced,
      C.resolve step.before.custody id .assigned = .ok result ∧
      result.item.value.payload = .ingress index produced ∧ step.before.outputs[index]? = some produced ∧
      ∀ item ∈ step.result.state.custody.pending, item.id ≠ id := by
  obtain ⟨id, result, _, computed, selected, absent⟩ := Step.assign step index ingress event (Report.each_history report step member)
  obtain ⟨produced, same⟩ := ingress_stage _ _ selected
  have sourced := Report.each_sources report step member result.item (List.mem_append_right _ result.member)
  rw [same] at sourced
  exact ⟨id, result, produced, computed, same, sourced, absent⟩

theorem Report.delivery_source (report : M.Report input events) (step : M.Step input) (member : step ∈ report.steps)
    (index : Nat) (bytes : List UInt8) (policy : Bool) (event : step.event = .deliver index bytes policy) :
    ∃ id, ∃ result : Theory.PacketCustody.Resolved step.before.custody id .delivered,
      ∃ served, ∃ emission, ∃ emitted,
      C.resolve step.before.custody id .delivered = .ok result ∧
      result.item.value.payload = .link index served emission emitted ∧ step.before.services[index]? = some served ∧
      bytes = emission.bytes ∧ ∀ item ∈ step.result.state.custody.pending, item.id ≠ id := by
  obtain ⟨id, result, _, computed, selected, bytesEq, absent⟩ := Step.deliver step index bytes policy event (Report.each_history report step member)
  obtain ⟨served, emission, emitted, same⟩ := link_stage _ _ selected
  have sourced := Report.each_sources report step member result.item (List.mem_append_right _ result.member)
  rw [same] at sourced bytesEq
  exact ⟨id, result, served, emission, emitted, computed, same, sourced, bytesEq, absent⟩

end Netlib.Check.CampusTCPCustodyFacts
