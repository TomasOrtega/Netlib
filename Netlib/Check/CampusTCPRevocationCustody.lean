import Netlib.Check.CampusTCPCustodyFacts
import Netlib.Check.CampusTCPStartupQueueBound
import Netlib.Theory.PacketCustodyFrontier

/-!
# The actual receiver-link frontier

Ingress responses stay outside the frontier. A delivery resolves the first
pending custody identity for its stored gateway service.
-/

namespace Netlib.Check.CampusTCPRevocationCustody

open CampusTCPModel

namespace C
export Theory.PacketCustody (Item State History Resolved resolve)
end C

variable {input : Input}

def isLink : Transit input → Bool
  | .ingress .. => false
  | .link .. => true

def frontier (state : CampusTCPModel.State input) : List (C.Item (Transit input)) :=
  state.custody.frontier isLink

def potential (state : CampusTCPModel.State input) : Nat := state.custody.frontierCount isLink

theorem potential_length (state : CampusTCPModel.State input) :
    potential state = (frontier state).length := state.custody.frontierCount_length isLink

theorem potential_zero (state : CampusTCPModel.State input) :
    potential state = 0 ↔ frontier state = [] := (state.custody.frontier_empty isLink).symm

theorem potential_le_queued (state : CampusTCPModel.State input) :
    potential state ≤ CampusTCPStartupQueueBound.queued state := by
  have bounded := state.custody.frontierCount_le_pending isLink
  unfold potential CampusTCPStartupQueueBound.queued
  omega

theorem linkAt_isLink (index : Nat) (packet : Transit input) (selected : Transit.linkAt index packet = true) :
    isLink packet = true := by
  cases packet <;> simp_all [Transit.linkAt, isLink]

theorem first_link (state : CampusTCPModel.State input) (item : C.Item (Transit input))
    (selected : (frontier state).head? = some item) :
    ∃ index served emission emitted,
      item.value.payload = .link index served emission emitted ∧
      state.custody.pendingID (Transit.linkAt index) = some item.id := by
  have member : item ∈ state.custody.frontier isLink := List.mem_of_head? selected
  have matching := ((state.custody.frontier_member isLink item).mp member).2
  cases packet : item.value.payload with
  | ingress index produced => simp only [packet, isLink, Bool.false_eq_true] at matching
  | link index served emission emitted =>
    refine ⟨index, served, emission, emitted, rfl, ?_⟩
    exact state.custody.frontier_head_subpredicate isLink (Transit.linkAt index)
      (linkAt_isLink index) item selected (by simp only [packet, Transit.linkAt, beq_self_eq_true])

theorem first_pending (state : CampusTCPModel.State input) (item : C.Item (Transit input))
    (selected : (frontier state).head? = some item) : item ∈ state.custody.pending :=
  ((state.custody.frontier_member isLink item).mp (List.mem_of_head? selected)).1

theorem first_delivery_prepares (state : CampusTCPModel.State input) (item : C.Item (Transit input))
    (history : C.History state.custody) (selected : (frontier state).head? = some item)
    (index : Nat) (served : Served input) (emission : W.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission)
    (payload : item.value.payload = .link index served emission emitted) :
    ∃ resolved : C.Resolved state.custody item.id .delivered,
      C.resolve state.custody item.id .delivered = .ok resolved ∧
      resolved.item = item ∧
      prepareCustody state (.deliver index emission.bytes true) = .ok resolved.state := by
  have pending := first_pending state item selected
  obtain ⟨resolved, computed⟩ := Theory.PacketCustody.resolve_completes state.custody item pending .delivered
  have exactItem := resolved.item_eq history.valid item pending rfl
  have selectedID : state.custody.pendingID (Transit.linkAt index) = some item.id :=
    state.custody.frontier_head_subpredicate isLink (Transit.linkAt index) (linkAt_isLink index)
      item selected (by simp only [payload, Transit.linkAt, beq_self_eq_true])
  refine ⟨resolved, computed, exactItem, ?_⟩
  simp only [prepareCustody, selectedID, computed, Except.mapError, bind, Except.bind,
    exactItem, payload, Transit.bytes, ↓reduceIte, pure, Except.pure]

theorem finish_frontier (before : CampusTCPModel.State input) (effect : Effect input) (custody : Custody input)
    (denied : ∀ served, effect.service = some served → served.evidence.output = none) :
    (finishCustody before effect custody).frontier isLink = custody.frontier isLink := by
  cases output : effect.output with
  | none =>
    cases service : effect.service with
    | none => simp only [finishCustody, output, service]
    | some served =>
      simp only [finishCustody, output, service]
      split
      · rfl
      · rename_i emission emitted
        rw [denied served service] at emitted
        cases emitted
  | some produced =>
    cases service : effect.service with
    | none =>
      simpa only [finishCustody, output, service] using
        Theory.PacketCustody.mint_frontier custody (.ingress before.outputs.length produced) isLink rfl
    | some served =>
      simp only [finishCustody, output, service]
      split
      · exact Theory.PacketCustody.mint_frontier custody (.ingress before.outputs.length produced) isLink rfl
      · rename_i emission emitted
        rw [denied served service] at emitted
        cases emitted

theorem finish_count (before : CampusTCPModel.State input) (effect : Effect input) (custody : Custody input)
    (denied : ∀ served, effect.service = some served → served.evidence.output = none) :
    (finishCustody before effect custody).frontierCount isLink = custody.frontierCount isLink := by
  rw [Theory.PacketCustody.State.frontierCount_length, finish_frontier before effect custody denied,
    ← Theory.PacketCustody.State.frontierCount_length]

theorem mint_ingress_count (custody : Custody input) (index : Nat)
    (produced : Produced input.active input.passive) :
    (Theory.PacketCustody.mint custody (.ingress index produced)).frontierCount isLink =
      custody.frontierCount isLink := by
  rw [Theory.PacketCustody.mint_frontierCount]
  rfl

theorem mint_link_count (custody : Custody input) (index : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission) :
    (Theory.PacketCustody.mint custody (.link index served emission emitted)).frontierCount isLink =
      custody.frontierCount isLink + 1 := by
  rw [Theory.PacketCustody.mint_frontierCount]
  rfl

theorem finish_count_le (before : CampusTCPModel.State input) (effect : Effect input) (custody : Custody input) :
    (finishCustody before effect custody).frontierCount isLink ≤ custody.frontierCount isLink + 1 := by
  unfold finishCustody
  cases effect.output <;> cases effect.service <;> simp only
  all_goals repeat' split
  all_goals try simp only [mint_link_count, mint_ingress_count]
  all_goals omega

private theorem prepare_count_le (before : CampusTCPModel.State input) (event : Event) (custody : Custody input)
    (nocopy : ∀ id, event ≠ .copyPacket id) (computed : prepareCustody before event = .ok custody) :
    custody.frontierCount isLink ≤ before.custody.frontierCount isLink := by
  cases event <;> simp only [prepareCustody] at computed
  all_goals repeat' first
    | (solve | cases computed; exact Nat.le_refl _)
    | (solve | cases computed)
    | (solve | exact False.elim (nocopy _ rfl))
    | (solve | cases computed; exact (by assumption : C.Resolved _ _ _).frontierCount_le isLink)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem mapError_ok (value : Except ε α) (map : ε → ε') (output : α)
    (computed : value.mapError map = .ok output) : value = .ok output := by
  cases value <;> simp_all [Except.mapError]

private theorem prepare_frontier_sublist (before : CampusTCPModel.State input) (event : Event) (custody : Custody input)
    (nocopy : ∀ id, event ≠ .copyPacket id) (computed : prepareCustody before event = .ok custody) :
    (custody.frontier isLink).Sublist (before.custody.frontier isLink) := by
  cases event <;> simp only [prepareCustody] at computed
  all_goals repeat' first
    | (solve | cases computed; exact .refl _)
    | (solve | cases computed)
    | (solve | exact False.elim (nocopy _ rfl))
    | (solve | cases computed; exact (by assumption : C.Resolved _ _ _).frontier_sublist (mapError_ok _ _ _ (by assumption)) isLink)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.potential_le_succ (actual : Step input) (nocopy : ∀ id, actual.event ≠ .copyPacket id) :
    potential actual.result.state ≤ potential actual.before + 1 := by
  obtain ⟨effect, custody, _, prepared, result⟩ := actual.transaction
  have preparation := prepare_count_le actual.before actual.event custody nocopy prepared
  have finished := finish_count_le actual.before effect custody
  rw [result]
  unfold potential
  exact Nat.le_trans finished (Nat.add_le_add_right preparation 1)

theorem Step.potential_nonincrease (actual : Step input) (nocopy : ∀ id, actual.event ≠ .copyPacket id)
    (denied : ∀ served, actual.result.service = some served → served.evidence.output = none) :
    potential actual.result.state ≤ potential actual.before := by
  obtain ⟨effect, custody, _, prepared, result⟩ := actual.transaction
  have deniedCore : ∀ served, effect.service = some served → served.evidence.output = none := by
    simpa only [result] using denied
  have preparation := prepare_count_le actual.before actual.event custody nocopy prepared
  rw [result]
  unfold potential
  rw [finish_count actual.before effect custody deniedCore]
  exact preparation

theorem Step.frontier_sublist (actual : Step input) (nocopy : ∀ id, actual.event ≠ .copyPacket id)
    (denied : ∀ served, actual.result.service = some served → served.evidence.output = none) :
    (frontier actual.result.state).Sublist (frontier actual.before) := by
  obtain ⟨effect, custody, _, prepared, result⟩ := actual.transaction
  have deniedCore : ∀ served, effect.service = some served → served.evidence.output = none := by
    simpa only [result] using denied
  have preparation := prepare_frontier_sublist actual.before actual.event custody nocopy prepared
  rw [result]
  unfold frontier
  rw [finish_frontier actual.before effect custody deniedCore]
  exact preparation

theorem Step.frontier_eq_of_potential_eq (actual : Step input) (nocopy : ∀ id, actual.event ≠ .copyPacket id)
    (denied : ∀ served, actual.result.service = some served → served.evidence.output = none)
    (equal : potential actual.result.state = potential actual.before) :
    frontier actual.result.state = frontier actual.before := by
  apply (Step.frontier_sublist actual nocopy denied).eq_of_length
  simpa only [potential_length] using equal

theorem Step.deliver_strict (actual : Step input) (history : C.History actual.before.custody)
    (index : Nat) (bytes : List UInt8) (policy : Bool) (event : actual.event = .deliver index bytes policy)
    (denied : ∀ served, actual.result.service = some served → served.evidence.output = none) :
    potential actual.result.state < potential actual.before := by
  obtain ⟨id, resolved, selected, computed, linked, bytesEq, _⟩ :=
    CampusTCPCustodyFacts.Step.deliver actual index bytes policy event history
  obtain ⟨effect, custody, _, prepared, result⟩ := actual.transaction
  have deniedCore : ∀ served, effect.service = some served → served.evidence.output = none := by
    simpa only [result] using denied
  rw [event] at prepared
  simp only [prepareCustody, selected, computed, Except.mapError, bind, Except.bind,
    bytesEq, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at prepared
  subst custody
  rw [result]
  unfold potential
  rw [finish_count actual.before effect resolved.state deniedCore]
  exact resolved.frontierCount_strict isLink (linkAt_isLink index _ linked)

theorem Step.drop_strict (actual : Step input) (id : Nat) (event : actual.event = .dropPacket id)
    (selected : ∀ item ∈ actual.before.custody.pending, item.id = id → isLink item.value.payload = true) :
    potential actual.result.state < potential actual.before := by
  obtain ⟨resolved, _, after⟩ := CampusTCPCustodyFacts.Step.drop actual id event
  have matching := selected resolved.item resolved.member resolved.selected
  change actual.result.state.custody.frontierCount isLink < actual.before.custody.frontierCount isLink
  rw [after]
  exact resolved.frontierCount_strict isLink matching

theorem first_drop_enabled (state : CampusTCPModel.State input) (item : C.Item (Transit input))
    (selected : (frontier state).head? = some item) :
    ∃ actual : Step input, actual.before = state ∧ actual.event = .dropPacket item.id ∧
      actual.result.supported = true ∧ actual.result.passed = true := by
  have pending := first_pending state item selected
  obtain ⟨resolved, computed⟩ := Theory.PacketCustody.resolve_completes state.custody item pending .dropped
  let effect : Effect input := { state := { state with custody := resolved.state, time := state.time + 1 } }
  have accepted : step input state (.dropPacket item.id) = .ok effect := by
    simp only [step, process, processCore, prepareCustody, computed, Except.mapError,
      bind, Except.bind, pure, Except.pure]
    rfl
  exact ⟨⟨state, .dropPacket item.id, effect, accepted⟩, rfl, rfl, rfl, rfl⟩

theorem Trace.potential_le_slots (trace : Trace input initial events steps final remaining)
    (nocopy : ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id) :
    potential final ≤ potential initial + steps.length := by
  induction trace with
  | done state => simp
  | stop head _ _ =>
    have bounded := Step.potential_le_succ head (nocopy head (by simp))
    simpa only [List.length_cons, List.length_nil] using bounded
  | next head _ rest ih =>
    have bounded := Step.potential_le_succ head (nocopy head (by simp))
    have later := ih (fun actual member => nocopy actual (List.mem_cons_of_mem _ member))
    simp only [List.length_cons]
    omega

theorem Trace.frontier_sublist (trace : Trace input initial events steps final remaining)
    (nocopy : ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id)
    (denied : ∀ actual ∈ steps, ∀ served,
      actual.result.service = some served → served.evidence.output = none) :
    (frontier final).Sublist (frontier initial) := by
  induction trace with
  | done state => exact .refl _
  | stop head _ _ =>
    exact Step.frontier_sublist head (nocopy head (by simp)) (denied head (by simp))
  | next head _ rest ih =>
    have current := Step.frontier_sublist head (nocopy head (by simp)) (denied head (by simp))
    have later := ih (fun actual member => nocopy actual (List.mem_cons_of_mem _ member))
      (fun actual member => denied actual (List.mem_cons_of_mem _ member))
    exact later.trans current

theorem Trace.frontier_empty (trace : Trace input initial events steps final remaining)
    (nocopy : ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id)
    (denied : ∀ actual ∈ steps, ∀ served,
      actual.result.service = some served → served.evidence.output = none)
    (empty : frontier initial = []) : frontier final = [] := by
  have preserved := Trace.frontier_sublist trace nocopy denied
  rw [empty] at preserved
  exact preserved.eq_of_length_le (by simp)

theorem Trace.queued_le_slots (trace : Trace input initial events steps final remaining)
    (nocopy : ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id) :
    CampusTCPStartupQueueBound.queued final ≤ CampusTCPStartupQueueBound.queued initial + steps.length := by
  induction trace with
  | done state => simp
  | stop head _ _ =>
    have bounded := CampusTCPStartupQueueBound.Step.queued_le head (nocopy head (by simp))
    have single : head.result.output.toList.length ≤ 1 := by cases head.result.output <;> simp
    simp only [List.length_cons, List.length_nil]
    omega
  | next head _ rest ih =>
    have bounded := CampusTCPStartupQueueBound.Step.queued_le head (nocopy head (by simp))
    have single : head.result.output.toList.length ≤ 1 := by cases head.result.output <;> simp
    have later := ih (fun actual member => nocopy actual (List.mem_cons_of_mem _ member))
    simp only [List.length_cons]
    omega

end Netlib.Check.CampusTCPRevocationCustody
