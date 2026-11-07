import Netlib.Check.CampusRevocationCompletion
import Netlib.Check.CampusRevocationDrainBound
import Netlib.Check.CampusRevocationHistory
import Netlib.Check.CampusRevocationTrigger

/-!
# A recorded session revocation certificate

One report retains authentication, both native installs, packet effects, and FIFO service.
The certificate selects a recorded completion cut within the static bound.
-/

namespace Netlib.Check.CampusRevocation

open Packet Protocol
open StatefulFailover (Gateway)
open CampusRevocationModel
open CampusRevocationTargets
open CampusRevocationControl

structure Result (report : Report input budget events) (cut bound : Nat)
    (targets : Targets input (stateAt input.initial report.steps cut).campus.authentication) where
  slot : Nat
  found : findCompletion report cut targets bound = some slot
  positive : 0 < bound
  trigger : CampusRevocationTrigger.triggerAt report.steps cut = true
  actions : CampusRevocationControl.actions report cut targets = true
  service : CampusRevocationControl.service report cut targets bound = true

variable {report : Report input budget events} {cut bound : Nat}
variable {targets : Targets input (stateAt input.initial report.steps cut).campus.authentication}

theorem Result.bounds (result : Result report cut bound targets) :
    cut ≤ result.slot ∧ result.slot ≤ deadline report cut bound ∧ result.slot ≤ report.steps.length := by
  have facts := findCompletion_facts report cut targets bound result.slot result.found
  exact ⟨facts.1, facts.2.1, facts.2.2.1⟩

def Result.current (result : Result report cut bound targets) : State :=
  stateAt input.initial report.steps result.slot

theorem Result.ready (result : Result report cut bound targets) : CampusRevocationControl.ready targets result.current = true :=
  (findCompletion_facts report cut targets bound result.slot result.found).2.2.2.1

theorem Result.empty (result : Result report cut bound targets) : result.current.queue.pending = [] :=
  (findCompletion_facts report cut targets bound result.slot result.found).2.2.2.2

theorem Result.revoked (result : Result report cut bound targets) :
    CampusRevocationTargets.revoked input (stateAt input.initial report.steps cut).campus.authentication = true :=
  CampusRevocationTrigger.report_triggerAt_revoked report cut result.trigger

theorem Result.installed (result : Result report cut bound targets) (gateway : Gateway) :
    result.current.campus.deployment.handoff.configurations gateway = targets.get gateway :=
  (installed_correct targets result.current gateway).mp ((ready_correct targets result.current).mp result.ready gateway)

theorem Result.authentication (result : Result report cut bound targets) :
    result.current.campus.authentication = (stateAt input.initial report.steps cut).campus.authentication :=
  authentication_at_after report cut targets result.actions result.slot result.bounds.1 result.bounds.2.2

theorem Result.binding (result : Result report cut bound targets) (entry : NetfilterNAT.Entry)
    (selected : (stateAt input.initial report.steps cut).campus.deployment.handoff.binding = some entry) :
    result.current.campus.deployment.handoff.binding = some entry :=
  binding_at_after report cut result.slot result.bounds.1 result.bounds.2.2 entry selected

theorem Result.history (result : Result report cut bound targets) :
    (Report.cut report result.slot result.bounds.2.2).steps = report.steps.take result.slot := rfl

theorem Result.delivered (result : Result report cut bound targets) :
    result.current.queue.delivered = arrivals (report.steps.take result.slot) := by
  have conservation := (report.trace.take result.slot result.bounds.2.2).conservation
  change result.current.queue.delivered ++ result.current.queue.pending =
    [] ++ [] ++ arrivals (report.steps.take result.slot) at conservation
  rw [result.empty] at conservation
  simpa only [List.append_nil, List.nil_append] using conservation

theorem Result.delivered_bytes (result : Result report cut bound targets) :
    result.current.queue.delivered.map Datagram.bytes =
      (arrivals (report.steps.take result.slot)).map Datagram.bytes :=
  congrArg (List.map Datagram.bytes) result.delivered

theorem Result.ready_after (result : Result report cut bound targets) (slot : Nat)
    (later : result.slot ≤ slot) (within : slot ≤ report.steps.length) :
    CampusRevocationControl.ready targets (stateAt input.initial report.steps slot) = true :=
  ready_at_after report cut targets result.actions result.slot slot result.bounds.1 later within result.ready

theorem Result.empty_after (result : Result report cut bound targets) (slot : Nat)
    (later : result.slot ≤ slot) (within : slot ≤ report.steps.length) :
    (stateAt input.initial report.steps slot).queue.pending = [] :=
  empty_at_after report cut targets result.actions result.revoked result.slot slot result.bounds.1 later within
    result.ready result.empty

theorem Result.future_arrivals (result : Result report cut bound targets) (slot : Nat)
    (later : result.slot ≤ slot) (actual : Step input budget) (found : report.steps[slot]? = some actual) :
    actual.effect.payload.arrivals = [] := by
  have within := (List.getElem?_eq_some_iff.mp found).1
  have installed := result.ready_after slot later (by omega)
  rw [← (report.trace.at_step found).1] at installed
  exact actual.arrivals_nil_of_ready targets result.revoked installed

theorem Result.future_served (result : Result report cut bound targets) (slot : Nat)
    (later : result.slot ≤ slot) (actual : Step input budget) (found : report.steps[slot]? = some actual) :
    actual.effect.served = [] :=
  served_nil_after report cut targets result.actions result.revoked result.slot slot result.bounds.1 later
    result.ready result.empty actual found

theorem Result.wire_output_none (result : Result report cut bound targets) (gateway : Gateway)
    (packet : Protocol.WireForwarding.Input) (outcome : Protocol.WireForwarding.Outcome packet.packet)
    (accepted : Protocol.WireForwarding.step (result.current.campus.deployment.handoff.configurations gateway).pipeline
      (result.current.campus.deployment.handoff.gateways.table gateway) packet = .ok outcome) :
    outcome.output = none := by
  rw [result.installed gateway] at accepted
  exact targets.wire_output_none result.revoked gateway _ packet outcome accepted

def complete (report : Report input budget events) (cut bound : Nat)
    (targets : Targets input (stateAt input.initial report.steps cut).campus.authentication)
    (positive : 0 < bound) (trigger : CampusRevocationTrigger.triggerAt report.steps cut = true)
    (permitted : CampusRevocationControl.actions report cut targets = true)
    (serviced : CampusRevocationControl.service report cut targets bound = true)
    (enough : deadline report cut bound ≤ report.steps.length) : Result report cut bound targets := by
  have closed := CampusRevocationTrigger.report_triggerAt_revoked report cut trigger
  have installed := ready_by report cut targets bound permitted serviced enough
  have empty := drain_by report cut targets bound permitted serviced closed enough
  have afterCut : cut ≤ deadline report cut bound := by unfold deadline; omega
  have witness := findCompletion_exists report cut targets bound (deadline report cut bound)
    afterCut (Nat.le_refl _) enough installed empty
  cases found : findCompletion report cut targets bound with
  | none =>
    have impossible : False := by
      obtain ⟨slot, selected⟩ := witness
      rw [found] at selected
      cases selected
    exact False.elim impossible
  | some slot => exact ⟨slot, found, positive, trigger, permitted, serviced⟩

structure Certificate (report : Report input budget events) (cut bound : Nat) where
  targets : Targets input (stateAt input.initial report.steps cut).campus.authentication
  result : Result report cut bound targets

def certify (report : Report input budget events) (cut bound : Nat)
    (primarySource standbySource : Check.ConntrackLifecycle.Config) :
    Except String (Certificate report cut bound) := do
  if positive : 0 < bound then
    if trigger : CampusRevocationTrigger.triggerAt report.steps cut = true then
      let targets ← Targets.check input (stateAt input.initial report.steps cut).campus.authentication
        primarySource standbySource budget
      if permitted : CampusRevocationControl.actions report cut targets = true then
        if serviced : CampusRevocationControl.service report cut targets bound = true then
          match found : findCompletion report cut targets bound with
          | none => throw "No completion is recorded within the revocation bound."
          | some slot => return ⟨targets, ⟨slot, found, positive, trigger, permitted, serviced⟩⟩
        else throw "The revocation trace violates its persistent service bound."
      else throw "The revocation trace violates its policy or observation contract."
    else throw "Select an actual Logoff, revoke, or close observation."
  else throw "The service bound must be positive."

end Netlib.Check.CampusRevocation
