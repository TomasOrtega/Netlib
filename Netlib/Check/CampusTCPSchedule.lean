import Netlib.Check.CampusTCPModel
import Netlib.Theory.BoundedProgress

/-!
# Actual campus schedules as finite checked executions

The projection reads stored step results. It does not run the endpoint or gateway again.
Only evaluated operations belong to the prefix. An unsupported suffix adds no slots.
-/

namespace Netlib.Check.CampusTCPSchedule

namespace M
export CampusTCPModel (Input State Event Effect Step Trace Report)
end M
namespace B
export Netlib.Theory.BoundedProgress (Adapter Prefix)
end B

open Netlib.Protocol

variable {input : M.Input} {initial final : M.State input}
variable {events remaining : List M.Event} {steps : List (M.Step input)}

def system (input : M.Input) : Transition (M.State input) M.Event :=
  ⟨fun before event after => ∃ effect, CampusTCPModel.step input before event = .ok effect ∧ effect.state = after⟩

def stateAt (initial : M.State input) : List (M.Step input) → Nat → M.State input
  | [], _ => initial
  | _ :: _, 0 => initial
  | head :: rest, index + 1 => stateAt head.result.state rest index

def eventAt (steps : List (M.Step input)) (index : Nat) : M.Event :=
  match steps[index]? with
  | none => .authentication 0
  | some head => head.event

@[simp] theorem stateAt_zero (initial : M.State input) (steps : List (M.Step input)) :
    stateAt initial steps 0 = initial := by cases steps <;> rfl

theorem Trace.at (trace : M.Trace input initial events steps final remaining)
    (index : Nat) (within : index < steps.length) :
    ∃ head, steps[index]? = some head ∧ head.before = stateAt initial steps index ∧
      head.event = eventAt steps index ∧ head.result.state = stateAt initial steps (index + 1) := by
  induction trace generalizing index with
  | done state => simp at within
  | stop head blocked tail =>
    have same : index = 0 := by simp only [List.length_cons, List.length_nil] at within; omega
    subst index
    exact ⟨head, rfl, rfl, rfl, rfl⟩
  | next head supported rest ih =>
    cases index with
    | zero => exact ⟨head, rfl, rfl, rfl, by simp [stateAt]⟩
    | succ index =>
      have smaller : index < _ := Nat.lt_of_succ_lt_succ within
      obtain ⟨selected, found, before, event, after⟩ := ih index smaller
      exact ⟨selected, found, before, event, after⟩

theorem Trace.last_state (trace : M.Trace input initial events steps final remaining) :
    stateAt initial steps steps.length = final := by
  induction trace with
  | done state => rfl
  | stop head blocked tail => rfl
  | next head supported rest ih => simpa only [List.length_cons, stateAt] using ih

def Trace.prefix (trace : M.Trace input initial events steps final remaining) : B.Prefix (system input) where
  length := steps.length
  state := stateAt initial steps
  action := eventAt steps
  checked index within := by
    obtain ⟨head, _, before, event, after⟩ := Trace.at trace index within
    exact ⟨head.result, by simpa only [← before, ← event] using head.computed, after⟩

@[simp] theorem Trace.prefix_initial (trace : M.Trace input initial events steps final remaining) :
    (Trace.prefix trace).state 0 = initial := stateAt_zero _ _

@[simp] theorem Trace.prefix_final (trace : M.Trace input initial events steps final remaining) :
    (Trace.prefix trace).state (Trace.prefix trace).length = final := Trace.last_state trace

@[simp] theorem Trace.prefix_length (trace : M.Trace input initial events steps final remaining) :
    (Trace.prefix trace).length = steps.length := rfl

/-- The caller constrains actions from preceding states, not their results. -/
def guardedSystem (input : M.Input) (allowed : M.State input → M.Event → Prop) :
    Transition (M.State input) M.Event :=
  ⟨fun before event after => allowed before event ∧ (system input).step before event after⟩

def Trace.guardedPrefix (trace : M.Trace input initial events steps final remaining)
    (allowed : M.State input → M.Event → Prop)
    (actions : ∀ head ∈ steps, allowed head.before head.event) : B.Prefix (guardedSystem input allowed) where
  length := steps.length
  state := stateAt initial steps
  action := eventAt steps
  checked index within := by
    obtain ⟨head, found, before, event, after⟩ := Trace.at trace index within
    have member : head ∈ steps := List.mem_of_getElem? found
    exact ⟨by simpa only [← before, ← event] using actions head member,
      head.result, by simpa only [← before, ← event] using head.computed, after⟩

theorem Trace.slot_time (trace : M.Trace input initial events steps final remaining)
    (index : Nat) (within : index ≤ steps.length) :
    (stateAt initial steps index).time = initial.time + index := by
  induction trace generalizing index with
  | done state =>
    have same : index = 0 := by simp only [List.length_nil] at within; omega
    subst index
    simp
  | stop head blocked tail =>
    cases index with
    | zero => simp
    | succ index =>
      have same : index = 0 := by simp only [List.length_cons, List.length_nil] at within; omega
      subst index
      simpa only [stateAt, Nat.add_zero] using head.clock
  | next head supported rest ih =>
    cases index with
    | zero => simp
    | succ index =>
      have smaller : index ≤ _ := Nat.le_of_succ_le_succ within
      have clock := ih index smaller
      simpa only [stateAt, head.clock, Nat.add_assoc, Nat.add_comm 1 index] using clock

theorem Trace.completes (trace : M.Trace input initial events steps final remaining)
    (adapter : B.Adapter (M.State input) M.Event Demand) (same : adapter.system = system input)
    (invariant : adapter.invariant initial)
    (service : ((Trace.prefix trace).cast same.symm).ServiceBound bound)
    (enough : adapter.rank initial * bound ≤ steps.length) : adapter.complete final := by
  have start : adapter.invariant (((Trace.prefix trace).cast same.symm).state 0) := by
    simpa only [Netlib.Theory.BoundedProgress.Prefix.cast_state, Trace.prefix_initial] using invariant
  have completed := ((Trace.prefix trace).cast same.symm).completes_after start service 0 (Nat.zero_le 0)
    steps.length (by simpa only [Netlib.Theory.BoundedProgress.Prefix.cast_state,
      Trace.prefix_initial, Nat.zero_add] using enough) (by simp [Trace.prefix])
  simpa only [Netlib.Theory.BoundedProgress.Prefix.cast_state, Trace.prefix, Trace.last_state trace] using completed

theorem Trace.take (trace : M.Trace input initial events steps final remaining)
    (count : Nat) (within : count ≤ steps.length) :
    M.Trace input initial ((steps.take count).map (·.event)) (steps.take count)
      (stateAt initial steps count) [] := by
  induction trace generalizing count with
  | done state =>
    have zero : count = 0 := by simp only [List.length_nil] at within; omega
    subst count
    exact .done state
  | stop head blocked tail =>
    cases count with
    | zero => exact .done head.before
    | succ count =>
      have zero : count = 0 := by simp only [List.length_cons, List.length_nil] at within; omega
      subst count
      exact .stop head blocked []
  | next head supported rest ih =>
    cases count with
    | zero => exact .done head.before
    | succ count =>
      have bound : count ≤ _ := Nat.le_of_succ_le_succ within
      simpa only [List.take_succ_cons, List.map_cons, stateAt] using .next head supported (ih count bound)

theorem Trace.take_supported (trace : M.Trace input initial events steps final remaining)
    (count : Nat) (within : count < steps.length) :
    (steps.take count).all (·.result.supported) = true := by
  induction trace generalizing count with
  | done state => simp at within
  | stop head blocked tail =>
    have zero : count = 0 := by simp only [List.length_cons, List.length_nil] at within; omega
    subst count
    rfl
  | next head supported rest ih =>
    cases count with
    | zero => rfl
    | succ count =>
      have smaller : count < _ := Nat.lt_of_succ_lt_succ within
      simpa only [List.take_succ_cons, List.all_cons, supported, Bool.true_and] using ih count smaller

def Report.cut (report : M.Report input events) (count : Nat) (within : count ≤ report.steps.length) :
    M.Report input ((report.steps.take count).map (·.event)) where
  final := stateAt input.initial report.steps count
  steps := report.steps.take count
  remaining := []
  trace := Trace.take report.trace count within

theorem Report.cut_supported (report : M.Report input events) (count : Nat) (within : count < report.steps.length) :
    (Report.cut report count (Nat.le_of_lt within)).supported = true :=
  Trace.take_supported report.trace count within

theorem Trace.append_complete (trace : M.Trace input initial events steps final leftRemaining)
    (finished : leftRemaining = []) (supported : ∀ head ∈ steps, head.result.supported = true)
    (tail : M.Trace input final later laterSteps last remaining) :
    M.Trace input initial (events ++ later) (steps ++ laterSteps) last remaining := by
  induction trace with
  | done state => exact tail
  | stop head blocked suffix =>
    have accepted := supported head (by simp)
    simp only [blocked, Bool.false_eq_true] at accepted
  | next head accepted rest ih =>
    exact .next head accepted (ih finished (fun selected member => supported selected (List.mem_cons_of_mem _ member)) tail)

def Report.appendStep (report : M.Report input events) (supported : report.supported = true)
    (finished : report.remaining = []) (actual : M.Step input) (before : actual.before = report.final)
    (accepted : actual.result.supported = true) : M.Report input (events ++ [actual.event]) where
  final := actual.result.state
  steps := report.steps ++ [actual]
  remaining := []
  trace := by
    have complete : M.Trace input input.initial events report.steps report.final [] := finished ▸ report.trace
    have all : ∀ head ∈ report.steps, head.result.supported = true :=
      List.all_eq_true.mp supported
    have tail : M.Trace input report.final [actual.event] [actual] actual.result.state [] := by
      rw [← before]
      exact .next actual accepted (.done actual.result.state)
    exact Trace.append_complete complete rfl all tail

theorem Report.appendStep_supported (report : M.Report input events) (supported : report.supported = true)
    (finished : report.remaining = []) (actual : M.Step input) (before : actual.before = report.final)
    (accepted : actual.result.supported = true) :
    (Report.appendStep report supported finished actual before accepted).supported = true := by
  simp only [Report.appendStep, CampusTCPModel.Report.supported, List.all_append, List.all_cons,
    List.all_nil, accepted, Bool.and_true]
  exact supported

end Netlib.Check.CampusTCPSchedule
