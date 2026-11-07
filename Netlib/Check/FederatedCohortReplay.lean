import Netlib.Check.FederatedCohortExecution
import Netlib.Theory.BoundedProgress

/-!
# Literal cohort action replay

Each stored row retains its preceding state and exact computed effect.
Only recorded slots contribute to the resulting finite prefix.
-/

namespace Netlib.Federation.Cohort.Replay

variable {input : Input} {size : Nat} {context : Context input size} {headers : Vector Packet.Header size}

structure Step (context : Context input size) (headers : Vector Packet.Header size) where
  before : State input size
  action : InFlight.Action
  advanced : Execution.Advanced context headers before action

def Step.after (step : Step context headers) : State input size := step.advanced.outcome.after

def Step.event (step : Step context headers) : Event input size := step.advanced.event

theorem Step.checked (step : Step context headers) :
    (Execution.system context headers).step step.before step.event step.after := step.advanced.step

def Chained : State input size → List (Step context headers) → State input size → Prop
  | before, [], after => after = before
  | before, step :: rest, after => step.before = before ∧ Chained step.after rest after

theorem Chained.trace {before after : State input size} {steps : List (Step context headers)}
    (chain : Chained before steps after) :
    (Execution.system context headers).Trace before (steps.map Step.event) after := by
  induction steps generalizing before with
  | nil =>
    change after = before at chain
    subst after
    exact .nil before
  | cons step rest ih =>
    obtain ⟨same, tail⟩ := chain
    have edge := step.checked
    rw [same] at edge
    exact .cons edge (ih tail)

def stateAt (before : State input size) : List (Step context headers) → Nat → State input size
  | [], _ => before
  | _ :: _, 0 => before
  | step :: rest, slot + 1 => stateAt step.after rest slot

def eventAt : List (Step context headers) → Nat → Event input size
  | [], _ => ⟨.idle, Vector.replicate size .idle⟩
  | step :: _, 0 => step.event
  | _ :: rest, slot + 1 => eventAt rest slot

@[simp] theorem stateAt_zero (before : State input size) (steps : List (Step context headers)) :
    stateAt before steps 0 = before := by cases steps <;> rfl

theorem Chained.checked {before after : State input size} {steps : List (Step context headers)}
    (chain : Chained before steps after) (slot : Nat) (within : slot < steps.length) :
    (Execution.system context headers).step (stateAt before steps slot)
      (eventAt steps slot) (stateAt before steps (slot + 1)) := by
  induction steps generalizing before slot with
  | nil => simp at within
  | cons step rest ih =>
    obtain ⟨same, tail⟩ := chain
    cases slot with
    | zero => simpa only [stateAt, eventAt, stateAt_zero, same] using step.checked
    | succ slot =>
      exact ih tail slot (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)

theorem Chained.final {before after : State input size} {steps : List (Step context headers)}
    (chain : Chained before steps after) : stateAt before steps steps.length = after := by
  induction steps generalizing before with
  | nil => exact chain.symm
  | cons step rest ih => exact ih chain.2

private def replayFrom (context : Context input size) (headers : Vector Packet.Header size) (before : State input size) :
    (actions : List InFlight.Action) → Except String ((after : State input size) ×
      { steps : List (Step context headers) // Chained before steps after ∧ steps.map Step.action = actions })
  | [] => return ⟨before, ⟨[], rfl, rfl⟩⟩
  | action :: rest => do
    let advanced ← (Execution.advance context headers before action).mapError
      (fun reason => s!"Cohort slot {before.nextIndex}: {reason}")
    let tail ← replayFrom context headers advanced.outcome.after rest
    let step : Step context headers := ⟨before, action, advanced⟩
    return ⟨tail.1, ⟨step :: tail.2.val, ⟨rfl, tail.2.property.1⟩,
      by simp only [List.map_cons, tail.2.property.2]; rfl⟩⟩

structure Report (context : Context input size) (headers : Vector Packet.Header size) (actions : List InFlight.Action) where
  steps : List (Step context headers)
  final : State input size
  chained : Chained (initialState context) steps final
  covered : steps.map Step.action = actions

def run (context : Context input size) (headers : Vector Packet.Header size) (actions : List InFlight.Action) :
    Except String (Report context headers actions) := do
  let value ← replayFrom context headers (initialState context) actions
  return ⟨value.2.val, value.1, value.2.property.1, value.2.property.2⟩

def Report.prefix (report : Report context headers actions) : Theory.BoundedProgress.Prefix (Execution.system context headers) where
  length := report.steps.length
  state := stateAt (initialState context) report.steps
  action := eventAt report.steps
  checked := report.chained.checked

theorem Report.initial (report : Report context headers actions) :
    report.prefix.state 0 = initialState context := stateAt_zero _ _

theorem Report.length (report : Report context headers actions) : report.prefix.length = actions.length := by
  simpa only [Report.prefix, List.length_map] using congrArg List.length report.covered

theorem Report.trace (report : Report context headers actions) :
    (Execution.system context headers).Trace (initialState context) (report.steps.map Step.event) report.final :=
  report.chained.trace

theorem Report.final_state (report : Report context headers actions) :
    report.prefix.state report.prefix.length = report.final := report.chained.final

theorem Chained.prefix_before {before after : State input size} {steps : List (Step context headers)}
    (chain : Chained before steps after) (index : Nat) (step : Step context headers)
    (found : steps[index]? = some step) :
    (Execution.system context headers).Trace before ((steps.take index).map Step.event) step.before ∧
      stateAt before steps index = step.before := by
  induction steps generalizing before index with
  | nil => simp at found
  | cons head rest ih =>
    obtain ⟨same, tail⟩ := chain
    cases index with
    | zero =>
      have selected : head = step := Option.some.inj found
      subst step
      exact ⟨same ▸ .nil head.before, same.symm⟩
    | succ index =>
      obtain ⟨lead, state⟩ := ih tail index found
      have edge := head.checked
      rw [same] at edge
      exact ⟨.cons edge lead, state⟩

theorem Report.prefix_before (report : Report context headers actions) (index : Nat)
    (step : Step context headers) (found : report.steps[index]? = some step) :
    (Execution.system context headers).Trace (initialState context)
        ((report.steps.take index).map Step.event) step.before ∧ report.prefix.state index = step.before :=
  report.chained.prefix_before index step found

end Netlib.Federation.Cohort.Replay
