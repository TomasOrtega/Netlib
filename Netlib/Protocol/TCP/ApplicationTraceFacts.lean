import Netlib.Protocol.TCP.ApplicationTrace

namespace Netlib.Protocol.TCP.ApplicationTrace

theorem Chain.append (first : Chain initial prior middle) (second : Chain middle later final) :
    Chain initial (prior ++ later) final := by
  induction first with
  | nil state => exact second
  | cons head tail ih => exact .cons head (ih second)

theorem Chain.snoc (prior : Chain initial steps head.before) :
    Chain initial (steps ++ [head]) head.result.state :=
  prior.append (.cons head (.nil head.result.state))

theorem chronological_snoc (ordered : Chronological steps)
    (earlier : ∀ step ∈ steps, step.stamp < head.stamp) : Chronological (steps ++ [head]) := by
  apply List.pairwise_append.mpr
  refine ⟨ordered, .cons (by intro item member; cases member) .nil, ?_⟩
  intro item member last present
  simp only [List.mem_singleton] at present
  subst last
  exact earlier item member


def stepOutput (step : Step) : Except String { output : Input // OutputOrigin step output } :=
  match event : step.event with
  | .send count policy =>
    match selected : step.result.decision with
    | .accepted (.send amount) =>
      if same : amount = count then
        match actual : step.result.output with
        | some output => .ok ⟨output, .send count policy event (by simpa only [same] using selected) actual⟩
        | none => .error "The selected send has no checked output."
      else .error "The selected send count differs from its event."
    | _ => .error "The selected send did not succeed."
  | .emitAck policy =>
    match selected : step.result.decision with
    | .accepted .emitAck =>
      match actual : step.result.output with
      | some output => .ok ⟨output, .ack policy event selected actual⟩
      | none => .error "The selected ACK event has no checked output."
    | _ => .error "The selected ACK event did not succeed."
  | _ => .error "The selected event cannot produce application-profile output."

def findOutput : (steps : List Step) → (stamp : Nat) →
    Except String { value : OutputAt steps // value.step.stamp = stamp }
  | [], _ => .error "The selected output event is absent from this application trace."
  | head :: tail, stamp => do
    if same : head.stamp = stamp then
      let output ← stepOutput head
      return ⟨⟨[], head, tail, rfl, output.val, output.property⟩, same⟩
    else
      let found ← findOutput tail stamp
      let value : OutputAt (head :: tail) :=
        ⟨head :: found.val.prior, found.val.step, found.val.later,
          congrArg (head :: ·) found.val.same, found.val.output, found.val.origin⟩
      return ⟨value, found.property⟩

end Netlib.Protocol.TCP.ApplicationTrace
