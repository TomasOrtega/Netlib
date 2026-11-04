import Netlib.Protocol.ConntrackOperations
import Netlib.Network.Upgrade

/-!
# Output exclusion through a late barrier

The forbidden class describes headers after both NAT stages.
The barrier applies to cached and fresh attachments, including established packets.
These theorems do not establish hook installation, packet freshness, or native transport validity.
-/

namespace Netlib.Protocol.ConntrackLifecycle

open Packet

def OutputExcluded (forbidden : Match) (output : Option Header) : Prop :=
  ∀ header, output = some header → ¬forbidden.Holds header

def Pipeline.Blocks (pipeline : Pipeline) (forbidden : Match) : Prop :=
  ∀ state header, forbidden.Holds header →
    StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late state header = .deny

theorem step_output_property (pipeline : Pipeline) (property : Header → Prop)
    (barrier : ∀ state header,
      StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late state header = .permit → property header)
    (before : State) (input : Input) (outcome : Outcome)
    (accepted : step pipeline before input = .ok outcome) :
    ∀ header, outcome.output = some header → property header := by
  intro header output
  exact barrier _ _ (step_filters pipeline before input outcome header accepted output).2.2.1

theorem step_output_excluded (pipeline : Pipeline) (forbidden : Match) (barrier : pipeline.Blocks forbidden)
    (before : State) (input : Input) (outcome : Outcome)
    (accepted : step pipeline before input = .ok outcome) : OutputExcluded forbidden outcome.output := by
  apply step_output_property pipeline (fun header => ¬forbidden.Holds header) ?_ before input outcome accepted
  intro state header permitted denied
  have blocked := barrier state header denied
  rw [blocked] at permitted
  cases permitted

namespace Operations

def Event.Blocks (forbidden : Match) : Event → Prop
  | .packet call => call.pipeline.Blocks forbidden
  | .erase .. => True

def Result.Excludes (forbidden : Match) (result : Result) : Prop :=
  ∀ outcome, result.packet = some outcome → OutputExcluded forbidden outcome.output

theorem step_excludes (before : State) (event : Event) (result : Result) (forbidden : Match)
    (barrier : event.Blocks forbidden) (accepted : step before event = .ok result) : result.Excludes forbidden := by
  cases event with
  | packet call =>
    cases packetStep : ConntrackLifecycle.step call.pipeline before call.input with
    | error error => simp [step, packetStep, bind, Except.bind] at accepted
    | ok outcome =>
      simp [step, packetStep, bind, Except.bind, pure] at accepted
      cases accepted
      intro actual same
      cases Option.some.inj same
      exact step_output_excluded call.pipeline forbidden barrier before call.input outcome packetStep
  | erase zone header =>
    simp only [step] at accepted
    repeat' first | (cases accepted; intro outcome impossible; cases impossible)
                  | (split at accepted <;> try simp [bind, throw, pure, Except.bind] at accepted)

theorem ExecutionTrace.drop {initial final : State} {events : List Event} {results : List Result}
    (trace : ExecutionTrace initial events results final) (start : Nat) :
    ∃ middle, ExecutionTrace middle (events.drop start) (results.drop start) final := by
  induction trace generalizing start with
  | nil => simp only [List.drop_nil]; exact ⟨_, .nil _⟩
  | cons accepted rest ih =>
    cases start with
    | zero => exact ⟨_, .cons accepted rest⟩
    | succ start => exact ih start

theorem ExecutionTrace.excludes {initial final : State} {events : List Event} {results : List Result}
    (trace : ExecutionTrace initial events results final) (forbidden : Match)
    (barriers : ∀ event ∈ events, event.Blocks forbidden) :
    ∀ result ∈ results, result.Excludes forbidden := by
  induction trace with
  | nil => simp
  | @cons before final event events result results accepted rest ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · exact step_excludes before event actual forbidden (barriers _ (by simp)) accepted
    · exact ih (fun next belongs => barriers next (List.mem_cons_of_mem _ belongs)) actual member

theorem ExecutionTrace.suffix_excludes {initial final : State} {events : List Event} {results : List Result}
    (trace : ExecutionTrace initial events results final) (start : Nat) (forbidden : Match)
    (barriers : ∀ event ∈ events.drop start, event.Blocks forbidden) :
    ∀ result ∈ results.drop start, result.Excludes forbidden := by
  obtain ⟨_, suffix⟩ := trace.drop start
  exact suffix.excludes forbidden barriers

theorem ExecutionTrace.excludes_of_upgrade
    {PolicyState : Type u} {Command : Type v} (advance : PolicyState → Command → PolicyState)
    (pipeline : PolicyState → Pipeline) (initialPolicy : PolicyState) (commands : List Command)
    (forbidden : Match)
    (safe : Network.Upgrade.Preserves advance (fun policy => (pipeline policy).Blocks forbidden) initialPolicy commands)
    {initial final : State} {events : List Event} {results : List Result}
    (trace : ExecutionTrace initial events results final)
    (selected : ∀ call, Event.packet call ∈ events →
      ∃ policy ∈ Network.Upgrade.snapshots advance initialPolicy commands, call.pipeline = pipeline policy) :
    ∀ result ∈ results, result.Excludes forbidden := by
  apply trace.excludes forbidden
  intro event member
  cases event with
  | erase => trivial
  | packet call =>
    obtain ⟨policy, belongs, same⟩ := selected call member
    change call.pipeline.Blocks forbidden
    rw [same]
    exact safe policy belongs

end Operations
end Netlib.Protocol.ConntrackLifecycle
