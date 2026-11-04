import Netlib.Protocol.Revocation
import Netlib.Theory.QueueDrain

/-!
# Buffered tracked forwarding

Only computed operation outputs enter the unbounded FIFO.
Service is a separate declared operation and leaves tracking unchanged.
A late barrier controls new admissions; earlier queued packets still need service.
-/

namespace Netlib.Protocol.BufferedLifecycle

open Packet
open Theory

structure State where
  tracker : ConntrackLifecycle.State
  queue : Queue.State Header
  deriving Repr, DecidableEq

def State.initial : State := ⟨ConntrackLifecycle.State.initial, {}⟩
def State.Valid (state : State) : Prop := state.tracker.Valid

inductive Event where
  | operation (event : ConntrackLifecycle.Operations.Event)
  | serve (capacity : Nat)

structure Result where
  state : State
  operation : Option ConntrackLifecycle.Operations.Result
  served : List Header

def operationOutput (result : ConntrackLifecycle.Operations.Result) : Option Header := result.packet.bind (·.output)
def Result.admitted (result : Result) : List Header := (result.operation.bind operationOutput).toList

def Event.capacity : Event → Nat
  | .operation _ => 0
  | .serve capacity => capacity

def tick (event : Event) (result : Result) : Queue.Tick Header := ⟨result.admitted, event.capacity⟩

def step (before : State) : Event → Except ConntrackLifecycle.Error Result
  | .operation event => do
    let result ← ConntrackLifecycle.Operations.step before.tracker event
    let queued := Queue.step before.queue ⟨(operationOutput result).toList, 0⟩
    return ⟨⟨result.state, queued.next⟩, some result, queued.served⟩
  | .serve capacity =>
    let queued := Queue.step before.queue ⟨[], capacity⟩
    .ok ⟨⟨before.tracker, queued.next⟩, none, queued.served⟩

theorem step_operation (before : State) (event : ConntrackLifecycle.Operations.Event) (result : Result)
    (accepted : step before (.operation event) = .ok result) :
    ∃ operation, ConntrackLifecycle.Operations.step before.tracker event = .ok operation ∧
      result.operation = some operation ∧ result.state.tracker = operation.state ∧ result.served = [] ∧
      result.state.queue.delivered = before.queue.delivered ∧
      result.state.queue.pending = before.queue.pending ++ (operationOutput operation).toList := by
  cases found : ConntrackLifecycle.Operations.step before.tracker event with
  | error error => simp [step, found, bind, Except.bind] at accepted
  | ok operation =>
    simp [step, found, bind, Except.bind, pure] at accepted
    cases accepted
    exact ⟨operation, rfl, rfl, rfl, rfl, by simp [Queue.step], by simp [Queue.step]⟩

theorem step_serve (before : State) (capacity : Nat) (result : Result)
    (accepted : step before (.serve capacity) = .ok result) :
    result.operation = none ∧ result.state.tracker = before.tracker ∧
      result.served = (Queue.step before.queue ⟨[], capacity⟩).served ∧
      result.state.queue = (Queue.step before.queue ⟨[], capacity⟩).next := by
  cases accepted
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem step_queue (before : State) (event : Event) (result : Result)
    (accepted : step before event = .ok result) :
    (Queue.step before.queue (tick event result)).served = result.served ∧
      (Queue.step before.queue (tick event result)).next = result.state.queue := by
  cases event with
  | serve capacity =>
    cases accepted
    exact ⟨rfl, rfl⟩
  | operation event =>
    cases found : ConntrackLifecycle.Operations.step before.tracker event with
    | error error => simp [step, found, bind, Except.bind] at accepted
    | ok operation =>
      simp [step, found, bind, Except.bind, pure] at accepted
      cases accepted
      exact ⟨rfl, rfl⟩

theorem step_valid (before : State) (event : Event) (result : Result)
    (valid : before.Valid) (accepted : step before event = .ok result) : result.state.Valid := by
  unfold State.Valid at valid ⊢
  cases event with
  | serve capacity =>
    rw [(step_serve before capacity result accepted).2.1]
    exact valid
  | operation event =>
    obtain ⟨operation, _, _, same, _⟩ := step_operation before event result accepted
    rw [same]
    exact operation.valid

inductive Trace : State → List Event → List Result → State → Prop
  | nil (state : State) : Trace state [] [] state
  | cons {before final : State} {event : Event} {events : List Event} {result : Result} {results : List Result}
      (accepted : step before event = .ok result) (rest : Trace result.state events results final) :
      Trace before (event :: events) (result :: results) final

structure Execution (initial : State) (events : List Event) where
  final : State
  results : List Result
  covered : results.length = events.length
  trace : Trace initial events results final

def execute (initial : State) : (events : List Event) → Except ConntrackLifecycle.Error (Execution initial events)
  | [] => .ok ⟨initial, [], rfl, .nil initial⟩
  | event :: events => do
    match accepted : step initial event with
    | .error error => throw error
    | .ok result =>
      let rest ← execute result.state events
      return ⟨rest.final, result :: rest.results, by simp only [List.length_cons, rest.covered], .cons accepted rest.trace⟩

def ticks (events : List Event) (results : List Result) : List (Queue.Tick Header) := List.zipWith tick events results

def serviceCapacity (events : List Event) : Nat := (events.map Event.capacity).sum

theorem Trace.covered {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) : results.length = events.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem Trace.valid {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) (valid : initial.Valid) :
    final.Valid ∧ ∀ result ∈ results, result.state.Valid := by
  induction trace with
  | nil => exact ⟨valid, by simp⟩
  | @cons before final event events result results accepted rest ih =>
    have head := step_valid before event result valid accepted
    obtain ⟨last, each⟩ := ih head
    refine ⟨last, ?_⟩
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact each actual member

theorem Trace.queue_run {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) : final.queue = Queue.run initial.queue (ticks events results) := by
  induction trace with
  | nil => rfl
  | @cons before final event events result results accepted rest ih =>
    rw [ih]
    change Queue.run result.state.queue _ = Queue.run (Queue.advance before.queue (tick event result)) _
    rw [Queue.advance, (step_queue before event result accepted).2]
    rfl

theorem Trace.ticks_capacity {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) :
    (ticks events results).map Queue.Tick.capacity = events.map Event.capacity := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simpa only [ticks, List.zipWith_cons_cons, List.map_cons, tick] using congrArg (List.cons _) ih

theorem Trace.ticks_arrivals {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) :
    (ticks events results).flatMap Queue.Tick.arrivals = results.flatMap Result.admitted := by
  induction trace with
  | nil => rfl
  | @cons before final event events result results accepted rest ih =>
    change result.admitted ++ (ticks events results).flatMap Queue.Tick.arrivals =
      result.admitted ++ results.flatMap Result.admitted
    rw [ih]

theorem Trace.delivered {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) :
    final.queue.delivered = initial.queue.delivered ++ results.flatMap Result.served := by
  induction trace with
  | nil => simp
  | @cons before final event events result results accepted rest ih =>
    rw [ih, ← (step_queue before event result accepted).2, Queue.delivered_append,
      (step_queue before event result accepted).1]
    simp [List.append_assoc]

theorem Trace.conservation {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) :
    final.queue.delivered ++ final.queue.pending = initial.queue.delivered ++ initial.queue.pending ++
      (ticks events results).flatMap Queue.Tick.arrivals := by
  rw [trace.queue_run]
  exact Queue.run_conservation _ _

theorem Trace.drop {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) (start : Nat) :
    ∃ middle, Trace middle (events.drop start) (results.drop start) final := by
  induction trace generalizing start with
  | nil => simp only [List.drop_nil]; exact ⟨_, .nil _⟩
  | cons accepted rest ih =>
    cases start with
    | zero => exact ⟨_, .cons accepted rest⟩
    | succ start => exact ih start

theorem Trace.split {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) (start : Nat) :
    ∃ middle, Trace initial (events.take start) (results.take start) middle ∧
      Trace middle (events.drop start) (results.drop start) final := by
  induction trace generalizing start with
  | nil => simp only [List.take_nil, List.drop_nil]; exact ⟨_, .nil _, .nil _⟩
  | cons accepted rest ih =>
    cases start with
    | zero => exact ⟨_, .nil _, .cons accepted rest⟩
    | succ start =>
      obtain ⟨middle, prefixTrace, suffixTrace⟩ := ih start
      exact ⟨middle, .cons accepted prefixTrace, suffixTrace⟩

def Event.toOperation : Event → Option ConntrackLifecycle.Operations.Event
  | .operation event => some event
  | .serve _ => none

theorem Trace.operations {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) :
    ConntrackLifecycle.Operations.ExecutionTrace initial.tracker (events.filterMap Event.toOperation)
      (results.filterMap Result.operation) final.tracker := by
  induction trace with
  | nil => exact .nil _
  | @cons before final event events result results accepted rest ih =>
    cases event with
    | operation event =>
      obtain ⟨operation, found, stored, tracker, _⟩ := step_operation before event result accepted
      simp only [List.filterMap_cons, Event.toOperation, stored]
      apply ConntrackLifecycle.Operations.ExecutionTrace.cons found
      simpa only [tracker] using ih
    | serve capacity =>
      obtain ⟨stored, tracker, _⟩ := step_serve before capacity result accepted
      simp only [List.filterMap_cons, Event.toOperation, stored]
      simpa only [tracker] using ih

def Event.Blocks (event : Event) (forbidden : Match) : Prop :=
  match event with
  | .operation event => event.Blocks forbidden
  | .serve _ => True

theorem step_admissions_excluded (before : State) (event : Event) (result : Result) (forbidden : Match)
    (barrier : event.Blocks forbidden) (accepted : step before event = .ok result) :
    ∀ header ∈ result.admitted, ¬forbidden.Holds header := by
  cases event with
  | serve capacity =>
    have absent := (step_serve before capacity result accepted).1
    simp [Result.admitted, absent]
  | operation event =>
    obtain ⟨operation, found, stored, _⟩ := step_operation before event result accepted
    have excluded := ConntrackLifecycle.Operations.step_excludes before.tracker event operation forbidden barrier found
    intro header member
    simp only [Result.admitted, stored, Option.bind_some, operationOutput, Option.mem_toList] at member
    cases packet : operation.packet with
    | none => simp [packet] at member
    | some outcome =>
      exact excluded outcome packet header (by simpa [packet] using member)

theorem Trace.arrivals_excluded {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) (forbidden : Match)
    (barriers : ∀ event ∈ events, event.Blocks forbidden) :
    ∀ queued ∈ ticks events results, ∀ header ∈ queued.arrivals, ¬forbidden.Holds header := by
  induction trace with
  | nil => simp [ticks]
  | @cons before final event events result results accepted rest ih =>
    intro queued member
    rcases List.mem_cons.mp member with rfl | member
    · exact step_admissions_excluded before event result forbidden (barriers _ (by simp)) accepted
    · exact ih (fun next belongs => barriers next (List.mem_cons_of_mem _ belongs)) queued member

theorem Trace.served_eq {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) :
    results.flatMap Result.served = QueueDrain.served initial.queue (ticks events results) := by
  have same := congrArg Queue.State.delivered trace.queue_run
  rw [trace.delivered, QueueDrain.run_delivered] at same
  exact List.append_cancel_left same

theorem Trace.remaining_old_bound {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) (forbidden : Match)
    (barriers : ∀ event ∈ events, event.Blocks forbidden) :
    QueueDrain.CleanTail (fun header => ¬forbidden.Holds header)
      (initial.queue.pending.length - serviceCapacity events) final.queue.pending := by
  rw [trace.queue_run]
  have initialTail : QueueDrain.CleanTail (fun header => ¬forbidden.Holds header)
      initial.queue.pending.length initial.queue.pending := by
    simp [QueueDrain.CleanTail, QueueDrain.Clean]
  have result := QueueDrain.run_tail_bound _ initial.queue (ticks events results)
    initial.queue.pending.length initialTail (trace.arrivals_excluded forbidden barriers)
  simpa only [QueueDrain.totalCapacity, trace.ticks_capacity, serviceCapacity] using result

theorem Trace.pending_clean_after_budget {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) (forbidden : Match)
    (barriers : ∀ event ∈ events, event.Blocks forbidden)
    (enough : initial.queue.pending.length ≤ serviceCapacity events) :
    QueueDrain.CleanPending (fun header => ¬forbidden.Holds header) final.queue := by
  have remaining := trace.remaining_old_bound forbidden barriers
  simpa [QueueDrain.CleanTail, QueueDrain.CleanPending, Nat.sub_eq_zero_of_le enough] using remaining

theorem Trace.served_excluded {initial final : State} {events : List Event} {results : List Result}
    (trace : Trace initial events results final) (forbidden : Match)
    (pending : QueueDrain.CleanPending (fun header => ¬forbidden.Holds header) initial.queue)
    (barriers : ∀ event ∈ events, event.Blocks forbidden) :
    ∀ result ∈ results, ∀ header ∈ result.served, ¬forbidden.Holds header := by
  have clean := QueueDrain.served_clean _ initial.queue (ticks events results) pending
    (trace.arrivals_excluded forbidden barriers)
  rw [← trace.served_eq] at clean
  intro result member header served
  exact clean header (List.mem_flatMap.mpr ⟨result, member, served⟩)

theorem Trace.clean_after_budget
    {cutover middle final : State} {drainEvents futureEvents : List Event} {drainResults futureResults : List Result}
    (draining : Trace cutover drainEvents drainResults middle)
    (future : Trace middle futureEvents futureResults final) (forbidden : Match)
    (drainBarriers : ∀ event ∈ drainEvents, event.Blocks forbidden)
    (futureBarriers : ∀ event ∈ futureEvents, event.Blocks forbidden)
    (enough : cutover.queue.pending.length ≤ serviceCapacity drainEvents) :
    ∀ result ∈ futureResults, ∀ header ∈ result.served, ¬forbidden.Holds header :=
  future.served_excluded forbidden (draining.pending_clean_after_budget forbidden drainBarriers enough) futureBarriers

end Netlib.Protocol.BufferedLifecycle
