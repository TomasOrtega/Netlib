import Netlib.Protocol.BufferedLifecycle

namespace NetlibTest.BufferedLifecycle

open Netlib.Packet Netlib.Protocol Netlib.Theory
open Netlib.Protocol.BufferedLifecycle

private def original : Header := ⟨3221225986, 3405803778, Protocol.udp, 32000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Protocol.udp, 40000, 9000⟩
private def clean : Header := ⟨3221225986, 3325256707, Protocol.udp, 32001, 9001⟩
private def oldEntry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def cleanEntry : NetfilterNAT.Entry := ⟨⟨clean, clean.reverse, 0, 0, 0⟩, false, false⟩
private def forbidden : Match := { destination := some ⟨wire.destination, 32⟩ }
private def openPipeline : ConntrackLifecycle.Pipeline := {
  routes := [Netlib.Routing.defaultRoute (some "outside")]
  forward := []
  forwardDefault := .permit }
private def barrier : ConntrackLifecycle.Pipeline :=
  { openPipeline with late := [⟨forbidden, none, .deny⟩] }
private def cached : ConntrackLifecycle.State := ⟨[⟨oldEntry, true⟩]⟩
private def cleanTracker : ConntrackLifecycle.State := ⟨[⟨cleanEntry, false⟩]⟩
private def both : ConntrackLifecycle.State := ⟨[⟨oldEntry, true⟩, ⟨cleanEntry, false⟩]⟩
private def oldCall : ConntrackLifecycle.Call := ⟨barrier, ⟨0, original, none⟩⟩
private def cleanCall : ConntrackLifecycle.Call := ⟨barrier, ⟨0, clean, none⟩⟩
private def freshCall : ConntrackLifecycle.Call := ⟨barrier, ⟨0, clean, some cleanEntry⟩⟩
private def queued : State := ⟨cached, ⟨[], [wire]⟩⟩

private def view (result : Except ConntrackLifecycle.Error Result) :
    Except ConntrackLifecycle.Error (List Header × List Header × List Header) :=
  result.map fun result => (result.state.queue.delivered, result.state.queue.pending, result.served)

theorem barrier_blocks : barrier.Blocks forbidden := by
  intro state header selected
  apply StatefulACL.Policy.evaluate_cons_accepts
  simpa [StatefulACL.Rule.accepts, StatefulACL.Rule.stateAccepts] using (Match.accepts_iff _ _).mpr selected

theorem drop_does_not_remove_old_queue :
    view (step queued (.operation (.packet oldCall))) = .ok ([], [wire], []) := by rfl

theorem old_forbidden_delivery_after_barrier :
    (execute queued [.operation (.packet oldCall), .serve 1]).map (fun execution => execution.final.queue) =
      .ok ⟨[wire], []⟩ := by rfl

example : forbidden.Holds wire := (Match.accepts_iff _ _).mp (by decide)

example : view (step State.initial (.operation (.packet freshCall))) = .ok ([], [clean], []) := by rfl

example : view (step ⟨cleanTracker, ⟨[], [clean]⟩⟩ (.operation (.packet cleanCall))) =
    .ok ([], [clean, clean], []) := by rfl

example : view (step queued (.serve 0)) = .ok ([], [wire], []) := by rfl
example : view (step queued (.operation (.erase 0 original))) = .ok ([], [wire], []) := by rfl

private def overloaded (rounds : Nat) : List BufferedLifecycle.Event :=
  (List.replicate rounds [.operation (.packet cleanCall), .operation (.packet cleanCall), .serve 1]).flatten

private def initialBurst : State := ⟨both, ⟨[wire], [wire, wire]⟩⟩

example : (execute initialBurst (overloaded 3)).map (fun execution => execution.final.queue) =
    .ok ⟨[wire, wire, wire, clean], [clean, clean, clean, clean, clean]⟩ := by rfl

example (trace : Trace initial events results final) :
    final.queue.delivered ++ final.queue.pending = initial.queue.delivered ++ initial.queue.pending ++
      (ticks events results).flatMap Queue.Tick.arrivals := trace.conservation

example (draining : Trace cutover drainEvents drainResults middle)
    (future : Trace middle futureEvents futureResults final)
    (drainBarriers : ∀ event ∈ drainEvents, event.Blocks forbidden)
    (futureBarriers : ∀ event ∈ futureEvents, event.Blocks forbidden)
    (enough : cutover.queue.pending.length ≤ serviceCapacity drainEvents) :
    ∀ result ∈ futureResults, ∀ header ∈ result.served, ¬forbidden.Holds header :=
  draining.clean_after_budget future forbidden drainBarriers futureBarriers enough

private def load (result : Except ConntrackLifecycle.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let dropped ← load (step queued (.operation (.packet oldCall)))
  ensure (dropped.served.isEmpty && dropped.admitted.isEmpty && dropped.state.queue.pending == [wire])
    "A late drop must enqueue nothing and retain the earlier FIFO backlog."
  let stale ← load (step dropped.state (.serve 1))
  ensure (stale.served == [wire] && stale.served.any forbidden.accepts && stale.operation.isNone)
    "Service after barrier installation can still deliver an earlier forbidden packet."
  let openCall : ConntrackLifecycle.Call := ⟨openPipeline, ⟨0, original, none⟩⟩
  let admitted ← load (step ⟨cached, ⟨[], [clean]⟩⟩ (.operation (.packet openCall)))
  ensure (admitted.admitted == [wire] && admitted.state.queue.pending == [clean, wire] && admitted.served.isEmpty)
    "A cached output must enter the FIFO tail without bypassing earlier packets."
  let fresh ← load (step State.initial (.operation (.packet freshCall)))
  ensure (fresh.admitted == [clean] && fresh.state.queue.pending == [clean] && fresh.state.tracker == cleanTracker)
    "A successful fresh packet must confirm its binding and enqueue its actual output."
  let repeated ← load (step fresh.state (.operation (.packet cleanCall)))
  ensure (repeated.state.queue.pending == [clean, clean] && repeated.admitted == [clean])
    "Identical packet values must remain separate FIFO admissions."
  let zero ← load (step repeated.state (.serve 0))
  ensure (zero.served.isEmpty && decide (zero.state = repeated.state))
    "Zero capacity must leave both state components unchanged."
  let erased ← load (step repeated.state (.operation (.erase 0 clean)))
  ensure (erased.admitted.isEmpty && erased.state.tracker.records.isEmpty &&
    decide (erased.state.queue = repeated.state.queue))
    "Deleting a binding must not delete or reorder queued packets."
  let drained ← load (step erased.state (.serve 20))
  ensure (drained.served == [clean, clean] && drained.state.queue.pending.isEmpty &&
    drained.state.tracker == erased.state.tracker)
    "Declared service must preserve duplicate order and leave tracking unchanged."
  let deniedPipeline := { barrier with late := [], lateDefault := Action.deny }
  let deniedCall : ConntrackLifecycle.Call := ⟨deniedPipeline, ⟨0, clean, some cleanEntry⟩⟩
  let denied ← load (step ⟨ConntrackLifecycle.State.initial, ⟨[], [wire]⟩⟩ (.operation (.packet deniedCall)))
  ensure (denied.admitted.isEmpty && denied.state.tracker.records.isEmpty && denied.state.queue.pending == [wire])
    "A fresh preconfirmation drop must neither enqueue a packet nor install a binding."
  let underloaded ← load (execute ⟨cleanTracker, {}⟩
    [.operation (.packet cleanCall), .serve 1, .operation (.packet cleanCall), .serve 1])
  ensure (underloaded.final.queue.pending.isEmpty && underloaded.final.queue.delivered == [clean, clean])
    "Service matching arrivals must drain the admitted sequence."
  let drainedPrefix ← load (execute initialBurst (overloaded 2))
  ensure (drainedPrefix.results.flatMap Result.served == [wire, wire] && drainedPrefix.final.queue.pending.length == 4 &&
    drainedPrefix.final.queue.pending.all (fun header => !forbidden.accepts header))
    "Two service slots must clear the old prefix even while clean arrivals exceed service."
  let future ← load (execute drainedPrefix.final (overloaded 2))
  ensure (future.results.flatMap Result.served == [clean, clean] && future.final.queue.pending.length == 6 &&
    future.results.all (fun result => result.served.all (fun header => !forbidden.accepts header)))
    "Later service must remain clean under sustained overload after the old prefix clears."
  ensure (future.final.queue.delivered == initialBurst.queue.delivered ++ [wire, wire, clean, clean])
    "The clean-service claim must leave earlier delivered history intact."
  IO.println "Buffered tracked forwarding tests passed."

end NetlibTest.BufferedLifecycle
