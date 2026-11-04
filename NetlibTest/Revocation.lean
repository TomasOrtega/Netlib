import Netlib.Protocol.Revocation

namespace NetlibTest.Revocation

open Netlib Packet Protocol Protocol.ConntrackLifecycle

private def original : Header := ⟨3221225986, 3405803778, Protocol.udp, 32000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def cached : State := ⟨[⟨entry, true⟩]⟩
private def unreplied : State := ⟨[⟨entry, false⟩]⟩
private def forbidden : Match := { destination := some ⟨wire.destination, 32⟩ }
private def openPipeline : Pipeline := {
  routes := [Routing.defaultRoute (some "outside")]
  forward := [establishedPermit]
  forwardDefault := .permit }
private def barrier : Pipeline :=
  { openPipeline with late := [⟨forbidden, none, .deny⟩], lateDefault := .permit }
private def oldInput : Input := ⟨0, original, none⟩
private def freshInput : Input := ⟨0, original, some entry⟩

theorem barrier_blocks : barrier.Blocks forbidden := by
  intro state header selected
  apply StatefulACL.Policy.evaluate_cons_accepts
  simpa [StatefulACL.Rule.accepts, StatefulACL.Rule.stateAccepts] using (Match.accepts_iff _ _).mpr selected

private def view (result : Except Error Outcome) : Except Error (State × Option Header × Disposition) :=
  result.map fun outcome => (outcome.state, outcome.output, outcome.disposition)

theorem cached_established_still_forwards :
    view (step openPipeline cached oldInput) = .ok (cached, some wire, .forwarded) := by rfl

theorem cached_established_blocked :
    view (step barrier cached oldInput) = .ok (cached, none, .lateDrop) := by rfl

example : forbidden.Holds wire := (Match.accepts_iff _ _).mp (by decide)
example : view (step barrier unreplied oldInput) = .ok (unreplied, none, .lateDrop) := by rfl
example : view (step barrier State.initial freshInput) = .ok (State.initial, none, .lateDrop) := by rfl

example (before : State) (input : Input) (outcome : Outcome) (accepted : step barrier before input = .ok outcome) :
    OutputExcluded forbidden outcome.output := step_output_excluded barrier forbidden barrier_blocks before input outcome accepted

example (trace : Operations.ExecutionTrace initial events results final) (start : Nat)
    (blocked : ∀ event ∈ events.drop start, event.Blocks forbidden) :
    ∀ result ∈ results.drop start, result.Excludes forbidden := trace.suffix_excludes start forbidden blocked

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

def run : IO Unit := do
  let old ← load (step openPipeline cached oldInput)
  ensure (old.output == some wire && old.attachment.classification == StatefulACL.CTState.established)
    "The counterexample must retain an established cached flow through the earlier permit."
  let guarded ← load (step barrier cached oldInput)
  ensure (guarded.output.isNone && guarded.disposition == .lateDrop && guarded.state == cached)
    "A late barrier must exclude the cached output without requiring prior state deletion."
  let early ← load (step barrier unreplied oldInput)
  ensure (early.output.isNone && !early.attachment.fresh && early.attachment.classification == StatefulACL.CTState.new)
    "The barrier must also cover an unreplied NEW packet with a cached binding."
  let fresh ← load (step barrier State.initial freshInput)
  ensure (fresh.output.isNone && fresh.state == State.initial)
    "The barrier must block a fresh candidate before confirmation."
  let reply ← load (step barrier unreplied ⟨0, wire.reverse, none⟩)
  ensure (reply.output == some original.reverse && reply.state.records.all (·.seenReply))
    "A destination quarantine must retain its exact output-header scope."
  let execution ← load (Operations.execute cached [
    .packet ⟨barrier, oldInput⟩, .erase 0 original, .packet ⟨barrier, freshInput⟩])
  ensure (execution.results.length == 3 && execution.final.records.isEmpty &&
    execution.results.all (fun result => result.packet.all (·.output.isNone)))
    "The barrier must remain effective across explicit deletion and a later fresh attempt."
  IO.println "Operational output exclusion tests passed."

end NetlibTest.Revocation
