import Netlib.Check.BufferedDrain

namespace NetlibTest.BufferedReplay

open Netlib Packet Check.BufferedReplay

private def wire : Header := ⟨3405803777, 3325256706, Protocol.udp, 40000, 9000⟩
private def restored : Header := ⟨3405803778, 3221225986, Protocol.udp, 8080, 31000⟩
private def forbidden : Match := { destination := some ⟨3325256706, 32⟩, protocol := some Protocol.udp }

private def object (fields : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj fields
private def headers (values : List Header) : Lean.Json := Lean.toJson (values.map Import.PacketFields.headerJson)
private def operation : Lean.Json := object [("type", .str "operation"), ("pending", .null)]

private def serve (capacity : Nat) (observed : List Header) (pending : Option (List Header)) : Lean.Json :=
  object [("type", .str "serve"), ("capacity", Lean.toJson capacity), ("served", headers observed),
    ("pending", (pending.map headers).getD .null)]

private def wrap (lifecycle : Lean.Json) : Lean.Json :=
  object [("schema", Lean.toJson (1 : Nat)), ("lifecycle", lifecycle), ("initialPending", headers []),
    ("schedule", Lean.toJson (List.replicate 7 operation ++ [
      serve 1 [wire] (some [restored, wire]), serve 2 [restored, wire] (some []), serve 1 [] (some [])]))]

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def expectAt (values : List α) (index : Nat) : IO α :=
  match values[index]? with
  | some value => pure value
  | none => throw (IO.userError s!"Expected fixture element {index}.")

private def schedule (json : Lean.Json) : Except String (Array Lean.Json) :=
  json.getObjVal? "schedule" >>= Lean.Json.getArr?

private def setSchedule (json : Lean.Json) (values : Array Lean.Json) : Lean.Json :=
  json.setObjVal! "schedule" (.arr values)

private def without (json : Lean.Json) (name : String) : Except String Lean.Json := do
  return object ((← json.getObj?).toList.filter (fun field => field.1 != name))

private def sourceIndices (observations : List Observation) : List Nat :=
  observations.filterMap fun observation => match observation.event with
    | .operation source => some source.index
    | .serve .. => none

example (report : Report routing initial observations) (start drainedAt : Nat) (selection : Match)
    (ready : report.ready start drainedAt selection = true) :
    Theory.QueueDrain.CleanPending (fun header => ¬selection.Holds header) (report.stateAt drainedAt).queue :=
  report.pending_clean_of_ready start drainedAt selection ready

example (report : Report routing initial observations) (start drainedAt : Nat) (selection : Match)
    (ready : report.ready start drainedAt selection = true) :
    ∀ finding ∈ report.findings.drop drainedAt, ∀ header ∈ finding.result.served, ¬selection.Holds header :=
  report.model_served_excluded start drainedAt selection ready

example (report : Report routing initial observations) (start drainedAt : Nat) (selection : Match)
    (ready : report.ready start drainedAt selection = true) (compliant : report.compliant = true) :
    ∀ observation ∈ observations.drop drainedAt, ∀ header ∈ observation.event.observedServed, ¬selection.Holds header :=
  report.observed_served_excluded start drainedAt selection ready compliant

example (report : Report routing initial observations) (start drainedAt : Nat) (selection : Match)
    (ready : report.ready start drainedAt selection = true)
    (future : Protocol.BufferedLifecycle.Trace (report.stateAt drainedAt) events results finalState)
    (barriers : ∀ event ∈ events, event.Blocks selection) :
    ∀ result ∈ results, ∀ header ∈ result.served, ¬selection.Holds header :=
  report.continuation_served_excluded start drainedAt selection ready future barriers

private def baseTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  ensure (report.compliant && report.findings.length == 10 && input.observations.length == 10)
    "The retained operations and declared FIFO service must all match."
  ensure (sourceIndices input.observations == List.range 7)
    "The schedule must consume the lifecycle source operations once in their original order."
  let queued ← expectAt report.findings 6
  ensure (queued.result.state.queue.pending == [wire, restored, wire] && queued.result.served.isEmpty)
    "Only three pre-barrier computed outputs must enter the queue, including duplicate wire headers."
  let first ← expectAt report.findings 7
  let boundary ← expectAt report.findings 8
  let after ← expectAt report.findings 9
  ensure (first.before.queue.pending == [wire, restored, wire] && first.result.served == [wire] &&
      first.result.state.queue.pending == [restored, wire])
    "The first service operation must remove only the oldest queued output."
  ensure (boundary.result.served == [restored, wire] && boundary.result.served.any forbidden.accepts &&
      boundary.result.state.queue.pending.isEmpty)
    "The final flushing batch can contain forbidden old output even though its next queue is clean."
  ensure (after.result.served.isEmpty && report.final.queue.pending.isEmpty &&
      report.final.queue.delivered == [wire, restored, wire] && report.final.tracker.records.isEmpty)
    "An empty later service must preserve prior delivery history and the explicitly deleted tracker state."
  ensure (report.final.queue.delivered.any forbidden.accepts)
    "A clean future-delivery boundary must not erase bad delivered history."
  let rendered := report.renderJson
  let findings ← unwrap ((← unwrap (rendered.getObjVal? "findings")).getArr?)
  ensure ((← unwrap ((← unwrap (findings[0]!.getObjVal? "pendingObserved")).getBool?)) == false &&
      (← unwrap ((← unwrap (findings[8]!.getObjVal? "pendingObserved")).getBool?)) == true)
    "Unobserved pending state and an explicitly observed empty queue must remain distinct."
  let zeroInserted := setSchedule json ((← unwrap (schedule json)).toList.take 3 ++
    [serve 0 [] none] ++ (← unwrap (schedule json)).toList.drop 3 |>.toArray)
  let interleaved ← unwrap (Input.fromJson zeroInserted)
  let interleavedReport ← unwrap interleaved.check
  ensure (interleavedReport.compliant && sourceIndices interleaved.observations == List.range 7 &&
      interleavedReport.final.queue = report.final.queue)
    "Interleaving zero service must retain source-operation order and the complete queue execution."

private def observationTests (json : Lean.Json) : IO Unit := do
  let values ← unwrap (schedule json)
  for observed in [headers [], headers [wire, wire]] do
    let changed := setSchedule json (values.set! 0 (values[0]!.setObjVal! "pending" observed))
    let input ← unwrap (Input.fromJson changed)
    let report ← unwrap input.check
    ensure (!report.compliant && !(← expectAt report.findings 0).passed &&
        (report.findings.drop 1).all (·.passed) && report.final.queue.delivered == [wire, restored, wire])
      "A false pending observation must not replace the queue or poison later service results."
  let missingDuplicate := values[2]!.setObjVal! "pending" (headers [wire, restored])
  let input ← unwrap (Input.fromJson (setSchedule json (values.set! 2 missingDuplicate)))
  let report ← unwrap input.check
  ensure (!(← expectAt report.findings 2).passed && (← expectAt report.findings 7).passed)
    "Pending comparison must preserve FIFO multiplicity instead of treating the queue as a set."
  let wrongService := values[7]!.setObjVal! "served" (headers [restored])
  let input ← unwrap (Input.fromJson (setSchedule json (values.set! 7 wrongService)))
  let report ← unwrap input.check
  ensure (!(← expectAt report.findings 7).passed && (← expectAt report.findings 8).passed &&
      report.final.queue.delivered == [wire, restored, wire])
    "A stale served observation must not determine which model packet is removed."
  let falseEmpty := values[7]!.setObjVal! "pending" (headers [])
  let input ← unwrap (Input.fromJson (setSchedule json (values.set! 7 falseEmpty)))
  let report ← unwrap input.check
  ensure (!(← expectAt report.findings 7).passed && (← expectAt report.findings 8).passed)
    "An observed empty queue must not create a premature drain boundary."
  let lifecycle ← unwrap (json.getObjVal? "lifecycle")
  let events ← unwrap ((← unwrap (lifecycle.getObjVal? "events")).getArr?)
  let observed ← unwrap (events[0]!.getObjVal? "observed")
  let stale := events[0]!.setObjVal! "observed" (observed.setObjVal! "output" .null)
  let changed := json.setObjVal! "lifecycle" (lifecycle.setObjVal! "events" (.arr (events.set! 0 stale)))
  let input ← unwrap (Input.fromJson changed)
  let report ← unwrap input.check
  ensure (!report.compliant && !(← expectAt report.findings 0).passed &&
      (← expectAt report.findings 0).result.admitted == [wire] && (report.findings.drop 1).all (·.passed))
    "Stale lifecycle observations must not suppress computed outputs entering the FIFO."

private def parserTests (json : Lean.Json) : IO Unit := do
  let values ← unwrap (schedule json)
  reject (Input.fromJson (setSchedule json (values.push operation)))
    "Extra operation consumers must be rejected."
  reject (Input.fromJson (setSchedule json ((values.toList.take 6 ++ values.toList.drop 7).toArray)))
    "A schedule missing a lifecycle operation must be rejected."
  reject (Input.fromJson (setSchedule json (values.set! 7
    (values[7]!.setObjVal! "capacity" (Lean.toJson (-1 : Int))))))
    "A negative service capacity must be rejected."
  reject (Input.fromJson (setSchedule json (values.set! 0 (values[0]!.setObjVal! "source" (Lean.toJson (6 : Nat))))))
    "Operation consumers cannot select a source index out of order."
  reject (Input.fromJson (json.setObjVal! "ignored" (.bool true))) "Unknown buffered fields must be rejected."
  reject (Input.fromJson (setSchedule json (values.set! 7 (values[7]!.setObjVal! "ignored" (.bool true)))))
    "Unknown service fields must be rejected."
  reject (Input.fromJson (← unwrap (without json "initialPending"))) "Missing initial queue data must be rejected."
  reject (Input.fromJson (setSchedule json (values.set! 7 (← unwrap (without values[7]! "served")))))
    "A service event must supply its observation list."
  reject (Input.fromJson (setSchedule json (values.set! 7 (values[7]!.setObjVal! "served" .null))))
    "An unobserved service list cannot be confused with an observed empty list."
  reject (Input.parse ("{\"schema\":1," ++ json.compress.drop 1))
    "Duplicate buffered JSON keys must be rejected."

private def certificateTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  ensure (Check.BufferedDrain.blocksFrom input.observations 3 forbidden &&
      !(Check.BufferedDrain.blocksFrom input.observations 2 forbidden))
    "Only the actual post-barrier schedule suffix may certify clean admissions."
  ensure ((report.stateAt 3).queue.pending == [wire, restored, wire] &&
      report.capacityBetween 3 8 == 1 && report.capacityBetween 3 9 == 3)
    "Drain accounting must start from the real cutover queue and count only the selected service interval."
  ensure (report.ready 3 9 forbidden && !(report.ready 3 8 forbidden) &&
      (report.stateAt 8).queue.pending == [restored, wire] && (report.stateAt 9).queue.pending.isEmpty)
    "The flushing boundary is after serve2; the earlier partial-service boundary is premature."
  ensure (!(report.ready 9 3 forbidden) && !(report.ready 3 11 forbidden))
    "Reversed and out-of-range drain positions cannot be ready."
  let indexedObservations := input.observations.map fun observation =>
    let event := match observation.event with
      | .operation source => .operation { source with index := 0 }
      | .serve capacity observed => .serve capacity observed
    { observation with index := 0, event }
  let indexed : Input := { input with observations := indexedObservations }
  let indexedReport ← unwrap indexed.check
  ensure (indexedReport.compliant && indexedReport.ready 3 9 forbidden &&
      !(indexedReport.ready 3 8 forbidden) && (indexedReport.stateAt 3).queue.pending == [wire, restored, wire])
    "Cutover and drain positions must not depend on repeated schedule or source metadata indices."
  let values ← unwrap (schedule json)
  let stale := setSchedule json (values.set! 9 (values[9]!.setObjVal! "served" (headers [wire])))
  let staleInput ← unwrap (Input.fromJson stale)
  let staleReport ← unwrap staleInput.check
  ensure (staleReport.ready 3 9 forbidden && !staleReport.compliant &&
      (← expectAt staleReport.findings 9).result.served.isEmpty)
    "A ready model cannot grant observed-service exclusion to an invented forbidden delivery."
  let initialOld := json.setObjVal! "initialPending" (headers [restored])
  let initialInput ← unwrap (Input.fromJson initialOld)
  let initialReport ← unwrap initialInput.check
  ensure ((initialReport.stateAt 3).queue.pending == [restored, wire, restored, wire] &&
      !(initialReport.ready 3 9 forbidden) && initialReport.ready 3 10 forbidden &&
      (initialReport.stateAt 10).queue.pending.isEmpty && !initialReport.compliant)
    "An arbitrary initial queue must increase the drain obligation even when its observations are stale."
  let lifecycle ← unwrap (json.getObjVal? "lifecycle")
  let configs ← unwrap ((← unwrap (lifecycle.getObjVal? "configs")).getArr?)
  let events ← unwrap ((← unwrap (lifecycle.getObjVal? "events")).getArr?)
  let hidden := (configs[2]!.setObjVal! "id" (.str "unsafe-hidden-context")).setObjVal! "late"
    (← unwrap (configs[0]!.getObjVal? "late"))
  let lifecycle := (lifecycle.setObjVal! "configs" (.arr (configs.push hidden))).setObjVal! "events"
    (.arr (events.set! 5 (events[5]!.setObjVal! "config" (.str "unsafe-hidden-context"))))
  let unsafeInput ← unwrap (Input.fromJson (json.setObjVal! "lifecycle" lifecycle))
  let unsafeReport ← unwrap unsafeInput.check
  ensure (unsafeReport.compliant && !(unsafeReport.ready 3 9 forbidden) &&
      unsafeReport.final.queue.delivered == [wire, restored, wire])
    "An unobserved unsafe late-policy context must invalidate the certificate without requiring a sampled bad output."

def run : IO Unit := do
  let lifecycle ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/revocation/replay.json"))
  let json := wrap lifecycle
  baseTests json
  observationTests json
  parserTests json
  certificateTests json
  IO.println "Buffered replay tests passed."

end NetlibTest.BufferedReplay
