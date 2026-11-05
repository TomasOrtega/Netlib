import Netlib.Check.ConntrackRevocation

namespace NetlibTest.ConntrackRevocation

open Netlib Packet Protocol Protocol.ConntrackLifecycle
open Netlib.Check.ConntrackLifecycle
open Netlib.Check.ConntrackRevocation

private def forbidden : Match := { destination := some ⟨3325256706, 32⟩ }

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def guardSnapshot (json : Lean.Json) : Except String Lean.Json := do
  let objects ← (← json.getObjVal? "nftables").getArr?
  let chain ← objects[2]!.getObjVal? "chain"
  let table ← chain.getObjVal? "table"
  let name ← chain.getObjVal? "name"
  let rule := Lean.Json.mkObj [("rule", Lean.Json.mkObj [
    ("family", .str "ip"), ("table", table), ("chain", name), ("handle", Lean.toJson (999999 : Nat)),
    ("comment", .str "synthetic output quarantine"),
    ("expr", .arr #[Lean.Json.mkObj [("match", Lean.Json.mkObj [
      ("op", .str "=="), ("left", Lean.Json.mkObj [("payload", Lean.Json.mkObj [
        ("protocol", .str "ip"), ("field", .str "daddr")])]), ("right", .str "198.51.100.2/32")])],
      Lean.Json.mkObj [("drop", .null)]])])]
  return json.setObjVal! "nftables" (.arr ((objects.toList.take 3 ++ [rule] ++ objects.toList.drop 3).toArray))

private def guardedReplay (json : Lean.Json) (start : Nat) : Except String Lean.Json := do
  let configs ← (← json.getObjVal? "configs").getArr?
  let guarded ← configs.toList.mapM fun config => do
    let id ← (← config.getObjVal? "id").getStr?
    let late ← guardSnapshot (← config.getObjVal? "late")
    return (config.setObjVal! "id" (.str (id ++ "-barrier"))).setObjVal! "late" late
  let source ← (← json.getObjVal? "events").getArr?
  let events ← source.toList.zipIdx |>.mapM fun (event, index) => do
    if start ≤ index && (← (← event.getObjVal? "type").getStr?) == "packet" then
      let id ← (← event.getObjVal? "config").getStr?
      return event.setObjVal! "config" (.str (id ++ "-barrier"))
    else return event
  return (json.setObjVal! "configs" (.arr (configs.toList ++ guarded).toArray)).setObjVal! "events" (.arr events.toArray)

private def expectedObservations (input : Netlib.Check.ConntrackLifecycle.Input) : Except String Lean.Json := do
  let mut before := input.initial
  let mut events := []
  for observation in input.events do
    let result ← (Operations.step before (observation.event.toModel input.routing before)).mapError (·.describe)
    let event := match result.packet with
      | none => observation.raw
      | some outcome => observation.raw.setObjVal! "observed" (PacketObservation.expected outcome).renderJson
    events := events ++ [event]
    before := result.state
  return input.raw.setObjVal! "events" (.arr events.toArray)

example (report : Report routing initial observations) (start : Nat)
    (barriers : blocksFrom observations start forbidden = true) :
    ∀ finding ∈ report.findings.drop start, finding.result.Excludes forbidden :=
  report.model_outputs_excluded start forbidden barriers

example (report : Report routing initial observations) (start : Nat)
    (barriers : blocksFrom observations start forbidden = true) (compliant : report.compliant = true) :
    ∀ observation ∈ observations.drop start, OutputExcluded forbidden observation.event.observedOutput :=
  report.observed_outputs_excluded start forbidden barriers compliant

def run : IO Unit := do
  let json ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/lifecycle/replay.json"))
  let native ← unwrap (Netlib.Check.ConntrackLifecycle.Input.fromJson json)
  let current ← unwrap native.check
  ensure (current.compliant && !blocksFrom native.events 5 forbidden)
    "Agreement with the native trace must not imply revocation of its cached established flow."
  let some retained := current.findings[5]?.bind (·.result.packet)
    | throw (IO.userError "The native retained packet is missing.")
  ensure (retained.attachment.classification == StatefulACL.CTState.established &&
    !retained.attachment.fresh && retained.output.any forbidden.accepts)
    "The counterexample must contain a cached established output to the quarantined backend."
  let guarded ← unwrap (Netlib.Check.ConntrackLifecycle.Input.fromJson (← unwrap (guardedReplay json 5)))
  ensure (blocksFrom guarded.events 5 forbidden && !blocksFrom guarded.events 4 forbidden)
    "The barrier certificate must cover exactly the selected suffix, including repeated configurations."
  let mismatched ← unwrap guarded.check
  ensure (!mismatched.compliant && (mismatched.findings.drop 5).all (fun finding =>
    finding.result.packet.all (fun outcome => !outcome.output.any forbidden.accepts)))
    "Model exclusion must hold even while stale observed outputs make replay noncompliant."
  let some stopped := mismatched.findings[5]?.bind (·.result.packet)
    | throw (IO.userError "The guarded cached packet is missing.")
  ensure (stopped.output.isNone && stopped.disposition == .lateDrop &&
    stopped.attachment.classification == StatefulACL.CTState.established && !stopped.attachment.fresh &&
    stopped.attachment.entry.flow.reply.destinationPort == 40000 && stopped.state.records.all (·.seenReply))
    "Suffix certification must retain the prefix table and block the existing cached binding at the late stage."
  ensure (mismatched.findings[5]?.any (fun finding => finding.observation.event.observedOutput.any forbidden.accepts))
    "Noncompliant observations must not acquire an observed-output guarantee."
  let coherent ← unwrap (expectedObservations guarded)
  let matched ← unwrap (Netlib.Check.ConntrackLifecycle.Input.fromJson coherent)
  let report ← unwrap matched.check
  ensure (report.compliant && blocksFrom matched.events 5 forbidden &&
    (matched.events.drop 5).all (fun observation => !observation.event.observedOutput.any forbidden.accepts))
    "A compliant guarded replay must transfer exclusion to every supplied suffix output."
  ensure (report.findings.length == native.events.length && report.final.records.isEmpty)
    "The guarded suffix must retain event coverage and explicit deletion."
  let events ← unwrap ((← unwrap (coherent.getObjVal? "events")).getArr?)
  let firstObserved ← unwrap (events[0]!.getObjVal? "observed")
  let firstEvent := events[0]!.setObjVal! "observed" (firstObserved.setObjVal! "fresh" (.bool false))
  let badPrefix ← unwrap (Netlib.Check.ConntrackLifecycle.Input.fromJson
    (coherent.setObjVal! "events" (.arr (events.set! 0 firstEvent))))
  let prefixReport ← unwrap badPrefix.check
  ensure (!prefixReport.compliant && blocksFrom badPrefix.events 5 forbidden &&
    (prefixReport.findings.drop 5).all (·.passed))
    "A mismatched prefix observation must not reset the table or change the guarded suffix expectations."
  let indexed : Netlib.Check.ConntrackLifecycle.Input :=
    { matched with events := matched.events.map (fun observation : Observation => { observation with index := 0 }) }
  let indexedReport ← unwrap indexed.check
  ensure (blocksFrom indexed.events 5 forbidden && !blocksFrom indexed.events 4 forbidden && indexedReport.compliant)
    "Cutover uses list position rather than the supplied source index."
  IO.println "Tracked revocation suffix tests passed."

end NetlibTest.ConntrackRevocation
