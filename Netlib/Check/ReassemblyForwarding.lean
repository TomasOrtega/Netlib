import Netlib.Check.MTUForwarding
import Netlib.Protocol.ReassemblyForwarding
import Netlib.Protocol.IPv4ReassemblyFacts
import Netlib.Protocol.IPv4ReassemblyLayout

/-!
# Raw IPv4 ingress reassembly replay

Post-defragmentation observations use raw IPv4 bytes. Output captures retain Ethernet envelopes.
Observed families check computed emissions without replacing computed state or selecting a layout.
-/

namespace Netlib.Check.ReassemblyForwarding

open Packet Protocol
namespace Model
export Netlib.Protocol.ReassemblyForwarding (State Pipeline Input Completed Result Source Outcome
  allowsDF source input process step budget exceeds)
end Model

abbrev Config := Check.ConntrackLifecycle.Config
abbrev State := Model.State

structure RawIPv4 where
  bytes : List UInt8
  decoded : IPv4Fragment.Decoded
  checked : IPv4InputFragment.decode bytes = .ok decoded

def rawIPv4 (bytes : List UInt8) : Except String RawIPv4 :=
  match checked : IPv4InputFragment.decode bytes with
  | .error error => .error error
  | .ok decoded => .ok ⟨bytes, decoded, checked⟩

structure RawUDP where
  bytes : List UInt8
  decoded : UDP.DecodedIPv4
  checked : UDP.decodeIPv4 bytes = .ok decoded

def rawUDP (bytes : List UInt8) : Except String RawUDP :=
  match checked : UDP.decodeIPv4 bytes with
  | .error error => .error error
  | .ok decoded => .ok ⟨bytes, decoded, checked⟩

structure WireFragment where
  bytes : List UInt8
  envelope : Import.EthernetIPv4.Envelope
  decoded : IPv4Fragment.Decoded
  ethernet : Import.EthernetIPv4.decode bytes = .ok envelope
  ipv4 : IPv4InputFragment.decode envelope.payload = .ok decoded

def wireFragment (bytes : List UInt8) : Except String WireFragment := do
  match ethernet : Import.EthernetIPv4.decode bytes with
  | .error error => throw error
  | .ok envelope =>
    match ipv4 : IPv4InputFragment.decode envelope.payload with
    | .error error => throw error
    | .ok decoded => return ⟨bytes, envelope, decoded, ethernet, ipv4⟩

structure Environment where
  forwarding : Check.MTUForwarding.Environment
  userBase : Nat

def Environment.pipeline (environment : Environment) (config : Config) : Model.Pipeline :=
  ⟨environment.forwarding.pipeline config, config.nat.candidate⟩

def arrival (environment : Environment) (now zone vif : Nat) (packet : RawIPv4) : Model.Input :=
  ⟨now, ⟨environment.userBase + zone, vif⟩, zone, packet.decoded⟩

structure PacketObservation where
  reassembled : Option RawIPv4
  forwarded : List WireFragment

def singleWholeRequired (completed : Model.Completed) : Bool :=
  !completed.reassembled.reassembled &&
    (completed.outcome.selectedMTU.map (fun mtu => decide (completed.source.packet.ip.packet.wireLength ≤ mtu.val))).getD false

def wholeLayoutMatches (completed : Model.Completed) (forwarded : List WireFragment) : Bool :=
  if singleWholeRequired completed then
    match forwarded with
    | [first] => decide (first.decoded.packet.offset.val = 0) && !first.decoded.packet.moreFragments
    | _ => false
  else true

def OutputMatches (completed : Model.Completed) (forwarded : List WireFragment) : Prop :=
  match completed.outcome.output, completed.outcome.sizeCap, forwarded with
  | none, _, [] => True
  | some emission, some cap, first :: rest =>
    (Model.allowsDF completed.reassembled first.decoded.packet.dontFragment = true ∧
      IPv4Refragmentation.Accepts emission.decoded.ip.packet cap first.decoded.packet.dontFragment
        ((first :: rest).map (·.decoded))) ∧ wholeLayoutMatches completed (first :: rest) = true
  | _, _, _ => False

instance (completed : Model.Completed) (forwarded : List WireFragment) :
    Decidable (OutputMatches completed forwarded) := by
  unfold OutputMatches
  split <;> infer_instance

def PacketObservation.Matches (observed : PacketObservation) (result : Model.Result) : Prop :=
  observed.reassembled.map (·.decoded.packet.toPacket) = result.reassembly.output.map (·.packet) ∧
    match result.completed with
    | none => observed.forwarded.isEmpty = true
    | some completed => OutputMatches completed observed.forwarded

instance (observed : PacketObservation) (result : Model.Result) : Decidable (observed.Matches result) := by
  unfold PacketObservation.Matches
  cases result.completed <;> infer_instance

inductive Event where
  | fragment (now : Nat) (config : Config) (policy : IPv4Reassembly.Policy) (zone vif : Nat)
      (packet : RawIPv4) (observed : PacketObservation) (state : Option Import.ConntrackNetlink.Snapshot)
  | wait (now : Nat) (state : Option Import.ConntrackNetlink.Snapshot)
  | erase (now zone : Nat) (packet : RawUDP) (state : Option Import.ConntrackNetlink.Snapshot)

def Event.stateObservation : Event → Option Import.ConntrackNetlink.Snapshot
  | .fragment _ _ _ _ _ _ _ state | .wait _ state | .erase _ _ _ state => state

def Event.isFragment : Event → Bool
  | .fragment .. => true
  | _ => false

structure Result where
  state : State
  valid : state.conntrack.Valid
  fragment : Option Model.Result

def age (before : State) (now : Nat) : State :=
  ⟨{ before.fragments.age now with lastTime := now }, before.conntrack⟩

def step (environment : Environment) (before : State) : Event → Except String Result
  | .fragment now config policy zone vif packet _ _ => do
    let result ← Model.step (environment.pipeline config) policy before (arrival environment now zone vif packet)
    return ⟨result.state, result.valid, some result⟩
  | .wait now _ => do
    if now < before.fragments.lastTime then throw "Event times must be monotonic."
    if valid : before.conntrack.check = true then
      return ⟨age before now, (ConntrackLifecycle.State.check_correct _).mp valid, none⟩
    else throw "The ordinary conntrack table is invalid."
  | .erase now zone packet _ => do
    if now < before.fragments.lastTime then throw "Event times must be monotonic."
    let erased ← (ConntrackLifecycle.Operations.step before.conntrack (.erase zone packet.decoded.header)).mapError (·.describe)
    return ⟨⟨(age before now).fragments, erased.state⟩, erased.valid, none⟩

structure Observation where
  index : Nat
  event : Event
  raw : Lean.Json

def StateMatches (event : Event) (after : State) : Prop :=
  ∀ snapshot, event.stateObservation = some snapshot →
    Check.ConntrackLifecycle.SameRecords after.conntrack (Check.ConntrackLifecycle.snapshotState snapshot)

def stateMatches (event : Event) (after : State) : Bool :=
  match event.stateObservation with
  | none => true
  | some snapshot => Check.ConntrackLifecycle.sameRecords after.conntrack (Check.ConntrackLifecycle.snapshotState snapshot)

theorem stateMatches_correct (event : Event) (after : State) : stateMatches event after = true ↔ StateMatches event after := by
  cases found : event.stateObservation <;> simp [stateMatches, StateMatches, found, Check.ConntrackLifecycle.sameRecords_correct]

def PacketMatches (event : Event) (result : Result) : Prop :=
  match event, result.fragment with
  | .fragment _ _ _ _ _ _ observed _, some actual => observed.Matches actual
  | .wait .., none | .erase .., none => True
  | _, _ => False

instance (event : Event) (result : Result) : Decidable (PacketMatches event result) := by
  cases result with
  | mk state valid fragment => cases event <;> cases fragment <;> unfold PacketMatches <;> infer_instance

def Matches (observation : Observation) (result : Result) : Prop :=
  PacketMatches observation.event result ∧ StateMatches observation.event result.state

def passed (observation : Observation) (result : Result) : Bool :=
  decide (PacketMatches observation.event result) && stateMatches observation.event result.state

theorem passed_correct (observation : Observation) (result : Result) :
    passed observation result = true ↔ Matches observation result := by
  simp [passed, Matches, stateMatches_correct]

def replay (environment : Environment) : Replay.System State Observation Result where
  step before observation := step environment before observation.event
  state := Result.state
  passed := passed
  Matches := Matches
  correct := passed_correct

abbrev Finding := Replay.Finding Observation Result
abbrev Agreement (environment : Environment) := Replay.Agreement (replay environment)
abbrev Report (environment : Environment) (initial : State) (observations : List Observation) :=
  Replay.Report (replay environment) initial observations

def audit (environment : Environment) (initial : State) (observations : List Observation) :
    Except String (Report environment initial observations) := Replay.audit (replay environment) initial observations

def Report.compliant (report : Report environment initial observations) : Bool := report.findings.all (·.passed)

theorem Report.compliant_iff (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.correct

theorem Report.valid (report : Report environment initial observations) (valid : initial.conntrack.Valid) :
    report.final.conntrack.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.conntrack.Valid :=
  report.trace.invariant (fun state => state.conntrack.Valid) (fun _ _ result _ _ => result.valid) valid

theorem Report.finding_matches (report : Report environment initial observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) : Matches finding.observation finding.result :=
  Replay.Report.finding_matches report compliant finding member

theorem step_fragment (environment : Environment) (before : State) (now : Nat) (config : Config)
    (policy : IPv4Reassembly.Policy) (zone vif : Nat) (packet : RawIPv4) (observed : PacketObservation)
    (snapshot : Option Import.ConntrackNetlink.Snapshot) (result : Result)
    (computed : step environment before (.fragment now config policy zone vif packet observed snapshot) = .ok result) :
    ∃ actual, Model.step (environment.pipeline config) policy before (arrival environment now zone vif packet) = .ok actual ∧
      result.fragment = some actual ∧ result.state = actual.state := by
  cases actual : Model.step (environment.pipeline config) policy before (arrival environment now zone vif packet) with
  | error error => simp [step, actual, bind, Except.bind] at computed
  | ok value =>
    simp only [step, actual, bind, Except.bind, pure, Except.pure] at computed
    cases computed
    exact ⟨value, rfl, rfl, rfl⟩

theorem step_completed (pipeline : Model.Pipeline) (policy : IPv4Reassembly.Policy) (before : State)
    (input : Model.Input) (result : Model.Result) (completed : Model.Completed)
    (computed : Model.step pipeline policy before input = .ok result) (seen : result.completed = some completed) :
    ∃ prepared : ConntrackLifecycle.Prepared completed.wire.lifecycle,
      IPv4Reassembly.arrive policy before.fragments input.now input.domain input.fragment = .ok result.reassembly ∧
      result.reassembly.output = some completed.reassembled ∧
      Model.source completed.reassembled = .ok completed.source ∧
      completed.wire = Model.input pipeline before.conntrack input.zone completed.source ∧
      ConntrackLifecycle.prepare before.conntrack completed.wire.lifecycle = .ok prepared ∧
      Model.process pipeline completed.reassembled completed.source completed.wire completed.same prepared = .ok completed.outcome ∧
      result.state.conntrack = completed.outcome.state ∧ result.state.fragments = result.reassembly.state := by
  unfold Model.step at computed
  split at computed
  · cases received : IPv4Reassembly.arrive policy before.fragments input.now input.domain input.fragment with
    | error error => simp [received, Except.mapError, bind, Except.bind] at computed
    | ok fragments =>
      simp only [received, Except.mapError, bind, Except.bind] at computed
      cases output : fragments.output with
      | none =>
        simp only [output, pure, Except.pure] at computed
        cases computed
        cases seen
      | some packet =>
        simp only [output] at computed
        cases decoded : Model.source packet with
        | error error => simp [decoded] at computed
        | ok source =>
          simp only [decoded] at computed
          cases attached : ConntrackLifecycle.prepare before.conntrack
              (Model.input pipeline before.conntrack input.zone source).lifecycle with
          | error error => simp [attached] at computed
          | ok prepared =>
            simp only [attached] at computed
            cases processed : Model.process pipeline packet source
                (Model.input pipeline before.conntrack input.zone source) rfl prepared with
            | error error => simp [processed] at computed
            | ok outcome =>
              simp only [processed, pure, Except.pure] at computed
              cases computed
              have equal := Option.some.inj seen
              subst completed
              exact ⟨prepared, rfl, output, decoded, rfl, attached, processed, rfl, rfl⟩
  · simp [throw] at computed

theorem step_reassembly (pipeline : Model.Pipeline) (policy : IPv4Reassembly.Policy) (before : State)
    (input : Model.Input) (result : Model.Result) (computed : Model.step pipeline policy before input = .ok result) :
    IPv4Reassembly.arrive policy before.fragments input.now input.domain input.fragment = .ok result.reassembly ∧
      result.state.fragments = result.reassembly.state := by
  cases completed : result.completed with
  | some value =>
    obtain ⟨_, received, _, _, _, _, _, _, same⟩ := step_completed pipeline policy before input result value computed completed
    exact ⟨received, same⟩
  | none =>
    unfold Model.step at computed
    split at computed
    · cases received : IPv4Reassembly.arrive policy before.fragments input.now input.domain input.fragment with
      | error error => simp [received, Except.mapError, bind, Except.bind] at computed
      | ok fragments =>
        simp only [received, Except.mapError, bind, Except.bind] at computed
        cases output : fragments.output with
        | none =>
          simp only [output, pure, Except.pure] at computed
          cases computed
          exact ⟨rfl, rfl⟩
        | some packet =>
          simp only [output] at computed
          cases decoded : Model.source packet with
          | error error => simp [decoded] at computed
          | ok source =>
            simp only [decoded] at computed
            cases attached : ConntrackLifecycle.prepare before.conntrack
                (Model.input pipeline before.conntrack input.zone source).lifecycle with
            | error error => simp [attached] at computed
            | ok prepared =>
              simp only [attached] at computed
              cases processed : Model.process pipeline packet source
                  (Model.input pipeline before.conntrack input.zone source) rfl prepared with
              | error error => simp [processed] at computed
              | ok outcome =>
                simp only [processed, pure, Except.pure] at computed
                cases computed
                cases completed
    · simp [throw] at computed

theorem step_queue_valid (environment : Environment) (before : State) (event : Event) (result : Result)
    (valid : before.fragments.Valid) (computed : step environment before event = .ok result) : result.state.fragments.Valid := by
  cases event with
  | fragment now config policy zone vif packet observed snapshot =>
    obtain ⟨actual, stepped, _, state⟩ := step_fragment environment before now config policy zone vif packet observed snapshot result computed
    obtain ⟨received, same⟩ := step_reassembly _ _ _ _ _ stepped
    rw [state, same]
    exact IPv4Reassembly.arrive_valid _ _ _ _ _ _ received valid
  | wait now snapshot =>
    by_cases backwards : now < before.fragments.lastTime
    · simp [step, backwards, throw, bind, Except.bind] at computed
    · by_cases checked : before.conntrack.check = true
      · simp [step, backwards, checked] at computed
        cases computed
        exact IPv4Reassembly.State.age_valid _ _ valid
      · simp [step, backwards, checked, throw] at computed
  | erase now zone packet snapshot =>
    by_cases backwards : now < before.fragments.lastTime
    · simp [step, backwards, throw, bind, Except.bind] at computed
    · cases erased : ConntrackLifecycle.Operations.step before.conntrack (.erase zone packet.decoded.header) with
      | error error => simp [step, backwards, erased, Except.mapError, bind, Except.bind] at computed
      | ok actual =>
        simp [step, backwards, erased, Except.mapError, bind, Except.bind] at computed
        cases computed
        exact IPv4Reassembly.State.age_valid _ _ valid

theorem Report.queue_valid (report : Report environment initial observations) (valid : initial.fragments.Valid) :
    report.final.fragments.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.fragments.Valid :=
  report.trace.invariant (fun state => state.fragments.Valid)
    (fun before observation result valid computed => step_queue_valid environment before observation.event result valid computed) valid

theorem step_queue_layout (environment : Environment) (before : State) (event : Event) (result : Result)
    (valid : before.fragments.LayoutValid) (computed : step environment before event = .ok result) :
    result.state.fragments.LayoutValid := by
  cases event with
  | fragment now config policy zone vif packet observed snapshot =>
    obtain ⟨actual, stepped, _, state⟩ := step_fragment environment before now config policy zone vif packet observed snapshot result computed
    obtain ⟨received, same⟩ := step_reassembly _ _ _ _ _ stepped
    rw [state, same]
    exact IPv4Reassembly.arrive_layout _ _ _ _ _ _ received valid
  | wait now snapshot =>
    by_cases backwards : now < before.fragments.lastTime
    · simp [step, backwards, throw, bind, Except.bind] at computed
    · by_cases checked : before.conntrack.check = true
      · simp [step, backwards, checked] at computed
        cases computed
        have aged := IPv4Reassembly.State.age_layout before.fragments now valid
        exact ⟨aged.unique, aged.queues⟩
      · simp [step, backwards, checked, throw] at computed
  | erase now zone packet snapshot =>
    by_cases backwards : now < before.fragments.lastTime
    · simp [step, backwards, throw, bind, Except.bind] at computed
    · cases erased : ConntrackLifecycle.Operations.step before.conntrack (.erase zone packet.decoded.header) with
      | error error => simp [step, backwards, erased, Except.mapError, bind, Except.bind] at computed
      | ok actual =>
        simp [step, backwards, erased, Except.mapError, bind, Except.bind] at computed
        cases computed
        have aged := IPv4Reassembly.State.age_layout before.fragments now valid
        exact ⟨aged.unique, aged.queues⟩

theorem Report.queue_layout (report : Report environment initial observations) (valid : initial.fragments.LayoutValid) :
    report.final.fragments.LayoutValid ∧ ∀ finding ∈ report.findings, finding.result.state.fragments.LayoutValid :=
  report.trace.invariant (fun state => state.fragments.LayoutValid)
    (fun before observation result valid computed => step_queue_layout environment before observation.event result valid computed) valid

theorem step_queue_sources (environment : Environment) (before : State) (event : Event) (result : Result)
    (history : List IPv4Fragment.Decoded) (sources : before.fragments.Sources history)
    (computed : step environment before event = .ok result) :
    result.state.fragments.Sources (((fun input : Event => match input with
      | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
      | _ => []) event) ++ history) := by
  cases event with
  | fragment now config policy zone vif packet observed snapshot =>
    obtain ⟨actual, stepped, _, state⟩ := step_fragment environment before now config policy zone vif packet observed snapshot result computed
    obtain ⟨received, same⟩ := step_reassembly _ _ _ _ _ stepped
    rw [state, same]
    exact IPv4Reassembly.arrive_sources _ _ _ _ _ _ _ received sources
  | wait now snapshot =>
    by_cases backwards : now < before.fragments.lastTime
    · simp [step, backwards, throw, bind, Except.bind] at computed
    · by_cases checked : before.conntrack.check = true
      · simp [step, backwards, checked] at computed
        cases computed
        exact IPv4Reassembly.State.age_sources _ _ _ sources
      · simp [step, backwards, checked, throw] at computed
  | erase now zone packet snapshot =>
    by_cases backwards : now < before.fragments.lastTime
    · simp [step, backwards, throw, bind, Except.bind] at computed
    · cases erased : ConntrackLifecycle.Operations.step before.conntrack (.erase zone packet.decoded.header) with
      | error error => simp [step, backwards, erased, Except.mapError, bind, Except.bind] at computed
      | ok actual =>
        simp [step, backwards, erased, Except.mapError, bind, Except.bind] at computed
        cases computed
        exact IPv4Reassembly.State.age_sources _ _ _ sources

theorem trace_queue_sources
    (trace : Replay.Trace (replay environment) initial findings final)
    (history : List IPv4Fragment.Decoded) (sources : initial.fragments.Sources history) :
    final.fragments.Sources (findings.reverse.flatMap (fun finding => match finding.observation.event with
      | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
      | _ => []) ++ history) ∧
    ∀ finding ∈ findings, ∃ prior later before,
      findings = prior ++ finding :: later ∧
      step environment before finding.observation.event = .ok finding.result ∧
      before.fragments.Sources (prior.reverse.flatMap (fun finding => match finding.observation.event with
        | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
        | _ => []) ++ history) := by
  induction trace generalizing history with
  | nil => exact ⟨sources, by simp⟩
  | @cons before final head tail computed rest ih =>
    have accepted : step environment before head.observation.event = .ok head.result := computed
    have next := step_queue_sources environment before head.observation.event head.result history sources accepted
    obtain ⟨last, each⟩ := ih _ next
    constructor
    · simpa [List.reverse_cons, List.flatMap_append, List.append_assoc] using last
    · intro finding member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨[], tail, before, rfl, accepted, sources⟩
      · obtain ⟨prior, later, preceding, covered, stepped, previous⟩ := each finding member
        refine ⟨head :: prior, later, preceding, by simp [covered], stepped, ?_⟩
        simpa [List.reverse_cons, List.flatMap_append, List.append_assoc] using previous

theorem Report.queue_sources (report : Report environment initial observations)
    (history : List IPv4Fragment.Decoded) (sources : initial.fragments.Sources history) :
    report.final.fragments.Sources (observations.reverse.flatMap (fun observation => match observation.event with
      | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
      | _ => []) ++ history) ∧
    ∀ finding ∈ report.findings, ∃ prior later before,
      observations = prior ++ finding.observation :: later ∧
      step environment before finding.observation.event = .ok finding.result ∧
      before.fragments.Sources (prior.reverse.flatMap (fun observation => match observation.event with
        | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
        | _ => []) ++ history) ∧
      finding.result.state.fragments.Sources ((finding.observation :: prior.reverse).flatMap
        (fun observation => match observation.event with
          | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
          | _ => []) ++ history) := by
  obtain ⟨last, each⟩ := trace_queue_sources report.trace history sources
  constructor
  · have aligned : observations.reverse.flatMap (fun observation => match observation.event with
        | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
        | _ => []) = report.findings.reverse.flatMap (fun finding => match finding.observation.event with
          | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
          | _ => []) := by
      have covered := congrArg (fun values : List Observation => values.reverse.flatMap
        (fun observation => match observation.event with
          | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
          | _ => [])) report.covered.symm
      simpa only [← List.map_reverse, List.flatMap_map] using covered
    simpa only [aligned] using last
  · intro finding member
    obtain ⟨prior, later, before, covered, computed, previous⟩ := each finding member
    refine ⟨prior.map (·.observation), later.map (·.observation), before, ?_, computed, ?_, ?_⟩
    · rw [← report.covered, covered]
      simp
    · simpa only [← List.map_reverse, List.flatMap_map] using previous
    · have current := step_queue_sources environment before finding.observation.event finding.result _ previous computed
      simpa only [List.flatMap_cons, ← List.map_reverse, List.flatMap_map, List.append_assoc] using current

theorem Report.output_source_prefix (report : Report environment initial observations)
    (history : List IPv4Fragment.Decoded) (sources : initial.fragments.Sources history)
    (finding : Finding) (member : finding ∈ report.findings)
    (now : Nat) (config : Config) (policy : IPv4Reassembly.Policy) (zone vif : Nat) (packet : RawIPv4)
    (observed : PacketObservation) (snapshot : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .fragment now config policy zone vif packet observed snapshot)
    (actual : Model.Result) (computed : finding.result.fragment = some actual)
    (output : IPv4Reassembly.Output) (emitted : actual.reassembly.output = some output)
    (piece : IPv4Reassembly.Piece) (stored : piece ∈ output.pieces) :
    ∃ prior later,
      observations = prior ++ finding.observation :: later ∧
      piece.fragment ∈ (finding.observation :: prior.reverse).flatMap
        (fun observation => match observation.event with
          | .fragment _ _ _ _ _ packet _ _ => [packet.decoded]
          | _ => []) ++ history := by
  obtain ⟨prior, later, before, covered, stepped, previous, _⟩ :=
    (report.queue_sources history sources).2 finding member
  rw [event] at stepped
  obtain ⟨value, accepted, same, _⟩ := step_fragment environment before now config policy zone vif packet observed snapshot finding.result stepped
  have equal : value = actual := Option.some.inj (same.symm.trans computed)
  subst value
  obtain ⟨received, _⟩ := step_reassembly _ _ _ _ _ accepted
  have origin := IPv4Reassembly.arrive_output_sources _ _ _ _ _ _ _ _ received emitted previous piece stored
  refine ⟨prior, later, covered, ?_⟩
  simpa only [List.flatMap_cons, event, List.singleton_append, List.cons_append, List.nil_append, arrival] using origin

theorem Report.observed_output_source_member (report : Report environment initial observations)
    (history : List IPv4Fragment.Decoded) (sources : initial.fragments.Sources history)
    (finding : Finding) (member : finding ∈ report.findings)
    (now : Nat) (config : Config) (policy : IPv4Reassembly.Policy) (zone vif : Nat) (packet : RawIPv4)
    (observed : PacketObservation) (snapshot : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .fragment now config policy zone vif packet observed snapshot)
    (actual : Model.Result) (computed : finding.result.fragment = some actual)
    (output : IPv4Reassembly.Output) (emitted : actual.reassembly.output = some output)
    (piece : IPv4Reassembly.Piece) (stored : piece ∈ output.pieces) :
    ∃ prior later,
      observations = prior ++ finding.observation :: later ∧
      (piece.fragment ∈ history ∨ ∃ input ∈ prior ++ [finding.observation], ∃ raw : RawIPv4,
        (match input.event with
          | .fragment _ _ _ _ _ packet _ _ => packet = raw
          | _ => False) ∧
        raw.decoded = piece.fragment ∧ IPv4InputFragment.decode raw.bytes = .ok piece.fragment) := by
  obtain ⟨prior, later, covered, origin⟩ := report.output_source_prefix history sources finding member
    now config policy zone vif packet observed snapshot event actual computed output emitted piece stored
  refine ⟨prior, later, covered, ?_⟩
  rcases List.mem_append.mp origin with current | previous
  · obtain ⟨input, belongs, inputFragment⟩ := List.mem_flatMap.mp current
    have within : input ∈ prior ++ [finding.observation] := by
      rcases List.mem_cons.mp belongs with rfl | previous
      · simp
      · exact List.mem_append_left _ ((List.mem_reverse.mp previous))
    cases eventEq : input.event with
    | fragment timestamp config policy zone vif raw observed snapshot =>
      simp only [eventEq, List.mem_singleton] at inputFragment
      exact Or.inr ⟨input, within, raw, by simp only [eventEq], inputFragment.symm,
        by simpa only [inputFragment] using raw.checked⟩
    | wait timestamp snapshot => simp [eventEq] at inputFragment
    | erase timestamp zone raw snapshot => simp [eventEq] at inputFragment
  · exact Or.inl previous

theorem output_matches_nonempty (completed : Model.Completed) (first : WireFragment) (rest : List WireFragment)
    (matched : OutputMatches completed (first :: rest)) :
    ∃ (emission : WireForwarding.Emission completed.wire.packet) (cap : IPv4Refragmentation.Budget),
      completed.outcome.output = some emission ∧ completed.outcome.sizeCap = some cap ∧
      Model.allowsDF completed.reassembled first.decoded.packet.dontFragment = true ∧
      IPv4Refragmentation.Accepts emission.decoded.ip.packet cap first.decoded.packet.dontFragment
        ((first :: rest).map (·.decoded)) := by
  cases emitted : completed.outcome.output with
  | none => simp [OutputMatches, emitted] at matched
  | some emission =>
    cases sized : completed.outcome.sizeCap with
    | none => simp [OutputMatches, emitted, sized] at matched
    | some cap =>
      simp only [OutputMatches, emitted, sized] at matched
      exact ⟨emission, cap, rfl, rfl, matched.1⟩

theorem Report.observed_output_facts (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (now : Nat) (config : Config) (policy : IPv4Reassembly.Policy) (zone vif : Nat) (packet : RawIPv4)
    (observed : PacketObservation) (snapshot : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .fragment now config policy zone vif packet observed snapshot)
    (first : WireFragment) (rest : List WireFragment) (seen : observed.forwarded = first :: rest) :
    ∃ (before : State) (actual : Model.Result) (completed : Model.Completed)
      (prepared : ConntrackLifecycle.Prepared completed.wire.lifecycle)
      (emission : WireForwarding.Emission completed.wire.packet) (cap : IPv4Refragmentation.Budget) (hop : String),
      Model.step (environment.pipeline config) policy before (arrival environment now zone vif packet) = .ok actual ∧
      actual.completed = some completed ∧
      IPv4Reassembly.arrive policy before.fragments now (arrival environment now zone vif packet).domain packet.decoded =
        .ok actual.reassembly ∧ actual.reassembly.output = some completed.reassembled ∧
      Model.source completed.reassembled = .ok completed.source ∧
      completed.wire = Model.input (environment.pipeline config) before.conntrack zone completed.source ∧
      ConntrackLifecycle.prepare before.conntrack completed.wire.lifecycle = .ok prepared ∧
      Model.process (environment.pipeline config) completed.reassembled completed.source completed.wire completed.same prepared =
        .ok completed.outcome ∧ completed.outcome.output = some emission ∧ completed.outcome.sizeCap = some cap ∧
      Model.allowsDF completed.reassembled first.decoded.packet.dontFragment = true ∧
      IPv4Refragmentation.Accepts emission.decoded.ip.packet cap first.decoded.packet.dontFragment ((first :: rest).map (·.decoded)) ∧
      WireForwarding.route (environment.pipeline config).forwarding.forwarding completed.wire prepared = some hop ∧
      1 < completed.wire.packet.ip.packet.ttl.toNat ∧
      Model.exceeds completed.reassembled (environment.forwarding.mtu hop) = false ∧
      Model.budget completed.reassembled (environment.forwarding.mtu hop) = .ok cap ∧
      cap.val ≤ (environment.forwarding.mtu hop).val ∧
      (completed.reassembled.reassembled = true → cap.val ≤ completed.reassembled.maxSize) ∧
      emission.decoded.datagram.payload = completed.source.packet.datagram.payload ∧
      (∀ fragment ∈ first :: rest, fragment.decoded.packet.wireLength ≤ cap.val ∧
        fragment.decoded.packet.ttl.toNat = completed.reassembled.packet.ttl.toNat - 1) ∧
      actual.state.conntrack.Valid := by
  obtain ⟨before, computed⟩ := report.trace.steps finding member
  change step environment before finding.observation.event = .ok finding.result at computed
  rw [event] at computed
  obtain ⟨actual, stepped, stored, _⟩ := step_fragment environment before now config policy zone vif packet observed snapshot finding.result computed
  have matched := (report.finding_matches compliant finding member).1
  rw [event] at matched
  simp only [PacketMatches, stored] at matched
  have matchedOutput := matched.2
  cases completedEq : actual.completed with
  | none => simp [completedEq, seen] at matchedOutput
  | some completed =>
    simp only [completedEq] at matchedOutput
    rw [seen] at matchedOutput
    obtain ⟨emission, cap, emitted, sized, allowed, accepted⟩ := output_matches_nonempty completed first rest matchedOutput
    obtain ⟨prepared, received, queueOutput, sourced, wire, attached, processed, _, _⟩ :=
      step_completed (environment.pipeline config) policy before (arrival environment now zone vif packet) actual completed stepped completedEq
    obtain ⟨hop, _, routed, live, permitted, capComputed, _, _, _⟩ :=
      Netlib.Protocol.ReassemblyForwarding.process_output_cap _ _ _ _ _ prepared _ processed cap sized emission emitted
    have bounds := Netlib.Protocol.ReassemblyForwarding.budget_bounds _ _ cap capComputed
    let certified : IPv4Refragmentation.CertifiedFamily emission.decoded.ip.packet cap first.decoded.packet.dontFragment :=
      ⟨(first :: rest).map (·.decoded), accepted⟩
    have payload := emission.payload.trans (congrArg (fun packet => packet.datagram.payload) completed.same)
    have inputTTL : completed.wire.packet.ip.packet.ttl.toNat = completed.reassembled.packet.ttl.toNat := by
      rw [completed.same, completed.source.same]
    refine ⟨before, actual, completed, prepared, emission, cap, hop, stepped, completedEq,
      received, queueOutput, sourced, wire, attached, processed, emitted, sized, allowed, accepted,
      routed, live, permitted, capComputed, bounds.1, bounds.2, payload, ?_, actual.valid⟩
    intro fragment belongs
    have member : fragment.decoded ∈ certified.fragments := List.mem_map.mpr ⟨fragment, belongs, rfl⟩
    have ttl := (certified.metadata fragment.decoded member).2.2.2.1
    exact ⟨certified.fits fragment.decoded member,
      (congrArg UInt8.toNat ttl).trans (emission.ttl.trans (congrArg (· - 1) inputTTL))⟩

structure PolicyBinding where
  id : String
  policy : IPv4Reassembly.Policy

structure Input where
  environment : Environment
  configs : List Config
  policies : List PolicyBinding
  initial : State
  initialValid : initial.conntrack.Valid
  events : List Observation

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def optional (parse : Lean.Json → Except String α) (json : Lean.Json) : Except String (Option α) :=
  match json with
  | .null => .ok none
  | value => some <$> parse value

private def rawBytes (json : Lean.Json) : Except String (List UInt8) := do
  Import.EAPOL.bytesFromHex (← json.getStr?)

private def rawPacket (json : Lean.Json) : Except String RawIPv4 := do rawIPv4 (← rawBytes json)

private def wholeObservation (json : Lean.Json) : Except String RawIPv4 := do
  let packet ← rawPacket json
  require (!packet.decoded.packet.moreFragments && packet.decoded.packet.offset.val == 0)
    "A post-defragmentation observation must contain a whole IPv4 packet."
  return packet

private def packetObservation (json : Lean.Json) : Except String PacketObservation := do
  Import.PacketFields.fields json ["reassembled", "forwarded"]
  let reassembled ← optional wholeObservation (← json.getObjVal? "reassembled")
  let values ← (← json.getObjVal? "forwarded").getArr?
  let forwarded ← values.toList.mapM fun value => do wireFragment (← rawBytes value)
  return ⟨reassembled, forwarded⟩

private def stateObservation (json : Lean.Json) : Except String (Option Import.ConntrackNetlink.Snapshot) :=
  optional Import.ConntrackNetlink.Snapshot.fromJson json

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "routing", "mtus", "configs", "initial", "reassembly", "events"]
  let base ← ["schema", "routing", "mtus", "configs", "initial", "events"].mapM fun key => do
    return (key, ← json.getObjVal? key)
  let domain ← Check.MTUForwarding.domainFromJson (Lean.Json.mkObj base)
  let reassembly ← json.getObjVal? "reassembly"
  Import.PacketFields.fields reassembly ["policies", "userBase"]
  let userBase ← (← reassembly.getObjVal? "userBase").getNat?
  require (userBase + 65535 < 4294967296) "The effective defragmentation user must fit in 32 bits."
  let policyValues ← (← reassembly.getObjVal? "policies").getArr?
  let mut policies : List PolicyBinding := []
  for value in policyValues do
    Import.PacketFields.fields value ["id", "timeout"]
    let id ← (← value.getObjVal? "id").getStr?
    let timeout ← (← value.getObjVal? "timeout").getNat?
    require (0 < timeout) "The fragment queue timeout must be positive."
    require (!(policies.any (·.id == id))) "Queue policy IDs must be unique."
    policies := policies ++ [⟨id, ⟨timeout⟩⟩]
  let values ← (← json.getObjVal? "events").getArr?
  let mut events := []
  for index in [:values.size] do
    let value := values[index]!
    let kind ← (← value.getObjVal? "type").getStr?
    let event ← match kind with
      | "fragment" => do
        Import.PacketFields.fields value ["type", "at", "config", "queuePolicy", "zone", "vif", "rawIPv4", "observed", "state"]
        let id ← (← value.getObjVal? "config").getStr?
        let some config := domain.configs.find? (·.id == id) | throw s!"Unknown forwarding configuration: {id}."
        let policyID ← (← value.getObjVal? "queuePolicy").getStr?
        let some policy := policies.find? (·.id == policyID) | throw s!"Unknown fragment queue policy: {policyID}."
        let now ← (← value.getObjVal? "at").getNat?
        let zone ← (← value.getObjVal? "zone").getNat?
        let vif ← (← value.getObjVal? "vif").getNat?
        require (zone < 65536) "A conntrack zone must fit in 16 bits."
        require (vif < 4294967296) "An L3 master interface index must fit in 32 bits."
        pure (.fragment now config policy.policy zone vif (← rawPacket (← value.getObjVal? "rawIPv4"))
          (← packetObservation (← value.getObjVal? "observed")) (← stateObservation (← value.getObjVal? "state")))
      | "wait" => do
        Import.PacketFields.fields value ["type", "at", "state"]
        pure (.wait (← (← value.getObjVal? "at").getNat?) (← stateObservation (← value.getObjVal? "state")))
      | "erase" => do
        Import.PacketFields.fields value ["type", "at", "zone", "rawIPv4", "state"]
        let zone ← (← value.getObjVal? "zone").getNat?
        require (zone < 65536) "A conntrack zone must fit in 16 bits."
        let packet ← rawUDP (← rawBytes (← value.getObjVal? "rawIPv4"))
        pure (.erase (← (← value.getObjVal? "at").getNat?) zone packet (← stateObservation (← value.getObjVal? "state")))
      | _ => throw s!"Unsupported reassembly forwarding event: {kind}."
    events := events ++ [⟨index, event, value⟩]
  require (events.any (·.event.isFragment)) "Supply at least one IPv4 fragment arrival."
  return ⟨⟨domain.environment, userBase⟩, domain.configs, policies, ⟨.initial, domain.initial⟩, domain.initialValid, events⟩

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.environment input.initial input.events) :=
  audit input.environment input.initial input.events

def Report.assumptions : List String := [
  "Input and post-defragmentation observations are authoritative raw IPv4 bytes; output observations are actual untagged Ethernet captures.",
  "Captures identify complete selected observation scopes; null reassembled and empty forwarded arrays assert absence.",
  "Queue domains retain the namespace's defragmentation user plus conntrack zone and the L3 master interface identity.",
  "Times are monotonic; expiry is processed before each event, with ipfrag_max_dist zero and successful allocation.",
  "The selected queue policy sets newly created queue deadlines; later policy changes do not refresh existing queues.",
  "The completion event selects the current routing, NAT, and filter policy; incomplete arrivals never attach conntrack.",
  "Completed UDP packets must pass the strict transport profile; invalid transport acceptance without NAT is unsupported.",
  "Output families satisfy payload, metadata, checksum, coverage, DF-choice, and size-cap contracts without selecting a unique Linux allocation path.",
  "TTL or DF rejection has no selected UDP output; generated ICMP observations are outside this checker.",
  "Administrative conntrack erase does not erase unrelated IP fragment queues; native timeout seconds and IDs are not compared.",
  "Options, bridge paths, bypass hooks, concurrent updates, memory pressure, offload intermediates, and kernel C refinement are outside this profile."]

private def packetJson (packet : IPv4.Packet) : Lean.Json := Lean.Json.mkObj [
  ("tos", Lean.toJson packet.tos.toNat), ("identification", Lean.toJson packet.identification.val),
  ("ttl", Lean.toJson packet.ttl.toNat), ("dontFragment", Lean.toJson packet.dontFragment),
  ("source", Lean.toJson packet.source.val), ("destination", Lean.toJson packet.destination.val),
  ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex packet.payload))]

private def dispositionText : MTUForwarding.Disposition → String
  | .forwarded => "forwarded" | .routeDrop => "routeDrop" | .ttlExpired => "ttlExpired"
  | .mtuExceeded => "mtuExceeded" | .forwardDrop => "forwardDrop" | .lateDrop => "lateDrop"

private def classificationText : StatefulACL.CTState → String
  | .new => "new" | .established => "established" | .related => "related"
  | .invalid => "invalid" | .untracked => "untracked"

private def completedJson (completed : Model.Completed) : Lean.Json := Lean.Json.mkObj [
  ("classification", .str (classificationText completed.outcome.attachment.classification)),
  ("fresh", Lean.toJson completed.outcome.attachment.fresh),
  ("afterDestination", Import.PacketFields.headerJson completed.outcome.afterDestination),
  ("afterSource", Import.PacketFields.optionalHeaderJson completed.outcome.afterSource),
  ("nextHop", Lean.toJson completed.outcome.nextHop),
  ("disposition", .str (dispositionText completed.outcome.disposition)),
  ("routeMTU", Lean.toJson (completed.outcome.selectedMTU.map (·.val))),
  ("fragmentSizeCap", Lean.toJson (completed.outcome.sizeCap.map (·.val))),
  ("reassembled", Lean.toJson completed.reassembled.reassembled),
  ("maxSize", Lean.toJson completed.reassembled.maxSize),
  ("maxDFSize", Lean.toJson completed.reassembled.maxDFSize),
  ("output", (completed.outcome.output.map (fun emission => packetJson emission.decoded.ip.packet)).getD .null)]

def Report.renderJson (report : Report environment initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "ipv4-ingress-reassembly-forwarding"),
  ("assumptions", Lean.toJson Report.assumptions), ("eventCount", Lean.toJson observations.length),
  ("final", Check.ConntrackLifecycle.stateJson report.final.conntrack),
  ("pendingQueues", Lean.toJson report.final.fragments.queues.length),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.index}"), ("matched", Lean.toJson finding.passed),
    ("reassembled", (finding.result.fragment.bind (·.reassembly.output) |>.map (fun output => packetJson output.packet)).getD .null),
    ("expected", (finding.result.fragment.bind (·.completed) |>.map completedJson).getD .null),
    ("pendingQueues", Lean.toJson finding.result.state.fragments.queues.length),
    ("stateObserved", Lean.toJson finding.observation.event.stateObservation.isSome),
    ("stateMatched", Lean.toJson (stateMatches finding.observation.event finding.result.state)),
    ("expectedState", Check.ConntrackLifecycle.stateJson finding.result.state.conntrack)]))]

def Report.render (report : Report environment initial observations) : String :=
  (if report.compliant then "REASSEMBLY FORWARDING OBSERVATIONS MATCH\n" else "REASSEMBLY FORWARDING OBSERVATIONS MISMATCH\n") ++
    report.renderJson.pretty

end Netlib.Check.ReassemblyForwarding
