import Netlib.Packet.Transfer
import Netlib.Network.Certificate
import Netlib.Network.Change

namespace Netlib.Check.Transfer

open Packet Certificate

namespace Search

universe u
variable {State : Type u} [DecidableEq State]

def validSeparation (states : List State) (edge : State → State → Bool)
    (source : State) (targets region : List State) : Bool :=
  decide (source ∈ region) && targets.all (fun target => decide (target ∉ region)) &&
    region.all (fun a => states.all (fun b => !edge a b || decide (b ∈ region)))

theorem validSeparation_cut (states : List State) (edge : State → State → Bool)
    (source : State) (targets region : List State)
    (valid : validSeparation states edge source targets region = true)
    (target : State) (member : target ∈ targets) :
    validCut states edge source target region = true := by
  simp only [validSeparation, Bool.and_eq_true] at valid
  simp only [validCut, Bool.and_eq_true]
  exact ⟨⟨valid.1.1, (List.all_eq_true.mp valid.1.2) target member⟩, valid.2⟩

theorem validPath_walk (states : List State) (edge : State → State → Bool)
    (source target : State) (trace : List State)
    (valid : validPath states edge source target trace = true) :
    Network.Walk (finiteNetwork states edge) source target trace := by
  induction trace generalizing source with
  | nil => simp [validPath] at valid
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [validPath, Bool.and_eq_true, decide_eq_true_eq] at valid
      obtain ⟨⟨rfl, rfl⟩, _⟩ := valid
      exact .nil a
    | cons b rest =>
      simp only [validPath, Bool.and_eq_true, decide_eq_true_eq] at valid
      obtain ⟨⟨⟨⟨rfl, aMember⟩, bMember⟩, step⟩, tail⟩ := valid
      exact .cons ⟨aMember, bMember, step⟩ (ih b tail)

inductive Decision (states : List State) (edge : State → State → Bool)
    (source : State) (targets : List State) where
  | reachable (target : State) (member : target ∈ targets) (trace : List State)
      (valid : validPath states edge source target trace = true)
  | isolated (region : List State)
      (valid : validSeparation states edge source targets region = true)

namespace Decision

variable {states : List State} {edge : State → State → Bool} {source : State} {targets : List State}

def value : Decision states edge source targets → Bool
  | .reachable _ _ _ _ => true
  | .isolated _ _ => false

def path? : Decision states edge source targets → Option (List State)
  | .reachable _ _ trace _ => some trace
  | .isolated _ _ => none

def cut? : Decision states edge source targets → Option (List State)
  | .reachable _ _ _ _ => none
  | .isolated region _ => some region

theorem path_valid (result : Decision states edge source targets) (trace : List State)
    (found : result.path? = some trace) :
    ∃ target ∈ targets, validPath states edge source target trace = true := by
  cases result with
  | reachable target member recorded valid => cases found; exact ⟨target, member, valid⟩
  | isolated => cases found

theorem cut_valid (result : Decision states edge source targets) (region : List State)
    (found : result.cut? = some region) : validSeparation states edge source targets region = true := by
  cases result with
  | reachable => cases found
  | isolated recorded valid => cases found; exact valid

theorem correct (result : Decision states edge source targets) :
    result.value = true ↔
      ∃ target ∈ targets, (finiteNetwork states edge).Reachable source target := by
  cases result with
  | reachable target member trace valid =>
    exact ⟨fun _ => ⟨target, member, validPath_sound _ _ _ _ _ valid⟩, fun _ => rfl⟩
  | isolated region valid =>
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨target, member, path⟩
      exact False.elim (validCut_sound _ _ _ _ _
        (validSeparation_cut _ _ _ _ _ valid target member) path)

end Decision

private def discover (states : List State) (edge : State → State → Bool) (source : State) :
    List (State × List State) := Id.run do
  let mut known := [(source, [source])]
  let mut pending := known
  for _ in List.range states.length do
    match pending with
    | [] => break
    | (a, path) :: rest =>
      pending := rest
      for b in states do
        if edge a b && !(known.any (fun entry => decide (entry.1 = b))) then
          let discovered := (b, path ++ [b])
          known := known ++ [discovered]
          pending := pending ++ [discovered]
  return known

/-- Search limits cannot establish absence. Only a validated closed cut can do so. -/
def decide (states : List State) (edge : State → State → Bool)
    (source : State) (targets : List State) : Except String (Decision states edge source targets) := do
  let known := discover states edge source
  match found : known.find? (fun (entry : State × List State) => if entry.1 ∈ targets then true else false) with
  | some (target, trace) =>
    have member : target ∈ targets := by simpa using List.find?_some found
    if valid : validPath states edge source target trace = true then
      return .reachable target member trace valid
    else throw "Internal error: transfer path certificate rejected."
  | none =>
    let region := known.map Prod.fst
    if valid : validSeparation states edge source targets region = true then
      return .isolated region valid
    else throw "Internal error: transfer cut certificate rejected."

end Search

abbrev State := String × Header

/-- The guard sees the incoming packet. Rewriting occurs before arrival at the target. -/
structure Link where
  source : String
  target : String
  guard : Match := {}
  rewrite : Packet.Rewrite := {}
  deriving Repr, BEq, DecidableEq

structure Config where
  nodes : List String
  links : List Link
  deriving Repr

namespace Config

def Step (config : Config) (before after : State) : Prop :=
  before.1 ∈ config.nodes ∧ after.1 ∈ config.nodes ∧
    ∃ link ∈ config.links, link.source = before.1 ∧ link.target = after.1 ∧
      link.guard.accepts before.2 = true ∧ link.rewrite.apply before.2 = after.2

def transfer (config : Config) : Packet.Transfer String where
  step source header target nextHeader := config.Step (source, header) (target, nextHeader)

def network (config : Config) : Network State := config.transfer.network

def edge (config : Config) (before after : State) : Bool :=
  decide (before.1 ∈ config.nodes) && decide (after.1 ∈ config.nodes) &&
  config.links.any (fun link => decide (link.source = before.1) && decide (link.target = after.1) &&
    link.guard.accepts before.2 && decide (link.rewrite.apply before.2 = after.2))

theorem edge_correct (config : Config) (before after : State) :
    config.edge before after = true ↔ config.network.link before after := by
  simp only [edge, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    network, transfer, Packet.Transfer.network, Step, and_assoc]

def space (config : Config) (initial : Header) : Rewrite.Universe :=
  Rewrite.Universe.ofRewrites initial (config.links.map Link.rewrite)

def states (config : Config) (initial : Header) : List State :=
  config.nodes.flatMap fun node => (config.space initial).headers.map (node, ·)

def stateCount (config : Config) (initial : Header) : Nat :=
  config.nodes.length * (config.space initial).headerCount

theorem states_length (config : Config) (initial : Header) :
    (config.states initial).length = config.stateCount initial := by
  have count : ∀ nodes : List String,
      (nodes.flatMap fun node => (config.space initial).headers.map (node, ·)).length =
        nodes.length * (config.space initial).headers.length := by
    intro nodes
    induction nodes with
    | nil => simp
    | cons node nodes ih =>
      simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]
  simpa only [states, stateCount, Rewrite.Universe.headers_length] using count config.nodes

theorem mem_states (config : Config) (initial : Header) (state : State) :
    state ∈ config.states initial ↔ state.1 ∈ config.nodes ∧ state.2 ∈ (config.space initial).headers := by
  rcases state with ⟨node, header⟩
  simp [states, List.mem_flatMap, List.mem_map]

theorem initial_mem (config : Config) (initial : Header) (node : String)
    (declared : node ∈ config.nodes) : (node, initial) ∈ config.states initial := by
  apply (config.mem_states initial _).mpr
  exact ⟨declared, Rewrite.Universe.initial_mem initial (config.links.map Link.rewrite)⟩

theorem states_closed (config : Config) (initial : Header) :
    config.network.Closed (· ∈ config.states initial) := by
  intro before after inside step
  obtain ⟨_, headerInside⟩ := (config.mem_states initial before).mp inside
  obtain ⟨_, targetDeclared, link, member, _, _, _, rewritten⟩ := step
  apply (config.mem_states initial after).mpr
  refine ⟨targetDeclared, ?_⟩
  rw [← rewritten]
  exact Rewrite.Universe.rewrite_mem initial (config.links.map Link.rewrite) link.rewrite
    (List.mem_map.mpr ⟨link, member, rfl⟩) before.2 headerInside

def filtered (config : Config) (allowed : State → State → Bool) : Network State :=
  config.network.restrict (fun before after => allowed before after = true)

def filteredEdge (config : Config) (allowed : State → State → Bool) (before after : State) : Bool :=
  config.edge before after && allowed before after

theorem finite_reachable_iff (config : Config) (initial : Header)
    (allowed : State → State → Bool) (source target : State)
    (sourceInside : source ∈ config.states initial) :
    (finiteNetwork (config.states initial) (config.filteredEdge allowed)).Reachable source target ↔
      (config.filtered allowed).Reachable source target := by
  constructor
  · apply Network.Reachable.mono
    intro before after edge
    exact ⟨(config.edge_correct _ _).mp (Bool.and_eq_true_iff.mp edge.2.2).1,
      (Bool.and_eq_true_iff.mp edge.2.2).2⟩
  · intro path
    have lift : ∀ {a b}, (config.filtered allowed).Reachable a b → a ∈ config.states initial →
        (finiteNetwork (config.states initial) (config.filteredEdge allowed)).Reachable a b := by
      intro a b path
      induction path with
      | refl => exact fun _ => .refl _
      | @step a b c step _ ih =>
        intro inside
        have nextInside := config.states_closed initial a b inside step.1
        exact .step ⟨inside, nextInside, Bool.and_eq_true_iff.mpr
          ⟨(config.edge_correct _ _).mpr step.1, step.2⟩⟩ (ih nextInside)
    exact lift path sourceInside

def targetStates (config : Config) (initial : Header) (target : String) : List State :=
  (config.space initial).headers.map (target, ·)

theorem some_target_correct (config : Config) (initial : Header)
    (allowed : State → State → Bool) (source target : String)
    (declared : source ∈ config.nodes)
    (result : Search.Decision (config.states initial) (config.filteredEdge allowed)
      (source, initial) (config.targetStates initial target)) :
    result.value = true ↔ ∃ header, (config.filtered allowed).Reachable (source, initial) (target, header) := by
  rw [result.correct]
  constructor
  · rintro ⟨state, member, reached⟩
    obtain ⟨header, _, rfl⟩ := List.mem_map.mp member
    exact ⟨header, (config.finite_reachable_iff initial allowed _ _
      (config.initial_mem initial source declared)).mp reached⟩
  · rintro ⟨header, reached⟩
    have basePath : config.network.Reachable (source, initial) (target, header) :=
      Network.Reachable.mono (net := config.filtered allowed) (net' := config.network)
        (fun _ _ step => step.1) reached
    have inside := (config.states_closed initial).reachable
      basePath
      (config.initial_mem initial source declared)
    refine ⟨(target, header), List.mem_map.mpr ⟨header, ?_, rfl⟩, ?_⟩
    · exact ((config.mem_states initial _).mp inside).2
    · exact (config.finite_reachable_iff initial allowed _ _
        (config.initial_mem initial source declared)).mpr reached

end Config

inductive Kind where
  | reach | isolate | mediated
  deriving Repr, BEq, DecidableEq

structure Query where
  kind : Kind
  source : String
  target : String
  initial : Header
  gateways : List String := []
  deriving Repr

namespace Query

def Gateway (query : Query) (state : State) : Prop := state.1 ∈ query.gateways

def allowed (query : Query) : State → State → Bool :=
  match query.kind with
  | .mediated => fun before after =>
    !query.gateways.contains before.1 && !query.gateways.contains after.1
  | .reach | .isolate => fun _ _ => true

def Meaning (config : Config) (query : Query) : Prop :=
  match query.kind with
  | .reach => ∃ header, config.network.Reachable (query.source, query.initial) (query.target, header)
  | .isolate => ∀ header, ¬config.network.Reachable (query.source, query.initial) (query.target, header)
  | .mediated => ∀ header,
    ¬config.network.Bypass query.Gateway (query.source, query.initial) (query.target, header)

private theorem filtered_base (config : Config) (query : Query) (ordinary : query.kind ≠ .mediated) :
    config.filtered query.allowed = config.network := by
  unfold Config.filtered Network.restrict
  congr 1
  funext before after
  apply propext
  cases kind : query.kind <;> simp_all [allowed, Config.network, Packet.Transfer.network]

private theorem filtered_bypass (config : Config) (query : Query) (mediated : query.kind = .mediated) :
    config.filtered query.allowed = config.network.without query.Gateway := by
  unfold Config.filtered Network.without Network.restrict
  congr 1
  funext before after
  apply propext
  simp [allowed, mediated, Gateway]

end Query

private abbrev CertificateFor (config : Config) (query : Query) :=
  Search.Decision (config.states query.initial) (config.filteredEdge query.allowed)
    (query.source, query.initial) (config.targetStates query.initial query.target)

/-- The result retains the checked packet-state path or closed cut. -/
inductive Result (config : Config) (query : Query) where
  | endpoint (mediated : query.kind = .mediated)
      (incident : query.source ∈ query.gateways ∨ query.target ∈ query.gateways)
  | searched (declared : query.source ∈ config.nodes)
      (outside : query.kind = .mediated → query.source ∉ query.gateways ∧ query.target ∉ query.gateways)
      (certificate : CertificateFor config query)

namespace Result

def value : Result config query → Bool
  | .endpoint _ _ => true
  | .searched _ _ certificate =>
    match query.kind with
    | .reach => certificate.value
    | .isolate | .mediated => !certificate.value

def path? : Result config query → Option (List State)
  | .endpoint _ _ => none
  | .searched _ _ certificate => certificate.path?

def cut? : Result config query → Option (List State)
  | .endpoint _ _ => none
  | .searched _ _ certificate => certificate.cut?

theorem path_sound (result : Result config query) (trace : List State)
    (found : result.path? = some trace) :
    ∃ header, Network.Walk (config.filtered query.allowed)
      (query.source, query.initial) (query.target, header) trace := by
  cases result with
  | endpoint => cases found
  | searched declared outside certificate =>
    obtain ⟨target, member, valid⟩ := certificate.path_valid trace found
    obtain ⟨header, _, rfl⟩ := List.mem_map.mp member
    refine ⟨header, ?_⟩
    have walk := Search.validPath_walk _ _ _ _ _ valid
    have convert : ∀ {a b trace},
        Network.Walk (finiteNetwork (config.states query.initial)
          (config.filteredEdge query.allowed)) a b trace →
        Network.Walk (config.filtered query.allowed) a b trace := by
      intro a b trace walk
      induction walk with
      | nil => exact .nil _
      | cons edge _ ih =>
        exact .cons ⟨(config.edge_correct _ _).mp (Bool.and_eq_true_iff.mp edge.2.2).1,
          (Bool.and_eq_true_iff.mp edge.2.2).2⟩ ih
    exact convert walk

theorem cut_valid (result : Result config query) (region : List State)
    (found : result.cut? = some region) :
    Search.validSeparation (config.states query.initial) (config.filteredEdge query.allowed)
      (query.source, query.initial) (config.targetStates query.initial query.target) region = true := by
  cases result with
  | endpoint => cases found
  | searched _ _ certificate => exact certificate.cut_valid region found

theorem correct (result : Result config query) : result.value = true ↔ query.Meaning config := by
  cases result with
  | endpoint mediated incident =>
    simp only [value, Query.Meaning, mediated, true_iff]
    intro header bypass
    rcases incident with sourceGateway | targetGateway
    · exact bypass.1 sourceGateway
    · exact bypass.2.1 targetGateway
  | searched declared outside certificate =>
    have reached := config.some_target_correct query.initial query.allowed query.source query.target
      declared certificate
    have absent : (!certificate.value) = true ↔
        ¬∃ header, (config.filtered query.allowed).Reachable
          (query.source, query.initial) (query.target, header) := by
      cases status : certificate.value <;> simp_all
    cases kind : query.kind with
    | reach =>
      have same := Query.filtered_base config query (by simp [kind])
      simpa only [value, kind, Query.Meaning, same] using reached
    | isolate =>
      have same := Query.filtered_base config query (by simp [kind])
      simpa only [value, kind, Query.Meaning, same, not_exists] using absent
    | mediated =>
      obtain ⟨sourceOutside, targetOutside⟩ := outside kind
      have same := Query.filtered_bypass config query kind
      simpa only [value, kind, Query.Meaning, same, not_exists, Network.Bypass,
        Query.Gateway, sourceOutside, targetOutside, not_false_eq_true, true_and] using absent

end Result

private def nameOK (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun char => char.isAlphanum || char == '_' || char == '-' || char == '.')

def Config.validate (config : Config) : Except String Unit := do
  if config.nodes.isEmpty then throw "Supply transfer devices."
  if !(config.nodes.all nameOK) then throw "Invalid transfer device name."
  if config.nodes.eraseDups.length != config.nodes.length then throw "Duplicate transfer device."
  if config.links.eraseDups.length != config.links.length then throw "Duplicate transfer link."
  for link in config.links do
    if !config.nodes.contains link.source || !config.nodes.contains link.target then
      throw "Unknown transfer link endpoint."

def Query.validate (query : Query) (config : Config) : Except String Unit := do
  if !config.nodes.contains query.source || !config.nodes.contains query.target then
    throw "Unknown transfer query endpoint."
  if !(query.gateways.all config.nodes.contains) then throw "Unknown transfer gateway."
  if query.gateways.eraseDups.length != query.gateways.length then throw "Duplicate transfer gateway."
  match query.kind with
  | .mediated =>
    if query.gateways.isEmpty then throw "Supply at least one transfer gateway."
  | .reach | .isolate =>
    if !query.gateways.isEmpty then throw "Only mediated queries accept transfer gateways."

/-- The budget bounds the exact state product before header enumeration starts. -/
def check (config : Config) (query : Query) (budget : Nat := 4096) :
    Except String (Result config query) := do
  config.validate
  query.validate config
  if config.stateCount query.initial > budget then
    throw s!"Transfer needs {config.stateCount query.initial} states; budget is {budget}."
  if declared : query.source ∈ config.nodes then
    if mediated : query.kind = .mediated then
      if incident : query.source ∈ query.gateways ∨ query.target ∈ query.gateways then
        return .endpoint mediated incident
      else
        let certificate ← Search.decide (config.states query.initial) (config.filteredEdge query.allowed)
          (query.source, query.initial) (config.targetStates query.initial query.target)
        return .searched declared (fun _ => by simpa using incident) certificate
    else
      let certificate ← Search.decide (config.states query.initial) (config.filteredEdge query.allowed)
        (query.source, query.initial) (config.targetStates query.initial query.target)
      return .searched declared (fun impossible => False.elim (mediated impossible)) certificate
  else throw "Unknown transfer source."

end Netlib.Check.Transfer
