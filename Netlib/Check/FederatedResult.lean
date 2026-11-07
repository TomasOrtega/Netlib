import Netlib.Check.FederatedQueries
import Netlib.Check.FederatedRefinement

/-!
# Public query results on checked native revisions

Availability expands the retained public must-path through checked native
paths. Isolation and mediation follow the native-to-public upper refinement.
-/

namespace Netlib.Federation.Queries

variable {leftContract rightContract : Contract} {left right : Revision}
variable {intent : Intent} {query : Query}

def NativeMeaning (left right : Revision) (first second : Case) (intent : Intent)
    (query : Query) (header : Packet.Header) : Prop :=
  let network := Composition.nativeModel left right first second intent.borders header
  let source := Composition.anchor left right query.source
  let target := Composition.anchor left right query.target
  match query.kind with
  | .reach => network.Reachable source target
  | .isolate => ¬network.Reachable source target
  | .mediated => ¬network.Bypass (fun node => Composition.project left right node ∈ query.gateways) source target

theorem AtRole.reference {reference : PublicRef} {role : Role}
    (value : AtRole leftContract rightContract reference role) :
    reference ∈ references leftContract rightContract := by
  rcases reference with ⟨side, node⟩
  cases side with
  | left => exact (Composition.reference_left _ _ _).mpr value.known
  | right => exact (Composition.reference_right _ _ _).mpr value.known

theorem Result.first_mem (value : Result leftContract rightContract intent query) :
    value.first ∈ leftContract.cases :=
  List.mem_of_find?_eq_some value.firstFound

theorem Result.second_mem (value : Result leftContract rightContract intent query) :
    value.second ∈ rightContract.cases :=
  List.mem_of_find?_eq_some value.secondFound

theorem Result.second_accepted (value : Result leftContract rightContract intent query)
    (header : Packet.Header) (accepted : value.first.selector.accepts header = true) :
    value.second.selector.accepts header = true := by
  rw [← value.agreement.2.1]
  exact accepted

theorem Result.source_known (value : Result leftContract rightContract intent query) :
    query.source ∈ references leftContract rightContract :=
  value.validated.source.reference

theorem Result.target_known (value : Result leftContract rightContract intent query) :
    query.target ∈ references leftContract rightContract :=
  value.validated.target.reference

theorem Result.gateways_typed (value : Result leftContract rightContract intent query) :
    ∀ gateway ∈ query.gateways, ∃ node,
      (contracts leftContract rightContract gateway.side).node? gateway.node = some node ∧
        node.role = .enforcement := by
  intro gateway member
  obtain ⟨typed⟩ := value.validated.gateways gateway member
  exact ⟨typed.node, typed.found, typed.roleEq⟩

theorem Result.public_walk (value : Result leftContract rightContract intent query)
    (kind : query.kind = .reach) :
    Network.Walk (publicModel leftContract rightContract value.first value.second intent.borders true)
      query.source query.target value.witness := by
  apply Certificate.validPath_walk
  simpa only [WitnessValid, kind] using value.witnessValid

theorem Result.native_reach (value : Result leftContract rightContract intent query)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (header : Packet.Header) (accepted : value.first.selector.accepts header = true)
    (kind : query.kind = .reach) :
    (Composition.nativeModel left right value.first value.second intent.borders header).Reachable
      (Composition.anchor left right query.source) (Composition.anchor left right query.target) :=
  (Composition.lower leftChecked rightChecked value.first value.second value.first_mem value.second_mem
    intent.borders header accepted (value.second_accepted header accepted)).reachable (value.public_walk kind).reachable

theorem Result.native_walk (value : Result leftContract rightContract intent query)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (header : Packet.Header) (accepted : value.first.selector.accepts header = true)
    (kind : query.kind = .reach) :
    Network.Walk (publicModel leftContract rightContract value.first value.second intent.borders true)
        query.source query.target value.witness ∧
      ∃ trace, Network.Walk (Composition.nativeModel left right value.first value.second intent.borders header)
        (Composition.anchor left right query.source) (Composition.anchor left right query.target) trace :=
  ⟨value.public_walk kind,
    Network.Walk.exists_of_reachable (value.native_reach leftChecked rightChecked header accepted kind)⟩

theorem Result.native_isolate (value : Result leftContract rightContract intent query)
    (compatible : Compatibility.Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (header : Packet.Header) (accepted : value.first.selector.accepts header = true)
    (kind : query.kind = .isolate) :
    ¬(Composition.nativeModel left right value.first value.second intent.borders header).Reachable
      (Composition.anchor left right query.source) (Composition.anchor left right query.target) := by
  intro path
  have projected := (Composition.upper compatible leftChecked rightChecked value.first value.second
    value.first_mem value.second_mem header accepted (value.second_accepted header accepted)).toRefinement.reachable path
  change (publicModel leftContract rightContract value.first value.second intent.borders false).Reachable
    (Composition.project left right (Composition.anchor left right query.source))
    (Composition.project left right (Composition.anchor left right query.target)) at projected
  rw [Composition.anchor_project leftChecked rightChecked query.source value.source_known,
    Composition.anchor_project leftChecked rightChecked query.target value.target_known] at projected
  exact (show ¬(publicModel leftContract rightContract value.first value.second intent.borders false).Reachable
    query.source query.target from by simpa only [Meaning, kind] using value.correct) projected

theorem Result.public_mediated (value : Result leftContract rightContract intent query)
    (kind : query.kind = .mediated) :
    (publicModel leftContract rightContract value.first value.second intent.borders false).Mediated
      (· = query.source) (· = query.target) (· ∈ query.gateways) := by
  intro source target sourceEq targetEq bypass
  subst source target
  exact (show ¬(publicModel leftContract rightContract value.first value.second intent.borders false).Bypass
    (· ∈ query.gateways) query.source query.target from by simpa only [Meaning, kind] using value.correct) bypass

theorem Result.native_mediated (value : Result leftContract rightContract intent query)
    (compatible : Compatibility.Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (header : Packet.Header) (accepted : value.first.selector.accepts header = true)
    (kind : query.kind = .mediated) :
    ¬(Composition.nativeModel left right value.first value.second intent.borders header).Bypass
      (fun node => Composition.project left right node ∈ query.gateways)
      (Composition.anchor left right query.source) (Composition.anchor left right query.target) := by
  have mediated := (Composition.upper compatible leftChecked rightChecked value.first value.second
    value.first_mem value.second_mem header accepted (value.second_accepted header accepted)).mediated
    (value.public_mediated kind)
  exact mediated _ _ (Composition.anchor_project leftChecked rightChecked query.source value.source_known)
    (Composition.anchor_project leftChecked rightChecked query.target value.target_known)

theorem Result.native_correct (value : Result leftContract rightContract intent query)
    (compatible : Compatibility.Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (header : Packet.Header) (accepted : value.first.selector.accepts header = true) :
    NativeMeaning left right value.first value.second intent query header := by
  cases kind : query.kind with
  | reach => simpa only [NativeMeaning, kind] using value.native_reach leftChecked rightChecked header accepted kind
  | isolate => simpa only [NativeMeaning, kind] using value.native_isolate compatible leftChecked rightChecked header accepted kind
  | mediated => simpa only [NativeMeaning, kind] using value.native_mediated compatible leftChecked rightChecked header accepted kind

theorem Result.native_enforcement (value : Result leftContract rightContract intent query)
    (compatible : Compatibility.Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (header : Packet.Header) (accepted : value.first.selector.accepts header = true)
    (kind : query.kind = .mediated) :
    (Composition.nativeModel left right value.first value.second intent.borders header).Mediated
      (· = Composition.anchor left right query.source) (· = Composition.anchor left right query.target)
      (Composition.Enforcement left right) :=
  Composition.mediated_enforcement compatible leftChecked rightChecked value.first value.second
    value.first_mem value.second_mem header accepted (value.second_accepted header accepted)
    query.source query.target value.source_known value.target_known query.gateways
    (Composition.enforcementOnly_of_found _ _ _ value.gateways_typed) (value.public_mediated kind)

theorem Result.native_mediated_on (value : Result leftContract rightContract intent query)
    (compatible : Compatibility.Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (header : Packet.Header) (accepted : value.first.selector.accepts header = true)
    (kind : query.kind = .mediated) (side : Side)
    (sameSide : ∀ gateway ∈ query.gateways, gateway.side = side) :
    (Composition.nativeModel left right value.first value.second intent.borders header).Mediated
      (· = Composition.anchor left right query.source) (· = Composition.anchor left right query.target)
      (fun node => Composition.EnforcementOn side left right node ∧
        Composition.project left right node ∈ query.gateways) :=
  Composition.mediated_on compatible leftChecked rightChecked value.first value.second value.first_mem value.second_mem
    header accepted (value.second_accepted header accepted) query.source query.target value.source_known value.target_known
    query.gateways value.gateways_typed side sameSide (value.public_mediated kind)

end Netlib.Federation.Queries
