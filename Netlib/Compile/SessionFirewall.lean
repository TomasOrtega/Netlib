import Netlib.Compile.Nftables
import Netlib.Import.NftablesStateful
import Netlib.Protocol.EAPSession

/-!
# Current-session packet policy

Requirements bind packet classes to application scopes. Compilation rejects overlapping
permit and deny requirements. The emitted policy captures one current session state.
-/

namespace Netlib.Compile.SessionFirewall

open Packet Protocol

structure Intent where
  id : String
  scope : Scope
  test : Match
  deriving Repr, BEq, DecidableEq

def intents (context : Context) (state : EAPSession.State) (requirements : List Intent) : List ACL.Intent :=
  requirements.map fun requirement =>
    ⟨requirement.id, requirement.test,
      if state.session.permits context requirement.scope then .permit else .deny⟩

def Allowed (context : Context) (state : EAPSession.State) (requirements : List Intent) (header : Header) : Prop :=
  ∃ requirement ∈ requirements, state.session.permits context requirement.scope = true ∧
    requirement.test.Holds header

theorem permitted_iff (context : Context) (state : EAPSession.State) (requirements : List Intent) (header : Header) :
    ACL.Permitted (intents context state requirements) header ↔ Allowed context state requirements header := by
  constructor
  · rintro ⟨intent, member, permitted, matched⟩
    unfold intents at member
    obtain ⟨requirement, sourceMember, same⟩ := List.mem_map.mp member
    subst intent
    refine ⟨requirement, sourceMember, ?_, (Match.accepts_iff _ _).mp matched⟩
    cases allowed : state.session.permits context requirement.scope <;> simp_all
  · rintro ⟨requirement, member, allowed, matched⟩
    refine ⟨⟨requirement.id, requirement.test, .permit⟩, ?_, rfl, (Match.accepts_iff _ _).mpr matched⟩
    exact List.mem_map.mpr ⟨requirement, member, by simp [allowed]⟩

structure Certified (context : Context) (state : EAPSession.State) (requirements : List Intent) where
  emitted : Nftables.Emitted (intents context state requirements)

def compile (context : Context) (state : EAPSession.State) (requirements : List Intent) (budget : Nat := 100000) :
    Except (Nftables.Error (intents context state requirements)) (Certified context state requirements) := do
  return ⟨← Nftables.compile (intents context state requirements) budget⟩

def stateful (snapshot : Import.Nftables.Snapshot) : Import.NftablesStateful.Snapshot where
  version := snapshot.version
  releaseName := snapshot.releaseName
  table := snapshot.table
  chain := snapshot.chain
  tableHandle := snapshot.tableHandle
  chainHandle := snapshot.chainHandle
  tableIndex := snapshot.tableIndex
  chainIndex := snapshot.chainIndex
  hook := "forward"
  priority := snapshot.priority
  policy := snapshot.policy
  rules := snapshot.rules.map fun rule => { toSourceRule := rule }

theorem stateful_compile (snapshot : Import.Nftables.Snapshot) :
    (stateful snapshot).compile = StatefulACL.Policy.ofACL snapshot.compile := by
  simp [stateful, Import.NftablesStateful.Snapshot.compile, Import.Nftables.Snapshot.compile,
    StatefulACL.Policy.ofACL, List.map_map, Import.NftablesStateful.SourceRule.compile,
    StatefulACL.Rule.ofRule]
  intro rule _
  rfl

theorem stateful_evaluate (snapshot : Import.Nftables.Snapshot) (fallback : Action)
    (ctstate : StatefulACL.CTState) (header : Header) :
    StatefulACL.Policy.evaluate fallback (stateful snapshot).compile ctstate header = snapshot.evaluate header := by
  rw [stateful_compile, StatefulACL.Policy.evaluate_ofACL, Import.Nftables.Snapshot.compile_evaluate]

theorem stateful_permits (snapshot : Import.Nftables.Snapshot) (ctstate : StatefulACL.CTState) (header : Header) :
    (stateful snapshot).permits ctstate header = snapshot.permits header := by
  rw [← Import.NftablesStateful.Snapshot.compile_allows, stateful_compile,
    StatefulACL.Policy.allows_ofACL, Import.Nftables.Snapshot.compile_allows]

namespace Certified

def snapshot (compiled : Certified context state requirements) : Import.Nftables.Snapshot := compiled.emitted.snapshot

def statefulSnapshot (compiled : Certified context state requirements) : Import.NftablesStateful.Snapshot :=
  stateful compiled.snapshot

def requirementIds (compiled : Certified context state requirements) : List String := compiled.emitted.requirementIds

def toJson (compiled : Certified context state requirements) : Lean.Json := compiled.emitted.toJson

theorem permits_iff (compiled : Certified context state requirements) (header : Header) :
    compiled.snapshot.permits header = true ↔ Allowed context state requirements header := by
  rw [snapshot, compiled.emitted.permits_eq, ACL.Certified.rules, compiled.emitted.compiled.generated,
    ACL.emit_allows_iff, permitted_iff]

theorem permitted_valid (compiled : Certified context state requirements) (safe : state.Safe context)
    (header : Header) (permitted : compiled.snapshot.permits header = true) :
    ∃ requirement ∈ requirements, requirement.test.Holds header ∧
      Session.Valid context state.session requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext context) state.auth := by
  obtain ⟨requirement, member, allowed, matched⟩ := (compiled.permits_iff header).mp permitted
  have valid := (Session.permits_iff context state.session requirement.scope).mp allowed
  have authorized : state.auth.authorized = true := safe.2.1.symm.trans valid.1
  exact ⟨requirement, member, matched, valid, safe.1 authorized⟩

theorem denied_requirement (compiled : Certified context state requirements) (requirement : Intent)
    (member : requirement ∈ requirements) (denied : state.session.permits context requirement.scope = false)
    (header : Header) (matched : requirement.test.Holds header) : compiled.snapshot.permits header = false := by
  rw [snapshot, compiled.emitted.permits_eq]
  apply compiled.emitted.compiled.satisfies.2 header
  refine ⟨⟨requirement.id, requirement.test, .deny⟩, ?_, rfl, (Match.accepts_iff _ _).mpr matched⟩
  apply List.mem_map.mpr
  exact ⟨requirement, member, by simp [denied]⟩

theorem unspecified_denied (compiled : Certified context state requirements) (header : Header)
    (unmatched : ∀ requirement ∈ requirements, ¬requirement.test.Holds header) :
    compiled.snapshot.permits header = false := by
  cases allowed : compiled.snapshot.permits header with
  | false => rfl
  | true =>
    obtain ⟨requirement, member, _, matched⟩ := (compiled.permits_iff header).mp allowed
    exact False.elim (unmatched requirement member matched)

theorem unauthorized_denied (compiled : Certified context state requirements) (coupled : state.Coupled)
    (unauthorized : state.auth.authorized = false) (header : Header) :
    compiled.snapshot.permits header = false := by
  cases allowed : compiled.snapshot.permits header with
  | false => rfl
  | true =>
    obtain ⟨requirement, _, permitted, _⟩ := (compiled.permits_iff header).mp allowed
    have denied := EAPSession.unauthorized_denied context state requirement.scope coupled unauthorized
    simp [denied] at permitted

theorem statefulSnapshot_permits (compiled : Certified context state requirements)
    (ctstate : StatefulACL.CTState) (header : Header) :
    compiled.statefulSnapshot.permits ctstate header = compiled.snapshot.permits header :=
  stateful_permits compiled.snapshot ctstate header

theorem statefulSnapshot_evaluate (compiled : Certified context state requirements) (fallback : Action)
    (ctstate : StatefulACL.CTState) (header : Header) :
    StatefulACL.Policy.evaluate fallback compiled.statefulSnapshot.compile ctstate header =
      compiled.snapshot.evaluate header := stateful_evaluate compiled.snapshot fallback ctstate header

theorem statefulSnapshot_allows (compiled : Certified context state requirements)
    (ctstate : StatefulACL.CTState) (header : Header) :
    compiled.statefulSnapshot.compile.allows ctstate header = compiled.snapshot.permits header := by
  rw [Import.NftablesStateful.Snapshot.compile_allows, compiled.statefulSnapshot_permits]

theorem statefulSnapshot_permitted_valid (compiled : Certified context state requirements) (safe : state.Safe context)
    (ctstate : StatefulACL.CTState) (header : Header)
    (permitted : compiled.statefulSnapshot.permits ctstate header = true) :
    ∃ requirement ∈ requirements, requirement.test.Holds header ∧
      Session.Valid context state.session requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext context) state.auth := by
  exact compiled.permitted_valid safe header ((compiled.statefulSnapshot_permits ctstate header).symm.trans permitted)

end Certified
end Netlib.Compile.SessionFirewall
