import Netlib.Protocol.Transition
import Netlib.Network.Upgrade

namespace NetlibTest.Transition

open Netlib
open Netlib.Protocol

private def counter : Protocol.Transition Nat Nat :=
  Protocol.Transition.ofFunction (· + ·)

private theorem counter_invariant (lower : Nat) :
    counter.Invariant (fun state => lower ≤ state) := by
  intro before event after initial edge
  change before + event = after at edge
  omega

example : (Protocol.Transition.product counter counter).Invariant
    (fun state => 10 ≤ state.1 ∧ 20 ≤ state.2) :=
  Protocol.Transition.invariant_product (counter_invariant 10) (counter_invariant 20)

example : (Protocol.Transition.product counter counter).Trace (10, 20)
    [.left 3, .both 2 4, .right 1] (15, 25) :=
  .cons (middle := (13, 20)) ⟨rfl, rfl⟩
    (.cons (middle := (15, 24)) ⟨rfl, rfl⟩
      (.cons (middle := (15, 25)) ⟨rfl, rfl⟩ (.nil _)))

private inductive CounterEvent where
  | add (value : Nat)
  | toggle

private def advanceCounter (state : Nat × Bool) : CounterEvent → Nat × Bool
  | .add value => (state.1 + value, state.2)
  | .toggle => (state.1, !state.2)

private def counterRefinement :
    TraceRefinement (Protocol.Transition.ofFunction advanceCounter) counter where
  project := Prod.fst
  labels event := match event with
    | .add value => [value]
    | .toggle => []
  simulate before event after edge := by
    change advanceCounter before event = after at edge
    subst after
    cases event with
    | add value => exact .cons rfl (.nil _)
    | toggle => exact .nil _

example {before after : Nat × Bool} {events : List CounterEvent}
    (initial : 10 ≤ before.1)
    (execution : (Protocol.Transition.ofFunction advanceCounter).Trace before events after) :
    10 ≤ after.1 := counterRefinement.safe (counter_invariant 10) initial execution

example : counterRefinement.labels .toggle = [] := rfl

inductive Node where
  | client
  | oldGateway
  | newGateway
  | server
  | management
  deriving Repr, DecidableEq

structure Deployment where
  oldActive : Bool
  newActive : Bool
  bypass : Bool
  deriving Repr, DecidableEq

def network (state : Deployment) : Network Node where
  link source target :=
    (state.oldActive = true ∧
      ((source = .client ∧ target = .oldGateway) ∨
       (source = .oldGateway ∧ target = .server))) ∨
    (state.newActive = true ∧
      ((source = .client ∧ target = .newGateway) ∨
       (source = .newGateway ∧ target = .server))) ∨
    (state.bypass = true ∧ source = .client ∧ target = .server)

def gateways (node : Node) : Prop := node = .oldGateway ∨ node = .newGateway

def Contract (state : Deployment) : Prop :=
  (network state).Available (· = .client) (· = .server) ∧
  (network state).Mediated (· = .client) (· = .server) gateways ∧
  (network state).Isolated (· = .client) (· = .management)

def observe (state : Deployment) : Bool :=
  (state.oldActive || state.newActive) && !state.bypass

private theorem isolation (state : Deployment) :
    (network state).Isolated (· = .client) (· = .management) := by
  apply Network.isolated_of_closed (fun node => node ≠ .management)
  · intro source target edge _ same
    subst target
    simp [network] at edge
  · intro source same
    subst source
    decide
  · intro target same outside
    exact outside same

private theorem mediation (state : Deployment) (noBypass : state.bypass = false) :
    (network state).Mediated (· = .client) (· = .server) gateways := by
  apply Network.mediated_of_cut (fun node => node = .client)
  · intro source target edge _ targetOutside sourceInside
    subst source
    simp only [network, noBypass, Bool.false_eq_true, false_and, or_false] at edge
    rcases edge with ⟨_, (⟨_, same⟩ | ⟨impossible, _⟩)⟩ | ⟨_, (⟨_, same⟩ | ⟨impossible, _⟩)⟩
    · exact False.elim (targetOutside (.inl same))
    · cases impossible
    · exact False.elim (targetOutside (.inr same))
    · cases impossible
  · exact fun _ same => same
  · intro target same inside
    subst target
    cases inside

private theorem availability (state : Deployment)
    (active : state.oldActive = true ∨ state.newActive = true) :
    (network state).Available (· = .client) (· = .server) := by
  intro source target sourceIsClient targetIsServer
  subst source
  subst target
  rcases active with old | new
  · exact .step (.inl ⟨old, .inl ⟨rfl, rfl⟩⟩)
      (.single (.inl ⟨old, .inr ⟨rfl, rfl⟩⟩))
  · exact .step (.inr (.inl ⟨new, .inl ⟨rfl, rfl⟩⟩))
      (.single (.inr (.inl ⟨new, .inr ⟨rfl, rfl⟩⟩)))

theorem observe_correct (state : Deployment) : observe state = true ↔ Contract state := by
  constructor
  · intro accepted
    have conditions : (state.oldActive = true ∨ state.newActive = true) ∧ state.bypass = false := by
      simpa [observe] using accepted
    exact ⟨availability state conditions.1, mediation state conditions.2, isolation state⟩
  · rintro ⟨available, mediated, _⟩
    have noBypass : state.bypass = false := by
      cases bypass : state.bypass with
      | false => rfl
      | true =>
        apply False.elim
        apply mediated .client .server rfl rfl
        refine ⟨by simp [gateways], by simp [gateways], .single ?_⟩
        exact ⟨.inr (.inr ⟨bypass, rfl, rfl⟩), by simp [gateways], by simp [gateways]⟩
    cases old : state.oldActive <;> cases new : state.newActive
    · have path := available .client .server rfl rfl
      cases path with
      | step edge _ => simp [network, old, new, noBypass] at edge
    all_goals simp [observe, old, new, noBypass]

inductive Command where
  | enableNew
  | disableOld
  | openBypass
  | closeBypass
  deriving Repr, DecidableEq

def advance (state : Deployment) : Command → Deployment
  | .enableNew => { state with newActive := true }
  | .disableOld => { state with oldActive := false }
  | .openBypass => { state with bypass := true }
  | .closeBypass => { state with bypass := false }

def initial : Deployment := ⟨true, false, false⟩

def migration : List Command := [.enableNew, .disableOld]

def outage : List Command := [.disableOld, .enableNew]

def bypassWindow : List Command := [.openBypass, .closeBypass]

def certifiedMigration : Network.Upgrade.Plan advance Contract initial migration :=
  ⟨(Network.Upgrade.check_correct advance observe Contract observe_correct initial migration).mp
    (by decide)⟩

theorem migration_safe : Network.Upgrade.Preserves advance Contract initial migration :=
  certifiedMigration.safe

theorem outage_endpoints_safe :
    Contract initial ∧ Contract (outage.foldl advance initial) := by
  constructor <;> apply (observe_correct _).mp <;> decide

theorem outage_unsafe : ¬Network.Upgrade.Preserves advance Contract initial outage := by
  intro safe
  have accepted := (Network.Upgrade.check_correct advance observe Contract observe_correct
    initial outage).mpr safe
  contradiction

theorem bypass_endpoints_safe :
    Contract initial ∧ Contract (bypassWindow.foldl advance initial) := by
  constructor <;> apply (observe_correct _).mp <;> decide

theorem bypass_window_unsafe :
    ¬Network.Upgrade.Preserves advance Contract initial bypassWindow := by
  intro safe
  have accepted := (Network.Upgrade.check_correct advance observe Contract observe_correct
    initial bypassWindow).mpr safe
  contradiction

example : Network.Upgrade.Preserves advance Contract initial ([.enableNew] ++ [.disableOld]) :=
  (Network.Upgrade.preserves_append advance Contract initial [.enableNew] [.disableOld]).mpr
    ⟨(Network.Upgrade.check_correct advance observe Contract observe_correct initial [.enableNew]).mp
        (by decide),
      (Network.Upgrade.check_correct advance observe Contract observe_correct
        ([.enableNew].foldl advance initial) [.disableOld]).mp (by decide)⟩

def run : IO Unit := do
  unless Network.Upgrade.check advance observe initial migration do
    throw (IO.userError "The rolling migration lost its contract.")
  if Network.Upgrade.check advance observe initial outage then
    throw (IO.userError "The outage window passed the update check.")
  if Network.Upgrade.check advance observe initial bypassWindow then
    throw (IO.userError "The bypass window passed the update check.")
  IO.println "Transition and upgrade tests passed."

end NetlibTest.Transition
