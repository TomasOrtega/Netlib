import Netlib.Network.Basic

namespace Netlib.Network

variable {Node : Type u}

/-- A closed region contains every next node of its members. -/
def Closed (net : Network Node) (region : Node → Prop) : Prop :=
  ∀ a b, region a → net.link a b → region b

/-- Two networks have the same links from each node in a region. -/
def AgreesOn (left right : Network Node) (region : Node → Prop) : Prop :=
  ∀ a b, region a → (left.link a b ↔ right.link a b)

theorem Closed.reachable {net : Network Node} {region : Node → Prop}
    (closed : net.Closed region) {a b : Node}
    (path : net.Reachable a b) (inside : region a) : region b := by
  induction path with
  | refl => exact inside
  | step edge _ ih => exact ih (closed _ _ inside edge)

theorem AgreesOn.symm {left right : Network Node} {region : Node → Prop}
    (agree : left.AgreesOn right region) : right.AgreesOn left region :=
  fun a b inside => (agree a b inside).symm

theorem AgreesOn.closed {left right : Network Node} {region : Node → Prop}
    (agree : left.AgreesOn right region) (closed : left.Closed region) :
    right.Closed region :=
  fun a b inside edge => closed a b inside ((agree a b inside).mpr edge)

private theorem transfer {left right : Network Node} {region : Node → Prop}
    (agree : left.AgreesOn right region) (closed : left.Closed region)
    {a b : Node} (inside : region a) (path : left.Reachable a b) :
    right.Reachable a b := by
  induction path with
  | refl a => exact .refl a
  | step edge _ ih =>
    exact .step ((agree _ _ inside).mp edge) (ih (closed _ _ inside edge))

/-- Changes outside a closed source region do not change a path query. -/
theorem reachable_iff_of_agreesOn {left right : Network Node} {region : Node → Prop}
    (agree : left.AgreesOn right region) (closed : left.Closed region)
    {a b : Node} (inside : region a) :
    left.Reachable a b ↔ right.Reachable a b :=
  ⟨transfer agree closed inside, transfer agree.symm (agree.closed closed) inside⟩

/-- The set of nodes reachable from a source is closed. -/
theorem reachable_closed (net : Network Node) (source : Node) :
    net.Closed (net.Reachable source) := by
  intro a b reachable edge
  exact reachable.trans (.single edge)

/-- A saved path query stays valid when all reachable nodes keep their links. -/
theorem reachable_iff_of_unchanged_reachable {left right : Network Node} (source target : Node)
    (agree : left.AgreesOn right (left.Reachable source)) :
    left.Reachable source target ↔ right.Reachable source target :=
  reachable_iff_of_agreesOn agree (left.reachable_closed source) (.refl source)

/-- A link restriction preserves agreement in the same region. -/
theorem AgreesOn.restrict {left right : Network Node} {region : Node → Prop}
    (agree : left.AgreesOn right region) (allowed : Node → Node → Prop) :
    (left.restrict allowed).AgreesOn (right.restrict allowed) region := by
  intro a b inside
  exact and_congr (agree a b inside) Iff.rfl

/-- A link restriction preserves a closed region. -/
theorem Closed.restrict {net : Network Node} {region : Node → Prop}
    (closed : net.Closed region) (allowed : Node → Node → Prop) :
    (net.restrict allowed).Closed region :=
  fun a b inside edge => closed a b inside edge.1

/-- Changes outside a closed source region preserve gateway bypass results. -/
theorem bypass_iff_of_agreesOn {left right : Network Node} {region : Node → Prop}
    (agree : left.AgreesOn right region) (closed : left.Closed region)
    (gateways : Node → Prop) {a b : Node} (inside : region a) :
    left.Bypass gateways a b ↔ right.Bypass gateways a b := by
  unfold Bypass without
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (reachable_iff_of_agreesOn (agree.restrict _) (closed.restrict _) inside))

/-- A saved isolation result stays valid for sources inside the closed region. -/
theorem isolated_iff_of_agreesOn {left right : Network Node} {region sources targets : Node → Prop}
    (agree : left.AgreesOn right region) (closed : left.Closed region)
    (inside : ∀ a, sources a → region a) :
    left.Isolated sources targets ↔ right.Isolated sources targets := by
  constructor
  · intro isolated a b source target path
    exact isolated a b source target
      ((reachable_iff_of_agreesOn agree closed (inside a source)).mpr path)
  · intro isolated a b source target path
    exact isolated a b source target
      ((reachable_iff_of_agreesOn agree closed (inside a source)).mp path)

/-- A saved gateway result stays valid for sources inside the closed region. -/
theorem mediated_iff_of_agreesOn {left right : Network Node}
    {region sources targets gateways : Node → Prop}
    (agree : left.AgreesOn right region) (closed : left.Closed region)
    (inside : ∀ a, sources a → region a) :
    left.Mediated sources targets gateways ↔ right.Mediated sources targets gateways := by
  constructor
  · intro mediated a b source target bypass
    exact mediated a b source target
      ((bypass_iff_of_agreesOn agree closed gateways (inside a source)).mpr bypass)
  · intro mediated a b source target bypass
    exact mediated a b source target
      ((bypass_iff_of_agreesOn agree closed gateways (inside a source)).mp bypass)

end Netlib.Network
