import Netlib.Check.FederatedDeployment
import Netlib.Check.FederatedResult
import Netlib.Check.FederatedProvenance

/-!
# Closed guarantees for every pair of native revisions

Every retained query applies to all selected headers and all local cursors.
Arbitrary interleavings and prefixes inherit these checked native facts.
-/

namespace Netlib.Federation.Deployment

structure QueryGuarantees (input : Input) (current : input.left.Cursor × input.right.Cursor)
    (query : Query) (result : Queries.Result input.left.contract input.right.contract input.intent query) : Prop where
  meaning : ∀ header, result.first.selector.accepts header = true →
    Queries.NativeMeaning (input.left.revisionAt current.1) (input.right.revisionAt current.2)
      result.first result.second input.intent query header
  reach : ∀ header, result.first.selector.accepts header = true → query.kind = .reach →
    Network.Walk (publicModel input.left.contract input.right.contract result.first result.second input.intent.borders true)
        query.source query.target result.witness ∧
      ∃ vertices, Network.Walk
          (Composition.nativeModel (input.left.revisionAt current.1) (input.right.revisionAt current.2)
            result.first result.second input.intent.borders header)
          (Composition.anchor (input.left.revisionAt current.1) (input.right.revisionAt current.2) query.source)
          (Composition.anchor (input.left.revisionAt current.1) (input.right.revisionAt current.2) query.target) vertices ∧
        ∀ index before after, vertices[index]? = some before → vertices[index + 1]? = some after →
          Nonempty (Provenance.Origin input.left.contract input.right.contract
            (input.left.revisionAt current.1) (input.right.revisionAt current.2)
            result.first result.second input.intent header before after)
  enforcement : ∀ header, result.first.selector.accepts header = true → query.kind = .mediated →
    (Composition.nativeModel (input.left.revisionAt current.1) (input.right.revisionAt current.2)
      result.first result.second input.intent.borders header).Mediated
      (· = Composition.anchor (input.left.revisionAt current.1) (input.right.revisionAt current.2) query.source)
      (· = Composition.anchor (input.left.revisionAt current.1) (input.right.revisionAt current.2) query.target)
      (Composition.Enforcement (input.left.revisionAt current.1) (input.right.revisionAt current.2))
  mediatedOn : ∀ header, result.first.selector.accepts header = true → query.kind = .mediated → ∀ side,
    query.gateways.all (fun gateway => decide (gateway.side = side)) = true →
    (Composition.nativeModel (input.left.revisionAt current.1) (input.right.revisionAt current.2)
      result.first result.second input.intent.borders header).Mediated
      (· = Composition.anchor (input.left.revisionAt current.1) (input.right.revisionAt current.2) query.source)
      (· = Composition.anchor (input.left.revisionAt current.1) (input.right.revisionAt current.2) query.target)
      (fun node => Composition.EnforcementOn side (input.left.revisionAt current.1) (input.right.revisionAt current.2) node ∧
        Composition.project (input.left.revisionAt current.1) (input.right.revisionAt current.2) node ∈ query.gateways)

variable {input : Input}

structure Snapshot (value : Checked input) (current : input.left.Cursor × input.right.Cursor) : Prop where
  localSources :
    ⟨input.left.revisionAt current.1, value.left.nativeAt current.1⟩ ∈ value.left.revisions ∧
      ⟨input.right.revisionAt current.2, value.right.nativeAt current.2⟩ ∈ value.right.revisions
  results : ∀ query result, ⟨query, result⟩ ∈ value.queries.results → QueryGuarantees input current query result

theorem Checked.snapshot (value : Checked input) (current : input.left.Cursor × input.right.Cursor) :
    Snapshot value current := by
  refine ⟨value.local_sources current.1 current.2, ?_⟩
  intro query result _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro header accepted
    exact result.native_correct value.compatible (value.left.nativeAt current.1) (value.right.nativeAt current.2) header accepted
  · intro header accepted kind
    obtain ⟨publicWalk, vertices, walk⟩ := result.native_walk
      (value.left.nativeAt current.1) (value.right.nativeAt current.2) header accepted kind
    refine ⟨publicWalk, vertices, walk, ?_⟩
    intro index before after beforeFound afterFound
    exact Provenance.walk_origins value.compatible _ _ result.first result.second header walk
      index before after beforeFound afterFound
  · intro header accepted kind
    exact result.native_enforcement value.compatible
      (value.left.nativeAt current.1) (value.right.nativeAt current.2) header accepted kind
  · intro header accepted kind side checkedSide
    have sameSide : ∀ gateway ∈ query.gateways, gateway.side = side := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using checkedSide
    exact result.native_mediated_on value.compatible
      (value.left.nativeAt current.1) (value.right.nativeAt current.2) header accepted kind side sameSide

theorem Snapshot.query_for {value : Checked input} {current : input.left.Cursor × input.right.Cursor}
    (snapshot : Snapshot value current) (query : Query) (member : query ∈ input.intent.queries) :
    ∃ result : Queries.Result input.left.contract input.right.contract input.intent query,
      ⟨query, result⟩ ∈ value.queries.results ∧ QueryGuarantees input current query result := by
  obtain ⟨result, stored⟩ := value.result_for query member
  exact ⟨result, stored, snapshot.results query result stored⟩

structure ExecutionFacts (value : Checked input)
    (events : List (Protocol.Transition.ProductLabel input.left.Operation input.right.Operation))
    (current : input.left.Cursor × input.right.Cursor) : Prop where
  snapshot : Snapshot value current
  localTraces :
    input.left.transition.Trace input.left.initialCursor (Plan.leftEvents input.left input.right events) current.1 ∧
      input.right.transition.Trace input.right.initialCursor (Plan.rightEvents input.left input.right events) current.2
  counts : current.1.val = (Plan.leftEvents input.left input.right events).length ∧
    current.2.val = (Plan.rightEvents input.left input.right events).length
  order : (Plan.leftEvents input.left input.right events).map Fin.val = List.range' 0 current.1.val ∧
    (Plan.rightEvents input.left input.right events).map Fin.val = List.range' 0 current.2.val

theorem Checked.interleaving_guarantees (value : Checked input)
    {events : List (Protocol.Transition.ProductLabel input.left.Operation input.right.Operation)}
    {current : input.left.Cursor × input.right.Cursor}
    (trace : (Plan.interleaving input.left input.right).Trace (Plan.jointInitial input.left input.right) events current) :
    ExecutionFacts value events current :=
  ⟨value.snapshot current, Plan.local_traces trace, Plan.interleaving_counts trace, Plan.interleaving_order trace⟩

theorem Checked.prefix_guarantees (value : Checked input)
    {prior later : List (Protocol.Transition.ProductLabel input.left.Operation input.right.Operation)}
    {current : input.left.Cursor × input.right.Cursor}
    (trace : (Plan.interleaving input.left input.right).Trace (Plan.jointInitial input.left input.right) (prior ++ later) current) :
    ∃ middle, (Plan.interleaving input.left input.right).Trace (Plan.jointInitial input.left input.right) prior middle ∧
      (Plan.interleaving input.left input.right).Trace middle later current ∧ ExecutionFacts value prior middle := by
  obtain ⟨middle, first, rest⟩ := trace.split
  exact ⟨middle, first, rest, value.interleaving_guarantees first⟩

end Netlib.Federation.Deployment
