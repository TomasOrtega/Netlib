import Netlib.Check.CampusTCPCustodyFacts
import Netlib.Theory.PacketCustodyDropIDs

/-!
# Actual dropped identities in a campus trace

Each explicit drop appends its selected custody identity.
The existing custody invariant makes full and selected-suffix IDs distinct.
-/

namespace Netlib.Check.CampusTCPDropIDs

open CampusTCPModel

namespace C
export Netlib.Theory.PacketCustody (History)
end C

def eventDropID : Event → Option Nat
  | .dropPacket id => some id
  | _ => none

def dropID (actual : Step input) : Option Nat := eventDropID actual.event

private theorem prepare_ids (before : State input) (event : Event) (after : Custody input)
    (computed : prepareCustody before event = .ok after) :
    after.droppedIDs = before.custody.droppedIDs ++ (eventDropID event).toList := by
  cases event <;> simp only [prepareCustody] at computed
  all_goals repeat' first
    | (solve | cases computed; simp [eventDropID])
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed)
    | (solve | cases computed; simp [eventDropID, Theory.PacketCustody.Resolved.droppedIDs])

private theorem finish_ids (before : State input) (effect : Effect input) (custody : Custody input) :
    (finishCustody before effect custody).droppedIDs = custody.droppedIDs := by
  cases effect.output <;> cases effect.service <;> simp only [finishCustody]
  all_goals repeat' first
    | (solve | rfl)
    | (split)
    | (simp only [Theory.PacketCustody.mint_droppedIDs])

theorem Step.droppedIDs (actual : Step input) :
    actual.result.state.custody.droppedIDs = actual.before.custody.droppedIDs ++ (dropID actual).toList := by
  obtain ⟨effect, custody, _, prepared, result⟩ := actual.transaction
  rw [result]
  exact (finish_ids _ _ _).trans (prepare_ids _ _ _ prepared)

private theorem filterMap_cons_toList (selected : α → Option β) (head : α) (rest : List α) :
    (head :: rest).filterMap selected = (selected head).toList ++ rest.filterMap selected := by
  cases chosen : selected head <;> simp only [List.filterMap_cons, chosen, Option.toList_none,
    Option.toList_some, List.nil_append, List.singleton_append]

theorem Trace.droppedIDs (trace : Trace input initial events steps final remaining) :
    final.custody.droppedIDs = initial.custody.droppedIDs ++ steps.filterMap dropID := by
  induction trace with
  | done state => simp only [List.filterMap_nil, List.append_nil]
  | stop head _ _ =>
    rw [filterMap_cons_toList, List.filterMap_nil, List.append_nil]
    exact Step.droppedIDs head
  | next head _ _ ih =>
    rw [ih, Step.droppedIDs, filterMap_cons_toList, List.append_assoc]

theorem Trace.ids_nodup (trace : Trace input initial events steps final remaining)
    (prior : C.History initial.custody) : (steps.filterMap dropID).Nodup := by
  have distinct := (CampusTCPCustodyFacts.Trace.history trace prior).droppedIDs_nodup
  rw [Trace.droppedIDs trace] at distinct
  exact (List.nodup_append.mp distinct).2.1

theorem Trace.prior_disjoint (trace : Trace input initial events steps final remaining)
    (prior : C.History initial.custody) :
    ∀ id ∈ initial.custody.droppedIDs, ∀ selected ∈ steps.filterMap dropID, id ≠ selected := by
  have distinct := (CampusTCPCustodyFacts.Trace.history trace prior).droppedIDs_nodup
  rw [Trace.droppedIDs trace] at distinct
  exact (List.nodup_append.mp distinct).2.2

theorem Report.droppedIDs (report : Report input events) :
    report.final.custody.droppedIDs = report.steps.filterMap dropID := by
  simpa only [Input.initial, Theory.PacketCustody.State.droppedIDs, Theory.PacketCustody.State.initial,
    List.filter_nil, List.map_nil, List.nil_append] using Trace.droppedIDs report.trace

theorem Report.ids_nodup (report : Report input events) : (report.steps.filterMap dropID).Nodup :=
  Trace.ids_nodup report.trace .initial

theorem Report.suffix_ids_nodup (report : Report input events) {past selected : List (Step input)}
    (history : report.steps = past ++ selected) : (selected.filterMap dropID).Nodup := by
  have distinct := Report.ids_nodup report
  rw [history, List.filterMap_append] at distinct
  exact (List.nodup_append.mp distinct).2.1

end Netlib.Check.CampusTCPDropIDs
