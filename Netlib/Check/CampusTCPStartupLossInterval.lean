import Netlib.Check.CampusTCPReportLoss
import Netlib.Check.CampusTCPSchedule

/-!
# Equal actual loss counters identify a drop-free interval

The interval uses the stored steps and their literal custody counters.
-/

namespace Netlib.Check.CampusTCPStartupLossInterval

open CampusTCPModel

namespace S
export CampusTCPSchedule (stateAt)
end S
namespace L
export CampusTCPReportLoss (drops)
end L

variable {input : Input} {events : List Event}

def lossAt (whole : Report input events) (slot : Nat) : Nat :=
  (S.stateAt input.initial whole.steps slot).custody.dropped

theorem prefix_count (whole : Report input events) (within : slot ≤ whole.steps.length) :
    lossAt whole slot = L.drops (whole.steps.take slot) :=
  CampusTCPReportLoss.Report.drop_count (CampusTCPSchedule.Report.cut whole slot within)

theorem interval_count (whole : Report input events) (order : start ≤ last) (within : last ≤ whole.steps.length) :
    lossAt whole last = lossAt whole start + L.drops ((whole.steps.drop start).take (last - start)) := by
  rw [prefix_count whole within, prefix_count whole (by omega : start ≤ whole.steps.length)]
  have sum : start + (last - start) = last := by omega
  have split : whole.steps.take last = whole.steps.take start ++ (whole.steps.drop start).take (last - start) := by
    simpa only [sum] using (List.take_add (l := whole.steps) (i := start) (j := last - start))
  rw [split, CampusTCPReportLoss.drops_append]

theorem monotone (whole : Report input events) (order : start ≤ last) (within : last ≤ whole.steps.length) :
    lossAt whole start ≤ lossAt whole last := by
  have exactCount := interval_count whole order within
  omega

theorem le_total (whole : Report input events) (within : slot ≤ whole.steps.length) :
    lossAt whole slot ≤ whole.final.custody.dropped := by
  have bounded := monotone whole within (Nat.le_refl whole.steps.length)
  have last := CampusTCPSchedule.Trace.last_state whole.trace
  simpa only [lossAt, last] using bounded

theorem prefix_bound (whole : Report input events) (within : slot ≤ whole.steps.length)
    (bounded : whole.final.custody.dropped ≤ allowance) : lossAt whole slot ≤ allowance :=
  Nat.le_trans (le_total whole within) bounded

theorem found_no_drop (whole : Report input events) (_order : start ≤ last) (within : last ≤ whole.steps.length)
    (equal : lossAt whole start = lossAt whole last) (early : start ≤ slot) (late : slot < last)
    (actual : Step input) (found : whole.steps[slot]? = some actual) :
    ∀ id, actual.event ≠ .dropPacket id := by
  have beforeBound := monotone whole early (by omega : slot ≤ whole.steps.length)
  have afterBound := monotone whole (by omega : slot + 1 ≤ last) within
  obtain ⟨selected, selectedAt, before, _, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot (by omega)
  have same : selected = actual := Option.some.inj (selectedAt.symm.trans found)
  subst selected
  have delta := CampusTCPCustodyFacts.Step.drop_count actual
  rw [before, after] at delta
  intro id dropped
  simp only [dropped, CampusTCPCustodyFacts.dropEvent, ↓reduceIte] at delta
  change lossAt whole (slot + 1) = lossAt whole slot + 1 at delta
  omega

theorem event_no_drop (whole : Report input events) (order : start ≤ last) (within : last ≤ whole.steps.length)
    (equal : lossAt whole start = lossAt whole last) (early : start ≤ slot) (late : slot < last) :
    ∀ id, CampusTCPSchedule.eventAt whole.steps slot ≠ .dropPacket id := by
  obtain ⟨actual, found, _, event, _⟩ := CampusTCPSchedule.Trace.at whole.trace slot (by omega)
  intro id dropped
  exact found_no_drop whole order within equal early late actual found id (event.trans dropped)

end Netlib.Check.CampusTCPStartupLossInterval
