import Netlib.Check.CampusTCPTwoProgressCoverage

/-!
# Range ledgers from actual gateway admissions

The actual admission selects the stored placement.
The placement retains old runs and adds the selected original source.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayCoverage

open Protocol Protocol.TCP
open CampusTCPTwoProgressCoverage

namespace A
export Admission (Session Result FreshReady)
end A

theorem fresh_fields (result : A.Result before input lifecycle prepared) (session : A.Session)
    (phase : before.phase = .data session)
    (ready : A.FreshReady session prepared.attachment.direction input.packet.segment) :
    ∃ after, result.state.phase = .data after ∧
      after.sender prepared.attachment.direction =
        Admission.sentLane (session.sender prepared.attachment.direction) input.packet.segment before.observations.length ∧
      after.peer prepared.attachment.direction =
        Admission.acknowledgedLane (session.peer prepared.attachment.direction) input.packet.segment := by
  cases direction : prepared.attachment.direction with
  | original =>
    have allowed := ready.allowed before.observations.length
    rw [direction] at allowed
    obtain ⟨after, afterPhase, _, own, peer, _, _⟩ :=
      CampusTCPRoundAdmission.Result.original_fresh_fields result session phase direction allowed
    exact ⟨after, afterPhase, own, peer⟩
  | reply =>
    have allowed := ready.allowed before.observations.length
    rw [direction] at allowed
    obtain ⟨after, afterPhase, _, peer, own, _, _⟩ :=
      CampusTCPRoundAdmission.Result.reply_fresh_fields result session phase direction allowed
    exact ⟨after, afterPhase, own, peer⟩

theorem placed_fields (result : A.Result before input lifecycle prepared) (session : A.Session)
    (phase : before.phase = .data session)
    (ready : A.FreshReady session prepared.attachment.direction input.packet.segment)
    (placed : Admission.Coverage.Result Nat)
    (accepted : Admission.placement (session.sender prepared.attachment.direction)
      input.packet.segment before.observations.length = .ok placed) :
    ∃ after, result.state.phase = .data after ∧
      (after.sender prepared.attachment.direction).coverage = placed.state ∧
      (after.peer prepared.attachment.direction).coverage = (session.peer prepared.attachment.direction).coverage := by
  obtain ⟨after, afterPhase, own, peer⟩ := fresh_fields result session phase ready
  refine ⟨after, afterPhase, ?_, ?_⟩
  · rw [own, Admission.sentLane, accepted]
  · rw [peer, Admission.acknowledgedLane_coverage]

theorem lower_admission (result : A.Result before input lifecycle prepared) (session : A.Session)
    (phase : before.phase = .data session)
    (ready : A.FreshReady session prepared.attachment.direction input.packet.segment)
    (seed : Admission.Coverage.State Nat) (finish : Nat) (lower upper : List UInt8)
    (ranges : TwoRanges seed (session.sender prepared.attachment.direction).coverage finish lower upper)
    (highEnd : seed.highEnd = finish) (missing : ranges.lowerRun = none)
    (nonempty : lower ≠ []) (inside : finish + lower.length ≤ Admission.coverageBound)
    (position : Seq.distance (session.sender prepared.attachment.direction).base input.packet.segment.sequence = finish)
    (payload : input.packet.segment.payload = lower) :
    ∃ after, result.state.phase = .data after ∧
      ∃ next : TwoRanges seed (after.sender prepared.attachment.direction).coverage finish lower upper,
        next.upperRun = ranges.upperRun ∧
        ∃ run, next.lowerRun = some run ∧ run.sourceID = (session.sender prepared.attachment.direction).coverage.nextID ∧
          run.metadata = before.observations.length ∧ run.position = finish ∧ run.bytes = lower := by
  obtain ⟨placed, accepted, next, lowerRun, upperRun, source, _, _⟩ := ranges.add_lower before.observations.length
    Admission.coverageBound highEnd (session.sender_valid prepared.attachment.direction).2.2.2 missing nonempty inside
  have placement : Admission.placement (session.sender prepared.attachment.direction)
      input.packet.segment before.observations.length = .ok placed := by
    simpa only [Admission.placement, position, payload] using accepted
  obtain ⟨after, afterPhase, own, _⟩ := placed_fields result session phase ready placed placement
  refine ⟨after, afterPhase, ?_⟩
  rw [own]
  refine ⟨next, upperRun, placed.source, lowerRun, ?_, ?_, ?_, ?_⟩
  all_goals rw [source]; rfl

theorem upper_admission (result : A.Result before input lifecycle prepared) (session : A.Session)
    (phase : before.phase = .data session)
    (ready : A.FreshReady session prepared.attachment.direction input.packet.segment)
    (seed : Admission.Coverage.State Nat) (finish : Nat) (lower upper : List UInt8)
    (ranges : TwoRanges seed (session.sender prepared.attachment.direction).coverage finish lower upper)
    (highEnd : seed.highEnd = finish) (missing : ranges.upperRun = none)
    (nonempty : upper ≠ []) (inside : finish + lower.length + upper.length ≤ Admission.coverageBound)
    (position : Seq.distance (session.sender prepared.attachment.direction).base input.packet.segment.sequence = finish + lower.length)
    (payload : input.packet.segment.payload = upper) :
    ∃ after, result.state.phase = .data after ∧
      ∃ next : TwoRanges seed (after.sender prepared.attachment.direction).coverage finish lower upper,
        next.lowerRun = ranges.lowerRun ∧
        ∃ run, next.upperRun = some run ∧ run.sourceID = (session.sender prepared.attachment.direction).coverage.nextID ∧
          run.metadata = before.observations.length ∧ run.position = finish + lower.length ∧ run.bytes = upper := by
  obtain ⟨placed, accepted, next, lowerRun, upperRun, source, _, _⟩ := ranges.add_upper before.observations.length
    Admission.coverageBound highEnd (session.sender_valid prepared.attachment.direction).2.2.2 missing nonempty inside
  have placement : Admission.placement (session.sender prepared.attachment.direction)
      input.packet.segment before.observations.length = .ok placed := by
    simpa only [Admission.placement, position, payload] using accepted
  obtain ⟨after, afterPhase, own, _⟩ := placed_fields result session phase ready placed placement
  refine ⟨after, afterPhase, ?_⟩
  rw [own]
  refine ⟨next, lowerRun, placed.source, upperRun, ?_, ?_, ?_, ?_⟩
  all_goals rw [source]; rfl

end Netlib.Check.CampusTCPTwoProgressGatewayCoverage
