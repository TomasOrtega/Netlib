import Netlib.Check.CampusTCPStartupSelection
import Netlib.Check.CampusTCPCustodyFacts
import Netlib.Check.CampusTCPFacts

/-!
# The actual source at each current job's output index

Packet copies may share an output index. They still refer to the same stored
production, actor, and control kind.
-/

namespace Netlib.Check.CampusTCPStartupJobSource

open CampusTCPModel CampusTCPStartupJobs

variable {input : Input} {index : Nat} {produced : Produced input.active input.passive}

private theorem append_lookup (before : State input) (actual : Step input)
    (state : actual.before = before) (found : before.outputs[index]? = some produced) :
    actual.result.state.outputs[index]? = some produced := by
  have within := (List.getElem?_eq_some_iff.mp found).1
  rw [CampusTCPOrigins.output_history actual, state, List.getElem?_append_left within]
  exact found

private theorem trace_lookup (trace : Trace input before events steps after remaining)
    (found : before.outputs[index]? = some produced) : after.outputs[index]? = some produced := by
  induction trace with
  | done => exact found
  | stop head blocked tail => exact append_lookup _ head rfl found
  | next head supported rest ih => exact ih (append_lookup _ head rfl found)

private theorem each_lookup (trace : Trace input before events steps after remaining)
    (actual : Step input) (member : actual ∈ steps)
    (found : actual.before.outputs[index]? = some produced) : after.outputs[index]? = some produced := by
  induction trace with
  | done => cases member
  | stop head blocked tail =>
    have same := List.mem_singleton.mp member
    subst actual
    exact append_lookup _ head rfl found
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst actual
      exact trace_lookup rest (append_lookup _ head rfl found)
    · exact ih later

variable {events : List Event} {report : Report input events}

theorem Report.ticket_lookup (report : Report input events) (item : TicketItem input)
    (pending : item ∈ report.final.work.pending) :
    report.final.outputs[item.value.outputIndex]? = some item.value.produced := by
  obtain ⟨actual, index, ingress, produced, member, event, found, selected, earlier⟩ :=
    CampusTCPOrigins.Report.pending_origin report item pending
  rw [selected]
  exact each_lookup report.trace actual member found

theorem Report.service_lookup (report : Report input events) (served : Served input)
    (member : served ∈ report.final.services) :
    report.final.outputs[served.ticket.value.outputIndex]? = some served.ticket.value.produced := by
  obtain ⟨actual, present, recorded, time, earlier⟩ := CampusTCPOrigins.Report.services_origin report served member
  obtain ⟨id, observed, completed, event, computed, selected, before, stamp⟩ :=
    CampusTCPOrigins.service_origin actual served recorded
  obtain ⟨prior, later, history, preceding, rest⟩ := CampusTCPFacts.step_origin report actual present
  let past : Report input (prior.map (·.event)) := ⟨actual.before, prior, [], preceding⟩
  have found := Report.ticket_lookup past completed.item completed.member
  rw [selected]
  exact each_lookup report.trace actual present found

theorem Report.job_lookup (report : Report input events) (job : Job input)
    (member : job ∈ inventory report.final) :
    report.final.outputs[job.outputIndex]? = some job.source.produced := by
  have pending := inventory_pending member
  cases job with
  | ingress item index source payload =>
    have found := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ pending)
    rw [payload] at found
    exact found
  | ticket item source production =>
    have found := Report.ticket_lookup report item pending
    simpa only [Job.outputIndex, Job.source, production] using found
  | link item index served emission emitted source production payload =>
    have found := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ pending)
    rw [payload] at found
    have stored : served ∈ report.final.services := List.mem_of_getElem? found
    have output := Report.service_lookup report served stored
    simpa only [Job.outputIndex, Job.source, production] using output

private def recoveryKind : Produced active passive → Option TCPHandshakeRecovery.Kind
  | .recovery _ output _ => some output.kind
  | _ => none

theorem Report.same_output (report : Report input events) (left right : Job input)
    (first : left ∈ inventory report.final) (second : right ∈ inventory report.final)
    (index : left.outputIndex = right.outputIndex) :
    left.actor = right.actor ∧ left.kind = right.kind := by
  have found := Report.job_lookup report left first
  rw [index] at found
  have same := Option.some.inj (found.symm.trans (Report.job_lookup report right second))
  exact ⟨congrArg Produced.actor same, Option.some.inj (congrArg recoveryKind same)⟩

theorem Report.useful_same (report : Report input events) (left right : Job input)
    (first : left ∈ inventory report.final) (second : right ∈ inventory report.final)
    (index : left.outputIndex = right.outputIndex) (phase : Nat) :
    CampusTCPStartupSelection.useful phase left = CampusTCPStartupSelection.useful phase right := by
  obtain ⟨actor, kind⟩ := Report.same_output report left right first second index
  unfold CampusTCPStartupSelection.useful
  rw [actor, kind]

end Netlib.Check.CampusTCPStartupJobSource
