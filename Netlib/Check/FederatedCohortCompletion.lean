import Netlib.Check.FederatedCohort
import Netlib.Check.FederatedCohortJson
import Netlib.Check.FederatedCohortProgress
import Netlib.Check.FederatedCohortReplay
import Netlib.Check.FederatedPacketCompletion

/-!
# Recorded completion of the whole finite group

The service checker uses joint demands with exact packet identities.
Completion must occur at an actual recorded cut, even for a short trace.
-/

namespace Netlib.Federation.Cohort

variable {input : Input} {size : Nat} {profile : Profile}
variable {context : Context input size} {headers : Vector Packet.Header size}
variable {prepared : Prepared input profile}

def accepts (context : Context input size) (headers : Vector Packet.Header size) : Bool :=
  (List.finRange size).all fun index => (context.packets.get index).first.selector.accepts (headers.get index)

theorem accepts_iff (context : Context input size) (headers : Vector Packet.Header size) :
    accepts context headers = true ↔ Accepted context headers := by
  simp only [accepts, Accepted, List.all_eq_true, List.mem_finRange, forall_const]

namespace Completion

def cut? (report : Replay.Report context headers actions) : Option Nat :=
  InFlight.Completion.findFrom (fun cut => finished (report.prefix.state cut).key) 0 (report.prefix.length + 1)

theorem cut_sound (report : Replay.Report context headers actions) (cut : Nat)
    (found : cut? report = some cut) : cut ≤ report.prefix.length ∧ Progress.Complete (report.prefix.state cut) := by
  have facts := InFlight.Completion.findFrom_sound _ _ _ cut found
  exact ⟨by omega, (Progress.finished_iff _).mp facts.2.2⟩

theorem cut_first (report : Replay.Report context headers actions) (cut : Nat)
    (found : cut? report = some cut) (prior : Nat) (earlier : prior < cut) :
    finished (report.prefix.state prior).key = false :=
  InFlight.Completion.findFrom_first _ _ _ cut found prior (Nat.zero_le _) earlier

def replayWork (certificate : Certified input profile) (actions : List InFlight.Action) (bound : Nat) : Nat :=
  let slots := actions.length + 1
  let costs := Graph.costs certificate.prepared.context
  let keys := (certificate.cells.map (fun entry => entry.2.checked.sparse.graph.size)).sum
  slots ^ 2 * (min bound slots + 1) *
    (costs.row + keys * (costs.key + 1) + certificate.prepared.size + slots + 1)

end Completion

structure CheckedExecution (certificate : Certified input profile)
    (headers : Vector Packet.Header certificate.prepared.size) (actions : List InFlight.Action) (bound : Nat) where
  accepted : Accepted certificate.prepared.context headers
  report : Replay.Report certificate.prepared.context headers actions
  positive : 0 < bound
  service : Theory.BoundedServiceCheck.Serviced report.prefix.length
    (fun slot => Progress.pending (certificate.cellAt headers accepted).checked (report.prefix.state slot))
    report.prefix.action (Progress.serves certificate.prepared.context) bound
  completion : Nat
  within : completion ≤ report.prefix.length
  complete : Progress.Complete (report.prefix.state completion)
  first : ∀ cut, cut < completion → finished (report.prefix.state cut).key = false
  deadline : completion ≤ Progress.deadline (certificate.cellAt headers accepted).checked bound
  workWithin : certificate.totalWork + Completion.replayWork certificate actions bound ≤ profile.limits.work

def checkExecution (certificate : Certified input profile)
    (headers : Vector Packet.Header certificate.prepared.size) (actions : List InFlight.Action) (bound : Nat) :
    Except String (CheckedExecution certificate headers actions bound) := do
  if acceptedCheck : accepts certificate.prepared.context headers = true then
    let accepted := (accepts_iff _ _).mp acceptedCheck
    if positive : 0 < bound then
      if work : certificate.totalWork + Completion.replayWork certificate actions bound ≤ profile.limits.work then
        let report ← Replay.run certificate.prepared.context headers actions
        let cell := certificate.cellAt headers accepted
        if serviced : Theory.BoundedServiceCheck.check report.prefix.length
            (fun slot => Progress.pending cell.checked (report.prefix.state slot)) report.prefix.action
            (Progress.serves certificate.prepared.context) bound = true then
          let service := (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mp serviced
          match found : Completion.cut? report with
          | none => throw "The cohort replay has no recorded whole-group completion."
          | some cut =>
            let done := Completion.cut_sound report cut found
            have deadline : cut ≤ Progress.deadline cell.checked bound := by
              by_cases enough : Progress.deadline cell.checked bound ≤ report.prefix.length
              · have completed := Progress.modeled_completion cell.checked report.prefix report.initial
                  bound positive service enough
                by_cases within : cut ≤ Progress.deadline cell.checked bound
                · exact within
                · have early := Completion.cut_first report cut found (Progress.deadline cell.checked bound) (by omega)
                  have yes := (Progress.finished_iff _).mpr completed
                  rw [yes] at early
                  cases early
              · have recorded := done.1
                omega
            return ⟨accepted, report, positive, service, cut, done.1, done.2,
              Completion.cut_first report cut found, deadline, work⟩
        else throw "The cohort replay violates its joint persistent-demand service bound."
      else throw "The full class and replay estimate exceeds the cohort work budget."
    else throw "The cohort service bound must be positive."
  else throw "A packet header is outside its certified class."

structure CheckedBundle (bundle : Bundle) where
  certificate : Certified bundle.input bundle.profile
  headerCount : bundle.headers.length = certificate.prepared.size
  execution : CheckedExecution certificate (Theory.FiniteProduct.vector bundle.headers headerCount)
    bundle.actions bundle.serviceBound

def checkBundle (bundle : Bundle) : Except String (CheckedBundle bundle) := do
  if bundle.serviceBound = 0 then throw "The cohort service bound must be positive."
  if rawCount : bundle.headers.length = bundle.profile.packets.length then
    let certificate ← certify bundle.input bundle.profile
    have sizeEq : certificate.prepared.size = bundle.profile.packets.length := by
      simpa only [List.length_map] using congrArg List.length certificate.prepared.profilesEq
    let headerCount := rawCount.trans sizeEq.symm
    let execution ← checkExecution certificate (Theory.FiniteProduct.vector bundle.headers headerCount)
      bundle.actions bundle.serviceBound
    return ⟨certificate, headerCount, execution⟩
  else throw "The cohort header count differs from its packet count."

def checkJson (text : String) : Except String ((bundle : Bundle) × CheckedBundle bundle) := do
  let bundle ← Json.parse text
  return ⟨bundle, ← checkBundle bundle⟩

theorem CheckedExecution.enabled_at {certificate : Certified input profile}
    {headers : Vector Packet.Header certificate.prepared.size} {actions : List InFlight.Action} {bound : Nat}
    (value : CheckedExecution certificate headers actions bound)
    (slot : Nat) (within : slot ≤ value.report.prefix.length)
    (positive : 0 < Progress.rank (certificate.cellAt headers value.accepted).checked (value.report.prefix.state slot)) :
    ∃ move, Progress.pending (certificate.cellAt headers value.accepted).checked (value.report.prefix.state slot) = some move ∧
      ∃ advanced : Execution.Advanced certificate.prepared.context headers (value.report.prefix.state slot)
          (canonicalAction certificate.prepared.context headers (value.report.prefix.state slot) move),
        Execution.advance certificate.prepared.context headers (value.report.prefix.state slot)
          (canonicalAction certificate.prepared.context headers (value.report.prefix.state slot) move) = .ok advanced ∧
        Progress.serves certificate.prepared.context move advanced.event = true ∧
        Progress.rank (certificate.cellAt headers value.accepted).checked advanced.outcome.after <
          Progress.rank (certificate.cellAt headers value.accepted).checked (value.report.prefix.state slot) :=
  Progress.current_enabled _ certificate.prepared.unique value.report.prefix value.report.initial slot within positive

end Netlib.Federation.Cohort
