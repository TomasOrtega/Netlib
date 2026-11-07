import Netlib.Check.FederatedPacketProgress
import Netlib.Check.FederatedPacketReplay
import Netlib.Check.FederatedPacketJson

/-!
# Recorded packet completion under checked service

Completion must occur at a recorded cut. A short trace cannot gain a receipt
from a service window that lies beyond its actual length.
-/

namespace Netlib.Federation.InFlight

namespace Completion

def findFrom (test : Nat → Bool) (start : Nat) : Nat → Option Nat
  | 0 => none
  | count + 1 => if test start then some start else findFrom test (start + 1) count

theorem findFrom_sound (test : Nat → Bool) (start count cut : Nat)
    (found : findFrom test start count = some cut) : start ≤ cut ∧ cut < start + count ∧ test cut = true := by
  induction count generalizing start with
  | zero => cases found
  | succ count ih =>
    simp only [findFrom] at found
    split at found
    · rename_i accepted
      have same : start = cut := Option.some.inj found
      subst cut
      exact ⟨Nat.le_refl _, by omega, accepted⟩
    · have tail := ih (start + 1) found
      exact ⟨by omega, by omega, tail.2.2⟩

theorem findFrom_first (test : Nat → Bool) (start count cut : Nat)
    (found : findFrom test start count = some cut) (prior : Nat) (lower : start ≤ prior) (earlier : prior < cut) :
    test prior = false := by
  induction count generalizing start with
  | zero => cases found
  | succ count ih =>
    simp only [findFrom] at found
    split at found
    · have same : start = cut := Option.some.inj found
      omega
    · rename_i rejected
      by_cases same : prior = start
      · subst prior
        exact Bool.eq_false_iff.mpr rejected
      · exact ih (start + 1) found (by omega)

def cut? (report : Replay.Report context header actions) : Option Nat :=
  findFrom (fun cut => finished (report.prefix.state cut).key) 0 (report.prefix.length + 1)

theorem cut_sound (report : Replay.Report context header actions) (cut : Nat)
    (found : cut? report = some cut) : cut ≤ report.prefix.length ∧ Progress.Complete (report.prefix.state cut) := by
  have facts := findFrom_sound _ _ _ cut found
  exact ⟨by omega, (Progress.finished_iff _).mp facts.2.2⟩

theorem cut_first (report : Replay.Report context header actions) (cut : Nat)
    (found : cut? report = some cut) (prior : Nat) (earlier : prior < cut) :
    finished (report.prefix.state prior).key = false :=
  findFrom_first _ _ _ cut found prior (Nat.zero_le _) earlier

def replayWork (context : Context input) (actions : List Action) (bound : Nat) : Nat :=
  let slots := actions.length + 1
  slots ^ 2 * (min bound slots + 1) * (Graph.sourceRows context + Graph.universeSize input + slots + 1)

end Completion

structure CheckedExecution (certificate : Certified input profile) (header : Packet.Header)
    (actions : List Action) (bound : Nat) where
  accepted : certificate.context.first.selector.accepts header = true
  report : Replay.Report certificate.context header actions
  positive : 0 < bound
  service : Theory.BoundedServiceCheck.Serviced report.prefix.length
    (fun slot => Progress.pending (certificate.cellAt header accepted) (report.prefix.state slot))
    report.prefix.action Progress.serves bound
  completion : Nat
  within : completion ≤ report.prefix.length
  complete : Progress.Complete (report.prefix.state completion)
  first : ∀ cut, cut < completion → finished (report.prefix.state cut).key = false
  deadline : completion ≤ Progress.deadline (certificate.cellAt header accepted) bound
  workWithin : certificate.totalWork + Completion.replayWork certificate.context actions bound ≤ profile.work

def checkExecution (certificate : Certified input profile) (header : Packet.Header)
    (actions : List Action) (bound : Nat) : Except String (CheckedExecution certificate header actions bound) := do
  if accepted : certificate.context.first.selector.accepts header = true then
    if positive : 0 < bound then
      if work : certificate.totalWork + Completion.replayWork certificate.context actions bound ≤ profile.work then
        let report ← Replay.run certificate.context header actions
        let cell := certificate.cellAt header accepted
        if serviced : Theory.BoundedServiceCheck.check report.prefix.length
            (fun slot => Progress.pending cell (report.prefix.state slot)) report.prefix.action Progress.serves bound = true then
          let service := (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mp serviced
          match found : Completion.cut? report with
          | none => throw "The packet replay has no recorded completion."
          | some cut =>
            let done := Completion.cut_sound report cut found
            have deadline : cut ≤ Progress.deadline cell bound := by
              by_cases enough : Progress.deadline cell bound ≤ report.prefix.length
              · have completed := Progress.modeled_completion certificate.valid cell report.prefix report.initial
                  bound positive service enough
                by_cases within : cut ≤ Progress.deadline cell bound
                · exact within
                · have early := Completion.cut_first report cut found (Progress.deadline cell bound) (by omega)
                  have yes := (Progress.finished_iff _).mpr completed
                  rw [yes] at early
                  cases early
              · have recorded := done.1
                omega
            return ⟨accepted, report, positive, service, cut, done.1, done.2,
              Completion.cut_first report cut found, deadline, work⟩
        else throw "The packet replay violates its persistent-demand service bound."
      else throw "Packet replay and class analysis exceed the supplied work budget."
    else throw "The packet service bound must be positive."
  else throw "The packet header is outside the certified class."

structure CheckedBundle (bundle : Bundle) where
  certificate : Certified bundle.deployment bundle.profile
  execution : CheckedExecution certificate bundle.header bundle.actions bundle.serviceBound

def checkBundle (bundle : Bundle) : Except String (CheckedBundle bundle) := do
  if bundle.serviceBound = 0 then throw "The packet service bound must be positive."
  let certificate ← certify bundle.deployment bundle.profile
  let execution ← checkExecution certificate bundle.header bundle.actions bundle.serviceBound
  return ⟨certificate, execution⟩

def checkJson (text : String) : Except String ((bundle : Bundle) × CheckedBundle bundle) := do
  let bundle ← Json.parse text
  return ⟨bundle, ← checkBundle bundle⟩

theorem CheckedExecution.enabled_at (value : CheckedExecution certificate header actions bound)
    (slot : Nat) (within : slot ≤ value.report.prefix.length)
    (positive : 0 < Progress.rank (certificate.cellAt header value.accepted) (value.report.prefix.state slot)) :
    ∃ move, Progress.pending (certificate.cellAt header value.accepted) (value.report.prefix.state slot) = some move ∧
      ∃ advanced : Execution.Advanced certificate.context header (value.report.prefix.state slot)
          (canonicalAction certificate.context header (value.report.prefix.state slot) move),
        Execution.advance certificate.context header (value.report.prefix.state slot)
          (canonicalAction certificate.context header (value.report.prefix.state slot) move) = .ok advanced ∧
        Progress.serves move advanced.event = true ∧
        Progress.rank (certificate.cellAt header value.accepted) advanced.outcome.after <
          Progress.rank (certificate.cellAt header value.accepted) (value.report.prefix.state slot) :=
  Progress.current_enabled certificate.valid _ value.report.prefix value.report.initial slot within positive

end Netlib.Federation.InFlight
