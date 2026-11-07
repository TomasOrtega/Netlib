import Netlib.Check.CampusTCPRecoveredSetup

/-!
# Drain readiness from an actual supported finish operation

The operation supplies its current complete phase and empty recovery queues.
Its report prefix retains the original startup history.
-/

namespace Netlib.Check.CampusTCPRecoveredDrainReady

open CampusTCPModel CampusTCPRecoveredSetup

variable {input : Input} {events : List Event} {report : Report input events}

private theorem ready_fields (supported : report.supported = true) (finished : report.remaining = [])
    (computed : finishStartup input report.final = .ok effect) (accepted : effect.supported = true) :
    Nonempty (DrainReady report) := by
  cases archived : report.final.recoveryArchive with
  | some archive => simp only [finishStartup, archived, Option.isSome_some, ↓reduceIte, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at computed
  | none =>
    cases tickets : report.final.work.pending.any (fun item => item.value.produced.isRecovery) with
    | true => simp only [finishStartup, archived, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, tickets,
        throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at computed
    | false =>
      cases packets : report.final.custody.pending.any (fun item => item.value.payload.isRecovery) with
      | true => simp only [finishStartup, archived, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          tickets, packets, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at computed
      | false =>
        cases connection : report.final.connection with
        | startup phase pending | application complete endpoints =>
          simp only [finishStartup, archived, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            tickets, packets, connection, pure, Except.pure, Except.ok.injEq] at computed
          subst effect
          cases accepted
        | recovering current =>
          cases current with
          | mk currentPhase activeTimer passiveTimer activeValid passiveValid emissions receipts last =>
            cases currentPhase with
            | idle | opened value | answered value | acknowledged value client =>
              simp [finishStartup, archived, tickets, packets, connection] at computed
            | complete complete client server =>
              exact ⟨⟨supported, finished, _, connection, complete, client, server, rfl, archived, tickets, packets⟩⟩

theorem Report.drain_ready (report : Report input events) (supported : report.supported = true)
    (finished : report.remaining = []) (actual : Step input) (before : actual.before = report.final)
    (event : actual.event = .finishStartup) (accepted : actual.result.supported = true) :
    Nonempty (DrainReady report) := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  rw [event, before] at computed
  exact ready_fields supported finished computed (by simpa only [final] using accepted)

theorem Step.determined (first second : Step input) (before : first.before = second.before)
    (event : first.event = second.event) : first = second := by
  cases first with
  | mk firstBefore firstEvent firstResult firstComputed =>
    cases second with
    | mk secondBefore secondEvent secondResult secondComputed =>
      dsimp only at before event
      subst secondBefore
      subst secondEvent
      have result := Except.ok.inj (firstComputed.symm.trans secondComputed)
      subst secondResult
      rfl

end Netlib.Check.CampusTCPRecoveredDrainReady
