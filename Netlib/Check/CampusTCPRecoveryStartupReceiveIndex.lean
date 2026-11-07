import Netlib.Check.TCPHandshakeRecoveryPhaseOrderFacts
import Netlib.Check.TCPHandshakeRecoveryReceiveConditions
import Netlib.Check.CampusTCPRecoveryStartupOrigins
import Netlib.Check.CampusTCPChronology
import Netlib.Check.CampusTCPOrigins

/-!
# Current receive stamps from the same campus report

The latest recovery event may be a clock, timeout, or receipt.
Every local ACK operation precedes the next outer event.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupReceiveIndex

open Protocol.TCP CampusTCPModel

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : C.State input.active input.passive}

private theorem time_before_final (trace : Trace input initial selected steps final remaining)
    (actual : Step input) (member : actual ∈ steps) : actual.before.time < final.time := by
  induction trace with
  | done => cases member
  | stop head blocked tail =>
    have same := List.mem_singleton.mp member
    subst actual
    rw [head.clock]
    exact Nat.lt_succ_self _
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst actual
      have elapsed := CampusTCPOrigins.Trace.time rest
      have clock := head.clock
      omega
    · exact ih later

theorem Report.recovery_last_earlier (report : Report input events)
    (connected : report.final.connection = .recovering current) (last : current.last = some index) :
    index < report.final.time := by
  let reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected
  obtain ⟨actual, member, stamp⟩ := reachable.last_origin last
  have stored : actual ∈ report.steps.filterMap (·.result.recovery) := member
  obtain ⟨joint, present, recorded, time⟩ := CampusTCPRecoveryStartupOrigins.Report.recovery_step_origin report stored
  rw [← stamp, time]
  exact time_before_final report.trace joint present

theorem Report.recovery_emission_before (report : Report input events)
    (connected : report.final.connection = .recovering current) (member : output ∈ current.emissions) :
    output.index < report.final.time := by
  obtain ⟨last, present, bound⟩ :=
    (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).emission_before_last member
  exact Nat.lt_of_le_of_lt bound (Report.recovery_last_earlier report connected present)

theorem Report.recovery_receipt_before (report : Report input events)
    (connected : report.final.connection = .recovering current) (member : receipt ∈ current.receipts) :
    receipt.index < report.final.time := by
  obtain ⟨last, present, bound⟩ :=
    (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).receipt_before_last member
  exact Nat.lt_of_le_of_lt bound (Report.recovery_last_earlier report connected present)

theorem Report.receive_index (report : Report input events)
    (connected : report.final.connection = .recovering current) :
    TCPHandshakeRecovery.ReceiveIndex current report.final.time := by
  cases last : current.last with
  | none => simp only [TCPHandshakeRecovery.ReceiveIndex, last, Option.isNone_none, Bool.true_or]
  | some index =>
    have earlier := Report.recovery_last_earlier report connected last
    simpa only [TCPHandshakeRecovery.ReceiveIndex, last, Option.isNone_some,
      Option.getD_some, Bool.false_or, decide_eq_true_eq] using earlier

theorem Report.recovery_application_before (report : Report input events)
    (connected : report.final.connection = .recovering current) :
    ∀ actor operation, operation ∈ current.applicationSteps actor → operation.stamp < report.final.time := by
  simpa only [CampusTCPChronology.Chronological, connected, CampusTCPChronology.Earlier] using
    CampusTCPChronology.Report.chronological report

theorem Report.acknowledged_client_before (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (phase : current.phase = .acknowledged acknowledged client) :
    ∀ operation ∈ client.steps, operation.stamp < report.final.time := by
  simpa only [TCPHandshakeRecovery.State.applicationSteps, phase] using
    Report.recovery_application_before report connected .active

theorem Report.complete_endpoints_before (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (phase : current.phase = .complete complete client server) :
    (∀ operation ∈ client.steps, operation.stamp < report.final.time) ∧
      (∀ operation ∈ server.steps, operation.stamp < report.final.time) := by
  constructor
  · simpa only [TCPHandshakeRecovery.State.applicationSteps, phase] using
      Report.recovery_application_before report connected .active
  · simpa only [TCPHandshakeRecovery.State.applicationSteps, phase] using
      Report.recovery_application_before report connected .passive

end Netlib.Check.CampusTCPRecoveryStartupReceiveIndex
