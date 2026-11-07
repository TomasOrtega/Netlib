import Netlib.Check.CampusTCPGapPayloadFacts
import Netlib.Check.CampusTCPRecoveryRoundOrigins

/-!
# Later reads retain receipts before the network cutoff

The payload history includes every actual application write. A later read may
return buffered bytes; revocation does not remove those bytes.
-/

namespace Netlib.Check.CampusTCPRevocationReadOrigin

open Protocol.TCP CampusTCPModel CampusTCPEnabled

variable {input : Input} {events : List Event} {report : Report input events}

def NoReceiptsAfter (report : Report input events) (cut : Nat) : Prop :=
  ∀ actual ∈ report.steps, cut ≤ actual.before.time → actual.result.receipt = none

def seed (complete : H.Completed input.active input.passive) : Actor → Endpoint.State
  | .client => complete.certificate.activeSeed
  | .server => complete.certificate.passiveSeed

structure Origin (report : Report input events) (cut : Nat) (peerInitial : Endpoint.State)
    (peer : List T.Step) (actor : Actor) (steps : List T.Step) (reader : T.Step) (index : Nat) (byte : UInt8) where
  readActual : Step input
  readMember : readActual ∈ report.steps
  readRecorded : readActual.result.application = some (actor, reader)
  readAfter : cut ≤ reader.stamp
  origin : CampusTCPGapFacts.ReadOrigin report peerInitial peer actor steps reader index byte
  jointBefore : origin.delivery.receive.joint.step.before.time < cut
  receiptBefore : origin.delivery.receive.receipt.time < cut
  issuerBefore : origin.read.origin.origin.issuer.stamp < cut

private theorem receipt_before (quiet : NoReceiptsAfter report cut)
    (actual : Step input) (member : actual ∈ report.steps) (receipt : Receipt input)
    (recorded : actual.result.receipt = some receipt) : actual.before.time < cut := by
  by_cases later : cut ≤ actual.before.time
  · have absent := quiet actual member later
    rw [recorded] at absent
    cases absent
  · omega

private def Origin.ofReadOrigin (quiet : NoReceiptsAfter report cut)
    (readActual : Step input) (readMember : readActual ∈ report.steps)
    (readRecorded : readActual.result.application = some (actor, reader)) (later : cut ≤ reader.stamp)
    (origin : CampusTCPGapFacts.ReadOrigin report peerInitial peer actor steps reader index byte) :
    Origin report cut peerInitial peer actor steps reader index byte := by
  have before := receipt_before quiet origin.delivery.receive.joint.step origin.delivery.receive.joint.member
    origin.delivery.receive.receipt origin.delivery.receive.recorded
  have time := CampusTCPRecoveryRoundOrigins.Step.receipt_application origin.delivery.receive.joint.step
    origin.delivery.receive.receipt origin.delivery.receive.recorded
  exact ⟨readActual, readMember, readRecorded, later, origin, before, by omega,
    by rw [← origin.delivery.receive.joint.time]; exact before⟩

theorem Report.read_origin_after_cut (report : Report input events) (cut : Nat)
    (quiet : NoReceiptsAfter report cut) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actor : Actor) (reader : T.Step) (member : reader ∈ applicationSteps endpoints actor)
    (count : Nat) (read : reader.event = .read count) (later : cut ≤ reader.stamp)
    (index : Nat) (byte : UInt8) (selected : reader.readBytes[index]? = some byte) :
    Nonempty (Origin report cut (seed complete actor.other) (applicationSteps endpoints actor.other)
      actor (applicationSteps endpoints actor) reader index byte) := by
  have actualMember : reader ∈ CampusTCPApplicationHistory.connectionSteps report.final.connection actor := by
    simpa only [connection, CampusTCPApplicationHistory.connectionSteps] using member
  obtain ⟨actual, actualMember, recorded⟩ :=
    CampusTCPApplicationHistory.Report.application_origin report actor reader actualMember
  have history := CampusTCPReceiveHistory.Report.payload_history report actor
  have receives := CampusTCPReceiveHistory.Report.payload_receives report actor
  rw [connection] at history receives
  simp only [CampusTCPApplicationHistory.connectionSteps] at history receives
  have localChain : ApplicationTrace.Chain (seed complete actor) (applicationSteps endpoints actor) (endpoint endpoints actor) := by
    cases actor
    · exact endpoints.client.chain
    · exact endpoints.server.chain
  have peerChain : ApplicationTrace.Chain (seed complete actor.other) (applicationSteps endpoints actor.other)
      (endpoint endpoints actor.other) := by
    cases actor
    · exact endpoints.server.chain
    · exact endpoints.client.chain
  have emptyUnread : (seed complete actor).core.received = [] := by
    cases actor
    · exact complete.certificate.empty.2.2.1
    · exact complete.certificate.empty.2.2.2.2.2
  have emptyHeld : (seed complete actor).receiveStore.held = [] := by
    cases actor
    · exact complete.certificate.empty_receiveStore.1
    · exact complete.certificate.empty_receiveStore.2
  have emptySent : (seed complete actor.other).core.sent = [] := by
    cases actor
    · exact complete.certificate.empty.2.2.2.2.1
    · exact complete.certificate.empty.2.1
  have emptyPending : (seed complete actor.other).pending = [] := by
    cases actor
    · exact complete.certificate.empty.2.2.2.1
    · exact complete.certificate.empty.1
  obtain ⟨origin⟩ := CampusTCPGapFacts.payload_read_origin localChain peerChain history receives
    emptyUnread emptyHeld emptySent emptyPending reader member count read index byte selected
  exact ⟨Origin.ofReadOrigin quiet actual actualMember recorded later origin⟩

end Netlib.Check.CampusTCPRevocationReadOrigin
