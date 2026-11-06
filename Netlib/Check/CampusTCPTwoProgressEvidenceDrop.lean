import Netlib.Check.CampusTCPTwoProgressEvidenceHop
import Netlib.Check.CampusTCPTwoProgressPhaseDropStateData
import Netlib.Check.CampusTCPTwoProgressPhaseDropStateMore

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressPhaseState CampusTCPTwoProgressPaths
open CampusTCPTwoProgressSetup (config)

namespace P
export CampusTCPTwoProgressPathDrop (original_ingress_at original_link_at retry_ingress_at retry_link_at
  ack_ingress_at ack_link_at ingress_at link_at)
end P
namespace DS
export CampusTCPTwoProgressPhaseDropState (lower_ingress lower_link upper_ingress upper_link retry_ingress retry_link
  ack_ingress_credited ack_link_credited ack_ingress_unassigned ack_link_unassigned received_bound)
end DS
namespace G
export CampusTCPGapProgressMonitor (nextAction packetAt)
end G

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {part : CampusTCPTwoProgressSender.Part} {lane : CampusTCPTwoProgressMonitor.Lane} {count : Nat}

private theorem exposed_none (cfg : CampusTCPTwoProgressMonitor.Config) (state : State input)
    (lane : CampusTCPTwoProgressMonitor.Lane) (empty : G.packetAt lane.toGap = none) :
    CampusTCPTwoProgressMonitor.exposedPacket cfg state lane = none := by
  unfold CampusTCPTwoProgressMonitor.exposedPacket
  cases next : G.nextAction cfg.toConfig state lane.toGap <;> simp only [empty, bind, Option.bind]

private theorem exposed_done (cfg : CampusTCPTwoProgressMonitor.Config) (lane : CampusTCPTwoProgressMonitor.Lane)
    (phase : lane.phase = .done) : CampusTCPTwoProgressMonitor.exposedPacket cfg current.report.final lane = none := by
  exact exposed_none cfg _ lane (by simp only [G.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, phase])

private theorem data_ingress_exposed (path : DataIngress initial current part lane) :
    CampusTCPTwoProgressMonitor.exposedPacket (config initial native quantum allowance) current.report.final lane = some path.packetID := by
  unfold CampusTCPTwoProgressMonitor.exposedPacket
  rw [path.action (config initial native quantum allowance)]
  simp only [bind, Option.bind, G.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.packetRef]

private theorem data_link_exposed (path : DataLink initial current part lane) :
    CampusTCPTwoProgressMonitor.exposedPacket (config initial native quantum allowance) current.report.final lane = some path.packetID := by
  unfold CampusTCPTwoProgressMonitor.exposedPacket
  rw [path.action (config initial native quantum allowance)]
  simp only [bind, Option.bind, G.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.packetRef]

private theorem data_ticket_unexposed (path : DataTicket initial native current part lane) :
    CampusTCPTwoProgressMonitor.exposedPacket (config initial native quantum allowance) current.report.final lane = none := by
  exact exposed_none _ _ lane (by simp only [G.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase])

private theorem ack_ingress_exposed (path : AckIngress initial current count lane) :
    CampusTCPTwoProgressMonitor.exposedPacket (config initial native quantum allowance) current.report.final lane = some path.packetID := by
  unfold CampusTCPTwoProgressMonitor.exposedPacket
  rw [path.action (config initial native quantum allowance)]
  simp only [bind, Option.bind, G.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.packetRef]

private theorem ack_link_exposed (path : AckLink initial current count lane) :
    CampusTCPTwoProgressMonitor.exposedPacket (config initial native quantum allowance) current.report.final lane = some path.packetID := by
  unfold CampusTCPTwoProgressMonitor.exposedPacket
  rw [path.action (config initial native quantum allowance)]
  simp only [bind, Option.bind, G.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.packetRef]

private theorem ack_ticket_unexposed (path : AckTicket initial native current count lane) :
    CampusTCPTwoProgressMonitor.exposedPacket (config initial native quantum allowance) current.report.final lane = none := by
  exact exposed_none _ _ lane (by simp only [G.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase])

private theorem current_head (active : Active core) :
    ∃ part head rest, CampusTCPTwoProgressRetry.HeadRange sent part head rest := by
  cases sent with
  | written => cases active.preparing
  | lower first => cases active.preparing
  | both first second head => exact ⟨.lower, head, [second.entry], .lower first second head⟩
  | tail first second head => exact ⟨.upper, head, [], .upper first second head⟩
  | retired first second => exact False.elim (active.nonempty rfl)

private theorem lower_drop_hop (active : Active core) (id : Nat)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor id = some .lower) :
    Nonempty (Hop initial native quantum allowance current monitor (.dropPacket id)) := by
  have exposed := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ selected
  cases active.lowerLane with
  | done phase => rw [exposed_done _ _ phase] at exposed; cases exposed
  | active work _ =>
    cases work with
    | ingress path _ =>
      have same : path.packetID = id := Option.some.inj ((data_ingress_exposed path).symm.trans exposed)
      have chosen : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .lower := by rw [same]; exact selected
      obtain ⟨actual, drop, ⟨credit⟩⟩ := P.original_ingress_at core path chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active credit.result.next (DS.lower_ingress active path drop credit)⟩⟩
    | ticket path _ => rw [data_ticket_unexposed path] at exposed; cases exposed
    | link path _ _ =>
      have same : path.packetID = id := Option.some.inj ((data_link_exposed path).symm.trans exposed)
      have chosen : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .lower := by rw [same]; exact selected
      obtain ⟨actual, drop, ⟨credit⟩⟩ := P.original_link_at core path chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active credit.result.next (DS.lower_link active path drop credit)⟩⟩

private theorem upper_drop_hop (active : Active core) (id : Nat)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor id = some .upper) :
    Nonempty (Hop initial native quantum allowance current monitor (.dropPacket id)) := by
  have exposed := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ selected
  cases active.upperLane with
  | done phase => rw [exposed_done _ _ phase] at exposed; cases exposed
  | active work _ =>
    cases work with
    | ingress path _ =>
      have same : path.packetID = id := Option.some.inj ((data_ingress_exposed path).symm.trans exposed)
      have chosen : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .upper := by rw [same]; exact selected
      obtain ⟨actual, drop, ⟨credit⟩⟩ := P.original_ingress_at core path chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active credit.result.next (DS.upper_ingress active path drop credit)⟩⟩
    | ticket path _ => rw [data_ticket_unexposed path] at exposed; cases exposed
    | link path _ _ =>
      have same : path.packetID = id := Option.some.inj ((data_link_exposed path).symm.trans exposed)
      have chosen : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .upper := by rw [same]; exact selected
      obtain ⟨actual, drop, ⟨credit⟩⟩ := P.original_link_at core path chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active credit.result.next (DS.upper_link active path drop credit)⟩⟩

private theorem retry_drop_hop (active : Active core) (id : Nat)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor id = some .retry) :
    Nonempty (Hop initial native quantum allowance current monitor (.dropPacket id)) := by
  have exposed := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ selected
  cases active.retry with
  | done phase => rw [exposed_done _ _ phase] at exposed; cases exposed
  | active part head rest selection work =>
    cases work with
    | ingress path _ =>
      have same : path.packetID = id := Option.some.inj ((data_ingress_exposed path).symm.trans exposed)
      have chosen : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .retry := by rw [same]; exact selected
      obtain ⟨actual, drop, ⟨credit⟩⟩ := P.retry_ingress_at core path (CampusTCPTwoProgressPhaseRetry.currentHead core selection) chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active credit.result.next (DS.retry_ingress active path selection drop credit)⟩⟩
    | ticket path _ => rw [data_ticket_unexposed path] at exposed; cases exposed
    | link path _ _ =>
      have same : path.packetID = id := Option.some.inj ((data_link_exposed path).symm.trans exposed)
      have chosen : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .retry := by rw [same]; exact selected
      obtain ⟨actual, drop, ⟨credit⟩⟩ := P.retry_link_at core path (CampusTCPTwoProgressPhaseRetry.currentHead core selection) chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active credit.result.next (DS.retry_link active path selection drop credit)⟩⟩

private theorem ack_drop_hop (active : Active core) (id : Nat)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor id = some .ack) :
    Nonempty (Hop initial native quantum allowance current monitor (.dropPacket id)) := by
  obtain ⟨lane, pending, exposed⟩ := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ selected
  have before : AckWork core lane := by simpa only [AckState, pending] using active.ack
  obtain ⟨part, head, rest, selection⟩ := current_head active
  cases before with
  | pending phase _ =>
    have absent := exposed_none (config initial native quantum allowance) current.report.final lane
      (by simp only [G.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, phase])
    rw [absent] at exposed
    cases exposed
  | ticket path => rw [ack_ticket_unexposed path] at exposed; cases exposed
  | ingress path =>
    have same : path.packetID = id := Option.some.inj ((ack_ingress_exposed path).symm.trans exposed)
    have chosen : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .ack := by rw [same]; exact selected
    by_cases covered : part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length
    · obtain ⟨actual, drop, ⟨credit⟩⟩ := P.ack_ingress_at core path (CampusTCPTwoProgressPhaseRetry.currentHead core selection)
        (DS.received_bound received) covered chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active credit.result.next (DS.ack_ingress_credited active path pending selection drop credit)⟩⟩
    · obtain ⟨actual, ⟨drop⟩⟩ := P.ingress_at core path.toIngress chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active drop.unassigned.next (DS.ack_ingress_unassigned active path pending selection covered drop)⟩⟩
  | link path =>
    have same : path.packetID = id := Option.some.inj ((ack_link_exposed path).symm.trans exposed)
    have chosen : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .ack := by rw [same]; exact selected
    by_cases covered : part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length
    · obtain ⟨actual, drop, ⟨credit⟩⟩ := P.ack_link_at core path (CampusTCPTwoProgressPhaseRetry.currentHead core selection)
        (DS.received_bound received) covered chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active credit.result.next (DS.ack_link_credited active path pending selection drop credit)⟩⟩
    · obtain ⟨actual, ⟨drop⟩⟩ := P.link_at core path.toLink chosen
      exact ⟨⟨actual, drop.selected.appended.move, by rw [drop.selected.appended.facts.event, drop.identity, same],
        .active drop.unassigned.next (DS.ack_link_unassigned active path pending selection covered drop)⟩⟩

theorem drop_hop (active : Active core) (id : Nat) (target : CampusTCPTwoProgressMonitor.DropTarget)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor id = some target) :
    Nonempty (Hop initial native quantum allowance current monitor (.dropPacket id)) := by
  cases target with
  | lower => exact lower_drop_hop active id selected
  | upper => exact upper_drop_hop active id selected
  | retry => exact retry_drop_hop active id selected
  | ack => exact ack_drop_hop active id selected

end Netlib.Check.CampusTCPTwoProgressEvidence
