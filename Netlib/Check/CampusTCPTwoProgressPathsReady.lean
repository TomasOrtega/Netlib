import Netlib.Check.CampusTCPTwoProgressPaths
import Netlib.Check.CampusTCPTwoProgressGatewayWindow

/-!
# Admission guards from current packet paths

The current range ledger selects fresh or repeated data admission.
Both choices use the actual packet fields and current window reserve.
-/

namespace Netlib.Check.CampusTCPTwoProgressPathsReady

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressSender
open CampusTCPTwoProgressGatewayState (View)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {part : Part} {produced : Produced input.active input.passive}

theorem peer_mss (initial : TwoWriteInitial cut sender gateway lower upper) (view : View initial current) (part : Part) :
    (part.bytes lower upper).length ≤ (view.gateway.session.peerMSS sender.direction).limit := by
  have total := Nat.le_trans initial.senderState.mss (initial.endpoint_peer_mss sender)
  have same : view.gateway.session.peerMSS sender.direction = initial.gatewayState.session.peerMSS sender.direction := by
    cases sender
    · exact view.gateway.identity.serverMSS
    · exact view.gateway.identity.clientMSS
  rw [same]
  cases part <;> simp only [Part.bytes] <;> omega

def rangeAt (view : View initial current) : Part → Option (Admission.Coverage.Run Nat)
  | .lower => view.ranges.lowerRun
  | .upper => view.ranges.upperRun

inductive DataAdmission (view : View initial current) (produced : Produced input.active input.passive) : Part → Prop where
  | lower (missing : view.ranges.lowerRun = none)
      (ready : Admission.FreshReady view.gateway.session sender.direction produced.source.packet.segment) :
      DataAdmission view produced .lower
  | upper (missing : view.ranges.upperRun = none)
      (ready : Admission.FreshReady view.gateway.session sender.direction produced.source.packet.segment) :
      DataAdmission view produced .upper
  | repeated {part : Part} (present : (rangeAt view part).isSome = true)
      (ready : Admission.RepeatedReady view.gateway.session sender.direction produced.source.packet.segment
      (beforeService input current.report.final gateway).admission.observations) : DataAdmission view produced part

theorem data_admission (view : View initial current) (space : CampusTCPTwoProgressGatewayWindow.Reserved view)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced) :
    DataAdmission view produced part := by
  have mss : produced.source.packet.segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit := by
    rw [fields.payload]
    exact peer_mss initial view part
  cases part with
  | lower =>
    have sequence : produced.source.packet.segment.sequence = (endpoint cut.endpoints sender).core.sendNext := by
      simpa only [Part.offset, Seq.add_zero] using fields.sequence
    cases present : view.ranges.lowerRun with
    | none =>
      apply DataAdmission.lower present
      exact CampusTCPTwoProgressGatewayWindow.lower_fresh view space _ present sequence fields.payload fields.profile mss fields.acknowledgment
    | some run =>
      exact DataAdmission.repeated (by simp only [rangeAt, present, Option.isSome_some])
        (view.lower_repeated run present _ sequence fields.payload fields.profile mss fields.acknowledgment)
  | upper =>
    cases present : view.ranges.upperRun with
    | none =>
      apply DataAdmission.upper present
      exact CampusTCPTwoProgressGatewayWindow.upper_fresh view space _ present fields.sequence fields.payload fields.profile mss fields.acknowledgment
    | some run =>
      exact DataAdmission.repeated (by simp only [rangeAt, present, Option.isSome_some])
        (view.upper_repeated run present _ fields.sequence fields.payload fields.profile mss fields.acknowledgment)

theorem current_zone (initial : TwoWriteInitial cut sender gateway lower upper) (view : View initial current) (actor : Actor) :
    view.gateway.session.entry.flow.zone actor.direction = input.zone := by
  rw [view.gateway.identity.entry, initial.entry_eq]
  cases actor
  · exact initial.basis.aligned.originalZone
  · exact initial.basis.aligned.replyZone

theorem data_header (view : View initial current)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced) :
    produced.source.packet.header = view.gateway.session.entry.flow.input sender.direction := by
  rw [view.gateway.identity.entry]
  exact fields.header

theorem ack_header (view : View initial current) (fields : CampusTCPTwoProgressWire.AckFields initial count produced) :
    produced.source.packet.header = view.gateway.session.entry.flow.input sender.other.direction := by
  rw [view.gateway.identity.entry]
  exact fields.header

end Netlib.Check.CampusTCPTwoProgressPathsReady
