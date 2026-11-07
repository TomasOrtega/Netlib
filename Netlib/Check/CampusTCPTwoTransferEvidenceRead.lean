import Netlib.Check.CampusTCPTwoTransferEvidence

/-!
# The forward read extends the same actual task

The current readable phase supplies the exact before Core and receipt sources.
The accepted read retains one action record and its selected byte origins.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferRecorded (Recorded)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

structure ReadAdvanced
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (actual : Step input) where
  first : S.Original initial .lower
  second : S.Original initial .upper
  core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location (.retired first second) .allReleased
  before : HEq core evidence.core
  senderDuplicate : core.live.senderFlight.recovery.duplicateAcks = 0
  mainAck : (core.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
    initial.geometry.«prefix» + (lower ++ upper).length
  value : CampusTCPTwoTransferLocatedRead.Complete core actual
  recorded : Recorded cut cfg value.finalCut (W.observe cfg monitor actual)

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

theorem Evidence.read_at (mode : monitor.exchange.forward.mode = .needRead) :
    ∃ actual, Nonempty (ReadAdvanced evidence actual) := by
  have finished := evidence.readable_finished mode
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    have impossible := state.mode
    rw [mode] at impossible
    cases impossible
  | pending state =>
    have impossible := state.mode
    rw [mode] at impossible
    cases impossible
  | active state =>
    rcases state.mode with impossible | impossible <;> rw [mode] at impossible <;> cases impossible
  | readable core exchange ready sources senderDuplicate mainAck =>
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoTransferLocatedRead.read_at core finished exchange mode sources
    exact ⟨actual, ⟨⟨_, _, core, HEq.rfl, senderDuplicate, mainAck, value,
      recorded.snoc value.value.move value.allowed⟩⟩⟩

theorem Evidence.read_step (mode : monitor.exchange.forward.mode = .needRead)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .read sender.other (lower ++ upper).length) :
    Nonempty (ReadAdvanced evidence actual) := by
  obtain ⟨chosen, ⟨value⟩⟩ := evidence.read_at mode
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
    (value.value.value.move.beforeEq.trans before.symm) (value.value.value.event.trans event.symm)
  exact same ▸ ⟨value⟩

theorem ReadAdvanced.suffix (advance : ReadAdvanced evidence actual) :
    advance.recorded.suffix = evidence.recorded.suffix ++ [actual] := by
  apply List.append_cancel_left
  rw [← advance.recorded.history]
  change advance.value.value.move.after.report.steps = _
  rw [advance.value.value.move.history, evidence.recorded.history, List.append_assoc]

theorem ReadAdvanced.loss_suffix (advance : ReadAdvanced evidence actual) :
    advance.recorded.suffix = advance.value.losses.suffix := advance.recorded.loss_suffix advance.value.losses

theorem ReadAdvanced.need_write (advance : ReadAdvanced evidence actual) :
    (W.observe cfg monitor actual).exchange.mode = .needWrite := advance.value.needWrite

theorem ReadAdvanced.sender_duplicate (advance : ReadAdvanced evidence actual) :
    advance.value.value.senderFlight.recovery.duplicateAcks = 0 := by
  have same := Option.some.inj (advance.value.value.senderFlight.runtime.symm.trans
    ((congrArg Endpoint.State.recovery advance.value.value.peer).trans advance.core.live.senderFlight.runtime))
  exact (congrArg Recovery.State.duplicateAcks same).trans advance.senderDuplicate

theorem ReadAdvanced.gateway_ack (advance : ReadAdvanced evidence actual) :
    (advance.value.gatewayState.gateway.session.lane sender.direction).acknowledged =
      initial.geometry.«prefix» + (lower ++ upper).length := advance.mainAck

theorem ReadAdvanced.permissions (advance : ReadAdvanced evidence actual) (prior : cut.report.compliant = true)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoTransferLocatedRead.ReadByte advance.value index byte,
      CampusTCPRoundOrigins.ServicePermissions origin.origin.delivery.service.joint.step
        origin.origin.delivery.receive.receipt.served := advance.value.read_permissions prior index byte selected

end Netlib.Check.CampusTCPTwoTransferEvidence
