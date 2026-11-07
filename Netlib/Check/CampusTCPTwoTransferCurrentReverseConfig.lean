import Netlib.Check.CampusTCPTwoTransferCurrentReverseGeometry

/-!
# The actual standby reverse selector

Current standby routing selects the same ingress and recovery inputs as the
reverse task created at the actual write.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseConfig

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferPostRead (After)
open CampusTCPTwoTransferCurrentReverseGeometry (Started)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore current later : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor monitor : CampusTCPTwoTransferMonitor.Monitor} {readActual actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual} {value : After forward current monitor}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem config_at (start : Started value actual) (resident : Routing later .standby) (forwardDrops : Nat) :
    CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum (allowance - forwardDrops) =
      ((cfg).at later.report.final).reverse forwardDrops := by
  simp only [CampusTCPTwoProgressSetup.config, config, CampusTCPTwoTransferNative.Checks.monitorConfig,
    CampusTCPTwoTransferMonitor.Config.at, CampusTCPTwoExchangeSetup.config,
    CampusTCPTwoExchangeMonitor.Config.reverse, CampusTCPTwoExchangeMonitor.Config.reverseBytes,
    start.reverse_ingress, start.reverse_rto, resident.owners .client, resident.owners .server]

theorem at_write (start : Started value actual) (forwardDrops : Nat) :
    CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum (allowance - forwardDrops) =
      ((cfg).at start.boundary.write.move.after.report.final).reverse forwardDrops :=
  config_at start (Routing.ofNative start.reverseNative) forwardDrops

end Netlib.Check.CampusTCPTwoTransferCurrentReverseConfig
