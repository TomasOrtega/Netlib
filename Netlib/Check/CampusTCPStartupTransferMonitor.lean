import Netlib.Check.CampusTCPStartupTransferConfig

/-!
# Tagged demands for one startup and transfer execution

The startup plan contains raw operations and the selected remote socket.
Data demands retain their exact bytes, clock targets, and custody identities.
-/

namespace Netlib.Check.CampusTCPStartupTransferMonitor

open CampusTCPModel

deriving instance BEq, DecidableEq for Event

namespace T
export CampusTCPStartupTransferConfig (Config Handoff)
end T
namespace W
export CampusTCPTwoTransferMonitor (Demand)
end W

structure StartupPlan where
  preparation : List Event
  remote : Protocol.TCP.Handshake.Socket

structure Config where
  startup : StartupPlan
  transfer : T.Config

inductive Demand where
  | startup (event : Event)
  | data (demand : W.Demand)
  deriving BEq, DecidableEq

def serves (config : Config) : Demand → Event → Bool
  | .startup expected, event => decide (expected = event)
  | .data demand, event => config.transfer.serves demand event

theorem Demand.data_injective (first second : W.Demand) (same : Demand.data first = .data second) : first = second := by
  cases same
  rfl

theorem data_serves (config : Config) (handoff : T.Handoff active passive) (demand : W.Demand) (event : Event) :
    serves config (.data demand) event = CampusTCPTwoTransferMonitor.serves (config.transfer.data handoff) demand event :=
  (config.transfer.data_serves handoff demand event).symm

end Netlib.Check.CampusTCPStartupTransferMonitor
