import Netlib.Model.FederatedCohort
import Netlib.Check.FederatedPacket

/-!
# Native certificates for each immutable packet context

A component retains its actual single-packet certificate. Header choices stay
separate so the cohort checker can cover their complete Cartesian product.
-/

namespace Netlib.Federation.Cohort

variable {input : Input} {size : Nat}

structure Component (context : Context input size) (index : Fin size) where
  profile : InFlight.Profile
  certificate : InFlight.Certified input profile
  contextEq : certificate.context = context.packets.get index

structure Family (context : Context input size) where
  component : (index : Fin size) → Component context index

def Accepted (context : Context input size) (headers : Vector Packet.Header size) : Prop :=
  ∀ index, (context.packets.get index).first.selector.accepts (headers.get index) = true

def Component.cellAt (value : Component context index) (header : Packet.Header)
    (accepted : (context.packets.get index).first.selector.accepts header = true) :
    InFlight.RankedCell (context.packets.get index) header :=
  value.contextEq ▸ value.certificate.cellAt header (by simpa only [value.contextEq] using accepted)

def Family.cell (family : Family context) (headers : Vector Packet.Header size)
    (accepted : Accepted context headers) (index : Fin size) :
    InFlight.RankedCell (context.packets.get index) (headers.get index) :=
  (family.component index).cellAt (headers.get index) (accepted index)

end Netlib.Federation.Cohort
