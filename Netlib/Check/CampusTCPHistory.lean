import Netlib.Check.CampusTCPService
import Netlib.Protocol.TCP.Checkpoint

/-!
# Reachable transport history from actual campus service

The checkpoint history uses the same preparation, admission, forwarding, and commitment as service.
An early ingress drop preserves that history.
-/

namespace Netlib.Check.CampusTCPService

open Protocol

def Processing.transition (value : Processing context before source zone mode) :
    TCP.Checkpoint.Transition ⟨before.tracker, before.admission⟩ mode :=
  ⟨⟨source.asInput, zone, (packetInput before source zone).candidate⟩,
    before.configuration.pipeline context.routing, value.prepared, value.attached,
    value.admitted, value.admissionComputed, value.outcome, value.computed,
    value.nextAdmission, value.committed⟩

def Evidence.history (value : Evidence context before source zone ingress mode)
    (history : TCP.Checkpoint.History ⟨before.tracker, before.admission⟩) :
    TCP.Checkpoint.History ⟨value.tracker, value.admission⟩ := by
  cases value with
  | mk checks operation =>
    cases operation with
    | earlyDrop denied => exact history
    | processed permitted processing => exact .advance history processing.transition

end Netlib.Check.CampusTCPService
