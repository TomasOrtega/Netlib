import Netlib.Check.FederatedDeployment
import NetlibTest.FederatedNativeFixture

namespace NetlibTest.FederatedBudget

open Netlib Federation

def run : IO Unit := do
  let input ← FederatedNativeFixture.load
  let baseline := { input with work := Deployment.workEstimate input }
  match Deployment.certify baseline with
  | .error reason => throw (IO.userError s!"The exact-budget baseline failed: {reason}")
  | .ok _ => pure ()
  let repeated := { baseline with intent :=
    { baseline.intent with borders := List.flatten (List.replicate 16 baseline.intent.borders) } }
  match Deployment.certify repeated with
  | .ok _ => throw (IO.userError "Repeated border records escaped the complete work guard.")
  | .error reason =>
    unless reason.startsWith "Complete federation work estimate" do
      throw (IO.userError s!"Repeated borders must fail the aggregate work guard: {reason}")
  IO.println "Federation border work guard passed."

end NetlibTest.FederatedBudget
