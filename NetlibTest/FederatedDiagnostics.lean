import Netlib.Check.FederatedDeployment
import NetlibTest.FederatedNativeFixture

namespace NetlibTest.FederatedDiagnostics

open Netlib Federation

def run : IO Unit := do
  let input ← FederatedNativeFixture.load
  let some valid := input.intent.borders.head?
    | throw (IO.userError "The native fixture has no declared border.")
  let stale := { valid with sourceVersion := valid.sourceVersion + 1 }
  let changed := { input with intent := { input.intent with borders := [valid, stale] } }
  match Deployment.certify changed with
  | .ok _ => throw (IO.userError "The stale second border must fail public certification.")
  | .error reason =>
    unless reason.contains "Border 1" && reason.contains (toString (repr stale.source)) &&
        reason.contains (toString (repr stale.target)) do
      throw (IO.userError s!"The failure must name Border 1 and both exact endpoint references. Actual error: {reason}")
  IO.println "Federation diagnostics: the stale second border retains its exact index and endpoint references."

end NetlibTest.FederatedDiagnostics
