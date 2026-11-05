import Netlib.Import.IPv4

namespace NetlibTest.ImportIPv4

open Netlib

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "An invalid IPv4 spelling was accepted.")

def run : IO Unit := do
  for (text, expected) in [("0.0.0.0", 0), ("10.0.0.1", 167772161),
      ("192.168.1.1", 3232235777), ("255.255.255.255", 4294967295)] do
    let address ← unwrap (Import.IPv4.parseAddress text)
    require (address.val == expected) "The dotted IPv4 value changed."
  let host ← unwrap (Import.IPv4.parsePrefix "10.0.0.1")
  require (host.length == 32 && host.address == 167772161) "A host prefix changed."
  let whole ← unwrap (Import.IPv4.parsePrefix "0.0.0.0/0")
  require (whole.contains 4294967295) "The zero prefix lost an address."
  let noncanonical ← unwrap (Import.IPv4.parsePrefix "10.0.0.17/24")
  require (noncanonical.contains 167772161 && !noncanonical.contains 167772416)
    "The prefix did not preserve its leading bits."
  for text in ["", "10.0.0", "10.0.0.1.2", "10.0.0.256", "10.-1.0.1", "010.0.0.1",
      "10.0.0.1 ", " 10.0.0.1", "0x0a.0.0.1", "10..0.1", "::1"] do
    reject (Import.IPv4.parseAddress text)
  for text in ["default", "10.0.0.0/33", "10.0.0.0/-1", "10.0.0.0/024", "10.0.0.0/24/1"] do
    reject (Import.IPv4.parsePrefix text)
  IO.println "IPv4 import tests passed."

end NetlibTest.ImportIPv4
