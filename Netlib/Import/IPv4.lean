import Netlib.Packet.Basic

namespace Netlib.Import.IPv4

private def decimal (text : String) : Except String Nat := do
  if text.isEmpty || !(text.toList.all Char.isDigit) then throw "Use unsigned decimal digits."
  if text.length > 1 && text.startsWith "0" then throw "Leading zeroes are not supported."
  match text.toNat? with
  | some value => return value
  | none => throw "Invalid decimal value."

private def octet (text : String) : Except String (Fin 256) := do
  let value ← decimal text
  if fits : value < 256 then return ⟨value, fits⟩
  else throw "An IPv4 octet exceeds 255."

/-- The accepted spelling is four decimal octets without leading zeroes. -/
def parseAddress (text : String) : Except String Packet.Address := do
  match text.splitOn "." with
  | [a, b, c, d] =>
    let a ← octet a
    let b ← octet b
    let c ← octet c
    let d ← octet d
    let value := ((a.val * 256 + b.val) * 256 + c.val) * 256 + d.val
    if fits : value < 4294967296 then return ⟨value, fits⟩
    else throw "The IPv4 address exceeds 32 bits."
  | _ => throw "Use four decimal IPv4 octets."

/-- A host address without a prefix length denotes a single address. -/
def parsePrefix (text : String) : Except String Packet.Prefix := do
  match text.splitOn "/" with
  | [address] => return ⟨← parseAddress address, 32⟩
  | [address, length] =>
    let value ← decimal length
    if fits : value < 33 then return ⟨← parseAddress address, ⟨value, fits⟩⟩
    else throw "The IPv4 prefix length exceeds 32."
  | _ => throw "Use an IPv4 address and an optional prefix length."

end Netlib.Import.IPv4
