import Netlib.Check.Wire

namespace NetlibTest.WireCheck

open Netlib

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reject (result : Except String α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError "Malformed wire input unexpectedly passed.")
  | .error _ => pure ()

def run : IO Unit := do
  let input ← unwrap (Check.Wire.Input.parse (← IO.FS.readFile "examples/wire/frame.json"))
  let checked ← unwrap input.check
  ensure ((← unwrap checked.encode) == input.bytes) "A checked Ethernet packet must reconstruct the exact input bytes."
  ensure ((← unwrap (checked.renderJson.getObjVal? "udpChecksumVerified" >>= Lean.Json.getBool?)))
    "The fresh ordinary socket capture must carry a verified nonzero UDP checksum."
  let evidence ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/wire/checked-evidence.json"))
  let probes ← unwrap (evidence.getObjVal? "probes" >>= Lean.Json.getArr?)
  for index in [:probes.size] do
    let probe := probes[index]!
    let ingress ← unwrap (probe.getObjVal? "ingress")
    let raw ← unwrap (ingress.getObjVal? "raw")
    let input ← unwrap (Check.Wire.Input.fromJson (Lean.Json.mkObj [("schema", Lean.toJson (1 : Nat)), ("raw", raw)]))
    if index < 2 then
      let decoded ← unwrap input.check
      ensure ((← unwrap decoded.encode) == input.bytes) "Both checked and omitted UDP checksums must preserve raw bytes."
      ensure ((← unwrap (decoded.renderJson.getObjVal? "udpChecksumVerified" >>= Lean.Json.getBool?)) == (index == 0))
        "Checksum omission must remain distinct from verification in the public report."
    else reject input.check
  let raw := Lean.toJson (Import.EAPOL.bytesToHex input.bytes)
  reject (Check.Wire.Input.fromJson (Lean.Json.mkObj [
    ("schema", Lean.toJson (1 : Nat)), ("raw", raw), ("header", Import.PacketFields.headerJson checked.header)]))
  reject (Check.Wire.Input.parse "{\"schema\":1,\"schema\":1,\"raw\":\"\"}")
  reject (Check.Wire.Input.parse "{\"schema\":2,\"raw\":\"\"}")
  reject (Check.Wire.Input.parse "{\"schema\":1,\"raw\":\"0\"}")
  IO.println "Wire byte checker and report tests passed."

end NetlibTest.WireCheck
