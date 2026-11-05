import Netlib.Import.ConntrackNetlink

namespace NetlibTest.ConntrackNetlink

open Netlib
open Packet Protocol
open Import.ConntrackNetlink

private def original : Header := ⟨167772161, 3325256705, Packet.Protocol.tcp, 40000, 443⟩
private def aliasEndpoint : Endpoint := ⟨3405803777, 62000⟩
private def wire : Header := (Rewrite.sourceEndpoint aliasEndpoint).apply original

private def bytes : String := String.ofList (List.replicate 40 '0')
private def object (fields : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj fields
private def number (value : Nat) : Lean.Json := Lean.toJson value

private def row (packet reply : Header) (status : Nat) : Lean.Json :=
  object [
    ("original", Import.PacketFields.headerJson packet),
    ("reply", Import.PacketFields.headerJson reply),
    ("originalZone", number 0), ("replyZone", number 0), ("remainingTTL", number 0),
    ("status", number status), ("id", number 123), ("mark", .null), ("use", number 17), ("raw", .str bytes)]

private def sourceRow : Lean.Json := row original wire.reverse 152
private def plainRow : Lean.Json := row original original.reverse 8

private def document (rows : List Lean.Json) : Lean.Json :=
  object [("schema", number 1), ("family", number 2), ("entries", .arr rows.toArray),
    ("messages", .arr #[.str bytes]), ("request", .str bytes)]

private def update (json : Lean.Json) (key : String) (value : Lean.Json) : Except String Lean.Json := do
  let fields ← json.getObj?
  return object ((fields.toList.filter (·.1 != key)) ++ [(key, value)])

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def rejected (json : Lean.Json) : IO Unit := do
  match Snapshot.fromJson json with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Unsupported full-status capture passed.")

private def positiveTests : IO Unit := do
  let json := document [sourceRow]
  let parsed ← unwrap (Snapshot.parse json.compress)
  ensure (parsed.entries.length == 1 && parsed.messages == [bytes] && parsed.request == bytes)
    "The parser must preserve capture messages and request bytes."
  let selected ← match parsed.entries with
    | [selected] => pure selected
    | _ => throw (IO.userError "The source entry list changed.")
  ensure (selected.status == 152 && selected.index == 0 && selected.sourcePath == "/entries/0")
    "Source status and entry location must survive import."
  ensure (selected.id == some 123 && selected.mark.isNone && selected.use == some 17 && selected.raw == bytes)
    "Nullable metadata and source bytes must survive import."
  ensure (selected.supported && selected.entry.sourceNAT && !selected.entry.destinationNAT)
    "NAT flags must derive from the full status bits."
  ensure (selected.entry.flow.remainingTTL == 0) "Zero timeout seconds must remain captured evidence."
  ensure (parsed.model.translate 0 original == some wire && parsed.model.translate 0 wire.reverse == some original.reverse)
    "The supported source tuple pair must project in both directions."
  let peer := { original with source := 167772163, sourcePort := 40001, destination := 3325256706 }
  let peerWire := (Rewrite.sourceEndpoint aliasEndpoint).apply peer
  let peers ← unwrap (Snapshot.fromJson (document [sourceRow, row peer peerWire.reverse 152]))
  ensure (peers.model.translate 0 peerWire.reverse == some peer.reverse)
    "Remote peers sharing an alias must retain distinct full-tuple associations."
  let plain ← unwrap (Snapshot.fromJson (document [plainRow]))
  ensure (plain.model.translate 0 original == some original) "Absent NAT status must retain coherent plain tuples."
  match plain.entries with
  | [selected] =>
    let forged := { selected with entry := { selected.entry with sourceNAT := true } }
    ensure (!forged.supported) "A native rewrite flag must agree with the full status mask."
  | _ => throw (IO.userError "The plain source entry list changed.")
  let allAllowed := 8 + 2 + 4 + 128 + 256 + 1024
  let allowed ← unwrap (Snapshot.fromJson (document [row original original.reverse allAllowed]))
  ensure (allowed.entries.all SourceEntry.supported) "Supported informational status bits must remain accepted."
  let empty ← unwrap (Snapshot.fromJson (document []))
  ensure (empty.entries.isEmpty && (empty.model.translate 0 original).isNone)
    "An empty reported table must not invent a flow association."
  let symmetricZones ← unwrap (update (row original original 440) "replyZone" (number 1))
  let zones ← unwrap (Snapshot.fromJson (document [symmetricZones]))
  ensure zones.model.check "Distinct effective zones must preserve direction-key separation."

private def rejectionTests : IO Unit := do
  for bit in unsupportedStatusBits ++ [16, 31] do
    rejected (document [row original original.reverse (8 + 2 ^ bit)])
  rejected (document [row original original.reverse 0])
  rejected (document [row original wire.reverse 24])
  let backend := (Rewrite.destinationEndpoint (⟨167772162, 8443⟩ : Endpoint)).apply original
  rejected (document [row original backend.reverse 40])
  rejected (document [row original wire.reverse 8])
  rejected (document [sourceRow, sourceRow])
  rejected (document [row original { wire.reverse with protocol := Packet.Protocol.udp } 152])
  for (key, value) in [
    ("remainingTTL", Lean.Json.null), ("remainingTTL", number 4294967296),
    ("originalZone", number 65536), ("replyZone", number 65536),
    ("status", number 4294967296), ("id", number 4294967296),
    ("mark", Lean.Json.str "0"), ("use", Lean.Json.num (-1)),
    ("raw", Lean.Json.str "0"), ("raw", Lean.Json.str "gg"),
    ("raw", Lean.Json.str ("gg" ++ (bytes.drop 2).toString)), ("raw", Lean.Json.str (bytes ++ "0")),
    ("raw", Lean.Json.str ""), ("unexpected", Lean.Json.null)
  ] do rejected (document [← unwrap (update sourceRow key value)])
  let valid := document [sourceRow]
  for (key, value) in [
    ("schema", number 2), ("family", number 10), ("unexpected", Lean.Json.null),
    ("request", Lean.Json.str "00"), ("request", Lean.Json.str (bytes ++ "00")),
    ("request", Lean.Json.str ("gg" ++ (bytes.drop 2).toString)),
    ("messages", Lean.Json.arr #[]), ("messages", Lean.Json.arr #[.str "00"]),
    ("messages", Lean.Json.arr #[Lean.Json.null])
  ] do rejected (← unwrap (update valid key value))
  match Snapshot.parse ("{\"schema\":0," ++ (valid.compress.drop 1).toString) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Duplicate capture keys must fail before import.")

private def nativeTests : IO Unit := do
  let snapshot ← unwrap (Snapshot.parse (← IO.FS.readFile "examples/conntrack/native/netlink.json"))
  ensure (snapshot.entries.length == 4 && snapshot.entries.all SourceEntry.supported)
    "The supported native capture must retain all four visible flows."
  ensure (snapshot.entries.all (fun row => row.status == 414 || row.status == 410))
    "The native full status masks must survive import."
  ensure (snapshot.entries.all (fun row => row.entry.flow.reply.destinationEndpoint == (⟨3405803777, 40000⟩ : Endpoint)))
    "The native remote peers must share the captured public endpoint."
  for row in snapshot.entries do
    ensure (snapshot.model.translate row.entry.flow.originalZone row.entry.flow.original ==
      some row.entry.flow.reply.reverse) "Every native original tuple must retain its projected wire tuple."
    ensure (snapshot.model.translate row.entry.flow.replyZone row.entry.flow.reply ==
      some row.entry.flow.original.reverse) "Every native reply tuple must retain its projected inside tuple."
    for direction in [FlowNAT.Direction.original, FlowNAT.Direction.reply] do
      ensure ((row.native.rewrite direction).apply (row.entry.flow.input direction) == row.entry.flow.output direction)
        "Captured NAT status must satisfy conditional rewrite compatibility."

example (row : SourceEntry) (supported : row.supported = true) (direction : FlowNAT.Direction) :
    (row.native.rewrite direction).apply (row.entry.flow.input direction) = row.entry.flow.output direction :=
  row.rewrite_correct supported direction

def run : IO Unit := do
  positiveTests
  rejectionTests
  nativeTests
  IO.println "Full-status conntrack import tests passed."

end NetlibTest.ConntrackNetlink
