import Netlib.Import.PacketFields
import Netlib.Protocol.NetfilterNAT

/-!
# Full-status conntrack capture records

The supported JSON is produced by the reviewed raw-Netlink capture script.
Hex strings retain capture evidence. This parser does not decode them or prove their agreement with JSON fields.
Kernel identity, capture completeness, and C refinement remain outside these checks.
-/

namespace Netlib.Import.ConntrackNetlink

open Packet Protocol

def unsupportedStatusBits : List Nat := [0, 6, 9, 11, 12, 13, 14, 15]

def StatusSupported (status : Nat) : Prop :=
  status < 65536 ∧ status.testBit 3 = true ∧
  (∀ bit ∈ unsupportedStatusBits, status.testBit bit = false) ∧
  (status.testBit 4 = true → status.testBit 7 = true) ∧
  (status.testBit 5 = true → status.testBit 8 = true)

instance (status : Nat) : Decidable (StatusSupported status) := by
  unfold StatusSupported
  infer_instance

structure SourceEntry where
  entry : NetfilterNAT.Entry
  status : Nat
  index : Nat
  id : Option Nat
  mark : Option Nat
  use : Option Nat
  raw : String
  deriving Repr, BEq, DecidableEq

namespace SourceEntry

def sourcePath (row : SourceEntry) : String := s!"/entries/{row.index}"

def native (row : SourceEntry) : NetfilterNAT.Entry := row.entry

def Supported (row : SourceEntry) : Prop :=
  StatusSupported row.status ∧ row.native.Compatible ∧
    row.entry.sourceNAT = row.status.testBit 4 ∧ row.entry.destinationNAT = row.status.testBit 5

instance (row : SourceEntry) : Decidable row.Supported := by
  unfold Supported
  infer_instance

def supported (row : SourceEntry) : Bool := decide row.Supported

theorem supported_iff (row : SourceEntry) : row.supported = true ↔ row.Supported := by simp [supported]

theorem compatible_of_supported (row : SourceEntry) (accepted : row.supported = true) : row.native.Compatible :=
  ((supported_iff row).mp accepted).2.1

theorem rewrite_correct (row : SourceEntry) (accepted : row.supported = true) (direction : FlowNAT.Direction) :
    (row.native.rewrite direction).apply (row.entry.flow.input direction) = row.entry.flow.output direction :=
  row.native.rewrite_correct (row.compatible_of_supported accepted) direction

end SourceEntry

structure Snapshot where
  entries : List SourceEntry
  messages : List String
  request : String
  raw : Lean.Json

def Snapshot.model (snapshot : Snapshot) : FlowNAT.Snapshot :=
  ⟨snapshot.entries.map (·.entry.flow)⟩

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def bounded (size : Nat) (json : Lean.Json) : Except String Nat := do
  let value ← json.getNat?
  require (value < size) s!"Value exceeds its {size}-value range."
  return value

private def hexDigit (char : Char) : Bool :=
  ('0' ≤ char && char ≤ '9') || ('a' ≤ char && char ≤ 'f') || ('A' ≤ char && char ≤ 'F')

private def hex (json : Lean.Json) (minimumBytes : Nat) : Except String String := do
  let value ← json.getStr?
  require (value.length % 2 == 0 && minimumBytes * 2 ≤ value.length && value.toList.all hexDigit)
    "Require an even-length hexadecimal string of the expected minimum size."
  return value

private def optionalU32 (json : Lean.Json) : Except String (Option Nat) :=
  match json with
  | .null => .ok none
  | value => some <$> bounded 4294967296 value

private def parseEntry (json : Lean.Json) (index : Nat) : Except String SourceEntry := do
  PacketFields.fields json ["original", "reply", "originalZone", "replyZone", "remainingTTL", "status",
    "id", "mark", "use", "raw"]
  let status ← bounded 4294967296 (← json.getObjVal? "status")
  require (decide (StatusSupported status)) "Unsupported or incomplete ordinary conntrack status."
  let flow : FlowNAT.Entry := {
    original := ← PacketFields.header (← json.getObjVal? "original")
    reply := ← PacketFields.header (← json.getObjVal? "reply")
    originalZone := ← bounded 65536 (← json.getObjVal? "originalZone")
    replyZone := ← bounded 65536 (← json.getObjVal? "replyZone")
    remainingTTL := ← bounded 4294967296 (← json.getObjVal? "remainingTTL") }
  let native : NetfilterNAT.Entry := ⟨flow, status.testBit 4, status.testBit 5⟩
  require native.check "NAT status flags and tuple endpoints are incompatible."
  let row : SourceEntry := {
    entry := native
    status
    index
    id := ← optionalU32 (← json.getObjVal? "id")
    mark := ← optionalU32 (← json.getObjVal? "mark")
    use := ← optionalU32 (← json.getObjVal? "use")
    raw := ← hex (← json.getObjVal? "raw") 20 }
  require row.supported "Unsupported conntrack tuple/status combination."
  return row

def Snapshot.fromJson (json : Lean.Json) : Except String Snapshot := do
  PacketFields.fields json ["schema", "family", "entries", "messages", "request"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use conntrack capture schema 1."
  require ((← (← json.getObjVal? "family").getNat?) == 2) "Only IPv4 conntrack captures are supported."
  let request ← hex (← json.getObjVal? "request") 20
  require (request.length == 40) "The IPv4 capture request must contain 20 bytes."
  let values ← (← json.getObjVal? "messages").getArr?
  require (!values.isEmpty) "The capture must retain its completion messages."
  let mut messages := []
  for index in [:values.size] do
    let value ← (hex values[index]! 20).mapError (s!"/messages/{index}: " ++ ·)
    messages := messages ++ [value]
  let values ← (← json.getObjVal? "entries").getArr?
  let mut entries := []
  for index in [:values.size] do
    let row ← (parseEntry values[index]! index).mapError (s!"/entries/{index}: " ++ ·)
    entries := entries ++ [row]
  let snapshot : Snapshot := ⟨entries, messages, request, json⟩
  snapshot.model.validate
  return snapshot

def Snapshot.parse (text : String) : Except String Snapshot := do
  Snapshot.fromJson (← Json.parse text)

end Netlib.Import.ConntrackNetlink
