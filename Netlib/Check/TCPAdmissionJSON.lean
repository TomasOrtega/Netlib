import Netlib.Protocol.TCP.Admission
import Netlib.Check.TCP

/-!
# Gateway observation report fields

First-source indices refer to actual committed observation records.
Sparse coverage records do not delay packet forwarding.
-/

namespace Netlib.Check.TCPAdmissionJSON

open Packet Protocol

def directionName : FlowNAT.Direction → String | .original => "original" | .reply => "reply"

def entryJson (entry : NetfilterNAT.Entry) : Lean.Json := Lean.Json.mkObj [
  ("original", Import.PacketFields.headerJson entry.flow.original), ("reply", Import.PacketFields.headerJson entry.flow.reply),
  ("originalZone", Lean.toJson entry.flow.originalZone), ("replyZone", Lean.toJson entry.flow.replyZone),
  ("sourceNAT", Lean.toJson entry.sourceNAT), ("destinationNAT", Lean.toJson entry.destinationNAT)]

private def sourceOrder : List (Theory.SparseCoverage.Run Nat) → Bool
  | first :: second :: rest => decide (first.sourceID < second.sourceID) && sourceOrder (second :: rest)
  | _ => true

def sparseSeen (lane : Protocol.TCP.Admission.Lane) : Bool :=
  decide (lane.observed ≠ lane.highEnd) || !sourceOrder lane.coverage.runs

def runJson (run : Theory.SparseCoverage.Run Nat) : Lean.Json := Lean.Json.mkObj [
  ("position", Lean.toJson run.position), ("end", Lean.toJson run.limit),
  ("sourceID", Lean.toJson run.sourceID), ("observationIndex", Lean.toJson run.metadata),
  ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex run.bytes))]

def coverageJson (lane : Protocol.TCP.Admission.Lane) : Lean.Json := Lean.Json.mkObj [
  ("highEnd", Lean.toJson lane.highEnd), ("uniqueBytes", Lean.toJson lane.uniqueBytes),
  ("nextID", Lean.toJson lane.coverage.nextID), ("runs", Lean.toJson (lane.coverage.runs.map runJson))]

def laneJson (lane : Protocol.TCP.Admission.Lane) : Lean.Json := Lean.Json.mkObj ([
  ("base", Lean.toJson lane.base.val), ("observed", Lean.toJson lane.observed), ("acknowledged", Lean.toJson lane.acknowledged),
  ("peerWindow", Lean.toJson lane.peerWindow.val), ("windowSequence", Lean.toJson lane.windowSequence.val),
  ("windowAcknowledgment", Lean.toJson lane.windowAcknowledgment.val)] ++
  if sparseSeen lane then [("coverage", coverageJson lane)] else [])

def mssJson : Protocol.TCP.MSS.Offer → Lean.Json
  | .absent => Lean.Json.mkObj [("kind", Lean.toJson "absent")]
  | .present value => Lean.Json.mkObj [("kind", Lean.toJson "present"), ("value", Lean.toJson value.word.val)]

def mssFields (client server : Protocol.TCP.MSS.Offer) : List (String × Lean.Json) :=
  match client, server with
  | .absent, .absent => []
  | _, _ => [("clientMSS", mssJson client), ("serverMSS", mssJson server),
      ("originalMSS", Lean.toJson server.limit), ("replyMSS", Lean.toJson client.limit)]

def seenJson (seen : Protocol.TCP.Admission.Seen) : Lean.Json := Lean.Json.mkObj [
  ("zone", Lean.toJson seen.zone), ("rawIPv4Hex", Lean.toJson (Import.EAPOL.bytesToHex seen.bytes)),
  ("header", Import.PacketFields.headerJson seen.header), ("segment", Check.TCP.segmentJson seen.segment),
  ("entry", entryJson seen.attachment.entry), ("direction", Lean.toJson (directionName seen.attachment.direction)),
  ("classification", Lean.toJson (match seen.attachment.classification with
    | .new => "new" | .established => "established" | .related => "related" | .invalid => "invalid" | .untracked => "untracked")),
  ("fresh", Lean.toJson seen.attachment.fresh)]

def admissionJson (state : Protocol.TCP.Admission.State) : Lean.Json :=
  let initialWindow (flags : UInt8) := ((state.observations.find? (·.segment.flags == flags)).map (·.segment.window.val)).getD 0
  Lean.Json.mkObj ([
    ("phase", Lean.toJson state.phase.name), ("observations", Lean.toJson state.observations.length),
    ("sourcePackets", Lean.toJson (state.observations.map seenJson))] ++ match state.phase with
    | .empty => []
    | .syn entry iss window clientMSS => [
      ("entry", entryJson entry), ("clientISS", Lean.toJson iss.val), ("clientWindow", Lean.toJson window.val)] ++
      (match clientMSS with
      | .absent => []
      | .present _ => [("clientMSS", mssJson clientMSS), ("replyMSS", Lean.toJson clientMSS.limit)])
    | .synAck entry iss window serverISS serverWindow clientMSS serverMSS => [
      ("entry", entryJson entry), ("clientISS", Lean.toJson iss.val), ("clientWindow", Lean.toJson window.val),
      ("serverISS", Lean.toJson serverISS.val), ("serverWindow", Lean.toJson serverWindow.val)] ++ mssFields clientMSS serverMSS
    | .data session => [
      ("entry", entryJson session.entry), ("clientISS", Lean.toJson session.original.controlOrigin.val),
      ("clientWindow", Lean.toJson (initialWindow 2)), ("serverISS", Lean.toJson session.reply.controlOrigin.val),
      ("serverWindow", Lean.toJson (initialWindow 18)), ("original", laneJson session.original), ("reply", laneJson session.reply)] ++
      mssFields session.clientMSS session.serverMSS)

end Netlib.Check.TCPAdmissionJSON
