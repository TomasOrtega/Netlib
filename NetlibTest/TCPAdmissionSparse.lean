import Netlib.Protocol.TCP.Admission
import Netlib.Protocol.TCP.WireForwarding

namespace NetlibTest.TCPAdmissionSparse

open Netlib Packet Protocol TCP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def tracked : Except ConntrackLifecycle.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.describe)

private def admitted : Except Admission.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.message)

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.tcp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.tcp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, translated.reverse, 0, 0, 0⟩, true, true⟩

private def permit : ConntrackLifecycle.Pipeline := {
  routes := [⟨⟨3325256706, 32⟩, some "server"⟩, ⟨⟨3221225986, 32⟩, some "client"⟩]
  forward := [], forwardDefault := .permit }

private def packet (header : Header) (sequence acknowledgment : Nat) (flags : UInt8)
    (payload : List UInt8 := []) (window : InternetChecksum.Word := 8) : IO EstablishedReceive.Input := do
  let segment := computed header.source header.destination {
    sourcePort := header.sourcePort, destinationPort := header.destinationPort,
    sequence := Seq.ofNat sequence, acknowledgment := Seq.ofNat acknowledgment,
    reserved := 0, flags := flags, window := window, checksum := 0, urgentPointer := 0,
    options := [], payload := payload }
  let bytes ← load (IPv4.encode ⟨0, 0, true, 64, Packet.Protocol.tcp, header.source, header.destination, segment.encodeBytes⟩)
  load (EstablishedReceive.input bytes)

private structure Served where
  admission : Admission.State
  tracker : ConntrackLifecycle.State
  emitted : Bool

private def serve (before : Served) (input : EstablishedReceive.Input)
    (candidate : Option NetfilterNAT.Entry := none) : IO Served := do
  let wire : TCP.WireForwarding.Input := ⟨0, input.packet, candidate⟩
  let prepared ← tracked (ConntrackLifecycle.prepare before.tracker wire.lifecycle)
  let result ← admitted (Admission.step before.admission input wire.lifecycle prepared rfl)
  let outcome ← tracked (TCP.WireForwarding.process permit wire input.valid prepared)
  let state ← admitted (Admission.commit result outcome.state)
  pure ⟨state, outcome.state, outcome.output.isSome⟩

private def startup (clientISS serverISS : Nat) : IO Served := do
  let initial : Served := ⟨.initial, .initial, false⟩
  let syn ← serve initial (← packet original clientISS 0 2) (some entry)
  let synAck ← serve syn (← packet translated.reverse serverISS ((Seq.ofNat clientISS).add 1).val 18)
  serve synAck (← packet original ((Seq.ofNat clientISS).add 1).val ((Seq.ofNat serverISS).add 1).val 16)

private def session (before : Served) : IO Admission.Session :=
  match before.admission.phase with
  | .data value => pure value
  | _ => throw (IO.userError "The checked startup has no data history.")

private def futureIngress : IO Unit := do
  let ready ← startup 1000 5000
  let future ← serve ready (← packet original 1005 5001 16 [5, 6])
  let observed ← session future
  ensure (future.emitted && observed.original.observed == 0 && future.admission.observations.length == 4)
    "Future ingress must emit immediately without certifying its missing prefix."

private def rejected (before : Served) (input : EstablishedReceive.Input) (expected : Admission.Unsupported) : IO Unit := do
  let wire : TCP.WireForwarding.Input := ⟨0, input.packet, none⟩
  let prepared ← tracked (ConntrackLifecycle.prepare before.tracker wire.lifecycle)
  match Admission.step before.admission input wire.lifecycle prepared rfl with
  | .error (.unsupported reason) => ensure (reason == expected) "The sparse admission scope is incorrect."
  | .ok _ => throw (IO.userError "The unsupported range acquired admission.")

private def twoHoles : IO Unit := do
  let ready ← startup 1000 5000
  let tail ← serve ready (← packet original 1007 5001 16 [7, 8])
  let sparse ← session tail
  ensure (tail.emitted && sparse.original.observed == 0 && sparse.original.highEnd == 8 &&
    sparse.original.uniqueBytes == 2 && sparse.original.outstanding == 8)
    "A future span must expose its actual extent without filling holes."
  rejected tail (← packet translated.reverse 5001 1009 16) .acknowledgment
  let middle ← serve tail (← packet original 1003 5001 16 [3, 4])
  let firstFill ← serve middle (← packet original 1001 5001 16 [1, 2])
  let partiallyCovered ← session firstFill
  ensure (firstFill.emitted && partiallyCovered.original.observed == 4 && partiallyCovered.original.highEnd == 8 &&
    partiallyCovered.original.uniqueBytes == 6 && partiallyCovered.original.outstanding == 8)
    "A lower unseen range must fill only its contiguous prefix."
  rejected firstFill (← packet translated.reverse 5001 1009 16) .acknowledgment
  let last ← serve firstFill (← packet original 1005 5001 16 [5, 6])
  let complete ← session last
  ensure (last.emitted && complete.original.observed == 8 && complete.original.highEnd == 8 &&
    complete.original.uniqueBytes == 8 && complete.original.coverage.nextID == 4)
    "The second unseen hole must close without counting old bytes again."
  let acknowledged ← serve last (← packet translated.reverse 5001 1009 16)
  let retired ← session acknowledged
  ensure (acknowledged.emitted && retired.original.acknowledged == 8 && retired.original.outstanding == 0)
    "A cumulative ACK may pass only after the observed holes close."

private def firstSource : IO Unit := do
  let ready ← startup 1000 5000
  let tail ← serve ready (← packet original 1007 5001 16 [7, 8])
  let before ← session tail
  let repeated ← serve tail (← packet original 1008 5001 16 [8])
  let after ← session repeated
  ensure (repeated.emitted && after.original.coverage == before.original.coverage &&
    (after.original.coverage.runs.head?).map (·.metadata) == some 3 &&
    repeated.admission.observations.length == 5)
    "A contained repeat must retain its first actual observation and allocate no coverage."
  rejected repeated (← packet original 1007 5001 16 [7, 9]) .conflict
  rejected repeated (← packet original 1006 5001 16 [6, 7]) .overlap
  rejected repeated (← packet original 1000 5001 16 [0]) .sequence

private def explicitAckEpoch : IO Unit := do
  let ready ← startup 1000 5000
  let tail ← serve ready (← packet original 1007 5001 16 [7, 8])
  let before ← session tail
  let inside ← serve tail (← packet original 1004 5001 16)
  let after ← session inside
  ensure (inside.emitted && after.original.coverage == before.original.coverage)
    "An empty ACK inside the bounded epoch must add no coverage."
  let edge ← serve inside (← packet original 1009 5001 16)
  ensure edge.emitted "An empty ACK at the observed high end must remain supported."
  rejected edge (← packet original 1010 5001 16) .sequence
  rejected edge (← packet original 1000 5001 16) .sequence

private def advertisedEdge : IO Unit := do
  let ready ← startup 1000 5000
  rejected ready (← packet original 1008 5001 16 [8, 9]) .window
  let tail ← serve ready (← packet original 1007 5001 16 [7, 8])
  let shrunk ← serve tail (← packet translated.reverse 5001 1001 16 [] 0)
  let repeated ← serve shrunk (← packet original 1007 5001 16 [7, 8])
  ensure repeated.emitted "A known range must survive a later peer-window reduction."
  rejected repeated (← packet original 1001 5001 16 [1, 2]) .window
  let ack ← serve repeated (← packet original 1009 5001 16)
  ensure ack.emitted "A zero peer window must not block an empty ACK."

private def reverseAndWrap : IO Unit := do
  let ready ← startup 1000 5000
  let reverse ← serve ready (← packet translated.reverse 5007 1001 16 [7, 8])
  let reversed ← session reverse
  ensure (reverse.emitted && reversed.reply.observed == 0 && reversed.reply.highEnd == 8 &&
    reversed.original.highEnd == 0) "Sparse coverage must remain directional."
  rejected reverse (← packet original 1001 5009 16) .acknowledgment
  let wrapped ← startup 4294967294 5000
  let tail ← serve wrapped (← packet original 5 5001 16 [7, 8])
  let middle ← serve tail (← packet original 1 5001 16 [3, 4])
  let firstFill ← serve middle (← packet original 4294967295 5001 16 [1, 2])
  let last ← serve firstFill (← packet original 3 5001 16 [5, 6])
  let complete ← session last
  ensure (last.emitted && complete.original.observed == 8 && complete.original.next.val == 7)
    "Sparse positions must retain one bounded epoch through sequence wrap."

def run : IO Unit := do
  futureIngress
  twoHoles
  firstSource
  explicitAckEpoch
  advertisedEdge
  reverseAndWrap
  IO.println "Checked sparse TCP admission tests passed."

end NetlibTest.TCPAdmissionSparse
