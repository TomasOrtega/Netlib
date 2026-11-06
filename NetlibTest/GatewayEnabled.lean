import Netlib.Protocol.ConntrackLifecycleEnabled
import Netlib.Protocol.TCP.AdmissionEnabled
import Netlib.Protocol.TCP.WireForwardingEnabled

namespace NetlibTest.GatewayEnabled

open Netlib Packet Protocol

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.tcp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.tcp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, translated.reverse, 0, 0, 0⟩, true, true⟩
private def tracker (seen : Bool) : ConntrackLifecycle.State := ⟨[⟨entry, seen⟩]⟩
private def pipeline : ConntrackLifecycle.Pipeline := {
  routes := [⟨⟨3325256706, 32⟩, some "server"⟩, ⟨⟨3221225986, 32⟩, some "client"⟩]
  forward := [], forwardDefault := .permit }

private theorem existingReady (seen : Bool) (direction : FlowNAT.Direction) :
    ConntrackLifecycle.ExistingReady pipeline (tracker seen)
      ⟨0, entry.flow.input direction, none⟩ ⟨entry.flow, direction⟩
      (match direction with | .original => "server" | .reply => "client") := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_⟩
  · apply (ConntrackLifecycle.State.check_correct _).mp
    cases seen <;> decide
  · change 0 < 65536
    decide
  · cases direction <;> decide
  · cases direction <;> cases seen <;> decide
  · intro actual member same
    have actualEq : actual = ⟨entry, seen⟩ := by simpa only [tracker, List.mem_singleton] using member
    subst actual
    cases direction <;> cases seen <;> exact ⟨rfl, by decide, rfl, rfl⟩

private def dataSession : TCP.Admission.Session :=
  ⟨entry, TCP.Admission.Lane.initial (TCP.Seq.ofNat 1001) 8 (TCP.Seq.ofNat 5000) (TCP.Seq.ofNat 1001),
    TCP.Admission.Lane.initial (TCP.Seq.ofNat 5001) 8 (TCP.Seq.ofNat 1001) (TCP.Seq.ofNat 5001),
    TCP.Admission.Lane.initial_valid _ _ _ _, TCP.Admission.Lane.initial_valid _ _ _ _,
    by constructor <;> decide, by constructor <;> decide, .absent, .absent⟩

private def segment (sequence acknowledgment : Nat) (payload : List UInt8) : TCP.Segment := {
  sourcePort := original.sourcePort, destinationPort := original.destinationPort,
  sequence := TCP.Seq.ofNat sequence, acknowledgment := TCP.Seq.ofNat acknowledgment,
  reserved := 0, flags := 16, window := 8, checksum := 0, urgentPointer := 0, options := [], payload }

private theorem fresh_geometry : TCP.Admission.FreshReady dataSession .original (segment 1001 5001 [1, 2, 3]) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, by decide, by decide⟩
  intro run member
  simp only [dataSession, TCP.Admission.Session.sender, TCP.Admission.Lane.initial,
    Theory.SparseCoverage.initial, List.not_mem_nil] at member

private theorem ack_geometry : TCP.Admission.AckReady dataSession .original (segment 1001 5001 []) :=
  ⟨by decide, rfl, by decide, by decide, by decide⟩

private theorem fresh_admission : TCP.Admission.Allowed (.data dataSession)
    (ConntrackLifecycle.selectedAttachment ⟨entry, true⟩ .original) (segment 1001 5001 [1, 2, 3]) [] :=
  TCP.Admission.DataReady.allowed _ _ _ _ rfl rfl (.inl fresh_geometry)

private theorem ack_admission : TCP.Admission.Allowed (.data dataSession)
    (ConntrackLifecycle.selectedAttachment ⟨entry, true⟩ .original) (segment 1001 5001 []) [] :=
  TCP.Admission.DataReady.allowed _ _ _ _ rfl rfl (.inr ack_geometry)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def tracked : Except ConntrackLifecycle.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.describe)

private def lifecycleTests : IO Unit := do
  for seen in [false, true] do
    for direction in [FlowNAT.Direction.original, .reply] do
      let ready := existingReady seen direction
      let _ := ConntrackLifecycle.step_existing_enabled _ _ _ _ _ ready
      let input : ConntrackLifecycle.Input := ⟨0, entry.flow.input direction, none⟩
      let outcome ← tracked (ConntrackLifecycle.step pipeline (tracker seen) input)
      let expected := match direction with | .original => "server" | .reply => "client"
      ensure (outcome.output == some (entry.flow.output direction) && outcome.nextHop == some expected &&
          !outcome.attachment.fresh && outcome.state.records.length == 1 &&
          (direction != .reply || outcome.state.records.all (·.seenReply)))
        "Existing lookup and current permits must derive the stored translation without fresh confirmation."
      let denied ← tracked (ConntrackLifecycle.step { pipeline with forwardDefault := .deny } (tracker seen) input)
      ensure (denied.output.isNone && denied.disposition == .forwardDrop)
        "Forward denial must prevent an output even when lookup and route are valid."
      let unrouted ← tracked (ConntrackLifecycle.step { pipeline with routes := [] } (tracker seen) input)
      ensure (unrouted.output.isNone && unrouted.disposition == .routeDrop)
        "A missing route cannot satisfy forwarding readiness."
      let late ← tracked (ConntrackLifecycle.step { pipeline with lateDefault := .deny } (tracker seen) input)
      ensure (late.output.isNone && late.disposition == .lateDrop)
        "Late denial must prevent output after destination routing."

def run : IO Unit := do
  lifecycleTests
  ensure (decide (ConntrackLifecycle.ExistingReady pipeline (tracker false) ⟨0, original, none⟩
      ⟨entry.flow, .original⟩ "server") &&
      decide (¬ConntrackLifecycle.ExistingReady { pipeline with forwardDefault := .deny } (tracker false)
        ⟨0, original, none⟩ ⟨entry.flow, .original⟩ "server") &&
      decide (¬ConntrackLifecycle.ExistingReady pipeline (tracker false)
        ⟨0, original, some entry⟩ ⟨entry.flow, .original⟩ "server"))
    "Readiness must check the actual old binding, absent replacement candidate, and installed permits."
  ensure (decide (TCP.Admission.DataReady dataSession .original (segment 1001 5001 [1, 2, 3])) &&
      decide (TCP.Admission.DataReady dataSession .original (segment 1001 5001 [])) &&
      decide (¬TCP.Admission.DataReady dataSession .original (segment 1001 5002 [])))
    "The executable readiness check must use old lane geometry for new data and pure ACKs."
  let _ := fresh_admission
  let _ := ack_admission
  ensure (decide (¬TCP.Admission.DataAllowed dataSession.original dataSession.reply (segment 1001 5002 []) .absent 0) &&
      decide (¬TCP.Admission.DataAllowed dataSession.original dataSession.reply (segment 1002 5001 []) .absent 0) &&
      decide (¬TCP.Admission.DataAllowed dataSession.original dataSession.reply (segment 1001 5001 (List.replicate 9 1)) .absent 0))
    "ACKs cannot pass a coverage hole or sender extent, and fresh data must fit the offered right edge."
  IO.println "Gateway predecessor readiness tests passed."

end NetlibTest.GatewayEnabled
