import Netlib.Protocol.TCP.EndpointGapReceiveEnabled
import Netlib.Protocol.TCP.EndpointFutureReceiveEnabled
import Netlib.Protocol.TCP.EndpointPartialAckEnabled
import Netlib.Protocol.TCP.EndpointZeroAckEnabled
import Netlib.Protocol.TCP.EndpointClockEnabled

/-!
# Retained endpoint window floors

Each processed header must retain the floor.
Gap filling includes the actual held upper header.
-/

namespace Netlib.Protocol.TCP.Endpoint

variable {state before after : State} {input : Input} {recovery : Recovery.State} {floor : Nat}

theorem outputState_offeredWindow (state : State) : offeredWindow (outputState state) = outputWindow state := by
  cases runtime : state.ackReaction with
  | none => simp only [outputState, offeredWindow, outputWindow, runtime, Option.map_none]
  | some reaction =>
    simp only [outputState, offeredWindow, outputWindow, runtime, Option.map_some]
    exact ReceiveAdvertisement.commit_window reaction.advertisement state.core.capacity state.core.window state.effectiveMSS

theorem offeredWindow_le_outputWindow_of_room (state : State) (room : offeredWindow state ≤ state.core.window) :
    offeredWindow state ≤ outputWindow state := by
  cases runtime : state.ackReaction with
  | none => simp only [offeredWindow, outputWindow, runtime, Nat.le_refl]
  | some reaction =>
    simp only [offeredWindow, outputWindow, runtime] at room ⊢
    change reaction.advertisement.window ≤ state.core.window at room
    change reaction.advertisement.window ≤ ReceiveAdvertisement.candidate reaction.advertisement
      state.core.capacity state.core.window state.effectiveMSS
    unfold ReceiveAdvertisement.candidate
    split
    · exact room
    · exact Nat.le_refl _

theorem offeredWindow_le_outputWindow (state : State) (coherent : AckCoherent state) :
    offeredWindow state ≤ outputWindow state :=
  offeredWindow_le_outputWindow_of_room state (offeredWindow_le state coherent)

theorem offeredWindow_le_outputState (state : State) (coherent : AckCoherent state) :
    offeredWindow state ≤ offeredWindow (outputState state) := by
  rw [outputState_offeredWindow]
  exact offeredWindow_le_outputWindow state coherent

theorem writeState_offeredWindow (state : State) (bytes : List UInt8) :
    offeredWindow (writeState state bytes) = offeredWindow state := rfl

theorem clockState_offeredWindow (state : State) (millis : Nat) :
    offeredWindow (clockState state millis) = offeredWindow state := rfl

theorem ClockFrame.offeredWindow (frame : ClockFrame before after) : offeredWindow after = offeredWindow before := by
  simp only [Endpoint.offeredWindow, frame.ackReaction, frame.core]

theorem AdvancingAck.ack_reaction (received : AdvancingAck state input recovery after) : after.ackReaction = state.ackReaction := by
  rw [received.afterEq]
  exact windowState_ackReaction state _ input.packet.segment

theorem AdvancingAck.offeredWindow (received : AdvancingAck state input recovery after) : offeredWindow after = offeredWindow state := by
  have same : after.core.window = state.core.window := by
    rw [received.core]
    simp only [EstablishedReceive.commit, EstablishedReceive.State.window, List.append_nil]
  simp only [Endpoint.offeredWindow, received.ack_reaction, same]

theorem ZeroAck.offeredWindow (received : ZeroAck state input recovery after) : offeredWindow after = offeredWindow state := by
  simp only [Endpoint.offeredWindow, received.ack_reaction, received.core]

theorem emit_window_floor (state : State) (payload : List UInt8) (packet : Input)
    (coherent : AckCoherent state) (old : floor ≤ offeredWindow state) (encoded : emit state payload = .ok packet) :
    floor ≤ packet.packet.segment.window.val := by
  rw [(emit_transport state payload packet encoded).2.2.2.1]
  exact Nat.le_trans old (offeredWindow_le_outputWindow state coherent)

theorem emitAt_window_floor (state : State) (sequence : Seq) (payload : List UInt8) (packet : Input)
    (coherent : AckCoherent state) (old : floor ≤ offeredWindow state) (encoded : emitAt state sequence payload = .ok packet) :
    floor ≤ packet.packet.segment.window.val := by
  rw [(emitAt_transport state sequence payload packet encoded).2.2.2.1]
  exact Nat.le_trans old (offeredWindow_le_outputWindow state coherent)

theorem windowState_sendWindow_floor (before prepared : State) (segment : Segment)
    (retained : floor ≤ prepared.sendWindow) (incoming : floor ≤ segment.window.val) :
    floor ≤ (windowState before prepared segment).sendWindow := by
  unfold windowState
  split
  · exact incoming
  · exact retained

theorem windowState_sendWindow_floor_of_frame (before prepared : State) (segment : Segment)
    (frame : prepared.sendWindow = before.sendWindow) (old : floor ≤ before.sendWindow)
    (incoming : floor ≤ segment.window.val) : floor ≤ (windowState before prepared segment).sendWindow :=
  windowState_sendWindow_floor before prepared segment (by rw [frame]; exact old) incoming

theorem inOrderAfterWith_sendWindow_floor (state : State) (input : Input) (recovery : Recovery.State) (reaction : AckReaction.State)
    (old : floor ≤ state.sendWindow) (incoming : floor ≤ input.packet.segment.window.val) :
    floor ≤ (inOrderAfterWith state input recovery reaction).sendWindow :=
  windowState_sendWindow_floor state _ input.packet.segment old incoming

theorem inOrderReceivedWith_sendWindow_floor (state : State) (input : Input) (recovery : Recovery.State)
    (old : floor ≤ state.sendWindow) (incoming : floor ≤ input.packet.segment.window.val) :
    floor ≤ (inOrderReceivedWith state input recovery).sendWindow :=
  windowState_sendWindow_floor state _ input.packet.segment old incoming

theorem AdvancingAck.window_floor (received : AdvancingAck state input recovery after)
    (old : floor ≤ state.sendWindow) (incoming : floor ≤ input.packet.segment.window.val) : floor ≤ after.sendWindow := by
  rw [received.afterEq]
  exact inOrderReceivedWith_sendWindow_floor state input _ old incoming

theorem futureAfter_sendWindow (state : State) (input : Input) (gap : Nat) (reaction : AckReaction.State) :
    (futureAfter state input gap reaction).sendWindow = state.sendWindow := rfl

theorem zeroRunState_sendWindow_floor (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run)
    (old : floor ≤ state.sendWindow) (incoming : floor ≤ run.metadata.segment.window.val) :
    floor ≤ (zeroRunState state recovery run).sendWindow := by
  simp only [zeroRunState]
  split
  · exact incoming
  · exact old

theorem gapAfter_sendWindow_floor (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) (old : floor ≤ state.sendWindow)
    (lowerWindow : floor ≤ input.packet.segment.window.val) (upperWindow : floor ≤ upper.metadata.segment.window.val) :
    floor ≤ (gapAfter state input upper recovery reaction).sendWindow := by
  change floor ≤ (gapReceived state input upper recovery).sendWindow
  unfold gapReceived
  apply zeroRunState_sendWindow_floor _ _ upper _ upperWindow
  exact zeroRunState_sendWindow_floor state recovery (gapLower state input) old lowerWindow

theorem applyHeader_sendWindow_floor (state : State) (header : ReceiveReassembly.HeaderEffect) (after : State)
    (old : floor ≤ state.sendWindow) (incoming : floor ≤ header.run.metadata.segment.window.val)
    (computed : applyHeader state header = .ok after) : floor ≤ after.sendWindow := by
  unfold applyHeader at computed
  split at computed
  · cases computed
  · cases runtime : state.recovery with
    | none =>
      simp only [runtime] at computed
      cases computed
      exact windowState_sendWindow_floor state _ header.run.metadata.segment old incoming
    | some recovery =>
      cases accepted : Recovery.acknowledgeAt recovery header.acknowledged header.run.metadata.receivedAt with
      | error reason => simp only [runtime, accepted, Except.map] at computed; cases computed
      | ok next =>
        simp only [runtime, accepted, Except.map] at computed
        cases computed
        exact windowState_sendWindow_floor state _ header.run.metadata.segment old incoming

theorem applyHeaders_sendWindow_floor (state : State) (headers : List ReceiveReassembly.HeaderEffect) (after : State)
    (old : floor ≤ state.sendWindow) (incoming : ∀ header ∈ headers, floor ≤ header.run.metadata.segment.window.val)
    (computed : applyHeaders state headers = .ok after) : floor ≤ after.sendWindow := by
  induction headers generalizing state with
  | nil => cases computed; exact old
  | cons head tail ih =>
    cases first : applyHeader state head with
    | error failure => simp only [applyHeaders, first] at computed; cases computed
    | ok next =>
      simp only [applyHeaders, first] at computed
      exact ih next (applyHeader_sendWindow_floor state head next old (incoming head (by simp)) first)
        (fun header member => incoming header (by simp only [List.mem_cons]; exact Or.inr member)) computed

theorem processRuns_sendWindow_floor (state : State) (runs : List ReceiveReassembly.Run) (processed : ReceiveProcessed)
    (old : floor ≤ state.sendWindow) (incoming : ∀ run ∈ runs, floor ≤ run.metadata.segment.window.val)
    (computed : processRuns state runs = .ok processed) : floor ≤ processed.received.sendWindow := by
  induction runs generalizing state processed with
  | nil => cases computed; exact old
  | cons head tail ih =>
    cases first : ReceiveReassembly.applyRun state.core head with
    | error failure => simp only [processRuns, first] at computed; cases computed
    | ok header =>
      cases second : applyHeader state header with
      | error failure => simp only [processRuns, first, second] at computed; cases computed
      | ok next =>
        cases rest : processRuns next tail with
        | error failure => simp only [processRuns, first, second, rest] at computed; cases computed
        | ok result =>
          simp only [processRuns, first, second, rest] at computed
          cases computed
          have headerWindow : floor ≤ header.run.metadata.segment.window.val := by
            rw [(ReceiveReassembly.applyRun_fields _ _ _ first).2.1]
            exact incoming head (by simp)
          exact ih next result (applyHeader_sendWindow_floor state header next old headerWindow second)
            (fun run member => incoming run (by simp only [List.mem_cons]; exact Or.inr member)) rest

end Netlib.Protocol.TCP.Endpoint
