import Netlib.Protocol.IPv4ReassemblyLayout
import Netlib.Protocol.ICMPForwarding
import Netlib.Protocol.IPv4QuotePrefix

/-!
# Reassembly timeout quotations

Timeout selection uses expired queues and their stored offset-zero fragment.
The quotation retains the original fragment header and only normalized data.
Input routing, return routing, and local output policy remain explicit inputs.
-/

namespace Netlib.Protocol.IPv4ReassemblyTimeout

open Packet InternetChecksum IPv4Reassembly

def expiredQueues (state : State) (now : Nat) : List Queue :=
  state.queues.filter (fun queue => decide (queue.expires ≤ now))

@[simp] theorem expiredQueues_member (state : State) (now : Nat) (queue : Queue) :
    queue ∈ expiredQueues state now ↔ queue ∈ state.queues ∧ queue.expires ≤ now := by
  simp [expiredQueues]

theorem expiredQueues_removed (state : State) (now : Nat) (queue : Queue)
    (expired : queue ∈ expiredQueues state now) : queue ∉ (state.age now).queues :=
  state.expired_absent now queue ((expiredQueues_member _ _ _).mp expired).2

def firstPiece (queue : Queue) : Option Piece := queue.pieces.find? (fun piece => decide (piece.start = 0))

theorem firstPiece_member (queue : Queue) (piece : Piece) (selected : firstPiece queue = some piece) :
    piece ∈ queue.pieces ∧ piece.start = 0 :=
  ⟨List.mem_of_find?_eq_some selected,
    of_decide_eq_true (List.find?_some (p := fun piece : Piece => decide (piece.start = 0)) selected)⟩

structure Source (queue : Queue) where
  firstPresent : queue.first.isSome = true
  piece : Piece
  selected : firstPiece queue = some piece
  minimum : 8 ≤ piece.data.length
  udp : piece.fragment.packet.protocol = Packet.Protocol.udp

def source (queue : Queue) : Option (Source queue) :=
  if firstPresent : queue.first.isSome = true then
    match selected : firstPiece queue with
    | none => none
    | some piece =>
      if minimum : 8 ≤ piece.data.length then
        if udp : piece.fragment.packet.protocol = Packet.Protocol.udp then some ⟨firstPresent, piece, selected, minimum, udp⟩
        else none
      else none
  else none

structure Emission (queue : Queue) where
  source : Source queue
  path : ICMPForwarding.ReturnPath
  identification : Word

def Emission.length (emission : Emission queue) : Nat :=
  min (emission.source.piece.data.length + 20) (ICMPForwarding.quoteLimit emission.path)

theorem Emission.length_bounds (emission : Emission queue) :
    28 ≤ emission.length ∧ emission.length ≤ emission.source.piece.data.length + 20 ∧
      emission.length + 28 ≤ emission.path.mtu.val ∧ emission.length + 28 ≤ 576 := by
  have minimum := emission.source.minimum
  have mtu := emission.path.mtu.property.1
  unfold Emission.length ICMPForwarding.quoteLimit
  omega

def Emission.quote (emission : Emission queue) : IPv4QuotePrefix.Decoded :=
  let fragment := emission.source.piece.fragment
  ⟨{ fragment.packet.toPacket with payload := emission.source.piece.data.take (emission.length - 20) },
    IPv4Fragment.flagsWord fragment.packet, fragment.checksum, IPv4Fragment.lengthWord fragment.packet⟩

theorem Emission.quote_header (emission : Emission queue) :
    IPv4QuotePrefix.headerBytes emission.quote =
      IPv4Fragment.headerBytes emission.source.piece.fragment.packet emission.source.piece.fragment.checksum := by
  simp only [IPv4QuotePrefix.headerBytes, IPv4QuotePrefix.headerPrefix, Emission.quote,
    IPv4Fragment.headerBytes, IPv4Fragment.headerPrefix, IPv4Fragment.headerSuffix]
  rfl

theorem Emission.quote_shape (emission : Emission queue) : emission.quote.Shape := by
  constructor
  · change 8 ≤ (emission.source.piece.data.take (emission.length - 20)).length
    rw [List.length_take]
    have bounds := emission.length_bounds
    omega
  · change emission.source.piece.fragment.packet.dontFragment =
      IPv4QuotePrefix.flagsDF (IPv4Fragment.flagsWord emission.source.piece.fragment.packet)
    have offset := emission.source.piece.fragment.packet.offset.isLt
    cases df : emission.source.piece.fragment.packet.dontFragment <;>
      cases mf : emission.source.piece.fragment.packet.moreFragments <;>
      simp [IPv4QuotePrefix.flagsDF, IPv4Fragment.flagsWord, df, mf] <;> omega

theorem Emission.quote_length (emission : Emission queue) :
    (IPv4QuotePrefix.bytes emission.quote).length = emission.length := by
  have bounds := emission.length_bounds
  simp only [IPv4QuotePrefix.bytes, List.length_append, IPv4QuotePrefix.headerBytes_length,
    Emission.quote, List.length_take]
  omega

theorem Emission.quote_prefix (emission : Emission queue) :
    IPv4QuotePrefix.bytes emission.quote =
      (IPv4Fragment.headerBytes emission.source.piece.fragment.packet emission.source.piece.fragment.checksum ++
        emission.source.piece.data).take emission.length := by
  have enough := emission.length_bounds.1
  have headerTake : (IPv4Fragment.headerBytes emission.source.piece.fragment.packet
      emission.source.piece.fragment.checksum).take emission.length =
        IPv4Fragment.headerBytes emission.source.piece.fragment.packet emission.source.piece.fragment.checksum := by
    apply List.take_of_length_le
    rw [IPv4Fragment.headerBytes_length]
    omega
  rw [List.take_append, headerTake, IPv4Fragment.headerBytes_length]
  rfl

theorem Emission.quote_metadata (emission : Emission queue) :
    emission.quote.flags = IPv4Fragment.flagsWord emission.source.piece.fragment.packet ∧
      emission.quote.declaredLength = IPv4Fragment.lengthWord emission.source.piece.fragment.packet ∧
      emission.quote.checksum = emission.source.piece.fragment.checksum ∧
      emission.quote.packet.ttl = emission.source.piece.fragment.packet.ttl := ⟨rfl, rfl, rfl, rfl⟩

def Emission.message (emission : Emission queue) : ICMP.Message :=
  ⟨.reassemblyTimeout, IPv4QuotePrefix.bytes emission.quote⟩

def Emission.packet (emission : Emission queue) : IPv4.Packet :=
  ⟨ICMPForwarding.errorTos emission.source.piece.fragment.packet.tos, emission.identification,
    false, emission.path.ttl, Packet.Protocol.icmp, emission.path.source,
    emission.source.piece.fragment.packet.source, ICMP.encode emission.message⟩

def Emission.bytes (emission : Emission queue) : List UInt8 :=
  IPv4.headerBytes emission.packet (IPv4.computedChecksum emission.packet) ++ emission.packet.payload

theorem Emission.fits (emission : Emission queue) :
    emission.packet.wireLength ≤ emission.path.mtu.val ∧ emission.packet.wireLength ≤ 576 := by
  have bounds := emission.length_bounds
  simpa only [Emission.packet, IPv4.Packet.wireLength, ICMP.encode, ICMP.bytes_length,
    Emission.message, emission.quote_length, Nat.add_assoc] using bounds.2.2

theorem Emission.encoded (emission : Emission queue) : IPv4.encode emission.packet = .ok emission.bytes := by
  have bounds := emission.fits
  have bounded : emission.packet.Encodable := by unfold IPv4.Packet.Encodable; omega
  simp only [IPv4.encode, bounded, ite_true, Emission.bytes]

theorem Emission.decoded (emission : Emission queue) :
    IPv4.decode emission.bytes = .ok ⟨emission.packet, IPv4.computedChecksum emission.packet, []⟩ :=
  IPv4.decode_encode _ _ emission.encoded

theorem Emission.icmp_decoded (emission : Emission queue) :
    ICMP.decode emission.packet.payload = .ok ⟨emission.message, ICMP.computedChecksum emission.message⟩ :=
  ICMP.decode_encode emission.message

theorem Emission.quoted_decoded (emission : Emission queue) :
    IPv4QuotePrefix.decode emission.message.quote = .ok emission.quote :=
  IPv4QuotePrefix.decode_bytes _ emission.quote_shape

structure Context where
  inputRouteLocal : IPv4.Packet → Option Bool
  requiresLocal : Domain → Bool
  returnPath : IPv4.Packet → Option ICMPForwarding.ReturnPath
  zone : Queue → Nat
  broadcasts : List Address := []
  linkGroup : Queue → Bool := fun _ => false
  output : StatefulACL.Policy := []
  outputDefault : Action := .deny
  late : StatefulACL.Policy := []
  lateDefault : Action := .permit

def eligible (context : Context) (queue : Queue) (source : Source queue) : Bool :=
  let packet := source.piece.fragment.packet
  !context.linkGroup queue && ICMPForwarding.unicastSource context.broadcasts packet.source &&
    decide (packet.destination.val < 3758096384) && !context.broadcasts.contains packet.destination

def Emission.header (emission : Emission queue) : Header :=
  ⟨emission.path.source, emission.source.piece.fragment.packet.source, Packet.Protocol.icmp, 0, 0⟩

inductive Disposition where
  | notExpired | noFirst | unsupportedFirst | noInputRoute | suppressed | noReturnRoute
  | unsupportedZone | unsupportedAssociation | outputDrop | lateDrop | sent
  deriving Repr, BEq, DecidableEq

structure Control (queue : Queue) where
  disposition : Disposition
  classification : Option StatefulACL.CTState := none
  output : Option (Emission queue) := none

/-- The selected local-output profile requires a reverse-quote lookup miss. -/
def generate (context : Context) (tracker : ConntrackLifecycle.State) (queue : Queue) (now : Nat)
    (identification : Word) : Control queue :=
  if now < queue.expires then ⟨.notExpired, none, none⟩
  else if queue.first.isNone || (firstPiece queue).isNone then ⟨.noFirst, none, none⟩
  else match source queue with
    | none => ⟨.unsupportedFirst, none, none⟩
    | some source =>
      match context.inputRouteLocal source.piece.fragment.packet.toPacket with
      | none => ⟨.noInputRoute, none, none⟩
      | some isLocal =>
        if context.requiresLocal queue.key.domain && !isLocal || !eligible context queue source then
          ⟨.suppressed, none, none⟩
        else match context.returnPath source.piece.fragment.packet.toPacket with
          | none => ⟨.noReturnRoute, none, none⟩
          | some path =>
            let emission : Emission queue := ⟨source, path, identification⟩
            if 65536 ≤ context.zone queue then ⟨.unsupportedZone, none, none⟩
            else if (tracker.model.lookup (context.zone queue) (IPv4QuotePrefix.header emission.quote).reverse).isSome then
              ⟨.unsupportedAssociation, none, none⟩
            else if StatefulACL.Policy.evaluate context.outputDefault context.output .invalid emission.header = .deny then
              ⟨.outputDrop, some .invalid, none⟩
            else if StatefulACL.Policy.evaluate context.lateDefault context.late .invalid emission.header = .deny then
              ⟨.lateDrop, some .invalid, none⟩
            else ⟨.sent, some .invalid, some emission⟩

structure Finding where
  queue : Queue
  control : Control queue

structure Result where
  state : State
  conntrack : ConntrackLifecycle.State
  findings : List Finding

def expire (context : Context) (tracker : ConntrackLifecycle.State) (before : State) (now : Nat)
    (identification : Queue → Word) : Except IPv4Reassembly.Error Result :=
  if now < before.lastTime then .error .backwardsClock
  else .ok ⟨{ before.age now with lastTime := now }, tracker,
    (expiredQueues before now).map (fun queue => ⟨queue, generate context tracker queue now (identification queue)⟩)⟩

theorem expire_fields (context : Context) (tracker : ConntrackLifecycle.State) (before : State) (now : Nat)
    (identification : Queue → Word) (result : Result)
    (computed : expire context tracker before now identification = .ok result) :
    result.state.queues = (before.age now).queues ∧ result.state.lastTime = now ∧ result.conntrack = tracker ∧
      result.findings = (expiredQueues before now).map (fun queue =>
        ⟨queue, generate context tracker queue now (identification queue)⟩) := by
  unfold expire at computed
  split at computed
  · cases computed
  · cases computed
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem expire_selected (context : Context) (tracker : ConntrackLifecycle.State) (before : State) (now : Nat)
    (identification : Queue → Word) (result : Result)
    (computed : expire context tracker before now identification = .ok result)
    (finding : Finding) (member : finding ∈ result.findings) :
    finding.queue ∈ before.queues ∧ finding.queue.expires ≤ now ∧
      finding.control = generate context tracker finding.queue now (identification finding.queue) := by
  rw [(expire_fields _ _ _ _ _ _ computed).2.2.2] at member
  obtain ⟨queue, expired, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨((expiredQueues_member _ _ _).mp expired).1, ((expiredQueues_member _ _ _).mp expired).2, rfl⟩

structure SentFacts (context : Context) (tracker : ConntrackLifecycle.State) (queue : Queue)
    (now : Nat) (emission : Emission queue) : Prop where
  expired : queue.expires ≤ now
  selected : source queue = some emission.source
  inputRoute : ∃ isLocal, context.inputRouteLocal emission.source.piece.fragment.packet.toPacket = some isLocal ∧
    (context.requiresLocal queue.key.domain = true → isLocal = true)
  eligible : eligible context queue emission.source = true
  returnRoute : context.returnPath emission.source.piece.fragment.packet.toPacket = some emission.path
  zone : context.zone queue < 65536
  missing : tracker.model.lookup (context.zone queue) (IPv4QuotePrefix.header emission.quote).reverse = none
  outputPermit : StatefulACL.Policy.evaluate context.outputDefault context.output .invalid emission.header = .permit
  latePermit : StatefulACL.Policy.evaluate context.lateDefault context.late .invalid emission.header = .permit

theorem generate_sent (context : Context) (tracker : ConntrackLifecycle.State) (queue : Queue) (now : Nat)
    (identification : Word) (emission : Emission queue)
    (emitted : (generate context tracker queue now identification).output = some emission) :
    SentFacts context tracker queue now emission := by
  unfold generate at emitted
  split at emitted
  · cases emitted
  · rename_i expired
    split at emitted
    · cases emitted
    · split at emitted
      · cases emitted
      · rename_i selected sourceFound
        split at emitted
        · cases emitted
        · rename_i isLocal inputRouted
          split at emitted
          · cases emitted
          · rename_i permitted
            split at emitted
            · cases emitted
            · rename_i path returned
              dsimp only at emitted
              split at emitted
              · cases emitted
              · rename_i zoneBound
                split at emitted
                · cases emitted
                · rename_i absent
                  split at emitted
                  · cases emitted
                  · rename_i outputAllowed
                    split at emitted
                    · cases emitted
                    · rename_i lateAllowed
                      cases Option.some.inj emitted
                      constructor
                      · omega
                      · exact sourceFound
                      · refine ⟨isLocal, inputRouted, ?_⟩
                        intro requires
                        cases localValue : isLocal
                        · simp [requires, localValue] at permitted
                        · rfl
                      · cases good : eligible context queue selected
                        · simp [good] at permitted
                        · rfl
                      · exact returned
                      · omega
                      · cases lookup : tracker.model.lookup (context.zone queue)
                            (IPv4QuotePrefix.header (⟨selected, path, identification⟩ : Emission queue).quote).reverse with
                        | none => rfl
                        | some hit => simp [lookup] at absent
                      · cases action : StatefulACL.Policy.evaluate context.outputDefault context.output .invalid
                            (⟨selected, path, identification⟩ : Emission queue).header with
                        | permit => rfl
                        | deny => exact False.elim (outputAllowed action)
                      · cases action : StatefulACL.Policy.evaluate context.lateDefault context.late .invalid
                            (⟨selected, path, identification⟩ : Emission queue).header with
                        | permit => rfl
                        | deny => exact False.elim (lateAllowed action)

theorem expire_output_facts (context : Context) (tracker : ConntrackLifecycle.State) (before : State)
    (now : Nat) (identification : Queue → Word) (result : Result)
    (computed : expire context tracker before now identification = .ok result)
    (finding : Finding) (member : finding ∈ result.findings) (emission : Emission finding.queue)
    (emitted : finding.control.output = some emission) :
    finding.queue ∈ before.queues ∧ finding.queue ∉ result.state.queues ∧
      SentFacts context tracker finding.queue now emission ∧
      emission.source.piece ∈ finding.queue.pieces ∧ emission.source.piece.start = 0 ∧
      result.conntrack = tracker := by
  obtain ⟨belongs, expired, generated⟩ := expire_selected _ _ _ _ _ _ computed finding member
  have stateFields := expire_fields _ _ _ _ _ _ computed
  have removed : finding.queue ∉ result.state.queues := by
    rw [stateFields.1]
    exact before.expired_absent now finding.queue expired
  rw [generated] at emitted
  have selected := firstPiece_member _ _ emission.source.selected
  exact ⟨belongs, removed, generate_sent _ _ _ _ _ _ emitted, selected.1, selected.2, stateFields.2.2.1⟩

theorem expire_valid (context : Context) (tracker : ConntrackLifecycle.State) (before : State) (now : Nat)
    (identification : Queue → Word) (result : Result)
    (computed : expire context tracker before now identification = .ok result) (valid : before.Valid) : result.state.Valid := by
  intro queue member
  rw [(expire_fields _ _ _ _ _ _ computed).1] at member
  exact (before.age_valid now valid) queue member

theorem expire_layout (context : Context) (tracker : ConntrackLifecycle.State) (before : State) (now : Nat)
    (identification : Queue → Word) (result : Result)
    (computed : expire context tracker before now identification = .ok result) (valid : before.LayoutValid) :
    result.state.LayoutValid := by
  have same := (expire_fields _ _ _ _ _ _ computed).1
  constructor
  · rw [same]
    exact (before.age_layout now valid).unique
  · intro queue member
    rw [same] at member
    exact (before.age_layout now valid).queues queue member

theorem expire_no_repeat (context : Context) (tracker : ConntrackLifecycle.State) (before : State) (now : Nat)
    (identification : Queue → Word) (result : Result)
    (computed : expire context tracker before now identification = .ok result) : expiredQueues result.state now = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro queue member
  obtain ⟨retained, expired⟩ := (expiredQueues_member _ _ _).mp member
  rw [(expire_fields _ _ _ _ _ _ computed).1] at retained
  have live := ((State.age_member _ _ _).mp retained).2
  omega

end Netlib.Protocol.IPv4ReassemblyTimeout
