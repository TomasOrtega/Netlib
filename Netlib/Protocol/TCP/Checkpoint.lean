import Netlib.Protocol.TCP.Admission
import Netlib.Protocol.TCP.WireForwarding

/-!
# Reachable TCP gateway checkpoints

The source starts empty and advances through actual checked packet computations.
A checkpoint retains the exact source cut and copies its tracker and admission history.
Current policy, assignment pause, ownership, and fencing remain separate obligations.
This module does not model Linux TCP state migration.
-/

namespace Netlib.Protocol.TCP.Checkpoint

namespace C
export Netlib.Protocol.ConntrackLifecycle (State Record Pipeline Prepared prepare)
end C
namespace A
export Netlib.Protocol.TCP.Admission (State Lane Seen Phase)
end A
namespace W
export Netlib.Protocol.TCP.WireForwarding (Input Outcome)
end W

structure Gateway where
  tracker : C.State
  admission : A.State

def Gateway.initial : Gateway := ⟨.initial, .initial⟩

inductive PhaseImage where
  | empty
  | syn (entry : NetfilterNAT.Entry) (clientISS : Seq) (clientWindow : InternetChecksum.Word)
  | synAck (entry : NetfilterNAT.Entry) (clientISS : Seq) (clientWindow : InternetChecksum.Word)
      (serverISS : Seq) (serverWindow : InternetChecksum.Word)
  | data (entry : NetfilterNAT.Entry) (original reply : A.Lane)
  deriving Repr, BEq, DecidableEq

def phaseImage : A.Phase → PhaseImage
  | .empty => .empty
  | .syn entry iss window => .syn entry iss window
  | .synAck entry clientISS clientWindow serverISS serverWindow =>
    .synAck entry clientISS clientWindow serverISS serverWindow
  | .data session => .data session.entry session.original session.reply

private theorem session_image_injective (left right : Admission.Session)
    (entry : left.entry = right.entry) (original : left.original = right.original) (reply : left.reply = right.reply) :
    left = right := by
  cases left
  cases right
  cases entry
  cases original
  cases reply
  rfl

theorem phaseImage_injective (left right : A.Phase) (same : phaseImage left = phaseImage right) : left = right := by
  cases left <;> cases right <;> simp only [phaseImage] at same
  all_goals first
    | rfl
    | (solve | cases same)
    | (obtain ⟨rfl, rfl, rfl⟩ := PhaseImage.syn.inj same; rfl)
    | (obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := PhaseImage.synAck.inj same; rfl)
    | (obtain ⟨entry, original, reply⟩ := PhaseImage.data.inj same
       exact congrArg Admission.Phase.data (session_image_injective _ _ entry original reply))

structure Image where
  tracker : C.State
  phase : PhaseImage
  observations : List A.Seen
  deriving Repr, BEq, DecidableEq

def Gateway.image (gateway : Gateway) : Image :=
  ⟨gateway.tracker, phaseImage gateway.admission.phase, gateway.admission.observations⟩

theorem Gateway.image_injective (left right : Gateway) (same : left.image = right.image) : left = right := by
  cases left with
  | mk leftTracker leftAdmission =>
    cases right with
    | mk rightTracker rightAdmission =>
      cases leftAdmission with
      | mk leftPhase leftSeen =>
        cases rightAdmission with
        | mk rightPhase rightSeen =>
          have fields := Image.mk.inj same
          obtain ⟨rfl, phase, rfl⟩ := fields
          cases phaseImage_injective leftPhase rightPhase phase
          rfl

def Gateway.same (left right : Gateway) : Bool := decide (left.image = right.image)

theorem Gateway.same_correct (left right : Gateway) : left.same right = true ↔ left = right := by
  constructor
  · intro same
    exact Gateway.image_injective left right (of_decide_eq_true same)
  · intro same
    cases same
    simp [Gateway.same]

structure Request where
  source : EstablishedReceive.Input
  zone : Nat
  candidate : Option NetfilterNAT.Entry := none

def Request.wire (request : Request) : W.Input :=
  ⟨request.zone, request.source.packet, request.candidate⟩

structure Transition (before : Gateway) where
  request : Request
  pipeline : C.Pipeline
  prepared : C.Prepared request.wire.lifecycle
  attached : C.prepare before.tracker request.wire.lifecycle = .ok prepared
  admitted : Admission.Result before.admission request.source request.wire.lifecycle prepared
  admissionComputed : Admission.step before.admission request.source request.wire.lifecycle prepared rfl = .ok admitted
  outcome : W.Outcome request.source.packet
  computed : WireForwarding.process pipeline request.wire request.source.valid prepared = .ok outcome
  nextAdmission : A.State
  committed : Admission.commit admitted outcome.state = .ok nextAdmission

def Transition.after (transition : Transition before) : Gateway :=
  ⟨transition.outcome.state, transition.nextAdmission⟩

inductive Error where
  | tracker (reason : ConntrackLifecycle.Error)
  | admission (reason : Admission.Error)
  | missingSelection
  | unconfirmedSelection
  | notTCP
  | notEstablished
  | staleSource
  | staleCut
  | occupiedTarget
  deriving Repr, BEq, DecidableEq

def Error.message : Error → String
  | .tracker reason => reason.describe
  | .admission reason => reason.message
  | .missingSelection => "The source has no selected TCP admission history."
  | .unconfirmedSelection => "The selected TCP entry is not confirmed at the source cut."
  | .notTCP => "The selected checkpoint entry must use TCP."
  | .notEstablished => "The selected checkpoint requires the TCP data phase."
  | .staleSource => "The source tracker or TCP history changed after checkpoint capture."
  | .staleCut => "The source transition cut changed after checkpoint capture."
  | .occupiedTarget => "The selected target tracker and TCP history must be empty."

def run (before : Gateway) (pipeline : C.Pipeline) (request : Request) : Except Error (Transition before) := do
  match attached : C.prepare before.tracker request.wire.lifecycle with
  | .error reason => throw (.tracker reason)
  | .ok prepared =>
    match admitted : Admission.step before.admission request.source request.wire.lifecycle prepared rfl with
    | .error reason => throw (.admission reason)
    | .ok admission =>
      match computed : WireForwarding.process pipeline request.wire request.source.valid prepared with
      | .error reason => throw (.tracker reason)
      | .ok outcome =>
        match committed : Admission.commit admission outcome.state with
        | .error reason => throw (.admission reason)
        | .ok nextAdmission =>
          return ⟨request, pipeline, prepared, attached, admission, admitted, outcome, computed, nextAdmission, committed⟩

theorem Transition.replay (transition : Transition before) :
    run before transition.pipeline transition.request = .ok transition := by
  unfold run
  split
  · rename_i reason failed
    rw [transition.attached] at failed
    cases failed
  · rename_i prepared attached
    have same := Except.ok.inj (attached.symm.trans transition.attached)
    subst prepared
    split
    · rename_i reason failed
      rw [transition.admissionComputed] at failed
      cases failed
    · rename_i admitted computed
      have same := Except.ok.inj (computed.symm.trans transition.admissionComputed)
      subst admitted
      split
      · rename_i reason failed
        rw [transition.computed] at failed
        cases failed
      · rename_i outcome computed
        have same := Except.ok.inj (computed.symm.trans transition.computed)
        subst outcome
        split
        · rename_i reason failed
          rw [transition.committed] at failed
          cases failed
        · rename_i nextAdmission committed
          have same := Except.ok.inj (committed.symm.trans transition.committed)
          subst nextAdmission
          cases transition
          rfl

inductive History : Gateway → Type where
  | initial : History Gateway.initial
  | advance (history : History before) (transition : Transition before) : History transition.after

def History.length : History gateway → Nat
  | .initial => 0
  | .advance history _ => history.length + 1

theorem History.tracker_valid (history : History gateway) : gateway.tracker.Valid := by
  cases history with
  | initial => exact ConntrackLifecycle.State.initial_valid
  | advance history transition => exact transition.outcome.valid

def dataPhase : A.Phase → Bool
  | .data _ => true
  | _ => false

theorem dataPhase_correct (phase : A.Phase) : dataPhase phase = true ↔ ∃ session, phase = .data session := by
  cases phase <;> simp [dataPhase]

structure Snapshot where
  source : Gateway
  history : History source
  record : C.Record
  member : record ∈ source.tracker.records
  selected : source.admission.phase.entry = some record.entry
  tcp : record.entry.flow.original.protocol = Packet.Protocol.tcp
  established : ∃ session, source.admission.phase = .data session

def Snapshot.cut (snapshot : Snapshot) : Nat := snapshot.history.length

def capture (history : History gateway) : Except Error Snapshot := do
  if established : dataPhase gateway.admission.phase = true then
    match selected : gateway.admission.phase.entry with
    | none => throw .missingSelection
    | some entry =>
      match found : gateway.tracker.records.find? (fun record => decide (record.entry = entry)) with
      | none => throw .unconfirmedSelection
      | some record =>
        have same : record.entry = entry := of_decide_eq_true
          (List.find?_some (p := fun record : C.Record => decide (record.entry = entry)) found)
        if tcp : record.entry.flow.original.protocol = Packet.Protocol.tcp then
          return ⟨gateway, history, record, List.mem_of_find?_eq_some found, by rw [same]; exact selected,
            tcp, (dataPhase_correct _).mp established⟩
        else throw .notTCP
  else throw .notEstablished

theorem capture_source (history : History gateway) (snapshot : Snapshot)
    (captured : capture history = .ok snapshot) :
    snapshot.source = gateway ∧ snapshot.cut = history.length ∧ HEq snapshot.history history := by
  unfold capture at captured
  repeat' first
    | (cases captured; exact ⟨rfl, rfl, HEq.rfl⟩)
    | (split at captured)
    | (simp at captured)

structure Installation (snapshot : Snapshot) (history : History current) (target : Gateway) where
  sourceSame : current = snapshot.source
  cutSame : history.length = snapshot.cut
  targetEmpty : target = Gateway.initial
  state : Gateway
  copied : state = snapshot.source

def install (snapshot : Snapshot) (history : History current) (target : Gateway) :
    Except Error (Installation snapshot history target) := do
  if sourceSame : current.same snapshot.source = true then
    if cutSame : history.length = snapshot.cut then
      if targetEmpty : target.same Gateway.initial = true then
        return ⟨(Gateway.same_correct _ _).mp sourceSame, cutSame,
          (Gateway.same_correct _ _).mp targetEmpty, snapshot.source, rfl⟩
      else throw .occupiedTarget
    else throw .staleCut
  else throw .staleSource

theorem install_stale (snapshot : Snapshot) (history : History current) (target : Gateway)
    (changed : current ≠ snapshot.source) : install snapshot history target = .error .staleSource := by
  have different : current.same snapshot.source ≠ true := by
    intro same
    exact changed ((Gateway.same_correct _ _).mp same)
  simp only [install, different, Bool.false_eq_true, dite_false]
  rfl

theorem install_cut_changed (snapshot : Snapshot) (history : History snapshot.source) (target : Gateway)
    (changed : history.length ≠ snapshot.cut) : install snapshot history target = .error .staleCut := by
  have same : snapshot.source.same snapshot.source = true := (Gateway.same_correct _ _).mpr rfl
  simp only [install, same, dite_true, changed, dite_false]
  rfl

theorem install_occupied (snapshot : Snapshot) (history : History snapshot.source) (target : Gateway)
    (cut : history.length = snapshot.cut) (occupied : target ≠ Gateway.initial) :
    install snapshot history target = .error .occupiedTarget := by
  have same : snapshot.source.same snapshot.source = true := (Gateway.same_correct _ _).mpr rfl
  have different : target.same Gateway.initial ≠ true := by
    intro empty
    exact occupied ((Gateway.same_correct _ _).mp empty)
  simp only [install, same, cut, different, Bool.false_eq_true, dite_false, dite_true]
  rfl

theorem Snapshot.confirmed (snapshot : Snapshot) : Admission.confirmed snapshot.record.entry snapshot.source.tracker = true :=
  (Admission.confirmed_correct _ _).mpr ⟨snapshot.record, snapshot.member, rfl⟩

theorem Snapshot.compatible (snapshot : Snapshot) : snapshot.record.entry.Compatible :=
  snapshot.history.tracker_valid.2 snapshot.record snapshot.member

theorem Snapshot.lookup (snapshot : Snapshot) (direction : FlowNAT.Direction) :
    snapshot.source.tracker.model.lookup (snapshot.record.entry.flow.zone direction)
      (snapshot.record.entry.flow.input direction) = some ⟨snapshot.record.entry.flow, direction⟩ := by
  have member : snapshot.record.entry.flow ∈ snapshot.source.tracker.model.entries :=
    List.mem_map.mpr ⟨snapshot.record, snapshot.member, rfl⟩
  exact FlowNAT.Snapshot.lookup_complete _ snapshot.history.tracker_valid.1 ⟨snapshot.record.entry.flow, direction⟩ member

def Installation.history (installation : Installation snapshot sourceHistory target) : History installation.state :=
  installation.copied.symm ▸ snapshot.history

theorem Installation.tracker (installation : Installation snapshot sourceHistory target) :
    installation.state.tracker = snapshot.source.tracker := congrArg Gateway.tracker installation.copied

theorem Installation.admission (installation : Installation snapshot sourceHistory target) :
    installation.state.admission = snapshot.source.admission := congrArg Gateway.admission installation.copied

theorem Installation.record (installation : Installation snapshot sourceHistory target) :
    snapshot.record ∈ installation.state.tracker.records := by
  rw [installation.copied]
  exact snapshot.member

theorem Installation.selected (installation : Installation snapshot sourceHistory target) :
    installation.state.admission.phase.entry = some snapshot.record.entry := by
  rw [installation.copied]
  exact snapshot.selected

theorem Installation.lookup (installation : Installation snapshot sourceHistory target) (direction : FlowNAT.Direction) :
    installation.state.tracker.model.lookup (snapshot.record.entry.flow.zone direction)
      (snapshot.record.entry.flow.input direction) = some ⟨snapshot.record.entry.flow, direction⟩ := by
  rw [installation.copied]
  exact snapshot.lookup direction

theorem Installation.prepare (installation : Installation snapshot sourceHistory target) (request : Request) :
    C.prepare installation.state.tracker request.wire.lifecycle = C.prepare snapshot.source.tracker request.wire.lifecycle := by
  rw [installation.tracker]

theorem Installation.admission_continuation (installation : Installation snapshot sourceHistory target)
    (request : Request) (prepared : C.Prepared request.wire.lifecycle)
    (admitted : Admission.Result snapshot.source.admission request.source request.wire.lifecycle prepared)
    (computed : Admission.step snapshot.source.admission request.source request.wire.lifecycle prepared rfl = .ok admitted) :
    ∃ continued : Admission.Result installation.state.admission request.source request.wire.lifecycle prepared,
      Admission.step installation.state.admission request.source request.wire.lifecycle prepared rfl = .ok continued ∧
      continued.state = admitted.state := by
  rw [installation.admission]
  exact ⟨admitted, computed, rfl⟩

theorem Installation.continuation (installation : Installation snapshot sourceHistory target)
    (transition : Transition snapshot.source) :
    ∃ continued : Transition installation.state,
      run installation.state transition.pipeline transition.request = .ok continued ∧
      continued.after = transition.after ∧ HEq continued.outcome transition.outcome := by
  rw [installation.copied]
  exact ⟨transition, transition.replay, rfl, HEq.rfl⟩

end Netlib.Protocol.TCP.Checkpoint
