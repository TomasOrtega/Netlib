import Netlib.Packet.Rewrite
import Netlib.Network.Architecture

namespace Netlib.Packet

/-- Packet programs relate incoming and outgoing headers. -/
structure Program where
  run : Header → Header → Prop

namespace Program

def identity : Program := ⟨fun input output => output = input⟩

def rewrite (change : Rewrite) : Program := ⟨fun input output => output = change.apply input⟩

def guard (test : Match) : Program :=
  ⟨fun input output => test.accepts input = true ∧ output = input⟩

def seq (first second : Program) : Program :=
  ⟨fun input output => ∃ middle, first.run input middle ∧ second.run middle output⟩

theorem seq_assoc (first second third : Program) :
    (first.seq second).seq third = first.seq (second.seq third) := by
  change Program.mk _ = Program.mk _
  apply congrArg Program.mk
  funext input output
  apply propext
  constructor
  · rintro ⟨secondOutput, ⟨firstOutput, firstRun, secondRun⟩, thirdRun⟩
    exact ⟨firstOutput, firstRun, secondOutput, secondRun, thirdRun⟩
  · rintro ⟨firstOutput, firstRun, secondOutput, secondRun, thirdRun⟩
    exact ⟨secondOutput, ⟨firstOutput, firstRun, secondRun⟩, thirdRun⟩

@[simp] theorem identity_seq (program : Program) : identity.seq program = program := by
  cases program
  simp [identity, seq]

@[simp] theorem seq_identity (program : Program) : program.seq identity = program := by
  cases program
  simp [identity, seq]

theorem rewrite_seq (first second : Rewrite) :
    (rewrite first).seq (rewrite second) = rewrite (first.comp second) := by
  change Program.mk _ = Program.mk _
  apply congrArg Program.mk
  funext input output
  apply propext
  simp [rewrite, Rewrite.comp_apply]

theorem guard_rewrite (test : Match) (change : Rewrite) (input output : Header) :
    ((guard test).seq (rewrite change)).run input output ↔
      test.accepts input = true ∧ output = change.apply input := by
  constructor
  · rintro ⟨middle, ⟨accepted, rfl⟩, transformed⟩
    exact ⟨accepted, transformed⟩
  · rintro ⟨accepted, transformed⟩
    exact ⟨input, ⟨accepted, rfl⟩, transformed⟩

end Program

/-- A forwarding step retains both its location and current packet state. -/
structure Transfer (Node : Type u) where
  step : Node → Header → Node → Header → Prop

namespace Transfer

def network (transfer : Transfer Node) : Network (Node × Header) :=
  ⟨fun source target => transfer.step source.1 source.2 target.1 target.2⟩

def ofPrograms (physical : Network Node) (programs : Node → Node → Program) : Transfer Node :=
  ⟨fun source before target after => physical.link source target ∧ (programs source target).run before after⟩

/-- Header changes cannot create physical adjacency. -/
def physicalProjection (physical : Network Node) (programs : Node → Node → Program) :
    StutteringRefinement (ofPrograms physical programs).network physical where
  project := Prod.fst
  simulate _ _ edge := .inr edge.1

theorem reachable_physical (physical : Network Node) (programs : Node → Node → Program)
    {source target : Node × Header}
    (path : (ofPrograms physical programs).network.Reachable source target) :
    physical.Reachable source.1 target.1 :=
  (physicalProjection physical programs).toRefinement.reachable path

theorem isolated_of_physical (physical : Network Node) (programs : Node → Node → Program)
    {sources targets : Node → Prop} (isolated : physical.Isolated sources targets) :
    (ofPrograms physical programs).network.Isolated
      (fun state => sources state.1) (fun state => targets state.1) :=
  (physicalProjection physical programs).toRefinement.isolated isolated

theorem mediated_of_physical (physical : Network Node) (programs : Node → Node → Program)
    {sources targets gateways : Node → Prop} (mediated : physical.Mediated sources targets gateways) :
    (ofPrograms physical programs).network.Mediated
      (fun state => sources state.1) (fun state => targets state.1) (fun state => gateways state.1) :=
  (physicalProjection physical programs).mediated mediated

theorem invariant (transfer : Transfer Node) (property : Node → Header → Prop)
    (preserved : ∀ source before target after,
      transfer.step source before target after → property source before → property target after)
    {source target : Node × Header} (path : transfer.network.Reachable source target)
    (initial : property source.1 source.2) : property target.1 target.2 := by
  induction path with
  | refl => exact initial
  | step edge _ ih => exact ih (preserved _ _ _ _ edge initial)

/-- The previous model is embedded by requiring every step to preserve its header. -/
def fixed (families : Header → Network Node) : Transfer Node :=
  ⟨fun source before target after => (families before).link source target ∧ after = before⟩

theorem fixed_header (families : Header → Network Node) {source target : Node × Header}
    (path : (fixed families).network.Reachable source target) : target.2 = source.2 := by
  induction path with
  | refl => rfl
  | step edge _ ih => exact ih.trans edge.2

theorem fixed_project (families : Header → Network Node) {source target : Node × Header}
    (path : (fixed families).network.Reachable source target) :
    (families source.2).Reachable source.1 target.1 := by
  induction path with
  | refl state => exact .refl state.1
  | step edge _ ih =>
    exact .step edge.1 (by simpa only [edge.2] using ih)

theorem fixed_lift (families : Header → Network Node) (header : Header) {source target : Node}
    (path : (families header).Reachable source target) :
    (fixed families).network.Reachable (source, header) (target, header) := by
  induction path with
  | refl node => exact .refl (node, header)
  | @step source next target edge _ ih =>
    exact Network.Reachable.step (next := (next, header)) ⟨edge, rfl⟩ ih

theorem fixed_reachable_iff (families : Header → Network Node) (source target : Node)
    (before after : Header) :
    (fixed families).network.Reachable (source, before) (target, after) ↔
      after = before ∧ (families before).Reachable source target := by
  constructor
  · intro path
    exact ⟨fixed_header families path, fixed_project families path⟩
  · rintro ⟨rfl, path⟩
    exact fixed_lift families _ path

end Transfer
end Netlib.Packet
