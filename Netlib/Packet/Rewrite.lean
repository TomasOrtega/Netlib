import Netlib.Packet.Basic

namespace Netlib.Packet

structure Endpoint where
  address : Address
  port : Port
  deriving Repr, BEq, DecidableEq

namespace Header

def sourceEndpoint (header : Header) : Endpoint := ⟨header.source, header.sourcePort⟩

def destinationEndpoint (header : Header) : Endpoint := ⟨header.destination, header.destinationPort⟩

def reverse (header : Header) : Header :=
  ⟨header.destination, header.source, header.protocol, header.destinationPort, header.sourcePort⟩

@[simp] theorem reverse_reverse (header : Header) : header.reverse.reverse = header := rfl

@[simp] theorem reverse_sourceEndpoint (header : Header) :
    header.reverse.sourceEndpoint = header.destinationEndpoint := rfl

@[simp] theorem reverse_destinationEndpoint (header : Header) :
    header.reverse.destinationEndpoint = header.sourceEndpoint := rfl

end Header

/-- Absent fields retain their incoming value. Present fields overwrite it. -/
structure Rewrite where
  source : Option Address := none
  destination : Option Address := none
  protocol : Option Protocol := none
  sourcePort : Option Port := none
  destinationPort : Option Port := none
  deriving Repr, BEq, DecidableEq

namespace Rewrite

def identity : Rewrite := {}

def apply (rewrite : Rewrite) (header : Header) : Header :=
  ⟨rewrite.source.getD header.source, rewrite.destination.getD header.destination,
    rewrite.protocol.getD header.protocol, rewrite.sourcePort.getD header.sourcePort,
    rewrite.destinationPort.getD header.destinationPort⟩

/-- Apply the first rewrite, then the second. Later overwrites take precedence. -/
def comp (first second : Rewrite) : Rewrite :=
  ⟨second.source.orElse (fun _ => first.source),
    second.destination.orElse (fun _ => first.destination),
    second.protocol.orElse (fun _ => first.protocol),
    second.sourcePort.orElse (fun _ => first.sourcePort),
    second.destinationPort.orElse (fun _ => first.destinationPort)⟩

@[simp] theorem identity_apply (header : Header) : identity.apply header = header := rfl

private theorem overwrite_getD (first second : Option α) (original : α) :
    (second.orElse (fun _ => first)).getD original = second.getD (first.getD original) := by
  cases second <;> rfl

theorem comp_apply (first second : Rewrite) (header : Header) :
    (first.comp second).apply header = second.apply (first.apply header) := by
  simp only [comp, apply]
  congr 1 <;> exact overwrite_getD _ _ _

@[simp] theorem comp_identity_left (rewrite : Rewrite) : identity.comp rewrite = rewrite := by
  cases rewrite
  simp [comp, identity]

@[simp] theorem comp_identity_right (rewrite : Rewrite) : rewrite.comp identity = rewrite := by
  cases rewrite
  rfl

private theorem overwrite_assoc (first second third : Option α) :
    third.orElse (fun _ => second.orElse (fun _ => first)) =
      (third.orElse (fun _ => second)).orElse (fun _ => first) := by
  cases third <;> rfl

theorem comp_assoc (first second third : Rewrite) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  cases first
  cases second
  cases third
  simp only [comp]
  congr 1 <;> exact overwrite_assoc _ _ _

def sourceEndpoint (endpoint : Endpoint) : Rewrite :=
  { source := some endpoint.address, sourcePort := some endpoint.port }

def destinationEndpoint (endpoint : Endpoint) : Rewrite :=
  { destination := some endpoint.address, destinationPort := some endpoint.port }

@[simp] theorem sourceEndpoint_apply (endpoint : Endpoint) (header : Header) :
    ((sourceEndpoint endpoint).apply header).sourceEndpoint = endpoint := rfl

@[simp] theorem sourceEndpoint_destination (endpoint : Endpoint) (header : Header) :
    ((sourceEndpoint endpoint).apply header).destinationEndpoint = header.destinationEndpoint := rfl

@[simp] theorem destinationEndpoint_apply (endpoint : Endpoint) (header : Header) :
    ((destinationEndpoint endpoint).apply header).destinationEndpoint = endpoint := rfl

@[simp] theorem destinationEndpoint_source (endpoint : Endpoint) (header : Header) :
    ((destinationEndpoint endpoint).apply header).sourceEndpoint = header.sourceEndpoint := rfl

/-- Static reply inversion needs the original endpoint as explicit information. -/
theorem source_reply_roundtrip (originalEndpoint translatedEndpoint : Endpoint) (header : Header)
    (original : header.sourceEndpoint = originalEndpoint) :
    (destinationEndpoint originalEndpoint).apply ((sourceEndpoint translatedEndpoint).apply header).reverse = header.reverse := by
  cases header
  cases originalEndpoint
  cases translatedEndpoint
  simp only [Header.sourceEndpoint, Endpoint.mk.injEq] at original
  rcases original with ⟨rfl, rfl⟩
  rfl

theorem destination_reply_roundtrip (originalEndpoint translatedEndpoint : Endpoint) (header : Header)
    (original : header.destinationEndpoint = originalEndpoint) :
    (sourceEndpoint originalEndpoint).apply ((destinationEndpoint translatedEndpoint).apply header).reverse = header.reverse := by
  cases header
  cases originalEndpoint
  cases translatedEndpoint
  simp only [Header.destinationEndpoint, Endpoint.mk.injEq] at original
  rcases original with ⟨rfl, rfl⟩
  rfl

structure Universe where
  addresses : List Address
  protocols : List Protocol
  ports : List Port
  deriving Repr

namespace Universe

/-- Symmetric fields also cover packet reversal without enumerating address spaces. -/
def ofRewrites (initial : Header) (rewrites : List Rewrite) : Universe where
  addresses := ([initial.source, initial.destination] ++
    rewrites.flatMap (fun rewrite => rewrite.source.toList ++ rewrite.destination.toList)).eraseDups
  protocols := (initial.protocol :: rewrites.flatMap (fun rewrite => rewrite.protocol.toList)).eraseDups
  ports := ([initial.sourcePort, initial.destinationPort] ++
    rewrites.flatMap (fun rewrite => rewrite.sourcePort.toList ++ rewrite.destinationPort.toList)).eraseDups

def headers (space : Universe) : List Header :=
  space.addresses.flatMap fun source =>
  space.addresses.flatMap fun destination =>
  space.protocols.flatMap fun protocol =>
  space.ports.flatMap fun sourcePort =>
  space.ports.map fun destinationPort => ⟨source, destination, protocol, sourcePort, destinationPort⟩

def headerCount (space : Universe) : Nat :=
  space.addresses.length * space.addresses.length * space.protocols.length *
    space.ports.length * space.ports.length

theorem mem_headers (space : Universe) (header : Header) :
    header ∈ space.headers ↔
      header.source ∈ space.addresses ∧ header.destination ∈ space.addresses ∧
      header.protocol ∈ space.protocols ∧ header.sourcePort ∈ space.ports ∧
      header.destinationPort ∈ space.ports := by
  rcases header with ⟨source, destination, protocol, sourcePort, destinationPort⟩
  simp only [headers, List.mem_flatMap, List.mem_map, Header.mk.injEq]
  constructor
  · rintro ⟨_, sourceMem, _, destinationMem, _, protocolMem, _, sourcePortMem,
      _, destinationPortMem, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨sourceMem, destinationMem, protocolMem, sourcePortMem, destinationPortMem⟩
  · rintro ⟨sourceMem, destinationMem, protocolMem, sourcePortMem, destinationPortMem⟩
    exact ⟨source, sourceMem, destination, destinationMem, protocol, protocolMem,
      sourcePort, sourcePortMem, destinationPort, destinationPortMem, rfl, rfl, rfl, rfl, rfl⟩

private theorem length_flatMap_constant (values : List α) (f : α → List β) (size : Nat)
    (same : ∀ value ∈ values, (f value).length = size) :
    (values.flatMap f).length = values.length * size := by
  induction values with
  | nil => simp
  | cons value values ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [same value (by simp), ih (fun next member => same next (List.mem_cons_of_mem _ member))]
    simp [Nat.add_mul, Nat.add_comm]

theorem headers_length (space : Universe) : space.headers.length = space.headerCount := by
  have counted : space.headers.length = space.addresses.length *
      (space.addresses.length * (space.protocols.length *
      (space.ports.length * space.ports.length))) := by
    apply length_flatMap_constant
    intro _ _
    apply length_flatMap_constant
    intro _ _
    apply length_flatMap_constant
    intro _ _
    apply length_flatMap_constant
    intro _ _
    exact List.length_map _
  simpa only [headerCount, Nat.mul_assoc] using counted

theorem initial_mem (initial : Header) (rewrites : List Rewrite) :
    initial ∈ (ofRewrites initial rewrites).headers := by
  rw [mem_headers]
  simp [ofRewrites]

private theorem getD_mem (selected : Option α) (values : List α) (original : α)
    (before : original ∈ values) (included : ∀ value, selected = some value → value ∈ values) :
    selected.getD original ∈ values := by
  cases selected with
  | none => exact before
  | some value => exact included value rfl

theorem rewrite_mem (initial : Header) (rewrites : List Rewrite) (rewrite : Rewrite)
    (member : rewrite ∈ rewrites) (header : Header)
    (covered : header ∈ (ofRewrites initial rewrites).headers) :
    rewrite.apply header ∈ (ofRewrites initial rewrites).headers := by
  rw [mem_headers] at covered ⊢
  rcases covered with ⟨source, destination, protocol, sourcePort, destinationPort⟩
  refine ⟨getD_mem _ _ _ source ?_, getD_mem _ _ _ destination ?_,
    getD_mem _ _ _ protocol ?_, getD_mem _ _ _ sourcePort ?_, getD_mem _ _ _ destinationPort ?_⟩
  all_goals
    intro value selected
    apply List.mem_eraseDups.mpr
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨rewrite, member, by simp [selected]⟩
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨rewrite, member, by simp [selected]⟩
  · apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨rewrite, member, by simp [selected]⟩
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨rewrite, member, by simp [selected]⟩
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨rewrite, member, by simp [selected]⟩

theorem reverse_mem (space : Universe) (header : Header) (member : header ∈ space.headers) :
    header.reverse ∈ space.headers := by
  rw [mem_headers] at member ⊢
  exact ⟨member.2.1, member.1, member.2.2.1, member.2.2.2.2, member.2.2.2.1⟩

end Universe
end Rewrite
end Netlib.Packet
