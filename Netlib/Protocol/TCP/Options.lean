import Netlib.Protocol.TCP.Basic

/-!
RFC 9293 sections 3.1–3.2 give the TCP option format.
Unknown length-bearing options remain unchanged; MSS placement is separate from framing.
https://www.rfc-editor.org/rfc/rfc9293.html#section-3.1
-/

namespace Netlib.Protocol.TCP.Options

open InternetChecksum

def valid : List UInt8 → Bool
  | [] => true
  | kind :: rest =>
    if kind == 0 then rest.all (· == 0)
    else if kind == 1 then valid rest
    else match rest with
      | [] => false
      | length :: tail =>
        if 2 ≤ length.toNat ∧ length.toNat - 2 ≤ tail.length ∧ (kind ≠ 2 ∨ length.toNat = 4) then
          valid (tail.drop (length.toNat - 2))
        else false
termination_by bytes => bytes.length
decreasing_by all_goals (simp_wf <;> omega)

def maximumSegmentSizes : List UInt8 → List Word
  | [] => []
  | kind :: rest =>
    if kind == 0 then []
    else if kind == 1 then maximumSegmentSizes rest
    else match rest with
      | [] => []
      | length :: tail =>
        if 2 ≤ length.toNat ∧ length.toNat - 2 ≤ tail.length then
          let following := maximumSegmentSizes (tail.drop (length.toNat - 2))
          if kind == 2 ∧ length.toNat = 4 then
            match tail with
            | high :: low :: _ => read16 high low :: following
            | _ => following
          else following
        else []
termination_by bytes => bytes.length
decreasing_by all_goals (simp_wf <;> omega)

def synCompatible (flags : UInt8) (bytes : List UInt8) : Bool :=
  (maximumSegmentSizes bytes).isEmpty || Flags.syn flags

@[simp] theorem valid_nil : valid [] = true := by rw [valid]

theorem valid_eol (rest : List UInt8) : valid (0 :: rest) = rest.all (· == 0) := by rw [valid.eq_def]; rfl

theorem valid_nop (rest : List UInt8) : valid (1 :: rest) = valid rest := by rw [valid.eq_def]; rfl

theorem valid_tlv (kind length : UInt8) (tail : List UInt8) (notEnd : kind ≠ 0) (notNop : kind ≠ 1) :
    valid (kind :: length :: tail) = true ↔
      2 ≤ length.toNat ∧ length.toNat - 2 ≤ tail.length ∧ (kind ≠ 2 ∨ length.toNat = 4) ∧
        valid (tail.drop (length.toNat - 2)) = true := by
  rw [valid]
  simp only [beq_iff_eq, notEnd, notNop, ↓reduceIte]
  split <;> simp_all

theorem tlv_progress (kind length : UInt8) (tail : List UInt8) :
    (tail.drop (length.toNat - 2)).length < (kind :: length :: tail).length := by
  simp only [List.length_drop, List.length_cons]
  omega

theorem eol_padding (rest : List UInt8) (accepted : valid (0 :: rest) = true) :
    ∀ byte ∈ rest, byte = 0 := by
  rw [valid_eol, List.all_eq_true] at accepted
  intro byte member
  exact of_decide_eq_true (accepted byte member)

end Netlib.Protocol.TCP.Options
