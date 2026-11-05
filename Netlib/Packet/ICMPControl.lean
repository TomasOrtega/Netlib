import Netlib.Packet.StatefulACL
import Netlib.Protocol.ICMP

/-! ICMP type/code guards compose with packet headers and supplied conntrack state. -/

namespace Netlib.Packet.ICMPControl

abbrev Byte := Fin 256

def typeByte : Protocol.ICMP.Kind → Byte
  | .timeExceeded | .reassemblyTimeout => 11
  | .fragmentationNeeded _ => 3

def codeByte : Protocol.ICMP.Kind → Byte
  | .timeExceeded => 0
  | .reassemblyTimeout => 1
  | .fragmentationNeeded _ => 4

theorem kindPrefix_eq (kind : Protocol.ICMP.Kind) :
    Protocol.ICMP.kindPrefix kind = [UInt8.ofNat (typeByte kind).val, UInt8.ofNat (codeByte kind).val] := by
  cases kind <;> rfl

theorem decoded_type_code (wire : List UInt8) (value : Protocol.ICMP.Decoded)
    (accepted : Protocol.ICMP.decode wire = .ok value) :
    wire.take 2 = [UInt8.ofNat (typeByte value.message.kind).val, UInt8.ofNat (codeByte value.message.kind).val] := by
  rw [← (Protocol.ICMP.decode_fields wire value accepted).2]
  cases selected : value.message.kind <;>
    simp [Protocol.ICMP.bytes, Protocol.ICMP.kindPrefix, selected, typeByte, codeByte] <;> decide

structure Rule where
  base : StatefulACL.Rule
  typeTests : List Byte := []
  codeTests : List Byte := []
  deriving Repr, BEq, DecidableEq

def Rule.kindAccepts (rule : Rule) (kind : Protocol.ICMP.Kind) : Bool :=
  rule.typeTests.all (fun selected => selected == typeByte kind) &&
    rule.codeTests.all (fun selected => selected == codeByte kind)

def Rule.accepts (rule : Rule) (kind : Protocol.ICMP.Kind) (state : StatefulACL.CTState) (header : Header) : Bool :=
  rule.kindAccepts kind && rule.base.accepts state header

structure Policy where
  rules : List Rule
  default : Action
  deriving Repr, BEq, DecidableEq

private def evaluateRules (fallback : Action) : List Rule → Protocol.ICMP.Kind → StatefulACL.CTState → Header → Action
  | [], _, _, _ => fallback
  | rule :: rest, kind, state, header =>
    if rule.accepts kind state header then rule.base.action else evaluateRules fallback rest kind state header

def Policy.evaluate (policy : Policy) (kind : Protocol.ICMP.Kind) (state : StatefulACL.CTState) (header : Header) : Action :=
  evaluateRules policy.default policy.rules kind state header

def Policy.compile (policy : Policy) (kind : Protocol.ICMP.Kind) : StatefulACL.Policy :=
  (policy.rules.filter (·.kindAccepts kind)).map (·.base) ++ [⟨{}, none, policy.default⟩]

private theorem compile_rules (rules : List Rule) (default fallback : Action) (kind : Protocol.ICMP.Kind)
    (state : StatefulACL.CTState) (header : Header) :
    StatefulACL.Policy.evaluate fallback ((rules.filter (·.kindAccepts kind)).map (·.base) ++ [⟨{}, none, default⟩]) state header =
      evaluateRules default rules kind state header := by
  induction rules with
  | nil => simp [StatefulACL.Policy.evaluate, StatefulACL.Policy.lookup, evaluateRules]
  | cons rule rest ih =>
    cases selected : rule.kindAccepts kind with
    | false => simpa [selected, evaluateRules, Rule.accepts] using ih
    | true =>
      cases matched : rule.base.accepts state header with
      | false =>
        simp only [List.filter_cons, selected, ↓reduceIte, List.map_cons, List.cons_append]
        rw [StatefulACL.Policy.evaluate_cons_rejects fallback rule.base _ state header matched]
        simpa only [evaluateRules, Rule.accepts, selected, matched, Bool.true_and, Bool.false_eq_true, ite_false] using ih
      | true =>
        simp only [List.filter_cons, selected, ↓reduceIte, List.map_cons, List.cons_append]
        rw [StatefulACL.Policy.evaluate_cons_accepts fallback rule.base _ state header matched]
        simp [evaluateRules, Rule.accepts, selected, matched]

theorem Policy.compile_evaluate (policy : Policy) (fallback : Action) (kind : Protocol.ICMP.Kind)
    (state : StatefulACL.CTState) (header : Header) :
    StatefulACL.Policy.evaluate fallback (policy.compile kind) state header = policy.evaluate kind state header :=
  compile_rules policy.rules policy.default fallback kind state header

end Netlib.Packet.ICMPControl
