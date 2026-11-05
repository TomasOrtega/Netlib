import Netlib.Theory.NATReuse

namespace NetlibTest.NATReuse

open Netlib.Packet Netlib.Protocol Netlib.Theory.NATReuse

private def oldFlow : Header := ⟨167772161, 3325256705, Protocol.tcp, 40000, 443⟩
private def newFlow : Header := { oldFlow with source := 167772162, sourcePort := 40001 }
private def alias : Endpoint := ⟨3405803777, 62000⟩

private def retired : NAT.State := NAT.run NAT.State.initial (retirementEvents oldFlow alias 10)
private def reused : NAT.State := NAT.run NAT.State.initial (reuseEvents oldFlow newFlow alias 10 20)

example : oldFlow.sourceEndpoint ≠ newFlow.sourceEndpoint := by decide

example : oldFlow ≠ newFlow ∧
    (translated alias oldFlow).reverse = (translated alias newFlow).reverse :=
  distinct_inside_same_reply alias oldFlow newFlow (by decide) rfl rfl

example : retired = ⟨⟨10, []⟩, []⟩ :=
  retired_state oldFlow alias 10 (by decide) (by decide)

example : reused.Safe := reused_state_safe oldFlow newFlow alias 10 20

example : (NAT.step reused (.inbound (translated alias oldFlow).reverse)).output = some newFlow.reverse :=
  delayed_reply_restored_to_new oldFlow newFlow alias 10 20
    (by decide) (by decide) (by decide) (by decide) rfl rfl

example : (NAT.step reused (.inbound (translated alias oldFlow).reverse)).output ≠ some oldFlow.reverse :=
  delayed_reply_not_original oldFlow newFlow alias 10 20
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl

example : ¬(reused.Safe → RejectsRetiredReply reused oldFlow alias) := by
  intro implication
  have witness := safe_but_not_retired_reply_rejection oldFlow newFlow alias 10 20
    (by decide) (by decide) (by decide) (by decide) rfl rfl
  exact witness.2 (implication witness.1)

example (decision : NAT.State → Header → Bool) :
    ¬(decision reused (translated alias oldFlow).reverse = false ∧
      decision reused (translated alias newFlow).reverse = true) :=
  cannot_reject_old_accept_new decision reused alias oldFlow newFlow rfl rfl

example (decode : NAT.State → Header → Endpoint) :
    ¬(decode reused (translated alias oldFlow).reverse = oldFlow.sourceEndpoint ∧
      decode reused (translated alias newFlow).reverse = newFlow.sourceEndpoint) :=
  cannot_recover_inside decode reused alias oldFlow newFlow (by decide) rfl rfl

example : translated alias oldFlow ≠ translated alias { newFlow with destination := 3325256706 } := by decide
example : translated alias oldFlow ≠ translated alias { newFlow with protocol := Protocol.udp } := by decide

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let opened := NAT.step NAT.State.initial (.outbound oldFlow alias true 10)
  ensure (opened.output == some (translated alias oldFlow)) "The old authorized flow did not open."
  ensure (retired.tracking.now == 10 && retired.tracking.entries.isEmpty && retired.bindings.isEmpty)
    "The retired flow retained a live mapping or grant."
  ensure ((NAT.step retired (.inbound (translated alias oldFlow).reverse)).output.isNone)
    "An expired alias admitted the delayed reply before reuse."
  let reopened := NAT.step retired (.outbound newFlow alias true 20)
  ensure (reopened.output == some (translated alias newFlow)) "The new authorized flow did not reuse the alias."
  ensure (reopened.output == opened.output) "Alias reuse did not reproduce the same wire five-tuple."
  let replayed := NAT.step reused (.inbound (translated alias oldFlow).reverse)
  ensure (replayed.output == some newFlow.reverse && replayed.output != some oldFlow.reverse)
    "The indistinguishable delayed reply did not follow the new binding."
  let otherPeer := NAT.step retired (.outbound { newFlow with destination := 3325256706 } alias true 20)
  ensure ((NAT.step otherPeer.state (.inbound (translated alias oldFlow).reverse)).output.isNone)
    "A different remote endpoint was incorrectly treated as indistinguishable."
  let otherProtocol := NAT.step retired (.outbound { newFlow with protocol := Protocol.udp } alias true 20)
  ensure ((NAT.step otherProtocol.state (.inbound (translated alias oldFlow).reverse)).output.isNone)
    "A different transport protocol was incorrectly treated as indistinguishable."
  let expiredAgain := NAT.step reused (.advance 20)
  ensure ((NAT.step expiredAgain.state (.inbound (translated alias oldFlow).reverse)).output.isNone)
    "The reused alias ignored its own expiration boundary."
  IO.println "NAT alias reuse limits passed."

end NetlibTest.NATReuse
