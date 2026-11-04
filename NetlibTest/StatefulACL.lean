import Netlib.Packet.StatefulACL

namespace NetlibTest.StatefulACL

open Netlib.Packet
open Netlib.Packet.StatefulACL

private def https : Header := ⟨167772162, 3325256706, Protocol.tcp, 40000, 443⟩
private def ssh : Header := { https with destinationPort := 22 }
private def udp : Header := { https with protocol := Protocol.udp }
private def web : Match := { protocol := some Protocol.tcp, destinationPorts := some (.single 443) }
private def permitNew : StatefulACL.Rule := ⟨web, some [.new], .permit⟩
private def permitEstablished : StatefulACL.Rule := ⟨{}, some [.established], .permit⟩
private def denyInvalid : StatefulACL.Rule := ⟨{}, some [.invalid], .deny⟩
private def denyWeb : StatefulACL.Rule := ⟨web, none, .deny⟩
private def permitAll : StatefulACL.Rule := ⟨{}, none, .permit⟩
private def firewall : Policy := [denyInvalid, permitEstablished, permitNew]

example : permitNew.Matches .new https := (StatefulACL.Rule.accepts_iff _ _ _).mp (by decide)
example : ¬permitNew.Matches .established https := by
  rw [← StatefulACL.Rule.accepts_iff]
  decide

example : Policy.FirstMatch firewall .established ssh .permit :=
  (Policy.lookup_eq_some_iff _ _ _ _).mp (by decide)

example : Policy.FirstMatch [denyWeb, permitEstablished] .established https .deny :=
  (Policy.lookup_eq_some_iff _ _ _ _).mp (by decide)

example (state : CTState) (header : Header) :
    (⟨{}, some [], .deny⟩ : StatefulACL.Rule).accepts state header = false :=
  StatefulACL.Rule.accepts_empty _ _ _ _

example (fallback : Action) (rules : Policy) (state : CTState) (header : Header) :
    Policy.evaluate fallback (⟨{}, some [], .deny⟩ :: rules) state header =
      Policy.evaluate fallback rules state header :=
  Policy.evaluate_cons_rejects _ _ _ _ _ (StatefulACL.Rule.accepts_empty _ _ _ _)

example (state : CTState) (header : Header) :
    Policy.evaluate .deny [permitAll, denyWeb] state header = .permit :=
  Policy.evaluate_cons_accepts _ _ _ _ _ (by simp [permitAll])

example : Policy.evaluate .permit [permitNew] .established ssh = .permit := by decide
example : Policy.evaluate .deny [permitNew] .established ssh = .deny := by decide
example : Policy.allows [permitEstablished, denyWeb] .established https = true := by decide
example : Policy.allows [denyWeb, permitEstablished] .established https = false := by decide

example : firewall.Refines [permitAll] := by
  intro state header _
  simp [Policy.allows, Policy.evaluate, Policy.lookup, permitAll]

example : ¬Policy.Refines [permitEstablished] [permitNew] := by
  intro refines
  have denied := refines .established ssh (by decide)
  have rejected : Policy.allows [permitNew] .established ssh = false := by decide
  simp_all

example (test : Match) (states : Option (List CTState)) (rules : Policy) :
    Policy.Refines (⟨test, states, .deny⟩ :: rules) rules :=
  Policy.prepend_deny_refines _ _ _

example (fallback : Action) (state : CTState) (header : Header) :
    ACL.evaluate fallback (firewall.specialize state) header =
      Policy.evaluate fallback firewall state header :=
  Policy.evaluate_specialize _ _ _ _

example (rules : ACL) (fallback : Action) (state : CTState) (header : Header) :
    Policy.evaluate fallback (Policy.ofACL rules) state header = ACL.evaluate fallback rules header :=
  Policy.evaluate_ofACL _ _ _ _

example (fallback : Action) (state : CTState) (header : Header) :
    Policy.evaluate fallback [denyWeb, permitAll] state header =
      ACL.evaluate fallback [⟨web, .deny⟩, ⟨{}, .permit⟩] header := by
  exact Policy.evaluate_eq_of_unguarded _ _ (by simp [denyWeb, permitAll]) _ _

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  ensure (firewall.allows .new https) "A NEW HTTPS packet must match both guards."
  ensure (!(firewall.allows .new ssh)) "A NEW SSH packet must miss the HTTPS rule."
  ensure (!(firewall.allows .new udp)) "Matching ports cannot replace the protocol guard."
  ensure (firewall.allows .established ssh && firewall.allows .established udp)
    "The supplied ESTABLISHED class is independent of TCP ports and transport handshakes."
  for state in [CTState.invalid, .untracked, .related] do
    ensure (!(firewall.allows state https)) "Unselected conntrack classes must remain denied."
  let related : Policy := [⟨{}, some [.established, .related], .permit⟩]
  ensure (related.allows .related udp && related.allows .established udp)
    "A state list must match each listed class."
  ensure (!(related.allows .new udp)) "A state list must reject classes outside the list."
  ensure (Policy.allows [permitEstablished, denyWeb] .established https)
    "An earlier matching state permit must win."
  ensure (!(Policy.allows [denyWeb, permitEstablished] .established https))
    "An earlier matching header deny must win."
  let emptyGuard : StatefulACL.Rule := ⟨{}, some [], .deny⟩
  let sourceGuard : StatefulACL.Rule := ⟨{ source := some ⟨167772160, 24⟩ }, some [.new], .permit⟩
  ensure (sourceGuard.accepts .new https)
    "Header prefixes and connection states must both match."
  ensure (!(sourceGuard.accepts .new { https with source := 3405803777 }))
    "An alias outside the source prefix must not inherit the original header's match."
  let ordinary : ACL := [⟨web, .deny⟩, ⟨{}, .permit⟩]
  for state in [CTState.new, .established, .related, .invalid, .untracked] do
    ensure (Policy.allows [emptyGuard, permitAll] state https)
      "An empty state selector must not shadow later rules."
    ensure (permitAll.accepts state https) "An absent state selector must accept every class."
    for header in [https, ssh, udp] do
      ensure (ACL.allows (firewall.specialize state) header == firewall.allows state header)
        "Specializing a fixed state must preserve ordered policy decisions."
      ensure (Policy.allows (Policy.ofACL ordinary) state header == ordinary.allows header)
        "Embedding an ordinary ACL must preserve its behavior in every state."
      for fallback in [Action.permit, .deny] do
        ensure (Policy.evaluate fallback [emptyGuard] state header == fallback)
          "An unmatched native chain must use its declared policy."
        ensure (Policy.evaluate fallback (firewall ++ [permitAll]) state header ==
            Policy.evaluate (Policy.evaluate fallback [permitAll] state header) firewall state header)
          "Appending rules must preserve the first matching action."
  IO.println "Stateful ACL tests passed."

end NetlibTest.StatefulACL
