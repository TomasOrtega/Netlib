import Netlib.Packet.ACL

namespace NetlibTest.Packet

open Netlib Netlib.Packet

private def localNet : Prefix := ⟨167772160, 24⟩
private def host : Address := 167772167
private def remote : Address := 167772423

private def https : Header :=
  ⟨host, 3232235786, Protocol.tcp, 49152, 443⟩

private def ssh : Header := { https with destinationPort := 22 }
private def udp : Header := { https with protocol := Protocol.udp }

private def httpsMatch : Match :=
  { source := some localNet
    protocol := some Protocol.tcp
    destinationPorts := some (.single 443) }

private def permitHttps : Rule := ⟨httpsMatch, .permit⟩
private def denyEverything : Rule := ⟨{}, .deny⟩
private def permitEverything : Rule := ⟨{}, .permit⟩

example : Address.ofNat? 4294967295 ≠ none := by decide
example : Address.ofNat? 4294967296 = none := by decide
example : Port.ofNat? 65535 ≠ none := by decide
example : Port.ofNat? 65536 = none := by decide
example : Protocol.ofNat? 255 ≠ none := by decide
example : Protocol.ofNat? 256 = none := by decide

example : localNet.contains host = true := by decide
example : localNet.contains remote = false := by decide
example : (⟨remote, 0⟩ : Prefix).contains host = true := by decide
example : (⟨host, 32⟩ : Prefix).contains host = true := by decide
example : (⟨host, 32⟩ : Prefix).contains remote = false := by decide
example : (⟨167772299, 24⟩ : Prefix).contains host = true := by decide

example : (PortRange.single 443).contains 443 = true := by decide
example : (PortRange.single 443).contains 444 = false := by decide
example : (⟨100, 99⟩ : PortRange).contains 100 = false := by decide
example : (⟨0, 65535⟩ : PortRange).contains 65535 = true := by decide

example : httpsMatch.accepts https = true := by decide
example : httpsMatch.accepts ssh = false := by decide
example : httpsMatch.accepts udp = false := by decide
example : httpsMatch.accepts { https with source := remote } = false := by decide
example : ({} : Match).accepts udp = true := by decide
example : httpsMatch.Holds https := (Match.accepts_iff _ _).mp (by decide)

example : ACL.evaluate .permit [] https = .permit := rfl
example : ACL.evaluate .deny [] https = .deny := rfl
example : ACL.allows [] https = false := rfl
example : ACL.allows [permitHttps] https = true := by decide
example : ACL.allows [permitHttps] ssh = false := by decide
example : ACL.allows [denyEverything, permitHttps] https = false := by decide
example : ACL.allows [permitHttps, denyEverything] https = true := by decide
example : ACL.allows [permitEverything, denyEverything] ssh = true := by decide
example : ACL.lookup [permitHttps] ssh = none := by decide
example : ACL.lookup [denyEverything, permitHttps] https = some .deny := by decide

example : ACL.FirstMatch [permitHttps, denyEverything] https .permit :=
  (ACL.lookup_eq_some_iff _ _ _).mp (by decide)

example : ACL.FirstMatch [permitHttps, denyEverything] ssh .deny :=
  (ACL.lookup_eq_some_iff _ _ _).mp (by decide)

example (rules : ACL) :
    ACL.evaluate .deny (permitEverything :: permitHttps :: rules) https =
      ACL.evaluate .deny (permitEverything :: rules) https :=
  ACL.shadowed_rule permitEverything permitHttps rules (Match.refines_any _) .deny https

example : ACL.serial [permitHttps] [permitEverything] https = true := by decide
example : ACL.serial [permitEverything] [permitHttps] ssh = false := by decide
example : ACL.allows ([permitEverything] ++ [denyEverything]) ssh = true := by decide

private def chain : Network Nat :=
  ⟨fun source target => (source = 0 ∧ target = 1) ∨ (source = 1 ∧ target = 2)⟩

private def policies (_source _target : Nat) : ACL := [permitHttps]

example : (Forwarding.filter chain policies https).Reachable 0 2 := by
  apply Network.Reachable.step (next := 1)
  · constructor
    · exact .inl ⟨rfl, rfl⟩
    · decide
  · apply Network.Reachable.single
    constructor
    · exact .inr ⟨rfl, rfl⟩
    · decide

example : ¬(Forwarding.filter chain policies ssh).Reachable 0 2 := by
  intro path
  cases path with
  | step edge _ =>
    have accepted := edge.2
    change ACL.allows [permitHttps] ssh = true at accepted
    have rejected : ACL.allows [permitHttps] ssh = false := by decide
    simp_all

example (net : Network Nat) (sources targets : Nat → Prop)
    (isolated : net.Isolated sources targets) :
    (Forwarding.filter net policies https).Isolated sources targets :=
  Forwarding.isolation_preserved isolated policies https

example (net : Network Nat) :
    (Forwarding.filter net (fun source target =>
      ⟨{}, .deny⟩ :: policies source target) https).Reachable 0 2 →
      (Forwarding.filter net policies https).Reachable 0 2 := by
  apply Forwarding.reachable_of_refines
  intro source target
  exact ACL.prepend_deny_refines {} (policies source target)

end NetlibTest.Packet
