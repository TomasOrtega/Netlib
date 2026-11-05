import Netlib.Packet.ICMPControl

namespace NetlibTest.ICMPControl

open Netlib Packet Packet.ICMPControl

example (policy : Policy) (fallback : Action) (kind : Netlib.Protocol.ICMP.Kind)
    (state : StatefulACL.CTState) (header : Header) :
    StatefulACL.Policy.evaluate fallback (policy.compile kind) state header = policy.evaluate kind state header :=
  policy.compile_evaluate _ _ _ _

private def header (protocol : Packet.Protocol) : Header := ⟨3221225986, 3405803778, protocol, 0, 0⟩
private def first : Packet.ICMPControl.Rule := ⟨⟨{ protocol := some Packet.Protocol.icmp }, some [.invalid], .deny⟩, [11], [1]⟩
private def second : Packet.ICMPControl.Rule := ⟨⟨{ protocol := some Packet.Protocol.icmp }, none, .permit⟩, [], []⟩
private def policy : Policy := ⟨[first, second], .deny⟩

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  for kind in [Netlib.Protocol.ICMP.Kind.timeExceeded, .reassemblyTimeout, .fragmentationNeeded 600] do
    for state in [StatefulACL.CTState.new, .established, .related, .invalid, .untracked] do
      for protocol in [Packet.Protocol.tcp, .udp, .icmp] do
        let packet := header protocol
        let expected : Action := if protocol != Packet.Protocol.icmp || (kind == .reassemblyTimeout && state == .invalid)
          then .deny else .permit
        ensure (policy.evaluate kind state packet == expected &&
            StatefulACL.Policy.evaluate .permit (policy.compile kind) state packet == expected)
          "Kind guards, state guards, header predicates, rule order, and the explicit default must compose exactly."
  let contradictory : Policy := ⟨[⟨second.base, [11, 3], [1]⟩], .deny⟩
  ensure (contradictory.compile .reassemblyTimeout == [⟨{}, none, .deny⟩])
    "All type predicates in the structured rule must hold before its base rule can compile."
  IO.println "ICMP control policy compilation tests passed."

end NetlibTest.ICMPControl
