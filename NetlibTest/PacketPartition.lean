import Netlib.Packet.Partition

namespace NetlibTest.PacketPartition

open Netlib Netlib.Packet

private def tcp : Match := { protocol := some Protocol.tcp }

private def https : Match :=
  { protocol := some Protocol.tcp, destinationPorts := some (PortRange.single 443) }

private def tcpPolicy : ACL := [⟨tcp, .permit⟩]

private def httpsPolicy : ACL := [⟨https, .permit⟩]

private def denyHttps : ACL := [⟨https, .deny⟩, ⟨tcp, .permit⟩]

example : Interval.floor [40, 10, 20, 10] 29 = 20 := by decide

example : Interval.points 4 [0, 1, 1, 4, 99] = [0, 1] := by decide

example : Partition.checkACLRefines httpsPolicy tcpPolicy = true := by decide

example : Partition.checkACLRefinesBudget httpsPolicy tcpPolicy 0 =
    .error "Packet partition exceeds its cell budget." := by rfl

example : Partition.checkACLRefinesBudget httpsPolicy tcpPolicy 9 = .ok true := by rfl

example : Partition.checkACLRefinesBudget tcpPolicy httpsPolicy 9 = .ok false := by rfl

example : httpsPolicy.Refines tcpPolicy :=
  (Partition.checkACLRefines_iff _ _).mp (by decide)

example : Partition.checkACLRefines tcpPolicy httpsPolicy = false := by decide

example : Partition.aclCounterexample tcpPolicy httpsPolicy = some ⟨0, 0, 6, 0, 0⟩ := by decide

example : Partition.aclCounterexample httpsPolicy tcpPolicy = none := by decide

example : ¬tcpPolicy.Refines httpsPolicy := by
  intro refines
  have result := (Partition.checkACLRefines_iff _ _).mpr refines
  have rejected : Partition.checkACLRefines tcpPolicy httpsPolicy = false := by decide
  simp [rejected] at result

example : Partition.checkACLRefines denyHttps tcpPolicy = true := by decide

example : Partition.checkACLRefines httpsPolicy denyHttps = false := by decide

private def emptyRange : Match :=
  { destinationPorts := some ⟨20, 10⟩ }

example : Partition.checkACLRefines [⟨emptyRange, .permit⟩] [] = true := by decide

private def lastAddress : Prefix := ⟨4294967295, 32⟩

private def fullAddress : Match := { source := some lastAddress }

private def allAddresses : Match := { source := some ⟨123, 0⟩ }

example : Partition.checkACLRefines [⟨fullAddress, .permit⟩] [⟨allAddresses, .permit⟩] = true := by decide

example : Partition.checkACLRefines [⟨allAddresses, .permit⟩] [⟨fullAddress, .permit⟩] = false := by decide

private def overlaps : ACL :=
  [⟨{ source := some ⟨167772160, 8⟩, destinationPorts := some ⟨440, 450⟩ }, .deny⟩,
   ⟨{ source := some ⟨167772417, 24⟩, destinationPorts := some ⟨443, 460⟩ }, .permit⟩]

private def drop : Routing.Entry Nat := ⟨⟨167772417, 24⟩, none⟩

private def next : Routing.Entry Nat := ⟨⟨167772160, 8⟩, some 1⟩

private def routes : List (Routing.Entry Nat) := [next, drop, ⟨⟨167772417, 24⟩, some 2⟩]

private def partition : Partition := Partition.ofRulesAndRoutes [overlaps] [routes]

example : Routing.nextHop routes 167772416 = none := by decide

example : Routing.nextHop routes 167772415 = some 1 := by decide

example : Routing.nextHop routes 167772672 = some 1 := by decide

example (header : Header) :
    Routing.lookup routes (partition.representative header).destination =
      Routing.lookup routes header.destination :=
  partition.route_lookup_stable routes
    (fun entry member => Partition.route_included [overlaps] [routes] [] routes
      (by simp) entry member) header

example (header : Header) :
    overlaps.allows (partition.representative header) = overlaps.allows header :=
  partition.acl_allows_stable overlaps
    (fun rule member => Partition.rule_included [overlaps] [routes] [] overlaps
      (by simp) rule member) header

private def checkThat (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let edgeHeaders : List Header := [
    ⟨0, 0, 0, 0, 0⟩,
    ⟨167772159, 167772415, 6, 65535, 439⟩,
    ⟨167772160, 167772416, 6, 65535, 440⟩,
    ⟨167772417, 167772671, 17, 0, 450⟩,
    ⟨167772671, 167772672, 255, 0, 451⟩,
    ⟨167772672, 167772673, 6, 0, 460⟩,
    ⟨4294967295, 4294967295, 255, 65535, 65535⟩]
  for header in edgeHeaders do
    let representative := partition.representative header
    checkThat (partition.representatives.contains representative) "A header cell has no representative."
    checkThat (overlaps.allows representative == overlaps.allows header) "ACL classification changed."
    checkThat (Routing.lookup routes representative.destination == Routing.lookup routes header.destination)
      "Routing classification changed."
  checkThat (partition.representatives.length < 1000) "The partition enumerates unnecessary field values."
  checkThat (partition.representatives.length == partition.cellCount) "The cell budget has the wrong size."
  match Partition.aclCounterexample tcpPolicy httpsPolicy with
  | none => throw (IO.userError "The widened policy has no counterexample.")
  | some header =>
    checkThat (tcpPolicy.allows header && !httpsPolicy.allows header) "The counterexample is invalid."
  IO.println "Packet partition tests passed."

end NetlibTest.PacketPartition
