import Netlib.Check.CampusRevocationModel

namespace NetlibTest.CampusRevocationFixture

open Netlib Packet Protocol
open StatefulFailover (Gateway)

namespace Model
export Check.CampusRevocationModel (Input Event PacketCall State Report)
end Model

def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
def protectedZone : Nat := 0
def freshZone : Nat := 8

def entry : NetfilterNAT.Entry :=
  ⟨⟨original, wire.reverse, protectedZone, protectedZone, 0⟩, true, true⟩

def freshOriginal : NetfilterNAT.Entry :=
  { entry with flow := { entry.flow with originalZone := freshZone, replyZone := freshZone } }

def freshReverse : NetfilterNAT.Entry :=
  ⟨⟨entry.flow.reply, entry.flow.original, freshZone, freshZone, entry.flow.remainingTTL⟩,
    entry.destinationNAT, entry.sourceNAT⟩

def requestPayload : List UInt8 := [0, 255, 65, 0, 17]
def replyPayload : List UInt8 := [17, 0, 66, 255, 0]
def stalePayload : List UInt8 := [0, 83, 84, 65, 76, 69, 255]

def source (header : Header) (payload : List UInt8) (ttl : UInt8 := 64) : Except String SafeHandoff.Source := do
  let transport ← UDP.encode header.source header.destination
    (UDP.computed header.source header.destination header.sourcePort header.destinationPort payload)
  let bytes ← IPv4.encode ⟨32, 4321, true, ttl, Packet.Protocol.udp,
    header.source, header.destination, transport⟩
  match decoded : UDP.decodeIPv4 bytes with
  | .error reason => throw reason
  | .ok packet => return ⟨bytes, packet, decoded⟩

private def ethernet : List UInt8 := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 8, 0]

def output (header : Header) (payload : List UInt8) : Except String Check.WireForwarding.WirePacket := do
  let packet ← source header payload 63
  let bytes := ethernet ++ packet.bytes
  let checked ← Check.Wire.checkBytes bytes
  return ⟨bytes, checked⟩

def permittedObservation (classification : StatefulACL.CTState) (fresh : Bool)
    (afterDestination target : Header) (nextHop : String) (payload : List UInt8) :
    Except String Check.WireForwarding.PacketObservation := do
  return ⟨some classification, some fresh, some afterDestination, some target,
    some nextHop, some .forwarded, some (← output target payload)⟩

def observe (index : Nat) (event : Check.SafeHandoff.Event) : Check.SafeHandoff.Observation :=
  ⟨index, event, none, none, none, Lean.Json.mkObj [("source", .str "SYNTHETIC revocation schedule")]⟩

def authenticationEvents (context : Context) (scope : Scope) : List EAPSession.Event := [
  .authentication .begin,
  .authentication (.server (.request 7 13 [32])),
  .authentication (.peer (.response 7 13 [0])),
  .authentication (.server (.success 7)),
  .authentication (.method ⟨1, context.consumer, 13, true,
    some "SYNTHETIC trusted revocation fixture method result"⟩),
  .application (.install ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩),
  .authentication .logoff]

def authentication (input : Model.Input) : Check.EAP.Input :=
  { input.authentication with observations :=
      (authenticationEvents input.authentication.context input.application).mapIdx fun index event =>
        ⟨index, event, none, none, none,
          Lean.Json.mkObj [("source", .str "SYNTHETIC revocation authentication")]⟩ }

structure Fixture where
  input : Model.Input
  established : SafeHandoff.Source
  request : SafeHandoff.Source
  reply : SafeHandoff.Source
  staleReply : SafeHandoff.Source
  primaryPermit : Check.ConntrackLifecycle.Config
  standbyPermit : Check.ConntrackLifecycle.Config
  primaryDeny : Check.ConntrackLifecycle.Config
  standbyDeny : Check.ConntrackLifecycle.Config

def Fixture.targets (fixture : Fixture) (gateway : Gateway) : SafeHandoff.Configuration :=
  Check.SafeHandoff.configuration fixture.input.handoff.routing gateway
    (match gateway with | .primary => fixture.primaryDeny | .standby => fixture.standbyDeny)

def campus (event : Check.CampusDeployment.Event) : Model.Event :=
  .campus ⟨0, event, Lean.Json.mkObj [("source", .str "SYNTHETIC revocation timeline")]⟩

def network (index : Nat) : Model.Event := campus (.network index)
def auth (index : Nat) : Model.Event := campus (.authentication index)

def Fixture.preparation (_fixture : Fixture) : List Model.Event :=
  (List.range 6).map auth ++ [network 0, network 1, network 2, .deliver 1] ++
    (List.range 8).map (fun index => network (index + 3))

def Fixture.revocation (_fixture : Fixture) : List Model.Event :=
  [auth 6, network 11, network 12, network 13]

def Fixture.draining (_fixture : Fixture) : List Model.Event := List.replicate 3 (.deliver 1)

def Fixture.cachedCalls (fixture : Fixture) : List Model.PacketCall :=
  [Gateway.primary, .standby].flatMap fun gateway =>
    [⟨gateway, protectedZone, fixture.request, none⟩,
      ⟨gateway, protectedZone, fixture.reply, none⟩]

def Fixture.freshCalls (fixture : Fixture) : List Model.PacketCall :=
  [Gateway.primary, .standby].flatMap fun gateway =>
    [⟨gateway, freshZone, fixture.request, some freshOriginal⟩,
      ⟨gateway, freshZone, fixture.reply, some freshReverse⟩]

def Fixture.after (fixture : Fixture) : List Model.Event :=
  (fixture.cachedCalls ++ fixture.freshCalls).map (fun call => .packet call) ++ [.deliver 1]

def Fixture.events (fixture : Fixture) : List Model.Event :=
  fixture.preparation ++ fixture.revocation ++ fixture.draining ++ fixture.after

def Fixture.logoffSlot (fixture : Fixture) : Nat := fixture.preparation.length
def Fixture.primaryInstallSlot (fixture : Fixture) : Nat := fixture.logoffSlot + 1
def Fixture.staleSlot (fixture : Fixture) : Nat := fixture.logoffSlot + 2
def Fixture.standbyInstallSlot (fixture : Fixture) : Nat := fixture.logoffSlot + 3
def Fixture.barrierCut (fixture : Fixture) : Nat := (fixture.preparation ++ fixture.revocation).length
def Fixture.completionCut (fixture : Fixture) : Nat := fixture.barrierCut + fixture.draining.length

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def config (input : Model.Input) (id : String) : IO Check.ConntrackLifecycle.Config :=
  match input.handoff.configs.find? (·.id == id) with
  | some selected => pure selected
  | none => throw (IO.userError s!"Missing source configuration {id}.")

def build : IO Fixture := do
  let base ← load (Check.CampusDeployment.Bundle.parse (← IO.FS.readFile "examples/campus/bundle.json"))
  let established ← load (source original [69, 83, 84, 65, 66, 76, 73, 83, 72])
  let request ← load (source original requestPayload)
  let reply ← load (source wire.reverse replyPayload)
  let staleReply ← load (source wire.reverse stalePayload)
  let primaryPermit ← config base.input "install-primary-permit"
  let standbyPermit ← config base.input "install-standby-permit"
  let primaryDeny ← config base.input "initial-primary"
  let standbyDeny ← config base.input "install-standby-deny"
  let forwardStage : Header := { original with destination := wire.destination, destinationPort := wire.destinationPort }
  let reverseStage : Header := { wire.reverse with destination := original.source, destinationPort := original.sourcePort }
  let establishment ← load (permittedObservation .new true forwardStage wire "server"
    established.packet.datagram.payload)
  let observedRequest ← load (permittedObservation .new false forwardStage wire "server" requestPayload)
  let observedReply ← load (permittedObservation .established false reverseStage original.reverse "client" replyPayload)
  let observedStale ← load (permittedObservation .established false reverseStage original.reverse "client" stalePayload)
  let events : List Check.SafeHandoff.Observation := [
    observe 0 (.install .primary primaryPermit),
    observe 1 (.install .standby standbyPermit),
    observe 2 (.establish protectedZone established establishment),
    observe 3 (.stage protectedZone original),
    observe 4 (.commit 180),
    observe 5 (.handoff .server .standby),
    observe 6 (.assign .original request (some 0)),
    observe 7 (.assign .reply reply (some 1)),
    observe 8 (.assign .reply staleReply (some 2)),
    observe 9 (.serve 0 request observedRequest),
    observe 10 (.serve 1 reply observedReply),
    observe 11 (.install .primary primaryDeny),
    observe 12 (.serve 2 staleReply observedStale),
    observe 13 (.install .standby standbyDeny)]
  let input : Model.Input := { base.input with
    authentication := authentication base.input
    handoff := { base.input.handoff with events } }
  return ⟨input, established, request, reply, staleReply,
    primaryPermit, standbyPermit, primaryDeny, standbyDeny⟩

end NetlibTest.CampusRevocationFixture
