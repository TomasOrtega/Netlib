import Netlib.Check.Traffic

namespace NetlibTest.Traffic

open Netlib Netlib.DataPlane Netlib.Packet

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def read (name : String) : IO Netlib.DataPlane.Config := do
  unwrap (Netlib.DataPlane.Config.parse (← IO.FS.readFile s!"examples/dataplane/{name}.json"))

private def query (config : Netlib.DataPlane.Config) (id : String) : IO Query :=
  match config.requirements.find? (·.id == id) with
  | some found => pure found
  | none => throw (IO.userError s!"Missing query {id}.")

private def https : Match :=
  { protocol := some Protocol.tcp, destinationPorts := some (PortRange.single 443) }

private def ssh : Match :=
  { protocol := some Protocol.tcp, destinationPorts := some (PortRange.single 22) }

private def fixtureTests : IO Unit := do
  let config ← read "secure"
  for id in ["AVAILABLE", "IDENTITY", "GATEWAY"] do
    let q ← query config id
    let result ← unwrap (Check.checkTraffic config q https)
    ensure result.value s!"The secure HTTPS traffic class failed {id}."
    ensure (result.evidence.any (·.startsWith "Packet ")) "The report lost its packet evidence."
  let noSsh ← query config "NO_SSH"
  let result ← unwrap (Check.checkTraffic config noSsh ssh)
  ensure result.value "The secure model must block every selected SSH packet."
  let bypass ← read "bypass"
  for id in ["IDENTITY", "GATEWAY"] do
    let q ← query bypass id
    let result ← unwrap (Check.checkTraffic bypass q https)
    ensure (!result.value) s!"The traffic class failed to detect a bypass for {id}."

private def hiddenPortTests : IO Unit := do
  let config ← read "secure"
  let exception : Rule :=
    ⟨{ https with sourcePorts := some (PortRange.single 50001) }, .deny⟩
  let hidden := { config with links := config.links.map fun link =>
    if link.source == "gateway" then { link with rules := exception :: link.rules } else link }
  let original ← unwrap (Check.check hidden)
  ensure original.compliant "The fixed packet should miss the hidden source-port denial."
  let available ← query hidden "AVAILABLE"
  let result ← unwrap (Check.checkTraffic hidden available https)
  ensure (!result.value) "The complete HTTPS class missed a one-port availability failure."
  let packet := { hidden.trafficFor "https" with sourcePort := 50001 }
  let direct ← unwrap (Check.evaluateAt hidden available packet)
  ensure (!direct.value) "The hidden packet must fail direct evaluation."
  let representative := (hidden.trafficPartition https).representative packet
  ensure (result.evidence.contains s!"Packet {repr representative}")
    "The report lost the concrete hidden-port packet."
  ensure (result.evidence.contains "client -> server: closed cut {client, gateway}")
    "The hidden-port failure must retain its cut certificate."
  let mediated ← query hidden "GATEWAY"
  let result ← unwrap (Check.checkTraffic hidden mediated https)
  ensure result.value "A dropped packet must not create a gateway bypass."

private def hiddenAddressConfig : IO Netlib.DataPlane.Config := do
  let config ← read "bypass"
  return { config with routes := config.routes.map fun table =>
    if table.node == "client" then
      { table with entries := table.entries.map fun entry =>
        if entry.destination.length == 32 then
          { entry with destination := ⟨167772163, 32⟩ }
        else entry }
    else table }

private def hiddenAddressTests : IO Unit := do
  let hidden ← hiddenAddressConfig
  let original ← unwrap (Check.check hidden)
  ensure original.compliant "The fixed packet should miss the hidden destination bypass."
  for id in ["IDENTITY", "GATEWAY"] do
    let q ← query hidden id
    let result ← unwrap (Check.checkTraffic hidden q https)
    ensure (!result.value) s!"The complete HTTPS class missed the hidden bypass for {id}."
    let packet := { hidden.trafficFor "https" with destination := 167772163 }
    let direct ← unwrap (Check.evaluateAt hidden q packet)
    ensure (!direct.value) "The hidden destination must fail direct evaluation."
    let representative := (hidden.trafficPartition https).representative packet
    ensure (result.evidence.contains s!"Packet {repr representative}")
      "The report lost the concrete hidden-destination packet."
    let path := if id == "GATEWAY" then "client -> server: bypass path client -> server"
      else "client -> server: path client -> server"
    ensure (result.evidence.contains path) "The bypass report lost its concrete path."

private def validationTests : IO Unit := do
  let config ← read "secure"
  let q ← query config "AVAILABLE"
  reject (Check.checkTraffic config { q with id := "UNLISTED" } https)
    "An unlisted query produced traffic assurance."
  reject (Check.checkTraffic config { q with request := "bob-read" } https)
    "An altered query produced traffic assurance."
  reject (Check.checkTraffic { config with requirements := [] } q https)
    "An invalid configuration produced traffic assurance."
  reject (Check.checkTraffic config q { destinationPorts := some ⟨20, 10⟩ })
    "An empty traffic class passed by vacuity."
  reject (Check.checkTraffic config q https 0) "An exhausted cell budget produced assurance."
  let cells := (config.trafficPartition https).cellCount
  reject (Check.checkTraffic config q https (cells - 1)) "An insufficient cell budget produced assurance."
  let exact ← unwrap (Check.checkTraffic config q https cells)
  ensure exact.value "The exact cell budget must permit a complete check."
  let many := { config with
    devices := config.devices ++ [⟨"other-server", "services", "server"⟩]
    requirements := [{ q with target := .zone "services" }] }
  let manyQuery ← query many "AVAILABLE"
  let result ← unwrap (Check.checkTraffic many manyQuery https)
  ensure (!result.value) "The traffic class skipped a selected endpoint pair."

private def directAgreementTests : IO Unit := do
  let config ← hiddenAddressConfig
  let selected : Match := {
    source := some ⟨167772161, 32⟩
    destination := some ⟨167772160, 30⟩
    protocol := some Protocol.tcp
    sourcePorts := some (PortRange.single 50000)
    destinationPorts := some ⟨442, 444⟩ }
  for id in ["AVAILABLE", "IDENTITY", "GATEWAY"] do
    let q ← query config id
    let complete ← unwrap (Check.checkTraffic config q selected)
    let mut direct := true
    for destination in ([167772160, 167772161, 167772162, 167772163] : List Address) do
      for port in ([442, 443, 444] : List Port) do
        let header : Header := ⟨167772161, destination, Protocol.tcp, 50000, port⟩
        ensure (selected.accepts header) "The bounded oracle generated an unselected packet."
        let result ← unwrap (Check.evaluateAt config q header)
        direct := direct && result.value
    ensure (complete.value == direct) s!"Traffic classes disagree with exhaustive bounded checking for {id}."

def run : IO Unit := do
  fixtureTests
  hiddenPortTests
  hiddenAddressTests
  validationTests
  directAgreementTests
  IO.println "Traffic class tests passed."

end NetlibTest.Traffic
