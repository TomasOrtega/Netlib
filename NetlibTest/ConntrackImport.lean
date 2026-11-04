import Netlib.Import.Conntrack
import Netlib.Import.ConntrackNetlink

namespace NetlibTest.ConntrackImport

open Netlib Netlib.Packet Netlib.Import.Conntrack

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (label : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"Expected a conntrack XML input error: {label}")
  | .error _ => pure ()

private def tuple (direction source destination : String) (sport dport protocol : Nat)
    (metadata : String := "") : String :=
  let name := if protocol == 6 then "tcp" else "udp"
  s!"<meta direction=\"{direction}\"><layer3 protonum=\"2\" protoname=\"ipv4\"><src>{source}</src><dst>{destination}</dst></layer3><layer4 protonum=\"{protocol}\" protoname=\"{name}\"><sport>{sport}</sport><dport>{dport}</dport></layer4>{metadata}</meta>"

private def original : String := tuple "original" "10.0.0.2" "198.51.100.10" 50000 443 6
private def reply : String := tuple "reply" "198.51.100.10" "203.0.113.5" 443 40000 6
private def independent : String :=
  "<meta direction=\"independent\"><state>ESTABLISHED</state><timeout>60</timeout><mark>7</mark><secmark>8</secmark><use>1</use><id>123</id><assured/></meta>"

private def flow (first : String := original) (second : String := reply)
    (metadata : String := independent) : String :=
  s!"<flow>{first}{second}{metadata}</flow>"

private def document (flows : List String) : String :=
  "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<conntrack>\n" ++
    String.intercalate "\n" flows ++ "\n</conntrack>\n"

-- These fixtures follow the pinned formatter source; they are not native captures.
private def sourceDerived : String := document [flow]

private def parseFirst (text : String) : IO SourceEntry := do
  let snapshot ← unwrap (Snapshot.parse text)
  match snapshot.entries.head? with
  | some row => pure row
  | none => throw (IO.userError "The parsed conntrack snapshot is empty.")

private def positiveTests : IO Unit := do
  let snapshot ← unwrap (Snapshot.parse sourceDerived)
  ensure (snapshot.raw == sourceDerived && snapshot.entries.length == 1)
    "The conntrack snapshot lost source evidence."
  let row ← parseFirst sourceDerived
  ensure (row.index == 0 && row.line == 3 && row.raw == flow)
    "The conntrack row lost its index, line, or exact XML."
  ensure (String.ofList (sourceDerived.toList.drop row.offset |>.take (row.endOffset - row.offset)) == row.raw)
    "The source character span does not recover the exact XML row."
  ensure (row.sourcePath == "/conntrack/flow[0]" &&
    row.fieldPath "meta[@direction='original']/layer3/src" ==
      "/conntrack/flow[0]/meta[@direction='original']/layer3/src")
    "The row lost its source field path."
  let location ← match row.fieldSource "meta[@direction='original']/layer3/src" with
    | none => throw (IO.userError "The source-address field lost its provenance.")
    | some location => pure location
  ensure (location.line == 3 &&
    String.ofList (sourceDerived.toList.drop location.offset |>.take (location.endOffset - location.offset)) ==
      "<src>10.0.0.2</src>") "The source-address field span changed."
  ensure (row.entry.original == ⟨167772162, 3325256714, 6, 50000, 443⟩ &&
    row.entry.reply == ⟨3325256714, 3405803781, 6, 443, 40000⟩)
    "The conntrack tuple fields changed."
  ensure (row.entry.originalZone == 0 && row.entry.replyZone == 0 && row.entry.remainingTTL == 60)
    "The default zones or remaining timeout changed."
  ensure (row.metadata.tcpState == some "ESTABLISHED" && row.metadata.mark == some 7 &&
    row.metadata.secmark == some 8 && row.metadata.use == some 1 && row.metadata.id == some 123 &&
    row.metadata.assured && !row.metadata.unreplied)
    "The visible conntrack metadata changed."
  ensure (snapshot.model.check &&
    snapshot.model.translate 0 row.entry.original == some row.entry.reply.reverse &&
    snapshot.model.translate 0 row.entry.reply == some row.entry.original.reverse &&
    (snapshot.model.lookup 1 row.entry.original).isNone)
    "The imported tuple model has incorrect directional lookup."
  let udpOriginal := tuple "original" "10.0.0.3" "192.0.2.53" 53000 53 17
    "<counters><packets>18446744073709551615</packets><bytes>300</bytes></counters>"
  let udpReply := tuple "reply" "192.0.2.53" "203.0.113.5" 53 41000 17
    "<counters><packets>0</packets><bytes>0</bytes></counters>"
  let udpIndependent :=
    "<meta direction=\"independent\"><timeout>0</timeout><unreplied/></meta>"
  let secondFlow := flow udpOriginal udpReply udpIndependent
  let two ← unwrap (Snapshot.parse (document [flow, secondFlow]))
  ensure (two.entries.map SourceEntry.index == [0, 1] && two.entries.map SourceEntry.line == [3, 4])
    "The snapshot reordered rows or changed their provenance."
  let udp ← match two.entries[1]? with
    | some row => pure row
    | none => throw (IO.userError "The UDP row was lost.")
  ensure (udp.entry.remainingTTL == 0 && udp.entry.original.protocol == Protocol.udp &&
    udp.metadata.tcpState.isNone && udp.metadata.unreplied && !udp.metadata.assured &&
    udp.metadata.originalCounters == some ⟨18446744073709551615, 300⟩ &&
    udp.metadata.replyCounters == some ⟨0, 0⟩)
    "The UDP timeout, counters, or marker evidence changed."
  let noMarkers ← parseFirst (sourceDerived.replace "<assured/>" "")
  ensure (!noMarkers.metadata.assured && !noMarkers.metadata.unreplied)
    "Absent markers supplied status evidence."
  for state in ["NONE", "SYN_SENT", "SYN_RECV", "ESTABLISHED", "FIN_WAIT", "CLOSE_WAIT",
      "LAST_ACK", "TIME_WAIT", "CLOSE", "SYN_SENT2"] do
    let row ← parseFirst (sourceDerived.replace "ESTABLISHED" state)
    ensure (row.metadata.tcpState == some state) "A supported TCP state was lost."
  let row ← parseFirst (sourceDerived.replace "<timeout>60</timeout>" "<timeout>4294967295</timeout>")
  ensure (row.entry.remainingTTL == 4294967295) "The maximum timeout was not preserved."
  let _ ← unwrap (Snapshot.parse (sourceDerived.replace "\n" "\r\n"))
  let _ ← unwrap (Snapshot.parse (sourceDerived.replace "<assured/>" "<assured></assured>"))
  let _ ← unwrap (Snapshot.parse (sourceDerived.replace
    "protonum=\"6\" protoname=\"tcp\"" "protoname = \"tcp\" protonum = \"6\""))
  pure ()

private def zoneTests : IO Unit := do
  let global := independent.replace "<timeout>60</timeout>" "<timeout>60</timeout><zone>7</zone>"
  let withOriginal := original.replace "</layer4>" "</layer4><zone>9</zone>"
  let withReply := reply.replace "</layer4>" "</layer4><zone>11</zone>"
  let row ← parseFirst (document [flow withOriginal withReply global])
  ensure (row.entry.originalZone == 9 && row.entry.replyZone == 11 &&
    row.metadata.originalZone == some 9 && row.metadata.replyZone == some 11 &&
    row.metadata.zone == some 7) "The directional zones did not override the global zone."
  let row ← parseFirst (document [flow withOriginal reply global])
  ensure (row.entry.originalZone == 9 && row.entry.replyZone == 7)
    "The reply zone did not fall back to the global zone."
  let row ← parseFirst (document [flow original reply global])
  ensure (row.entry.originalZone == 7 && row.entry.replyZone == 7)
    "The global zone did not apply in both directions."
  let zoneZero := original.replace "</layer4>" "</layer4><zone>0</zone>"
  let row ← parseFirst (document [flow zoneZero reply global])
  ensure (row.entry.originalZone == 0 && row.entry.replyZone == 7)
    "An explicit zone zero was treated as missing."
  let symmetric := tuple "reply" "10.0.0.2" "198.51.100.10" 50000 443 6 "<zone>1</zone>"
  let _ ← unwrap (Snapshot.parse (document [flow original symmetric independent]))
  let secondZone := independent.replace "<timeout>60</timeout>" "<timeout>60</timeout><zone>1</zone>"
  let sameTuples ← unwrap (Snapshot.parse (document [flow, flow original reply secondZone]))
  ensure (sameTuples.entries.length == 2) "Separate zones were collapsed."

private def syntaxTests : IO Unit := do
  for (label, text) in [
      ("empty stdout", ""), ("whitespace stdout", " \n"),
      ("empty root", document []), ("missing declaration", "<conntrack/>"),
      ("wrong encoding", sourceDerived.replace "utf-8" "utf-16"),
      ("truncated root", sourceDerived.replace "</conntrack>" ""),
      ("truncated tag", sourceDerived.replace "</conntrack>" "</conntrack"),
      ("mismatched tag", sourceDerived.replace "</conntrack>" "</flow>"),
      ("extra closing tag", sourceDerived ++ "</conntrack>"),
      ("multiple roots", sourceDerived ++ "<conntrack/>"),
      ("text before root", "x" ++ sourceDerived),
      ("text after root", sourceDerived ++ "x"),
      ("text in root", sourceDerived.replace "<conntrack>" "<conntrack>x"),
      ("comment", sourceDerived.replace "<conntrack>" "<conntrack><!--comment-->"),
      ("processing instruction", sourceDerived.replace "<conntrack>" "<conntrack><?x?>"),
      ("DTD", sourceDerived.replace "<conntrack>" "<!DOCTYPE conntrack><conntrack>"),
      ("CDATA", sourceDerived.replace "<src>10.0.0.2</src>" "<src><![CDATA[10.0.0.2]]></src>"),
      ("entity", sourceDerived.replace "10.0.0.2" "10.0.0.&#50;"),
      ("bad empty tag", sourceDerived.replace "<assured/>" "<assured/ >"),
      ("adjacent attributes", sourceDerived.replace "\"2\" protoname" "\"2\"protoname"),
      ("single quoted attribute", sourceDerived.replace "\"original\"" "'original'"),
      ("unquoted attribute", sourceDerived.replace "\"original\"" "original"),
      ("duplicate attribute", sourceDerived.replace
        "direction=\"original\"" "direction=\"original\" direction=\"reply\""),
      ("unsupported attribute", sourceDerived.replace "<flow>" "<flow id=\"1\">"),
      ("root attributes", sourceDerived.replace "<conntrack>" "<conntrack version=\"1\">"),
      ("wrong root", sourceDerived.replace "conntrack>" "connections>"),
      ("leaf child", sourceDerived.replace "<mark>7</mark>" "<mark><value>7</value></mark>"),
      ("leaf attributes", sourceDerived.replace "<mark>" "<mark name=\"mark\">"),
      ("marker content", sourceDerived.replace "<assured/>" "<assured>1</assured>") ] do
    reject (Snapshot.parse text) label

private def validationTests : IO Unit := do
  for (label, text) in [
      ("missing meta", document [flow original "" independent]),
      ("duplicate meta", document [flow (original ++ original) reply independent]),
      ("unknown direction", sourceDerived.replace "direction=\"original\"" "direction=\"both\""),
      ("unknown layer", sourceDerived.replace "</layer4>" "</layer4><layer5/>"),
      ("missing address", sourceDerived.replace "<src>10.0.0.2</src>" ""),
      ("duplicate address", sourceDerived.replace "<src>10.0.0.2</src>" "<src>10.0.0.2</src><src>10.0.0.3</src>"),
      ("invalid address", sourceDerived.replace "10.0.0.2" "10.0.0.256"),
      ("noncanonical address", sourceDerived.replace "10.0.0.2" "10.0.0.02"),
      ("IPv6 family", sourceDerived.replace "protonum=\"2\"" "protonum=\"10\""),
      ("wrong family name", sourceDerived.replace "protoname=\"ipv4\"" "protoname=\"ipv6\""),
      ("unsupported protocol", sourceDerived.replace "protonum=\"6\"" "protonum=\"1\""),
      ("wrong protocol name", sourceDerived.replace "protoname=\"tcp\"" "protoname=\"udp\""),
      ("mismatched protocols", document [flow original
        (reply.replace "protonum=\"6\" protoname=\"tcp\"" "protonum=\"17\" protoname=\"udp\"") independent]),
      ("UDP with TCP state", sourceDerived.replace
        "protonum=\"6\" protoname=\"tcp\"" "protonum=\"17\" protoname=\"udp\""),
      ("unknown TCP state", sourceDerived.replace "ESTABLISHED" "AUTHORIZED"),
      ("missing timeout", sourceDerived.replace "<timeout>60</timeout>" ""),
      ("duplicate timeout", sourceDerived.replace "<timeout>60</timeout>" "<timeout>60</timeout><timeout>60</timeout>"),
      ("duplicate marker", sourceDerived.replace "<assured/>" "<assured/><assured/>"),
      ("oversize port", sourceDerived.replace "<sport>50000</sport>" "<sport>65536</sport>"),
      ("oversize timeout", sourceDerived.replace "<timeout>60</timeout>" "<timeout>4294967296</timeout>"),
      ("oversize mark", sourceDerived.replace "<mark>7</mark>" "<mark>4294967296</mark>"),
      ("oversize id", sourceDerived.replace "<id>123</id>" "<id>4294967296</id>"),
      ("oversize zone", sourceDerived.replace "<timeout>60</timeout>" "<timeout>60</timeout><zone>65536</zone>"),
      ("negative value", sourceDerived.replace "<timeout>60</timeout>" "<timeout>-1</timeout>"),
      ("fractional value", sourceDerived.replace "<timeout>60</timeout>" "<timeout>1.5</timeout>"),
      ("leading zero", sourceDerived.replace "<timeout>60</timeout>" "<timeout>060</timeout>"),
      ("missing counter", sourceDerived.replace "</layer4>" "</layer4><counters><packets>1</packets></counters>"),
      ("oversize counter", sourceDerived.replace "</layer4>"
        "</layer4><counters><packets>18446744073709551616</packets><bytes>0</bytes></counters>"),
      ("duplicate flow", document [flow, flow]),
      ("same-direction collision", document [flow,
        flow original (reply.replace "40000" "40001") independent]),
      ("cross-direction collision", document [flow,
        flow (reply.replace "direction=\"reply\"" "direction=\"original\"")
          (original.replace "direction=\"original\"" "direction=\"reply\"") independent]),
      ("symmetric directional keys", document [flow original
        (original.replace "direction=\"original\"" "direction=\"reply\"") independent]) ] do
    reject (Snapshot.parse text) label
  for event in ["new", "update", "destroy"] do
    reject (Snapshot.parse (sourceDerived.replace "<flow>" s!"<flow type=\"{event}\">"))
      s!"event row {event}"
  for field in ["labels", "helper", "secctx", "timestamp", "start", "stop", "deltatime",
      "status", "confirmed", "srcnat", "dstnat", "offload", "unknown"] do
    reject (Snapshot.parse (sourceDerived.replace "<assured/>" s!"<assured/><{field}/>"))
      s!"unsupported metadata {field}"
  match Snapshot.parse (document [flow, (flow).replace "<timeout>60</timeout>" "<timeout>-1</timeout>"]) with
  | .ok _ => throw (IO.userError "The malformed second row was accepted.")
  | .error message =>
    ensure ((message.splitOn "/conntrack/flow[1] line 4:").length > 1)
      "The parse error lost its source row and line."

private def capturedTests : IO Unit := do
  let source ← IO.FS.readFile "examples/conntrack/native/conntrack.xml"
  let xml ← unwrap (Snapshot.parse source)
  let raw ← unwrap (Import.ConntrackNetlink.Snapshot.parse
    (← IO.FS.readFile "examples/conntrack/native/netlink.json"))
  ensure (xml.entries.length == 4 && raw.entries.length == 4 && xml.model.check && raw.model.check)
    "The genuine native dumps lost visible records or contain ambiguous keys."
  ensure ((xml.entries.filter (·.entry.original.protocol == Protocol.tcp)).length == 2 &&
    (xml.entries.filter (·.entry.original.protocol == Protocol.udp)).length == 2)
    "The genuine snapshot lost TCP or UDP coverage."
  for row in xml.entries do
    let other ← match raw.entries.find? (fun candidate =>
        candidate.entry.flow.originalZone == row.entry.originalZone &&
          candidate.entry.flow.original == row.entry.original) with
      | none => throw (IO.userError "A genuine XML tuple is missing from the raw capture.")
      | some candidate => pure candidate
    ensure (row.entry == other.entry.flow && row.metadata.id == other.id &&
      row.metadata.mark == other.mark && row.metadata.use == other.use)
      "The genuine XML and raw captures disagree on tuples or shared metadata."
    ensure (row.metadata.assured == other.status.testBit 2 &&
      row.metadata.unreplied == !other.status.testBit 1)
      "The genuine XML marker evidence differs from its raw status."
    ensure (row.entry.reply.destinationEndpoint == ⟨3405803777, 40000⟩ &&
      row.entry.originalZone == 0 && row.entry.replyZone == 0)
      "The genuine flows did not preserve their shared public endpoint."
    ensure (xml.model.translate 0 row.entry.original == some row.entry.reply.reverse &&
      xml.model.translate 0 row.entry.reply == some row.entry.original.reverse &&
      raw.model.translate 0 row.entry.original == some row.entry.reply.reverse)
      "The imported genuine tuple association changed."
    ensure (String.ofList (source.toList.drop row.offset |>.take (row.endOffset - row.offset)) == row.raw)
      "The genuine XML row lost its exact source span."
  let observations ← unwrap (Import.Json.parse
    (← IO.FS.readFile "examples/conntrack/native/packets.json"))
  let packets ← unwrap ((← unwrap (observations.getObjVal? "packets")).getArr?)
  ensure (packets.size == 6) "The genuine socket observations lost packet exchanges."
  for packet in packets do
    let original ← unwrap (Import.PacketFields.header (← unwrap (packet.getObjVal? "original")))
    let wire ← unwrap (Import.PacketFields.header (← unwrap (packet.getObjVal? "wire")))
    let reply ← unwrap (Import.PacketFields.header (← unwrap (packet.getObjVal? "reply")))
    let restored ← unwrap (Import.PacketFields.header (← unwrap (packet.getObjVal? "restored")))
    ensure (xml.model.translate 0 original == some wire && xml.model.translate 0 reply == some restored)
      "The frozen tuple projection differs from a genuine socket observation."

def run : IO Unit := do
  positiveTests
  zoneTests
  syntaxTests
  validationTests
  capturedTests
  IO.println "Conntrack XML snapshot import tests passed."

end NetlibTest.ConntrackImport
