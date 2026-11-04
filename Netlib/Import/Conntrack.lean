import Netlib.Import.IPv4
import Netlib.Protocol.FlowNAT

/-!
# Visible conntrack XML snapshots

The reference formatter is conntrack-tools 1.4.9 with libnetfilter_conntrack 1.1.1.
The supported command is `conntrack -L -f ipv4 -o xml` (optionally `xml,id`).
XML records omit the full status mask. Marker presence is evidence, not authorization.
Tuple pairs do not establish that native NAT hooks perform the modeled translation.
Producer version, namespace, capture success, completeness, and time remain external evidence.
-/

namespace Netlib.Import.Conntrack

open Packet

def sourceVersion : String := "conntrack-tools-1.4.9/libnetfilter_conntrack-1.1.1"
def sourceURL : String :=
  "https://www.netfilter.org/pub/libnetfilter_conntrack/libnetfilter_conntrack-1.1.1.tar.xz"

structure Counters where
  packets : Nat
  bytes : Nat
  deriving Repr, BEq, DecidableEq

structure Metadata where
  tcpState : Option String
  mark : Option Nat
  secmark : Option Nat
  use : Option Nat
  id : Option Nat
  zone : Option Nat
  originalZone : Option Nat
  replyZone : Option Nat
  originalCounters : Option Counters
  replyCounters : Option Counters
  assured : Bool
  unreplied : Bool
  deriving Repr, BEq, DecidableEq

structure SourceField where
  path : String
  line : Nat
  offset : Nat
  endOffset : Nat
  deriving Repr, BEq, DecidableEq

/-- Source spans use character offsets, with an exclusive end. -/
structure SourceEntry where
  entry : Protocol.FlowNAT.Entry
  index : Nat
  line : Nat
  offset : Nat
  endOffset : Nat
  raw : String
  metadata : Metadata
  fields : List SourceField
  deriving Repr, BEq, DecidableEq

namespace SourceEntry

def sourcePath (row : SourceEntry) : String := s!"/conntrack/flow[{row.index}]"

def fieldPath (row : SourceEntry) (field : String) : String := s!"{row.sourcePath}/{field}"

def fieldSource (row : SourceEntry) (field : String) : Option SourceField :=
  row.fields.find? (·.path == row.fieldPath field)

end SourceEntry

structure Snapshot where
  entries : List SourceEntry
  raw : String
  deriving Repr, BEq, DecidableEq

def Snapshot.model (snapshot : Snapshot) : Protocol.FlowNAT.Snapshot :=
  ⟨snapshot.entries.map SourceEntry.entry⟩

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def white (char : Char) : Bool :=
  char == ' ' || char == '\t' || char == '\r' || char == '\n'

private def splitWhile (predicate : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | char :: rest =>
    if predicate char then
      let (front, suffix) := splitWhile predicate rest
      (char :: front, suffix)
    else ([], char :: rest)

private structure Cursor where
  remaining : List Char
  consumed : List Char := []
  line : Nat := 1
  offset : Nat := 0

private def Cursor.advance (cursor : Cursor) : Cursor :=
  match cursor.remaining with
  | [] => cursor
  | char :: rest =>
    { remaining := rest, consumed := char :: cursor.consumed,
      line := if char == '\n' then cursor.line + 1 else cursor.line,
      offset := cursor.offset + 1 }

private def consume : List Char → Cursor → Except String Cursor
  | [], cursor => .ok cursor
  | char :: rest, cursor => do
    require (cursor.remaining.head? == some char) s!"Unexpected XML at line {cursor.line}."
    consume rest cursor.advance

private def untilChar (delimiter : Char) (chars : List Char) (cursor : Cursor) : String × Cursor :=
  let rec loop : List Char → Cursor → List Char → String × Cursor
    | [], cursor, reversed => (String.ofList reversed.reverse, cursor)
    | char :: rest, cursor, reversed =>
      if char == delimiter then (String.ofList reversed.reverse, cursor)
      else loop rest cursor.advance (char :: reversed)
  loop chars cursor []

private def nameChar (char : Char) : Bool :=
  ('a' ≤ char && char ≤ 'z') || ('A' ≤ char && char ≤ 'Z') ||
    ('0' ≤ char && char ≤ '9') || char == '_' || char == '-'

private def attributes : Nat → List Char → List (String × String) →
    Except String (List (String × String))
  | 0, _, _ => .error "XML attribute bound exhausted."
  | fuel + 1, chars, previous => do
    let (_, chars) := splitWhile white chars
    if chars.isEmpty then return previous.reverse
    let (key, rest) := splitWhile nameChar chars
    require (!key.isEmpty) "Invalid XML attribute name."
    let key := String.ofList key
    require (!(previous.map Prod.fst).contains key) s!"Duplicate XML attribute: {key}."
    let (_, rest) := splitWhile white rest
    let rest ← match rest with
      | '=' :: rest => pure rest
      | _ => throw "An XML attribute requires an equals sign."
    let (_, rest) := splitWhile white rest
    let rest ← match rest with
      | '"' :: rest => pure rest
      | _ => throw "An XML attribute requires double quotes."
    let (value, rest) := splitWhile (· != '"') rest
    require (value.all (fun c => nameChar c)) "Unsupported XML attribute value."
    let rest ← match rest with
      | '"' :: rest => pure rest
      | _ => throw "Unterminated XML attribute."
    require (rest.isEmpty || rest.head?.any white) "XML attributes require whitespace."
    attributes fuel rest ((key, String.ofList value) :: previous)

private inductive Tag where
  | start (name : String) (attributes : List (String × String)) (closed : Bool)
  | stop (name : String)

private def tag (text : String) : Except String Tag := do
  let chars := text.toList
  require (!chars.isEmpty) "Empty XML tag."
  require (!(chars.head?.any white)) "Whitespace before an XML tag name."
  match chars with
  | '/' :: rest =>
    let (name, rest) := splitWhile nameChar rest
    require (!name.isEmpty && rest.all white) "Invalid XML closing tag."
    return .stop (String.ofList name)
  | _ =>
    let (closed, body) := match chars.reverse with
      | '/' :: rest => (true, rest.reverse)
      | _ => (false, chars)
    let (name, rest) := splitWhile nameChar body
    require (!name.isEmpty) "Unsupported XML declaration, entity, or comment."
    require (rest.isEmpty || rest.head?.any white) "XML attributes require whitespace."
    let attrs ← attributes (rest.length + 1) rest []
    return .start (String.ofList name) attrs closed

private structure Element where
  name : String
  attributes : List (String × String)
  text : String
  children : List Element
  line : Nat
  offset : Nat
  endOffset : Nat
  raw : String
  deriving Inhabited

private structure Frame where
  name : String
  attributes : List (String × String)
  chunks : List String := []
  children : List Element := []
  line : Nat
  offset : Nat

private def fieldSources : Nat → Element → String → List SourceField
  | 0, _, _ => []
  | fuel + 1, element, path =>
    { path, line := element.line, offset := element.offset, endOffset := element.endOffset } ::
      element.children.flatMap (fun child =>
        let label := match child.attributes with
          | [("direction", direction)] => s!"{child.name}[@direction='{direction}']"
          | _ => child.name
        fieldSources fuel child s!"{path}/{label}")

private def Frame.finish (frame : Frame) (after : Cursor) : Element :=
  { name := frame.name, attributes := frame.attributes, text := String.join frame.chunks.reverse,
    children := frame.children.reverse, line := frame.line, offset := frame.offset,
    endOffset := after.offset,
    raw := if frame.name == "flow" then
      String.ofList ((after.consumed.take (after.offset - frame.offset)).reverse) else "" }

private def attach (element : Element) (frames : List Frame) (roots : List Element) :
    List Frame × List Element :=
  match frames with
  | [] => ([], element :: roots)
  | parent :: parents => ({ parent with children := element :: parent.children } :: parents, roots)

private def scan : Nat → Cursor → List Frame → List Element → Except String (List Element)
  | 0, _, _, _ => .error "XML token bound exhausted."
  | fuel + 1, cursor, frames, roots => do
    match cursor.remaining with
    | [] =>
      require frames.isEmpty "Unclosed XML element."
      return roots.reverse
    | '<' :: _ =>
      let start := cursor
      let cursor := cursor.advance
      let (body, cursor) := untilChar '>' cursor.remaining cursor
      require (cursor.remaining.head? == some '>') "Unterminated XML tag."
      let cursor := cursor.advance
      let (frames, roots) ← match ← tag body with
        | .stop name => do
          match frames with
          | [] => throw "An XML closing tag has no opening tag."
          | frame :: parents =>
            require (frame.name == name) s!"Mismatched XML closing tag: {name}."
            pure (attach (frame.finish cursor) parents roots)
        | .start name attrs closed => do
          require (frames.length < 8) "Unsupported XML nesting depth."
          let frame : Frame :=
            { name, attributes := attrs, line := start.line, offset := start.offset }
          if closed then pure (attach (frame.finish cursor) frames roots)
          else pure (frame :: frames, roots)
      scan fuel cursor frames roots
    | _ =>
      let (text, after) := untilChar '<' cursor.remaining cursor
      require (!(text.toList.any (fun c => c == '&' || c == '>')))
        "XML entities and unescaped delimiters are unsupported."
      match frames with
      | [] =>
        require (text.toList.all white) "Text outside the XML root."
        scan fuel after frames roots
      | frame :: parents =>
        scan fuel after ({ frame with chunks := text :: frame.chunks } :: parents) roots

private def parseXML (text : String) : Except String Element := do
  let chars := text.toList
  require (!chars.isEmpty) "An empty stdout payload is not an attested empty conntrack snapshot."
  let cursor : Cursor := { remaining := chars }
  let (_, cursor) := untilChar '<' chars cursor
  require (chars.take cursor.offset |>.all white) "Text before the XML declaration."
  let cursor ← consume "<?xml version=\"1.0\" encoding=\"utf-8\"?>".toList cursor
  let roots ← scan (cursor.remaining.length + 1) cursor [] []
  match roots with
  | [root] => return root
  | _ => throw "Require exactly one conntrack XML root."

private def plain (element : Element) : Except String Unit :=
  require element.attributes.isEmpty s!"Unsupported attributes on {element.name}."

private def fields (element : Element) (allowed : List String) : Except String Unit := do
  require (element.text.toList.all white) s!"Unexpected text in {element.name}."
  let mut seen : List String := []
  for child in element.children do
    require (allowed.contains child.name) s!"Unsupported {element.name} field: {child.name}."
    require (!seen.contains child.name) s!"Duplicate {element.name} field: {child.name}."
    seen := child.name :: seen

private def child (element : Element) (name : String) : Except String Element :=
  match element.children.find? (·.name == name) with
  | some value => .ok value
  | none => .error s!"Missing {element.name}/{name}."

private def leaf (element : Element) : Except String String := do
  plain element
  require element.children.isEmpty s!"Unexpected nested content in {element.name}."
  return element.text

private def decimal (text : String) (bound : Nat) : Except String Nat := do
  require (!text.isEmpty && text.length ≤ 20 && text.toList.all Char.isDigit)
    "Require bounded unsigned decimal digits."
  require (!(text.length > 1 && text.startsWith "0")) "Leading zeroes are unsupported."
  match text.toNat? with
  | none => throw "Invalid decimal value."
  | some number =>
    require (number < bound) s!"Decimal value exceeds its bound {bound - 1}."
    return number

private def number (element : Element) (bound : Nat) : Except String Nat :=
  leaf element >>= (decimal · bound)

private def optional (element : Element) (name : String)
    (parse : Element → Except String α) : Except String (Option α) :=
  match element.children.find? (·.name == name) with
  | none => .ok none
  | some value => some <$> parse value

private def attributesExactly (element : Element) (expected : List (String × String)) :
    Except String Unit :=
  require (element.attributes.length == expected.length &&
    expected.all (fun attr => element.attributes.contains attr))
    s!"Unsupported attributes on {element.name}."

private def counters (element : Element) : Except String Counters := do
  plain element
  fields element ["packets", "bytes"]
  return ⟨← number (← child element "packets") 18446744073709551616,
    ← number (← child element "bytes") 18446744073709551616⟩

private structure Tuple where
  header : Header
  zone : Option Nat
  counters : Option Counters

private def tuple (element : Element) : Except String Tuple := do
  fields element ["layer3", "layer4", "zone", "counters"]
  let layer3 ← child element "layer3"
  attributesExactly layer3 [("protonum", "2"), ("protoname", "ipv4")]
  fields layer3 ["src", "dst"]
  let source ← IPv4.parseAddress (← leaf (← child layer3 "src"))
  let destination ← IPv4.parseAddress (← leaf (← child layer3 "dst"))
  let layer4 ← child element "layer4"
  let protocol ←
    if layer4.attributes.contains ("protonum", "6") then do
      attributesExactly layer4 [("protonum", "6"), ("protoname", "tcp")]
      pure Protocol.tcp
    else do
      attributesExactly layer4 [("protonum", "17"), ("protoname", "udp")]
      pure Protocol.udp
  fields layer4 ["sport", "dport"]
  let sourcePort ← number (← child layer4 "sport") 65536
  let destinationPort ← number (← child layer4 "dport") 65536
  let some sourcePort := Port.ofNat? sourcePort | throw "Invalid source port."
  let some destinationPort := Port.ofNat? destinationPort | throw "Invalid destination port."
  let zone ← optional element "zone" (number · 65536)
  let observedCounters ← optional element "counters" counters
  return ⟨⟨source, destination, protocol, sourcePort, destinationPort⟩, zone, observedCounters⟩

private def marker (element : Element) : Except String Unit := do
  let text ← leaf element
  require text.isEmpty s!"Unexpected content in {element.name} marker."

private def state (element : Element) : Except String String := do
  let value ← leaf element
  require (["NONE", "SYN_SENT", "SYN_RECV", "ESTABLISHED", "FIN_WAIT", "CLOSE_WAIT",
    "LAST_ACK", "TIME_WAIT", "CLOSE", "SYN_SENT2"].contains value) "Unsupported TCP state."
  return value

private def sourceEntry (element : Element) (index : Nat) : Except String SourceEntry := do
  require (element.name == "flow") "Only flow snapshot rows are supported."
  plain element
  require (element.text.toList.all white) "Unexpected text in flow."
  let mut seen : List String := []
  for block in element.children do
    require (block.name == "meta") s!"Unsupported flow field: {block.name}."
    require (block.attributes.length == 1) "A meta block requires exactly one direction."
    let direction ← match block.attributes with
      | [("direction", value)] => pure value
      | _ => throw "A meta block requires a direction attribute."
    require (["original", "reply", "independent"].contains direction)
      s!"Unsupported meta direction: {direction}."
    require (!seen.contains direction) s!"Duplicate meta direction: {direction}."
    seen := direction :: seen
  let getMeta (direction : String) : Except String Element :=
    match element.children.find? (·.attributes.contains ("direction", direction)) with
    | none => .error s!"Missing {direction} metadata."
    | some block => .ok block
  let original ← tuple (← getMeta "original")
  let reply ← tuple (← getMeta "reply")
  let independent ← getMeta "independent"
  fields independent ["state", "timeout", "mark", "secmark", "zone", "use", "id", "assured", "unreplied"]
  let remainingTTL ← number (← child independent "timeout") 4294967296
  let tcpState ← optional independent "state" state
  require (tcpState.isNone || original.header.protocol == Protocol.tcp)
    "TCP state on a non-TCP tuple."
  let zone ← optional independent "zone" (number · 65536)
  let assured ← optional independent "assured" marker
  let unreplied ← optional independent "unreplied" marker
  let mark ← optional independent "mark" (number · 4294967296)
  let secmark ← optional independent "secmark" (number · 4294967296)
  let use ← optional independent "use" (number · 4294967296)
  let id ← optional independent "id" (number · 4294967296)
  return {
    entry := {
      original := original.header
      reply := reply.header
      originalZone := (original.zone.orElse fun _ => zone).getD 0
      replyZone := (reply.zone.orElse fun _ => zone).getD 0
      remainingTTL }
    index
    line := element.line
    offset := element.offset
    endOffset := element.endOffset
    raw := element.raw
    fields := fieldSources 8 element s!"/conntrack/flow[{index}]"
    metadata := {
      tcpState, mark, secmark, use, id, zone
      originalZone := original.zone
      replyZone := reply.zone
      originalCounters := original.counters
      replyCounters := reply.counters
      assured := assured.isSome
      unreplied := unreplied.isSome } }

/-- Parse the supported nonempty XML slice, then validate all directional lookup keys. -/
def Snapshot.parse (text : String) : Except String Snapshot := do
  let root ← parseXML text
  require (root.name == "conntrack") "Require a conntrack XML root."
  plain root
  require (root.text.toList.all white) "Unexpected text in conntrack."
  require (!root.children.isEmpty) "Require a nonempty visible conntrack snapshot."
  let mut entries : List SourceEntry := []
  for (element, index) in root.children.zipIdx do
    match sourceEntry element index with
    | .error message => throw s!"conntrack /conntrack/flow[{index}] line {element.line}: {message}"
    | .ok entry => entries := entry :: entries
  let snapshot : Snapshot := { entries := entries.reverse, raw := text }
  match snapshot.model.validate with
  | .error message => throw s!"conntrack snapshot: {message}"
  | .ok () => return snapshot

end Netlib.Import.Conntrack
