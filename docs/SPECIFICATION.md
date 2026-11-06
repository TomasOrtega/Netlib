# Netlib specification

## Source and purpose

The source is DARPA-SN-27-13, *Verification and Compliance Checking for
Natural-Language Network Requirements (FastVacc)*. The notice date is
October 29, 2026. The supplied file is `DARPA-SN-27-13-2.pdf`.
Page references below include the cover of this six-page PDF.

The notice requests research into requirements, abstract reasoning, concrete
networks, and compliance reports. This repository implements that direction as a
Lean library and a finite network checker. The [scope limits](#scope-limits)
identify research problems that this implementation does not resolve.

## Requirements traceability

| RFI concern | Netlib contract | Evidence |
| --- | --- | --- |
| Formal intermediate system (pp. 3–4, question 1) | Give requirements explicit syntax and semantics. Connect evaluation to those semantics. | Definitions and theorems in `Netlib/Core/Logic.lean`. |
| Abstract reasoning before configuration (p. 3) | Analyze consistency and implication without a concrete network. | `Netlib/Core/Reasoning.lean`, `Netlib/Policy/Analysis.lean`, and `Netlib/Policy/Observation.lean`. |
| Redundancy (pp. 2–3) | Preserve every policy model after removal of a redundant requirement. | Preservation theorems and examples with duplicate or equivalent requirements. |
| Incompleteness (p. 3) | Find supplied security goals that the requirements do not imply. | Countermodels for missing goals. |
| Architecture proofs (p. 4, question 3) | Prove reusable results for isolation, mediation, refinement, and network changes. | `Netlib/Network/Basic.lean` and `Netlib/Network/Architecture.lean`. |
| Clusters and extensions (pp. 2–3) | Represent several physical nodes by one abstraction. State the refinement assumptions for each security result. | Cluster examples and explicit theorem hypotheses. |
| Exhaustive evaluation (p. 3) | Evaluate the complete declared network and every relevant endpoint pair. | `Netlib/Model/Config.lean`, `Netlib/Check/Compliance.lean`, and boundary tests. |
| Verifiable evaluation (pp. 2–3) | Validate path and cut certificates against a graph with only declared nodes. | `validPath_sound`, `validCut_sound`, and `check_compliant_iff`. |
| Understandable output (p. 2) | Keep source IDs. Report the proposition, status, and useful evidence. | `Main.lean`, `Netlib/Check/Render.lean`, and passing and failing examples. |
| Translation fidelity (p. 4, question 4) | Accept a specified controlled language. Reject unsupported input. | `Netlib/Policy/Language.lean`, parser rejection tests, and formalized examples. |
| Evaluation quality and scale (p. 4, question 4) | State the scope and resource limits. Supply reproducible examples. | Local builds, tests, and documented algorithm costs. |

## Network model

The original `check` command uses a finite set of nodes and directed links. Each node has
an ID, a zone, and a role. A named group can contain several nodes. Each link
permits steps for a service.

A matching enabled link permits a step for the selected service. An absent,
disabled, or nonmatching link permits no step. Reachability includes a path with
zero steps from a node to itself.

Reachability describes permitted paths in the model. It does not guarantee
physical packet delivery. The model excludes congestion, timing, device faults,
routing convergence, and omitted protocol state.

The JSON input must contain these arrays and fields:

| Array | Fields for each entry |
| --- | --- |
| `devices` | `id`, `zone`, `role` |
| `links` | `from`, `to`, `service`, `enabled` |
| `groups` | `name`, `members` |

The importer rejects unknown fields, missing fields, duplicate IDs, invalid links,
and empty groups. A link service of `*` permits every named service.
JSON input also rejects duplicate decoded object keys at every nesting level.
A requirement must name one service and cannot use `*`.

## Packet models

The Lean library also provides packet models. A header contains source and
destination IPv4 addresses, a protocol number, and source and destination ports.
Addresses use 32 bits. Protocol numbers use 8 bits. Ports use 16 bits.

A packet match can select source and destination prefixes, a protocol, and port
ranges. An absent match field accepts every value for that field.
Address prefixes include `/0` and `/32`. Reversed port bounds accept no port.

An access control list evaluates rules in order. The first matching rule supplies
the permit or deny action. An explicit default applies when no rule matches.
The standard `allows` function uses a deny default.

Routing selects the longest matching destination prefix. Equal prefix lengths
preserve the first route. A route supplies a next hop or a drop action.
Routing and access control lists define packet-specific forwarding networks.

The `dataplane` and `traffic` forwarding models are stateless.
They keep the same header throughout a path.
They exclude dynamic routing protocols.
The `dataplane` command imports these models through JSON schema 1.
The `traffic` command checks every header selected by a packet match.
It partitions headers at every ACL, route, and selection boundary.
Proved decision equality lifts the finite representative checks to the complete selected class.
The [traffic guide](TRAFFIC.md) defines its interface and cell budget.

Each forwarding step needs four controls:

1. An enabled physical link joins declared nodes.
2. The longest matching route selects that link's target.
3. The link's first matching ACL rule permits the packet.
4. The request policy permits any step through an enforcement gateway.

An empty ACL denies the packet.
A missing route or a selected drop route permits no next hop.
A route cannot create physical adjacency.
Each query fixes one header and one named request throughout its path.
Every selected endpoint pair must satisfy the query.

The importer rejects invalid references, duplicate identities, unsupported fields, and invalid numeric values.
An empty selection cannot satisfy a query.
`Config.finiteNetwork_eq_model` connects executable edges to the composed library graph.
`DataPlane.Check.Report.compliant_iff` connects the final status to every original query.
The [data-plane guide](DATAPLANE.md) defines the complete schema.

## Header-changing forwarding

`Netlib/Packet/Rewrite.lean` provides constant overwrites of address, protocol, and port fields.
An absent overwrite preserves its incoming value.
Sequential rewrites compose, and flow reversal exchanges the two endpoints.
Reply inversion requires the original endpoint as explicit information.

`Netlib/Packet/Transfer.lean` defines guards, rewrites, and their ordered composition.
Its forwarding graph retains both the current node and current header.
Physical links still constrain each modeled program step.
Header-preserving programs embed the existing forwarding graph semantics.

The `transfer` command checks one initial packet.
`Netlib/Import/TransferConfig.lean` imports declared nodes, guarded links, constant rewrites, and one query.
Each link tests the incoming header, applies its rewrite, and arrives at its fixed target.
Matching links remain permitted alternatives.
Separate stage nodes express processing order.
Routing lookup and Linux hook order are not implicit.

Reachability permits any resulting header at the target node.
Isolation excludes every resulting header.
Mediation requires a gateway on every path, including rewritten paths.
Gateway endpoints and zero-step reachability retain their existing meanings.
`Netlib/Check/Transfer.lean` checks packet-state path and cut certificates.
Its returned status agrees exactly with the stated query.

Initial values and overwrite constants generate a finite header universe.
Closure proofs cover every modeled path from the initial packet.
The default budget is 4,096 device/header states.
The checker counts that product before constructing the states.
Budget exhaustion or certificate rejection returns an error without an answer.
There is no theorem guaranteeing successful search completion for every valid input.
All-header class verification across rewrites remains future work.

## Timed flow state and source NAPT

`Netlib/Protocol/Conntrack.lean` grants one TCP or UDP flow and its exact reverse reply until its deadline.
Time is monotone.
Closing a flow removes its grant.
`Netlib/Protocol/NAT.lean` maps an inside endpoint and protocol to a supplied public endpoint.
The mapping can serve several remote peers.
Each peer still needs a separate live reverse-flow grant.

Accepted transitions preserve live entries and unique mapping keys.
An accepted outbound packet has a source-endpoint rewrite.
Its exact reverse reply restores the inside endpoint while the grant remains live.
Public-endpoint collisions and changes to an existing live mapping cause denial.
Expiration removes old entries.
Closing a flow can leave its mapping in place.
Flush clears grants and mappings while preserving the clock.

The `nat-trace` command audits every supplied packet observation from an empty initial state.
`Netlib/Check/NATTrace.lean` obtains outbound permission from the declared packet-intent policy.
The input cannot supply an authorization result.
Each finding compares observed output with independently computed model output.
Correct denials can pass.
Every matched restored reply has an earlier outbound source permitted by that policy.
Accurate observations, complete traces, and clock interpretation remain assumptions.

Allocations and expiration deadlines remain supplied inputs.
The default budget covers 100,000 policy partition cells, not trace processing.
`Netlib/Import/PacketFields.lean` reads bounded packet fields and dotted IPv4 addresses.
Its codec and the trace parser have runtime tests rather than parser-correctness proofs.

`Netlib/Theory/NATReuse.lean` proves a freshness limit after public-alias reuse.
Different inside endpoints can produce identical external reply headers for the same remote endpoint and protocol.
No deterministic decision using only that header and the same current state can distinguish them.
A proved trace expires the old flow, reuses its alias, and delivers the delayed reply to the new inside endpoint.
The current mapping and grant safety invariant still holds.
That invariant therefore cannot establish rejection of retired replies.

These local flow models exclude checksums, fragmentation, TCP flags, sequence windows, and transport handshakes.
The separate byte-derived forwarding model below adds selected UDP checksum and TTL semantics.
They do not establish allocator correctness, public-address ownership, Linux conntrack correspondence, or complete RFC conformance.
The Linux deployment adapter retains its stateless subset.
The [stateful guide](STATEFUL.md) defines the input formats and evidence limits.

## Native conntrack snapshots

The separate `Protocol.FlowNAT` model represents reported original and reply TCP/UDP tuples in one implicit capture namespace.
Each direction has its effective zone and complete header as a lookup key.
Validation rejects duplicate combined keys, including original/reply collisions across entries.
Different remote peers may share the same public endpoint.
This differs from the local NAPT model's globally unique public-endpoint/protocol mapping.

A matching original tuple projects to the reversed reply tuple.
A matching reply tuple projects to the reversed original tuple.
Validated lookup and round-trip theorems establish those operations over the supplied table.
A miss means the table contains no association; it does not establish packet denial.
Remaining timeout is evidence in whole seconds.
Zero remains valid evidence because the native export truncates fractional seconds.
The model does not evolve time, allocate new flows, refresh timeouts, or validate transport packets.

`Protocol.NetfilterNAT` adds source/destination NAT flags to each tuple pair.
The flags select which endpoint fields change and reverse their roles for reply processing.
Compatibility requires unchanged endpoints wherever a NAT flag is absent.
The status-selected rewrite is proved equal to the tuple projection under those conditions.
This contract covers the complete modeled connection boundary, without an implicit per-hook execution order.

The `conntrack` command checks every supplied original tuple against a declared packet-intent policy.
It accepts the supported conntrack-tools XML slice or full-status collector JSON.
Its passing status means that all reported original tuples satisfy the certified intent.
The report preserves row order, source locations or indices, and available native IDs.
It does not establish the policy that admitted a flow or the provenance of a restored reply.
An empty raw snapshot has no rows to violate this condition; the XML slice requires a nonempty snapshot.

XML preserves original/reply tuples and selected metadata from conntrack-tools 1.4.9 with libnetfilter_conntrack 1.1.1.
Its status markers do not provide the full native status mask or establish NAT activation.
The `conntrack-map` command therefore requires full-status collector JSON.
It reports a frozen association and projected header, rather than a firewall-admission result.

The full-status profile requires confirmation and checks NAT initialization and tuple compatibility.
It rejects expected, sequence-adjustment, dying, template, NAT-clash, explicit-helper, offload, and unknown status bits.
Rejecting the explicit-helper bit does not establish absence of automatically assigned helper extensions.
Additional native attributes remain in raw evidence without modeled payload semantics.
Missing timeout metadata is unsupported in this profile; optional ID, mark, and use fields can remain unknown.

`scripts/capture_conntrack.py` sends a fixed IPv4 Netlink dump request inside the isolated native environment.
It retains the request and complete messages while rejecting malformed, interrupted, truncated, or lost dumps.
The requested IPv4 family filter is supported.
Capture budgets and transport errors produce no successful partial output.
The Lean JSON importer retains these bytes as hexadecimal evidence without independently decoding them.
The collector's decoding and the agreement between raw and structured fields remain reviewed implementation boundaries.

The retained native example has four flows and six successful socket round trips on Ubuntu kernel `6.8.0-117-generic`.
Both TCP and UDP reuse public `203.0.113.1:40000` across two remote peers.
Structured records agree with the retained Netlink bytes and XML tuples and IDs.
Socket metadata records server wire headers and client restored headers.
The joined reply tuples are derived from reversed server wire tuples, without independent pre-NAT reply IP captures.
The collision and late-drop examples record no replies and no additional visible confirmed records.
These observations support the demonstrated cases, without proving kernel C refinement, complete table coverage, or general packet delivery.
Upstream Linux v6.8 supplies the source reference; distribution patches remain outside that correspondence.
The [conntrack guide](CONNTRACK.md) defines the commands, supported records, and capture procedure.

## Stateful filters and fixed NAT snapshots

`Packet.StatefulACL` combines the existing header match with an optional connection-state selection.
The first matching rule supplies the action, followed by the explicit fallback.
The five labels are `new`, `established`, `related`, `invalid`, and `untracked`.
The matcher has independent propositional semantics.
Specialization at one fixed label gives an equivalent ordinary ACL for every header.
Unguarded rules recover the original stateless behavior.
The label is an input to this filter model; it does not establish transport state or authorization.

The shared nftables syntax decoder preserves the original stateless adapter's forward-only subset.
That adapter still rejects state predicates and NAT statements.
`Import.NftablesStateful` separately accepts one IPv4 filter chain at forward or postrouting.
It preserves ordered header/state matches, the chain policy, handles, and source expression indices.
Its compiler agrees with structured source evaluation for every supplied label and header.

`Import.NftablesNAT` accepts one IPv4 table with destination NAT at prerouting priority -100 and source NAT at postrouting priority 100.
Both chains have NAT type and accept policy.
Each rule has supported header matches and one fixed address target with an optional port.
The first matching target stops its chain, including an identity target.
A miss preserves the header, and an omitted target port preserves its incoming value in this model.
Ranges, maps, dynamic targets, masquerade, extra chains, and side effects are unsupported.

The structured NAT compiler preserves source-rule matching and endpoint translation.
Its candidate records the original tuple and reversed translated tuple, with NAT flags derived from endpoint changes.
Compatibility follows under explicit protocol, zone, and distinct-key conditions.
This candidate is a proposal, not proof of native allocation or port preservation.
The replay assumes that a confirmed fixed proposal is the applicable native allocation.
It rejects confirmation collisions instead of simulating native remapping or race recovery.

## Ordinary forwarded-packet lifecycle

`Protocol.ConntrackLifecycle` gives ordinary forwarded packets an explicit hook sequence.
A confirmed record contains a compatible tuple pair and a seen-reply flag.
Lookup uses the complete input header and zone once, before the stages below.
A miss requires a separate unconfirmed candidate whose original tuple and zone match the input.
Intermediate packet rewrites retain that attachment.

Processing follows this order:

1. Classify the attached original or reply and mark seen-reply for an existing valid reply.
2. Apply destination NAT, including inverse source NAT for replies.
3. Select the longest matching destination route using that translated destination.
4. Evaluate the stateful forward filter on the packet after destination NAT.
5. Apply source NAT, including inverse destination NAT for replies.
6. Evaluate the late filter on the packet after source NAT.
7. Confirm a fresh candidate only if all prior stages permit it and its combined keys remain unique.

A missing next hop, a forward denial, or a late denial produces no output.
A fresh drop leaves the confirmed table unchanged.
An existing reply can mark seen-reply even when one of those later stages drops it.
The next original can therefore be established without an application receiving that first reply.
These transitions do not infer a completed transport handshake.

An existing original is `new` before seen-reply and `established` afterward.
Both cases reuse the stored binding with `fresh = false`.
Changing NAT rules does not recreate that binding merely because the current original is `new`.
A leading established permit can also preserve old traffic after the filter starts denying new traffic.
Structural validity proves compatible records and unique lookup keys, without establishing the current policy's authorization of every stored flow.

`Protocol.ConntrackOperations` adds an explicit erase operation by either directional key.
It removes both directions of the associated record and preserves structural validity.
Its execution trace binds every returned result to the exact operation and preceding table.
Packet calls can select different policy snapshots within that ordered trace.
The model does not infer an erase from a later table observation.

The `lifecycle` checker accepts schema 1 with routing, named configurations, an initial table, and ordered events.
Routing imports the pinned iproute2 6.19.0 main-table slice and trusted device bindings.
Each configuration contains separate forward, late, and fixed NAT snapshots.
The forward chain must use the forward hook.
The late chain must use postrouting with priority greater than 100 and less than 2147483647.
This places it after source NAT and before modeled confirmation.

The checker derives a candidate from the selected NAT table only on a lookup miss.
The input cannot supply a candidate or an authorization Boolean.
Observations do not update the modeled table.
Every packet observation compares classification, freshness, both stage headers, next hop, disposition, and final output.
Every supplied state observation compares both tuples, zones, NAT flags, and seen-reply after the operation.
Timeout seconds, IDs, marks, use counts, other supported status metadata, and record order do not affect that comparison.
Native records and metadata remain retained evidence.

Root `initial: null` declares an empty initial table.
Event `state: null` records no table observation; it does not assert an empty table.
An initial native table normalizes timeout evidence to zero for replay without asserting expiration.
`Report.covered` preserves all events in order.
`Report.compliant_iff` states exact agreement with the complete supplied observation list.
`Report.prefixes_valid` proves structural validity of every modeled prefix and the final table.
Observation mismatch gives a noncompliant report.
Malformed input, unsupported execution, or confirmation collision gives an error without a compliance answer.

The native lifecycle evidence records nine UDP packets, 30 traced chain visits, and eight table observations.
All ten replay operations, including one erase, match the model.
The capture shows combined DNAT/SNAT stages, fresh drops before confirmation, cached unreplied bindings after a NAT change, and seen-reply after a dropped reply.
The independent evidence verifier checks retained trace, socket, and raw snapshot records.
These cases do not validate the complete TCP lifecycle or formally refine kernel C.

The domain requires valid unfragmented IPv4 TCP/UDP packets whose transport tracker accepts the modeled attachment.
The protocol-number check does not establish transport validity.
TCP reopen, replacement, and `NF_REPEAT` are unsupported.
Expiry, concurrent changes, helpers, related traffic, offload, hidden clashes, and allocator or race recovery are also excluded.
The main-table route context and exclusive captured NAT/filter hook sequence must apply to the selected traffic.
Faithful observations and complete selected-traffic coverage remain assumptions.
The [lifecycle guide](LIFECYCLE.md) defines the schema, producer versions, and native evidence boundary.

## TCP framing and sequence foundations

The `tcp-segment` command does a check of all TCP segment bytes against supplied IPv4 pseudoheader addresses.
The `tcp-wire` command derives those addresses from checked untagged Ethernet and whole IHL-five IPv4 bytes.
The two commands use mandatory TCP checksum verification. A received zero word also requires verification.
Accepted bytes preserve received reserved bits, all eight flags, options, and the checksum word exactly.
Data Offset and structural option validation bound the header to twenty through sixty bytes.
Unknown well-formed TLVs remain unchanged.
The report gives the MSS placement result separately from structural acceptance.

The selected serial comparison uses unsigned forward distance strictly between zero and `2^31`.
Equality and exact half-space differences are incomparable.
The opaque sequence type has no global ordering instance.
Transitivity requires an explicit short span or a common bounded arc.
SYN and FIN each contribute one sequence position independently of later transport-state interpretation.

Certified rewriting keeps the transport control fields and payload. It uses the declared tuple and caller TTL and computes the two checksums again.
The reassembly byte adapter connects a supplied completed IPv4 packet to the checked TCP segment.
Fragment provenance remains a separate arrival and output-validity obligation.
These results establish no handshake, receive-window acceptance, acknowledgment validity, retransmission behavior, or native TCP classification.
The [TCP guide](TCP.md) states the commands, proofs, static evidence, and remaining transport obligations.

## TCP receive projection

The `tcp-receive` command evaluates raw IPv4 packets against an explicit pre-established endpoint seed.
The caller supplies the initial state and sent-byte buffer.
The caller assumes that the endpoint transmitted these buffer bytes.
The state contains a TCP tuple, receive capacity and bytes, and send cursors.
It must satisfy buffer bounds, an unscaled capacity limit, and the stated short-arc conditions.
The seed does not prove an earlier handshake or transmission.

The profile uses the four sequence tests and the selected RFC 5961 DATA defense with fixed `MAX.SND.WND = 65535`.
Supported data must start at `RCV.NXT`.
Its byte count must not exceed the free receive window.
An old ACK inside the permitted arc can accompany new data.
Advancing ACKs remove the exact sent-byte prefix and preserve `SND.NXT`.
ACK requests remain separate from emitted packets.

Out-of-profile control fields and options require an unsupported continuation before ordinary sequence processing.
This scope classification prevents zero-window RST and URG inputs from becoming false supported rejections.
Partial overlap and out-of-order storage also remain unsupported.
Replay retains the processed prefix and stops at its first unsupported result.
The [receive-state guide](TCP_RECEIVE.md) defines the command, bounds, static evidence, and remaining endpoint obligations.

## TCP application events

The `tcp-endpoint` command extends the bounded receive model with writes, sends, reads, and peer-window history.
Only successful new-data sends advance the send-buffer end.
Selected timer retries produce checked output for an earlier outstanding range without adding stream bytes.
Reads return the exact receive-buffer prefix and increase local free space.
Peer-window updates use the pre-ACK state and the selected freshness formula.
Strictly old ACKs cannot update that window.
Duplicate ACKs can update it when the freshness condition holds.

Policy permission, effective MSS, IP size limits, and seed origin remain explicit inputs.
The paired application-prefix proof also requires earlier successful peer outputs and a bounded finite epoch.
The command does not establish those external delivery conditions from checksums alone.
Replay stops at the first unsupported event and retains the unprocessed suffix.
The [application guide](TCP_APPLICATION.md) gives the event schema, proof contract, and remaining obligations.
The automatic [receive-gap extension](TCP_RECEIVE_GAPS.md) holds non-overlapping future payloads and exact queued duplicates.
The [sparse gateway extension](TCP_SPARSE_ADMISSION.md) records disjoint observed ranges without delaying accepted packet output.
It separates covered prefix, greatest end, unique bytes, and cumulative ACK position.
Source indices derive from actual committed observations and survive exact checkpoint installation.
The campus checker automatically retains [packet custody](PACKET_CUSTODY.md) for each actual endpoint output and gateway emission.
Assignment and delivery consume pending identities; copies and drops are explicit actions.
The [bounded-round proof](TCP_ROUND_PROGRESS.md) gives completion of one fresh range by `9 * B` evaluated slots under its fixed-clock action and service contract.
Progress with additional copies, losses, advancing clocks, held gaps, and gateway transfer remains open.
The [enabled-operation proofs](TCP_ENABLED_OPERATIONS.md) derive current endpoint and gateway actions from their actual preceding states.
Queued headers retain their original receipt clocks and are processed in sequence order.
Novel input bytes, ordered release, and cumulative ACK retirement have separate counts.

## TCP startup histories

The `tcp-handshake` command accepts local configuration and ordinary startup events, without established endpoint seeds.
It constructs checked SYN and SYN,ACK outputs and the final ACK.
Every successful receipt must match an earlier output and its selected direct or certified tuple path.
The active seed becomes available on valid SYN,ACK receipt.
The passive seed becomes available only on valid final ACK receipt.

The three selected messages have no application data.
SYN and SYN,ACK support selected MSS/NOP/EOL semantics; the final ACK has no options.
An absent MSS option derives peer default 536.
Actual positive offers determine directional limits, bounded separately by the local IP send limit.
Window-history fields come from the accepted startup messages.
The active initialization selects the explicit RFC 1122 interpretation.

Unsupported phases or omitted RFC actions stop replay.
The command distinguishes supported partial histories from a completed model exchange.
The [startup guide](TCP_HANDSHAKE.md) gives the event schema, byte-history conditions, and connection to the application theorem.
The [MSS guide](TCP_MSS.md) states receive-capability evidence, automatic peer selection, and exact gateway/checkpoint preservation.
The [recovery guide](TCP_RECOVERY.md) adds explicit local clocks, bounded timer retries, exact range admission, and Karn checks.
The [ACK guide](TCP_ACK.md) adds checked receive and read causes, strict sub-500-ms local response bounds, and receive-window suppression.
ACK assurance retains actual packet output and gateway provenance on the same campus history.

## Authenticated campus TCP execution

The `campus-tcp` command combines current EAP evidence, imported policy, ingress attachments, routing, tracked NAT, and checked endpoint operations.
Assignment selects an earlier actual endpoint output and allocates immutable work.
Service uses the current stored configuration, actual early guard, selected TCP admission history, and common lifecycle pipeline.
Receipt bytes must equal an earlier actual gateway emission.
The input cannot supply replacement established states, source packets, forwarding tuples, or delivery paths.

Comparisons use the authentication prefix at service.
They never replace the actual installed policy decision.
Logoff followed by current denial prevents later gateway output, including with a cached binding.
Previously received bytes remain available to the application.

The base path has one live modeled gateway and one bounded ordinary TCP connection.
Native TCP replication and tracker refinement remain separate obligations.
The [campus TCP guide](CAMPUS_TCP.md) gives the timeline schema, assurance contract, and static evidence.

An optional standby deployment adds [planned TCP transfer](CAMPUS_TCP_TRANSFER.md) to the same command and global timeline.
Gateway-specific installation and ingress operations use local configurations and interface lifetimes.
Assignments derive an immutable gateway selection from the output producer's current route owner.
Checkpoint installation requires an actual reachable source cut, paused assignments, no pending primary work, and an empty target pair.
The target namespace lifetime must match the declared standby and its current guard.
Separate route, fence, and resume operations retain the existing endpoint states.
The final application proof uses actual service through each selected gateway.
This is modeled planned transfer; native migration and automatic recovery remain open.

## Byte-derived NAT and TTL forwarding

The `wire-forward` command extends the selected IPv4 UDP wire profile with tracked forwarding.
Input and observed output tuples come from raw Ethernet bytes through `Check.Wire`.
Supplied headers cannot replace decoded packet fields.
The profile requires untagged Ethernet without FCS, IPv4 IHL five, no fragmentation, and UDP length equal to the entire IP payload.
Zero UDP checksum denotes omission rather than successful checksum validation.
The [wire guide](WIRE.md) defines the codecs and checksum boundary.

`Protocol.UDPRewrite` takes a validated decoded packet, a translated tuple, and a chosen TTL.
It preserves the complete UDP payload, TOS, identification, and DF.
The generated packet has the chosen addresses, ports, and TTL, with canonical IPv4 checksum and no link padding.
An omitted UDP checksum stays omitted.
A present checksum is recomputed over the translated pseudoheader and preserved payload.
A computed zero is transmitted as 65535.
Input bounds prove the rewritten packet remains encodable, including the maximum selected IPv4 length.
Encoding therefore cannot fail after modeled confirmation.

`Protocol.WireForwarding` validates the input, attaches tracking, applies destination NAT, and selects the destination route.
A missing route produces a route drop.
For a selected route, TTL zero or one stops before forward filtering, source NAT, late filtering, and confirmation.
An existing reply retains its earlier seen-reply update after TTL expiry.
A fresh expired candidate does not enter the confirmed table.
Longer-TTL processing reuses the existing lifecycle's filter, NAT, and confirmation semantics.
Each emission preserves payload and contains the actual decremented TTL.
Its IPv4 checksum and any present UDP checksum are valid.
UDP checksum omission remains explicit through translation.

`Check.WireForwarding` retains the shared route, NAT, filter, and ordinary-table parsers.
Their earlier adapter semantics remain unchanged.
The checker derives candidates only on lookup misses and processes every supplied event in order.
Observation mismatches do not modify computed state.
Every finding remains linked to its actual preceding table and model step.
`Report.compliant_iff` establishes complete supplied-observation agreement.
`Trace.valid` proves structural table validity throughout the modeled replay.
`Report.observed_output_payload` proves compliant observed outputs preserve the input payload and decrement TTL.

Output comparison covers decoded IP fields and the complete UDP datagram, including its checksum word.
Both raw packets must pass their independent wire validation.
IPv4 checksums and present UDP checksums are validated.
Ethernet adjacency, link padding, and the IPv4 checksum's zero representation are separate from that equality.
Null intermediate fields mean unobserved values.
Null output asserts no selected UDP egress within the declared complete observation scope.
Table comparisons retain the existing tuple, zone, NAT-flag, and seen-reply projection.
Native IDs, order, and timeout evidence remain outside that projection.

`Examples.WireNATDeployment` connects these emissions to current scope permission and EAP readiness.
The input comes from a checked capture; the scope uses the computed post-destination-NAT header.
The theorem preserves exact payload and TTL effects without assuming a separate packet header.
It still requires the current native filter snapshot and the reviewed binding between the principal and packet class.
Global installation timing and source authenticity remain deployment assumptions.

The retained native experiment contains 17 IP frames: 14 UDP frames and three ICMP frames.
Four EAP stages distinguish missing authentication, missing credentials, permitted traffic, and cached denial after Logoff.
Additional probes cover an expired cached reply, a later real reply, targeted deletion, TTL zero through two, and UDP checksum omission.
ICMP observations remain evidence; the model does not generate those packets.
MTU handling, fragmentation, full transport behavior, expiry, concurrency, and kernel C refinement remain outside this profile.
The [wire forwarding guide](WIRE_FORWARDING.md) defines the schema, native cases, and assumptions.

## Effective MTU and fragment families

The `wire-mtu` command extends the whole-input UDP profile with effective-MTU decisions and output fragmentation.
It retains the earlier route, filter, NAT, and ordinary-table importers.
Each bound route next node requires a unique effective MTU between 68 and 65,535 bytes.
Device MTU alone need not establish that effective value.

Route selection precedes TTL expiry.
Oversized DF rejection follows TTL handling and precedes filtering, source NAT, and confirmation.
Both early rejections retain prepared tracking state without confirming fresh candidates.
A cached reply may retain its earlier seen-reply update.

Successful lifecycle output is split after translation and confirmation.
Nonfinal payload lengths are positive multiples of eight bytes.
Offsets describe a contiguous complete IP payload, including the UDP header.
Every fragment fits the selected effective MTU and has a valid IPv4 checksum.
The translated UDP checksum and payload remain exact across reconstruction.

Observed output is a complete Ethernet fragment array, or an empty array for no selected UDP output.
Strict reassembly accepts capture reordering and rejects gaps, overlaps, duplicates, mixed metadata, and incomplete families.
UDP validation follows complete reassembly.
Comparison checks normalized fragment packets and the entire recovered datagram.
Compliant replay transfers payload, TTL, and MTU bounds to the observed family.

The shared replay certificate preserves computed state across mismatching observations.
The deployment theorem connects fragmented output to current EAP readiness and valid scope credentials.
Current Logoff policy denies complete output families even through cached mappings.

The native evidence includes a 1,200-byte socket payload split into three parts and reassembled by a normal UDP receiver.
Separate cases record DF rejection, TTL priority, exact-MTU DF output, cached state retention, and omitted UDP checksums.
ICMP packets are retained as native evidence, while their generation remains outside the Lean model.
Input fragmentation, gateway reassembly, options, PMTU discovery, offloads, resource failures, and kernel refinement remain separate work.
The [MTU guide](MTU.md) defines the schema, proofs, and complete assumptions.

## Generated ICMP forwarding errors

The `wire-icmp` command adds generated Time Exceeded and Fragmentation Needed to the selected whole-input UDP profile.
It reuses the existing transit processing, NAT configuration, filters, and ordinary-table observations.
Rejection kind and reported MTU come from the computed transit outcome.
Return routing supplies effective MTU, initial source, and output TTL.
Identification is an explicit nondeterministic choice rather than a proved allocator result.

The model checks source, destination, configured broadcast addresses, and link-group suppression.
It constructs a post-destination-NAT quotation and restores its tuple through related NAT in the opposite connection direction.
Incremental checksum arithmetic proves valid translation without requiring unquoted application bytes.
Inverse translation restores the exact input quote packet and UDP checksum.
The IPv4 header checksum can use either valid zero representation.

The quote budget is the smaller of input length and `min(returnMTU, 576) - 28`.
Quoted IPv4 and UDP lengths continue to describe the original complete input.
The quotation parser accepts truncation, while complete quoted UDP datagrams receive checksum validation.
An incomplete quote establishes no whole-transport checksum validity.

Generated control packets traverse separate related-state output and late policies.
Their processing preserves the transit model's table effects.
Fresh rejected candidates remain unconfirmed, and earlier cached reply observations survive.
A control error does not establish application authorization because TTL and DF rejection precede forward filtering.

Replay schema one adds `icmpProfile`, per-configuration `output` and `icmpLate` snapshots, and per-packet `icmpOutput` arrays.
The checker derives semantic fields independently of the supplied identification choice.
It checks complete output presence, wire validity, quotation semantics, and table observations in order.
Observed mismatches cannot replace computed state.

The fresh capture retains twelve ICMP errors and checks related output hooks, NAT correction, quotation boundaries, TOS, and checksum omission.
The selected profile requires disabled rate limiting and successful allocation and transmission.
This generation profile excludes received errors and PMTU-cache evolution; the next profile connects both.
Input fragments, extensions, concurrency, and kernel implementation refinement remain separate work.
The [ICMP guide](ICMP.md) records the schema, proofs, native recipe, and environmental assumptions.

## Received ICMP and connected-host PMTU

The `wire-related` command processes received UDP-related ICMP errors through confirmed-table lookup, NAT, routing, policy, and output fragmentation.
It validates outer IPv4 and ICMP checksums while retaining untrusted quoted fields.
Quoted checksums and declared lengths are not repaired or accepted as original-datagram validity evidence.
Raw flag bits are preserved; noninitial quoted fragments cannot associate in this selected path.

Association reverses the quoted tuple and looks it up with its zone.
The outer destination must match the found tuple's destination.
A missing association creates no candidate.
Every received-error result preserves the complete frozen connection table, including seen-reply and timeout fields.
Timeout evolution and concurrent changes remain excluded.

Related destination translation precedes routing and TTL/DF handling.
Forward and late policies evaluate related state.
Rejected error packets produce no further ICMP error.
Permitted output decrements only the outer TTL and may form a certified fragment family.
The quotation restores the sender-boundary tuple while preserving application bytes, declarations, flags, checksum omission, and checksum residue.

The `host-pmtu` command derives connected UDP feedback from those forwarded error bytes.
It checks the quoted socket tuple and Fragmentation Needed kind, then applies the configured Linux PMTU update.
The model includes the minimum floor, locking, equal-update refresh threshold, exception lifetime, and expiration.
Positive-lifetime updates cannot raise the effective PMTU at that observation time.
Expired exceptions can restore the physical route MTU.

After pending errors are drained, DF send capacity requires application length plus 28 bytes within the current estimate.
The replay checks queries and send outcomes without using observations as state replacements.
The host feedback guard ignores the reporter address; matching forged errors can lower PMTU.
The selected model establishes association and state bounds, without establishing sender authenticity.

The four-namespace capture preserves EAP application checkpoints and adds a separate fixed-policy control suffix.
It records real downstream ICMP discovery, local oversized-send rejection, smaller UDP success, malformed quotations, and a forged-source reduction.
Only the final event using each post-episode table receives that native snapshot.
All computed prefixes retain their formal validity guarantee.
The [received-error guide](RECEIVED_ICMP.md) describes both schemas, observation attribution, proofs, and remaining scope.

## Ingress IPv4 queues and completion-time policy

The `wire-reassembly` command processes raw IPv4 arrivals before selected UDP forwarding.
Its queue keys include effective user, zone encoding, L3 master identity, source, destination, protocol, and identification.
Each model instance represents one network namespace.

The selected transition uses fixed queue expiry, MF trimming, source-dependent run grouping, duplicate suppression, and overlap destruction.
Accepted fragments supply the first header, ECN set, maximum size, and maximum DF size.
Completion requires exact byte coverage, first and last information, valid ECN, and a bounded reconstructed packet.
An incomplete oversized queue can persist until completion or expiry.

Incomplete arrivals cannot attach UDP, create NAT candidates, or change the ordinary table.
The completing event selects current forwarding policy.
Logoff or credential revocation installed before completion therefore governs the whole datagram.
Earlier buffering does not retain an older permission.

Reassembled packets retain their maximum fragment size for later output.
DF rejection uses that maximum under the selected Netfilter ignore-DF behavior.
The output cap is the smaller of that maximum and the outgoing route MTU.
The fragment-family contract supports 28-byte budgets and checks exact payload and metadata without selecting a kernel allocation path.
A fitting unreassembled whole input requires a single whole output.

The ICMP codec also accepts reassembly timeout type 11/code 1.
The timeout model selects expired queues and actual stored first-fragment bytes.
A locally assigned VIP can permit timeout ICMP even when the later destination-NAT route would forward the packet.
The selected timeout output profile requires a reverse-quote miss, invalid-state filtering, and no NAT rewrite.
Associated timeout output remains unsupported by that adapter.

Replay times and timeout values must share one declared clock unit.
Native projection uses monotonic nanoseconds and converts the namespace timeout from seconds.
Observation timestamps do not establish exact internal timer scheduling.
Pre-reassembly logging supplies immutable input bytes; deferred packet-socket observations retain explicit buffer-lifetime limitations.

The queue profile requires successful allocation and zero source-disorder distance control.
Memory-pressure eviction, positive disorder heuristics, concurrency, options, broader transport processing, and full kernel refinement remain open.
The [ingress guide](REASSEMBLY.md) records the selected semantics and evidence.

## Static stateful filter refinement

The `stateful-refines` command checks permission inclusion between two stateful source chains.
Every label and every modeled header is covered through ACL specialization and exact partitions.
The contexts include related, invalid, and untracked, even though the ordinary lifecycle only produces new and established.
A context in this comparison need not occur in a native history.

Both chains must have the same hook and priority.
The default budget is 100,000 header cells summed across all five labels.
A context mismatch or exhausted budget gives an error without a refinement answer.
A failed inclusion check returns a label and header permitted by the proposed stronger chain and denied by the weaker chain.
Theorems connect both successful inclusion and returned counterexamples to the structured source-chain semantics.

This is a static filter comparison.
It does not compare routing, NAT tables, allocations, stored bindings, or execution histories.
It does not prove revocation of old flows or a complete network upgrade contract.
Those claims require the relevant state transitions and intermediate-state obligations.

## Operational output exclusion

A late-filter barrier denies every header in a forbidden class for every modeled state label.
Its exact certificate includes policy and selection boundaries and preserves first-match order and explicit chain defaults.
A failed certificate has a concrete selected state/header context that the filter permits.
It need not be a packet in the supplied replay.

Every forwarded lifecycle output passed the late filter after both NAT stages.
The barrier therefore excludes the forbidden output class for fresh and cached bindings alike.
The theorem covers original and reply attachments without requiring deletion or a changed NAT allocation.
Ordered operations retain the result through packet calls and record deletion.
Certified upgrade snapshots supply the same contract when each packet pipeline selects one of those snapshots.

`lifecycle-blocks TRACE.json MATCH.json --from N` checks the complete replay and a selected event suffix.
`N` is a zero-based list position, including deletion events.
The suffix starts with the state produced by the full preceding replay.
The CLI requires at least one packet event in the suffix and rejects out-of-range positions.
It checks every late filter selected by suffix packet events; unused configurations are outside that check.
The default budget covers 100,000 partition cells across those events and all five state labels.
Repeated configurations are charged for every packet event.

The result separates the barrier certificate from replay agreement.
Success requires both.
The report proof then excludes the forbidden class from every supplied suffix output observation.
Prefix observation failures still prevent success.
The model exclusion theorem only needs the barrier certificate.

The forbidden class describes output headers after NAT.
It does not automatically describe a credential, user, session, or both directions of a connection.
Cutover follows effective barrier installation; packets already beyond the hook need a separate drain boundary.
The checker does not prove native install completion, barrier retention between observations, or absence of unreported configuration changes.
The [output exclusion guide](REVOCATION.md) states those obligations and the inherited lifecycle assumptions.

## Buffered admission and delivery

The buffered lifecycle composes tracked operations with an unbounded FIFO of output headers.
An operation first computes its tracker update and optional output.
Only that computed output enters the queue tail.
An explicit deletion or a dropped packet enqueues nothing.
Separate service events remove exactly the smaller of their declared capacity and the pending length.
They preserve the tracking table.

The queue theory tracks the prefix present at admission cutover.
Every later arrival must be outside the forbidden class.
Sufficient accumulated service clears the older prefix even if later arrivals exceed service and the total backlog keeps growing.
The final draining batch can still contain older forbidden packets.
The exclusion conclusion applies to service after that batch.

`buffered-lifecycle TRACE.json MATCH.json --from N --drained-at M` checks this contract with schema 1.
The root embeds a lifecycle input, initial queued headers, and an operation/service schedule.
Operations consume every embedded lifecycle event once, in order.
The schedule retains the modeled state reached by the complete prefix.
Optional pending lists and required served lists are observations, never model inputs for queue updates.
Null pending observations remain distinct from empty queues.

The admission suffix must be nonempty and include a packet operation.
The delivery boundary can be the end of the schedule.
Readiness requires all later packet configurations to retain the certified barrier and enough capacity to cover the computed admission backlog.
This is a sufficient capacity condition and need not find the earliest clean boundary.
A ready certificate proves a clean pending queue at the delivery boundary.
It also excludes selected later modeled service and arbitrary modeled continuations under retained barriers.
Agreement with the full replay transfers the result to supplied service observations.
Earlier forbidden deliveries remain in the report history.

The policy partition budget defaults to 100,000 cells across post-cutover packet operations and all five state labels.
It does not bound queue size or schedule length.
Service capacity is a declared model quantity; physical rate and elapsed time require separate premises.
Physical queue completeness, identity, placement, and order also require correspondence evidence.
The retained native UDP example demonstrates delayed delivery after barrier installation and a later packet's drop.
Its finite observations do not prove universal native FIFO behavior, a drain deadline, or kernel C refinement.
The [buffering guide](BUFFERING.md) records these assumptions and the source research.

## Stateful processing and shared execution

`Netlib/Packet/Processor.lean` models ordered packet processing with a shared store.
These compositional interfaces are Lean library definitions.
Each processor returns the next store and either an output packet or a drop.
Composition passes both the store and the packet to the next stage.
A drop skips later stages and retains earlier state updates.
Processor invariants must cover those drop results too.

`Netlib/Packet/Stateful.lean` gives forwarding vertices a node, header, and complete store.
A successful edge must use the exact store produced by its processor.
It cannot independently choose a store for the next hop.
Physical adjacency limits these steps.
Physical isolation, gateway mediation, and processor store invariants transfer to their paths.
Stateless processors retain their store and agree with the existing packet-transfer semantics.

This forwarding graph contains successful packet steps.
It does not account for every call or state change between packets.
`Netlib/Packet/ProcessorTrace.lean` supplies ordered executions for that purpose.
Its observations include calls that drop packets after changing the shared store.
An explicit ordered call list supplies the execution schedule.
Each valid finite observation trace agrees with the computed execution.
These are model executions. Actual event coverage and implementation correspondence still require evidence.

`Netlib/Packet/StatefulTrace.lean` projects each successful graph walk to its ordered processor observations.
The resulting execution retains the same initial and final stores and every hop's physical adjacency.
This is a one-way bridge from a valid walk.
It does not infer a walk from packet headers without the required intermediate stores.

`Netlib/Protocol/NATPipeline.lean` connects the local NAPT model to these processors.
ACLs can act before or after translation.
An earlier denial prevents the translation and grant update.
A later denial can leave the new mapping and grant installed.
A return-flow origin therefore identifies an earlier policy-permitted input, which may have dropped at a later stage.
State refinement preserves the underlying NAT updates while filtered packet outputs can differ.
Two successful translations restore their reverse reply in the opposite processing order.
This local NAPT pipeline does not define native Linux lifecycle behavior.

The campus NAPT example uses separate primary and standby stores on the duplex campus topology.
It proves management isolation, gateway mediation, store invariants, and session-controlled forwarding.
An accepted primary outbound call establishes the store used by its restored reply path.
After primary failure, physical connectivity alone cannot supply missing standby grants.
With an empty standby grant list, every modeled return to the client fails.

An exact copy of the accepted outbound state supplies a return path under each admissible single internal-node fault.
The fault model excludes independent link failures and keeps client/server endpoints live.
The copy is an explicit ideal operation before the fault.
The clock-preservation result requires the original clocks to agree.
Each path uses a static fault snapshot and fixed session and clock states.
Shared-alias ownership and suitable return routing remain assumptions.
The result establishes a permitted path, not physical delivery, temporal liveness, or routing convergence.
Replication protocols, delayed or stale copies, revocation, and packet freshness remain outside this example's guarantees.

## Request model

`Netlib/Security/ZeroTrust.lean` models a principal's operation on a resource.
A request policy supplies authentication and authorization functions.
Admission requires both results to be true. The model assumes that the supplied
functions describe the intended identity and permission checks.

An admitted request retains the base network and all its paths.
A denied request loses every link that enters or leaves the enforcement gateway
set. It retains links that avoid that set.

All selected sources and targets must lie outside the gateway set for the
denial-isolation equivalence. Under that assumption,
`denied_isolated_iff_mediated` proves that denial gives isolation exactly when
every base path visits a gateway. A surviving denied-request path must bypass
the gateway set. A bypass can therefore preserve unauthorized access.

A gateway still reaches itself through a zero-step path after denial.
The outside-endpoint condition prevents that case from invalidating the isolation
claim. Stronger request policies cannot introduce request paths.

The data-plane importer reads declared principals, identity results, and permission facts.
It does not query a live identity service.
These proofs do not establish cryptographic authentication or live enforcement behavior.

## Standards catalogue

Each source record contains the document, version, clause ID, and URL.
Each requirement also records its meaning, applicability, and assumptions.
Each finding preserves the requirement and its evidence.

The catalogue uses five finding statuses:

| Status | Meaning |
| --- | --- |
| Satisfied | The selected model condition holds under its assumptions. |
| Violated | The selected model condition fails. |
| Unsupported | The checker does not model the required property. |
| Missing evidence | The checker lacks a required input or observation. |
| Not applicable | The requirement does not concern the stated scope. |

Only satisfied and not-applicable findings can pass.
An empty report cannot pass.
Evidence completeness means that no finding is unsupported or missing evidence.
It does not mean that every requirement is satisfied.

## Enterprise Wi-Fi pilot

The strict hostapd importer covers one AP and one BSS from hostapd 2.12.
It preserves source lines and rejects unsupported configuration syntax.
Unknown fields, repeated fields, includes, multiple BSS declarations, and invalid numbers cause errors.
Reports hide the RADIUS shared-secret value.
The parser preserves SSID and shared-secret bytes.

The selected AP profile checks 12 explicit obligations.
Each obligation identifies a hostapd field or Campus WLAN 3.2.0 clause.
An AP setting establishes only its declared configuration condition.
It does not establish client behavior, negotiated algorithms, product approval, or operational assurance.

The deployment profile adds five fixed network requirements:

1. Permit selected guest HTTPS traffic to services.
2. Isolate guest traffic from the management network.
3. Mediate service paths through the boundary gateway.
4. Mediate service paths through the imported AP.
5. Isolate service traffic for the unauthenticated request.

The input cannot remove or reorder these queries.
The AP interface and bridge must match the deployment binding.
Exactly one modeled access point must have the bound identity.
That AP must belong to the enforcement group.

The report connects source clauses, imported settings, model queries, and checked path evidence.
Its 17 findings cover the selected AP and network obligations.
The separate coverage report identifies unsupported requirements and missing evidence.
The [Wi-Fi guide](WIFI.md) records the source versions, configuration fragment, and deployment assumptions.

## Session and 5G profile

The shared session model records identity results, a credential, a clock, and guarded admission.
Model transitions preserve its admission invariant.
Clock transitions cannot decrease time.
Credential changes and time changes clear the previous admission record.
Generic local revocation clears the current credential.
It does not maintain a persistent token blacklist.

The 5G profile checks a direct NF-instance service-request trace.
Its source is TS 33.501 version 19.5.0, clause 13.4.1.1.2.
Every observed admitted request must satisfy the selected guards.
The guards check identity, token presence, issuer, integrity, subject, audience, scope, and expiration.
Correct denied requests do not violate admission safety.
Valid token reuse remains permitted.

The trace supplies identity and integrity observations.
The model does not verify TLS certificates or token signatures.
It also assumes that the trace includes every actual service admission.
The selected procedure has no token-revocation step.
The profile rejects that event instead of inventing a standard requirement.

`FiveG.check_compliant_safe` establishes the guards for every observed admission in a passing report.
A separate coverage report identifies missing identity evidence, missing cryptographic evidence, and unsupported optional claims.
The [5G guide](FIVEG.md) defines the trace schema and exact procedure scope.

## EAP-derived authentication and admission

The EAP codec reads base Request, Response, Success, and Failure packets with bounded identifiers and lengths.
Request and Response payloads include a Type byte and opaque method data.
Terminal packets have a declared length of four.
Padding beyond declared lengths remains preserved and separate at each encapsulation layer.
Binary round-trip proofs cover structured encodings and reconstruction of arbitrary accepted bytes.
Hex and MAC text parsing remain tested implementations.

The selected EAPOL profile supports untagged Ethernet, versions 1 through 3, and EAP, Start, and Logoff bodies.
The checker binds a peer and authenticator MAC, checks destination consistency, and enforces message roles.
MAC equality does not establish source integrity.
Key, MKA, VLAN, and other unmodeled encapsulations produce errors.

Guarded authorization requires matching selected-method Request and Response identifiers, a corresponding terminal Success, and accepted current-round evidence for the expected principal.
The outer Identity remains untrusted bytes.
Method evidence can arrive before or after terminal Success.
Opaque TLS bytes alone do not establish cryptographic method acceptance.
The profile uses explicit local failclosed resets and unbounded local round tags.
Those tags are separate from wire identifiers and native producer-window labels.
Trusted evidence attribution and wire replay protection remain separate obligations.

The session bridge derives authentication from the guarded EAP state.
Its application events cannot directly set authentication.
Changed rounds or authorization results clear the previous credential and admission.
An application request still needs every current credential guard.
The configured-principal campus theorem uses the report's actual consumer and proves the selected admission's availability under each admitted internal-node fault.
Both modeled gateways share the current session state.
Native enforcement and distributed propagation remain outside that theorem.

The `eap` command checks schema 1 with context, link binding, and ordered events.
Raw frames, method results, credentials, clocks, and observed requests retain distinct roles.
Optional authorization observations and request outcomes cannot update model state.
A compliant report establishes agreement with all supplied observations, including correct denials.
The native examples record authentication observations only; application outcomes in tests are explicitly synthetic.

The wired capture retains 32 raw frames and sanitized hostapd/wpa_supplicant logs for TLS 1.3 success, Logoff, and server-name rejection.
Its verifier checks byte, fragment, identity-policy, producer-version, protected-success, and logical-state consistency.
It does not independently verify TLS cryptography, native current-round tagging, full IEEE 802.1X behavior, or physical port enforcement.
The [EAP guide](EAP.md) records the profile and evidence limits.
The original Wi-Fi coverage obligations remain unchanged.

## Native replication and fenced handoff

The `wire-failover` command checks whole IPv4 UDP executions across a primary and standby gateway.
Both ordinary tables and the selected external cache start empty.
A source packet establishes the primary's record before an explicit stage operation selects it from that computed table.

The selected replica carries normalized tuples, zone zero, NAT fields, and seen-reply state.
Commit validates a collision-free append into the standby table.
The configured positive timeout remains metadata without modeled aging.
Native destructive retry, replacement, and expiry remain outside this successful-installation profile.

Client and server route changes have separate ordered operations.
A later fence disables selected primary packet processing.
Every accepted packet names its current route owner and an unfenced gateway.
Its current configuration governs routing, filtering, NAT, and wire output.
The replica retains a binding without retaining an earlier policy permission.

Input IPv4 and output Ethernet bytes supply actual packet fields.
Optional observations compare both kernel tables and separately projected daemon cache attributes.
Observations never overwrite computed state.
Prefix provenance identifies the actual earlier stage and computed primary source for a committed record.
Matched output preserves payload, decrements TTL, and satisfies the current forward and late policies.

The native evidence requires received synchronization attributes, actual cache membership, and an observed target kernel record.
Transport acknowledgements and command success cannot replace those observations.
The evidence also checks complete rulesets, routes, command fences, endpoint results, and observer coverage.
Finite capture agreement does not establish automatic detection, reliable replication, convergence, split-brain prevention, or complete implementation refinement.
See [stateful failover](STATEFUL_FAILOVER.md) for the selected profile and source pins.

## Safe handoff with outstanding route assignments

The `wire-safe-handoff` command checks a protected ordinary IPv4 UDP flow across two gateways.
Both tables, replication cache, and outstanding work start empty.
An actual primary packet establishes the record selected by a later stage operation.
Collision-free commitment installs that selected binding before an endpoint route can select the standby.
The protected binding remains live without modeled aging or deletion.

Assignment records an endpoint route read and allocates a fresh ticket containing validated source bytes, gateway, direction, and operation epoch.
Lean calls this operation `assign`; JSON uses `admit`.
A separate `serve` operation selects an actual pending identity in arbitrary order.
Later route changes preserve the ticket's assigned gateway and input bytes.
Processing uses that gateway's current configuration, rather than the current endpoint route owner.
The epoch anchors the actual model prefix; it is not a native route-version field.

The protected-flow invariant requires valid tables, unique ticket identities, matching bindings, and ready, unfenced gateways for active routes and outstanding assignments.
Table validity alone does not imply this invariant or packet availability.
Handoff requires a ready, unfenced target.
Fencing requires both endpoint routes elsewhere and no pending ticket assigned to the fenced gateway.
Operation admissibility uses only conditions on the preceding state.
Progress constructs an actual successful step and proves preservation without assuming an accepted step or safe result.
Universal trace results cover every modeled admissible packet direction, repetition, retirement order, and control interleaving.

Both gateways may retain different seen-reply knowledge for the same binding.
An associated denied reply can update that local knowledge before an older ticket is processed.
Routing, live TTL, and current forward and late permits establish actual emission with the protected NAT target, unchanged payload, and one TTL decrement.
Policy denial instead preserves structural safety while withholding service.
Current-session conclusions require the assigned gateway's installed configuration to match the current certified session policy.
The separate synthetic EAP test demonstrates Logoff denial and the limit of a stale installed policy.

Every served ticket has an actual earlier assignment-prefix witness with exact stored bytes, identity, direction, gateway, and operation epoch.
Matched gateway input must equal those stored bytes.
Matched Ethernet output inherits their payload and TTL guarantees under the current policies.
Observed inputs, outputs, and table snapshots cannot replace computed state.
Successful commits likewise identify an earlier stage from an actual computed primary prefix.

The finite drain constructs exactly the initial target count of successful processing operations, including computed drops.
After both routes change, that sequence permits the final fence without a global FIFO assumption.
It proves no time bound, fairness, physical queue correspondence, or eventual delivery.
Route reads, processing steps, and configuration changes still require the declared linearization and stable packet hooks.
Native installation coherence, lifetime stability, observation completeness, and implementation refinement remain external premises.

The saved native example records 20 operations, seven datagrams, and six protected ticket identities.
It demonstrates old-route processing after both routes change, standby overtaking, current-policy denial, and fencing after selected work completes.
It supplies no native EAP enforcement claim.
See [safe handoff](SAFE_HANDOFF.md) for the schema, command, proof endpoints, and evidence boundaries.

## Fragment admission composition

`Protocol.FragmentAdmission` composes installed coarse admission, reassembly, installed full-datagram admission, and ordinary tracked MTU forwarding.
The coarse selector contains only IPv4 addresses and protocol, with numeric ingress evaluated separately.
Its typed guard excludes transport reads.
The strict source importer preserves raw priority `-450` and rejects transport predicates even when a complete-header equivalence check would accept them.

The model keeps the existing user/vif domain inside an explicit namespace lifetime.
The completing input supplies the later full-datagram ingress context.
Early rejection preserves queues and conntrack; later rejection retains computed reassembly changes while preserving conntrack.
Actual stale allows still execute before comparison with current desired policy.

Domain-aware source predicates and observation-clock bounds connect every output piece to a matching admitted receipt.
Identical duplicate occurrences do not gain unique physical identities through this theorem.
Active-only namespace residency archives old state and prohibits later packet operations through that interface.
Session residency requires retirement and a fresh namespace lifetime across authentication rounds.
Native queue retirement, namespace cutover, and joint observed stream correspondence remain open.

The [fragment admission guide](FRAGMENT_ADMISSION.md) describes these reusable formal contracts and passive checks.
This component does not claim a new native capture or completed campus integration.

## Current ingress attachments

The `attachment-campus` command adds explicit input-interface context to the joint campus history.
Each attachment is derived from the actual current authentication prefix and permitted application scope.
Its origin remains historical; current permission checks the active round, authentication port, and exact live ingress lifetime.
The controller supplies the trusted authentication-to-data-port association.

Installed numeric `iif` policies are evaluated independently of lifetime labels.
Their equivalence with current desired attachments is checked for every numeric interface index and packet header.
The importer requires raw prerouting priority `-300` and resolves exported names within the contemporaneous namespace inventory.
Maintenance exceptions must be disjoint from application classes.

Actual early rejection precedes ordinary conntrack and NAT.
It preserves both modeled tables and retires any selected immutable route ticket.
It has no fabricated ordinary classification or forwarding outcome.
Actual acceptance executes the current ordinary pipeline even when the guard is stale.
Such a stale policy can produce tracker changes before the report records its mismatch.

Historical flow ownership requires a fresh confirmed record and a current permitted attachment.
Replication selects the owned source record and checks the installed standby table before inheriting its origin.
Every stored origin refers to the computed EAP state at its actual creation prefix.

The unsafe impersonation prelude is separated from the guarded suffix by an explicit empty-table reset.
The finite capture covers whole IPv4 UDP on isolated routed Ethernet links.
It distinguishes a separate attacker port but establishes no cryptographic data provenance or protection against identical bytes on the trusted port.
The [attachment guide](INGRESS_ATTACHMENTS.md) states the remaining lifetime, installation, observation, and implementation assumptions.

## Joint campus deployment history

The `campus-deployment BUNDLE [--budget N] [--json]` command checks one authentication, policy installation, packet, handoff, and withdrawal history.
Its bundle supplies the actual authentication observations, a declared application scope, packet classes, gateway configurations, network observations, and their joint timeline.
Authentication and network operations each consume the next observation in their indexed source history.
A compliant checked report consumes both complete histories and records primary withdrawal.

The policy certificate selects the actual installed configuration by identity.
Its compiled rules and fallback must match that configuration's native source.
Both directions of policy refinement compare every modeled conntrack state and header at the certified hook context.
The generated comparison uses the actual consumed authentication prefix.
This derives forward equivalence rather than accepting that relation from the caller.
Authentication changes do not automatically change the stored installed configuration.
A stale policy therefore fails comparison with a current incompatible session policy.

All declared packet requirements name the same application scope.
Every processed packet must match a declared class at its actual post-destination-NAT header, including packets denied by current policy.
Computed next-hop labels must identify the selected request or reply endpoint role.
The reviewed native mapping binds those labels to the declared direct topology.
Class coverage and route labels do not establish principal ownership or prevent spoofed source headers.

Request and reply topology use client, primary, standby, and server data roles.
A formal management role retains the stated segmentation property.
The direct interpretation collapses abstract access-point vertices to the client role and expands direct edges to declared campus paths.
It establishes no physical AP, Wi-Fi link, or wireless key installation.
Current application permission is equivalent to duplex reachability in this declared enforced topology.
Actual packet availability still requires live TTL, a usable route, and current forward and late permits.

Withdrawal follows both endpoint route changes, retirement of actual primary assignments, and primary fencing.
The model archives the last primary table without claiming that it remains a live kernel table.
Later operations cannot process primary tickets or invoke primary controls.
Live primary observations after withdrawal are rejected.
Standby processing preserves the archive and uses its own current configuration and classification.
The operation-count drain proves no physical deadline, fairness, or eventual delivery.

Every served ticket cites an actual earlier assignment within the same joint replay prefix.
Matched output retains that source's exact NAT boundary, payload, and one TTL decrement.
The output theorem also supplies current application validity and method readiness at the actual consumed authentication prefix.
Current application denial excludes emission under the checked installed policy.
The generic decision theorem uses a covered-header premise to connect forward permission with duplex campus reachability.
The checked served-packet theorem derives that coverage from compliance.
Observed bytes and table snapshots never replace computed source or tracker state.

Two joint native captures exercise the selected sequence.
The saved example records 26 native operations, eight datagrams, and seven protected ticket identities.
Its 45 model operations comprise 21 authentication operations, 23 network operations, and one withdrawal.
Retained evidence includes 18 EAP frames, 88 live conntrack dumps, 28 packet-socket data frames, 30 Netfilter observations, and 26 synchronization frames.
These counts describe finite evidence rather than universal native correctness.
Wired EAP evidence does not establish cryptographic refinement, wireless behavior, principal anti-spoofing, physical correspondence, automatic failures, or lifetime evolution.
The complete campus objective remains open; the [campus deployment guide](CAMPUS_DEPLOYMENT.md) records the exact profile and remaining premises.

## Requirement language

The text interface accepts one requirement per line:

```text
ID: SOURCE must reach TARGET for SERVICE.
ID: SOURCE must be isolated from TARGET for SERVICE.
ID: SOURCE must traverse GATEWAYS before TARGET for SERVICE.
ID: if CLAUSE then CLAUSE.
```

A selector is `node:NAME`, `zone:NAME`, `role:NAME`, or `group:NAME`.
A clause uses one of the first three forms without the ID or final period.
The parser ignores blank lines and full-line `#` comments. Requirement IDs must
be unique. The parser keeps source line numbers and rejects other sentence forms.

Each requirement applies to every ordered source and target pair:

| Requirement | Meaning |
| --- | --- |
| `must reach` | Every pair has a permitted path. |
| `must be isolated` | No pair has a permitted path. |
| `must traverse` | Every path for every pair visits the gateway group. |

Universal reachability and the existence of some reachable pair are different
observations. A selector must select at least one device. This condition also
applies to conditional clauses with false premises.

A gateway visit at either endpoint satisfies mediation. Mediation can hold when
no path exists. A separate reachability requirement must express availability.

An abstract role can represent several nodes, such as a gateway cluster.
A path visits that role when it visits at least one cluster member. A cluster
name alone does not establish high availability or encryption. Those properties
need separate models and assumptions.

## Abstract analysis

The formula language supports Boolean connectives and atoms with explicit
interpretations. Propositional analysis considers assignments to atoms
independently. Some assignments describe combinations that no network can realize.
A countermodel therefore identifies a logical gap. It need not describe a
deployable configuration.

`Netlib/Policy/Analysis.lean` extracts observations from the requirements and goals.
It needs no configuration. Requirement minimization keeps these domain laws fixed:

- Universal reachability implies some reachability when both selections contain
  devices.
- Universal and existential reachability agree for two node selectors.
- Isolation implies mediation by any gateway set.
- Each nonempty selection has some reachability to itself.
- Universal reachability composes through a nonempty intermediate selection for the same service.

`Netlib/Policy/Observation.lean` proves these laws under explicit assumptions about
nonempty selections and node identities. Analysis infers no other relationships
unless supplied formulas state them.

Concrete evaluation validates each selector against the configuration. Offline
analysis assumes a stated interpretation. It cannot detect an undeclared device
or group in a configuration that it does not receive.

Completeness concerns the supplied goals, vocabulary, and model. The checker
cannot discover an unstated operational goal. An inconsistent policy has no
model. Classical implication from that policy does not establish a secure network.

## Policy and network changes

Redundancy removal must preserve the complete policy. Each removal must account
for dependencies between requirements. Independent removal of all individually
redundant clauses can delete both copies of a duplicate. Netlib removes clauses
in sequence and proves that this process preserves the policy models.

Removal of permitted links preserves isolation and mediation. It can remove
availability. Additional links can create bypasses and need a new compliance
evaluation.

Refinement transfers security from an abstract architecture to physical nodes
only under the stated transition relation. Device labels alone do not establish
that relation. Mediation needs the stronger stuttering refinement conditions.

`Netlib/Network/Change.lean` also gives conditions for reuse of query results.
Two networks must agree on every outgoing link from a closed region.
That region must contain all queried sources. Under these conditions, reachability,
isolation, and mediation have the same values in both networks.
These theorems do not implement an incremental CLI cache.

Labeled transitions also describe protocol and operational state changes.
Finite trace refinement transfers invariants between abstraction levels.
Independent and synchronized state transitions compose through the product model.
The existing session model supplies one concrete adapter.

Certified update plans check the initial state, final state, and every intermediate snapshot.
Plan concatenation preserves the same contract.
Projection transfers update guarantees when concrete and abstract steps commute.
Real device update adapters remain outside the current implementation.

Domain graphs compose through explicit border transitions and shared abstract refinements.
The sum node type keeps domain identities disjoint.
Each border transition must preserve the abstract contract.
The graph union theorems use a common closed region.
Separate isolation of the inputs does not establish isolation of their union.

The fault model states permitted node and link removals.
Internally disjoint paths establish availability after one internal-node failure.
This theorem excludes endpoint failures and independent link failures.
The campus example composes these results with session enforcement and management isolation.
The [roadmap](ROADMAP.md) separates this foundation from the complete deployment objective.

## Trust boundary

Linux snapshot import and packet-intent compilation have structured translation proofs.
The native forwarding graph preserves source route lookup and source firewall evaluation under the documented transit assumptions.
The intent compiler rejects incompatible permits and prohibitions before it emits a certified ACL.
The emitter's structured native-format snapshot preserves that ACL for every header.
JSON parsing, serialization, kernel execution, and deployment operations need separate evidence.
The [Linux](LINUX.md) and [compiler](COMPILER.md) guides distinguish these guarantees.
The transfer checker separately certifies header-changing paths and cuts.
The NAT auditor separately certifies agreement with supplied packet observations.
The byte-derived forwarding extension adds selected payload, TTL, and checksum effects through tracked NAT.
Native implementation correspondence still requires separate evidence and refinement.
The conntrack adapter adds checked visible tuples and status-aware endpoint algebra.
The separate lifecycle checker proves agreement with an explicit sequence of modeled route, filter, NAT, and deletion operations.
Its structural invariant does not establish transport validity or an arbitrary security contract.
The separate barrier proof establishes selected output exclusion through that sequence under its certified late-filter contract.
Collectors and native experiments supply evidence without proving kernel C refinement, complete kernel state, or historical admission beyond the supplied observations.

Lean verifies the theorem statements and proofs with the pinned toolchain.
Each theorem establishes its conclusion under its explicit hypotheses.
Review must establish the accuracy of source translation and the relation between
imported configurations and deployed equipment.

The input parser, configuration representation, abstractions, and reports need
review with the formal definitions. A path validator verifies the endpoints and
every step for the selected service. A cut validator verifies three properties:

1. The cut contains the source.
2. The cut excludes the target.
3. Every permitted step from the cut ends within the cut.

Gateway evaluation excludes the whole gateway set from bypass paths. It handles
endpoints in that set explicitly.

`Verification.evaluate` and `Verification.evaluateFormula` carry proofs of their
network and logical meanings. `VerifiedCompliance.check` audits reported
observations and certifies the original requirements. The CLI uses this function.

`check_compliant_iff` connects a successful report's final status to the formal
meaning of every original requirement. `check_results_covered` preserves their
exact list and order. The wrapper repeats certificate searches. This keeps the
report adapter separate from certified evaluation at the cost of repeated work.

Tests exercise the input and report code. They do not establish parser proofs or
vendor importer proofs. A theorem's stated model defines the scope of its claim.

The search returns a `Decision` with an accepted path or cut.
`Decision.correct` connects its Boolean value to finite network reachability.
A rejected certificate causes an internal error. It cannot produce an accepted
compliance result.

The build must contain no unfinished proof through `sorry` or `admit`.
Project-added axioms must not assert network properties. Examples supply
executable validation. Reusable theorems supply formal evidence.
The [proof inventory](PROOFS.md) lists the individual guarantees.

## Validation criteria

All Lean validation runs locally. CI must not compile Lean or invoke commands
that compile it indirectly. Documentation CI validates and deploys saved HTML.

1. The project builds with the pinned Lean version. No external theorem
   assumptions make examples pass.
2. Examples distinguish a compliant architecture, a bypass, an isolated target,
   and a change that invalidates an earlier claim.
3. Path evaluation terminates on cyclic graphs. It handles disconnected nodes,
   self reachability, and gateway endpoints according to the model.
4. Cluster examples distinguish a visit to one member from a bypass of all
   members. Unknown or empty selections cause errors.
5. Logical analysis distinguishes satisfiable policies, contradictions, redundant
   requirements, and goals with countermodels.
6. Requirement removal preserves meaning for duplicates and implication cycles.
   Analysis reports inconsistency before goal coverage can serve as evidence.
7. Malformed input causes errors. The parser rejects unsupported syntax.
   Concrete evaluation rejects selectors without devices.
8. Reports state their finite scope. They distinguish abstract countermodels from
   concrete path witnesses.
9. Packet, routing, and request suites contain 94 theorem examples.
   The request examples distinguish admission, denied mediated paths, surviving
   bypasses, and gateway self paths.
10. Transfer examples retain packet changes in witnesses and distinguish DNAT, bypasses, cycles, and exhausted state budgets.
11. Flow-state tests distinguish collisions, exact replies, independent peer grants, expiration, closure, and public-alias reuse.
12. The alias-reuse theorem identifies packet freshness that the current invariant cannot establish.
13. Lifecycle tests distinguish fresh preconfirmation drops, cached unreplied bindings, dropped-reply state updates, explicit deletion, and observation mismatch.
14. Static stateful refinement covers all five labels and every modeled header, with checked counterexamples and budget errors.
15. Output exclusion covers cached bindings, rule order, deletion, suffix state retention, unsafe unobserved contexts, and observation mismatch.
16. Buffered cutovers preserve FIFO order and multiplicity, separate old deliveries from later exclusion, reject premature drain boundaries, and handle growing clean backlogs.
17. EAP tests cover framing reconstruction, padding, identifier and method correlation, stale evidence, anonymous Identity, failclosed resets, session coupling, and configured-principal campus admission.
18. Session firewall tests cover scoped credentials, conflicting mappings, exact native equivalence, stale established-flow exceptions, and cached-flow denial after reset.
    Earlier queued packets can still be delivered.
19. Wire tests cover checksum synthesis, odd padding, zero representations, exact byte reconstruction, IPv4 profile errors, UDP pseudoheaders, and checksum omission.
    Fresh native socket packets carry complete checksums; separate malformed probes distinguish forwarding from transport reception.
20. Wire forwarding tests cover exact NAT payloads, checksum regeneration, omission, maximum lengths, TTL boundaries, cached reply updates, and fresh confirmation.
    Compliant observed outputs retain payload and TTL guarantees; current Logoff filters deny cached traffic without deleting its binding.
21. MTU tests cover fragment codecs, aligned layouts, arbitrary capture order, strict rejection, DF and TTL ordering, NAT, and current session enforcement.
    Native families recover full socket payloads; mismatching observations preserve computed replay state.

## Scope limits

Netlib does not translate arbitrary PDFs or recursively resolve external
requirements. It does not infer mission intent, device roles, or natural-language
meaning. Reviewers must supply and assess those inputs.

The implementation imports its declared hostapd fragment, selected Linux forwarding snapshots, and versioned model formats.
The [Linux guide](LINUX.md) defines the native input subset and its transit assumptions.
The [compiler guide](COMPILER.md) defines the proved intent-to-firewall translation and remaining correspondence work.
The [session firewall guide](SESSION_FIREWALL.md) connects current EAP-derived credentials to emitted policies and native snapshot checks.
It does not inspect live networks or deploy network changes.
It does not certify complete CSfC, NIST, or 5G compliance.
Reference architectures show formal patterns within the stated model.

The current models exclude dynamic routing protocols and cryptographic algorithm correctness.
Full authentication protocols, transport handshakes, temporal liveness, and adversarial compromise remain outside their scope.
Constant packet rewrites and one local timed source-NAPT model have the separate guarantees above.
Fixed-endpoint tuple translation and ordinary forwarded-packet replay also have explicit domain and evidence limits.
The selected byte-derived UDP model adds payload-preserving NAT, checksum regeneration, and TTL handling under its stated assumptions.
The MTU extension adds output fragmentation and strict family reassembly.
The ICMP extension adds selected local error generation and related quotation NAT.
The received-error extension adds confirmed association and connected UDP host PMTU feedback.
Input reassembly, broader transport behavior, concurrency, and kernel refinement remain separate work.
Processors support ordered stateful composition with explicit stores.
Network-wide concurrent execution, distributed replication protocols, and native implementation correspondence remain future work.
The handoff extension covers arbitrary selected operation interleavings under explicit lifetime, installation, observation, and linearization premises.
Extensions need semantics, proofs, and rules that connect their input to those semantics.

The executable analysis has no fixed atom limit.
Its branch solver simplifies formulas after each assignment.
Every completed result carries a proof.
The default search node budget is 100,000 for each query.
An exhausted query returns an error without a consistency or entailment claim.
The budget does not limit total analysis time or memory.
Worst-case search can still require exponential work.
The exact truth-table interface remains available for reference checks.

Exhaustive network evaluation also has finite resource costs. The DARPA notice
targets a reduction of two to three orders of magnitude in time and cost.
This repository has no measurement that establishes that target.

Scalable symbolic solvers and external certificate generators can extend the
existing interfaces. Each extension must establish its connection to the formal
semantics.
