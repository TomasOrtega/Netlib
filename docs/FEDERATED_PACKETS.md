# One packet through native updates

Netlib checks one identified packet across two independent native update plans.
Actual sends, later arrivals, endpoint receipt, and local updates share one report.
The [static federation result](FEDERATION.md) checks every revision pair.
This result also checks the packet's path across changing revisions.

## Public entry points

[`Netlib.Federation.InFlight.checkJson`](../Netlib/Check/FederatedPacketCompletion.lean) accepts raw JSON text.
It returns the parsed bundle, its all-header certificate, and its checked execution.
`checkBundle` accepts the typed bundle.
`certify input profile` constructs the reusable certificate for all selected headers.
`checkExecution` checks one literal action list against that certificate and its positive service bound.
These are library functions; there is no separate packet-update CLI command.

The [complete example](../examples/federation/packet-updates.json) uses schema `1` and scope `two-domain-packet-updates`.
The strict schema requires these fields:

| Object | Fields |
| --- | --- |
| Root | `schema`, `scope`, `deployment`, `profile`, `header`, `actions`, `serviceBound` |
| Profile | `query`, `packetID`, `fences`, `limits` |
| Fences | `left`, `right`; each contains one node-name list per local update. |
| Limits | `cells`, `work` |
| Observation | `packetID`, `header`, `node` |
| Native node | `side`, `node`; side is `left` or `right`. |
| Header | `source`, `destination`, `protocol`, `sourcePort`, `destinationPort` |

Addresses use dotted IPv4 text; protocol and port fields use bounded integers.
The embedded deployment uses the [federation schema](FEDERATION.md#entry-points-and-input).
Unknown fields, missing fields, duplicate keys, and unsupported native inputs cause errors.

Actions use `send`, `arrive`, `receive`, `updateLeft`, `updateRight`, `updateBoth`, or `idle`.
Send observations identify the held source.
Arrival actions identify the receiver and earlier `sendIndex`.
Receipt observations identify the held endpoint.
Each update names exactly the next local operation.

## Packet identity and update guards

Only an actual send creates a stamp.
It records the packet ID, unchanged header, source, receiver, sender revisions, and actual report index.
Arrival consumes that exact stamp once.
The old send stays justified by its sending revision after its source retires.
Its actual earlier raw action and native route, nftables, or border origin remain available through `Report.flight_source` and `Report.arrival_source`.

An update checks the current held node or pending receiver.
That node must remain known and keep its public projection.
Its retirement fence must be clear.
Fences cover removed or reprojected nodes and can contain extra drain nodes.
The native endpoint, ingress, and egress anchors stay fixed.
Internal and enforcement anchors may move when the local certificates and occupancy checks remain valid.

## Common history and progress

[`Safety.publicHistory`](../Netlib/Check/FederatedPacketSafety.lean) records the source and each actual arrival's old public receiver projection.
`common_history` proves a common public upper walk, with stutters, for every accepted header and actual trace.
`prefix_history` covers every trace prefix.
Every history vertex has a held-state witness in that same execution.
Matched isolation queries exclude their target.
Matched mediation queries identify actual native PEP visits for each named operator and exact gateway preimage.

The finite control key keeps the two cursors and the held node, pending receiver, or delivered phase.
Its node inventory includes every local revision, with operator tags that keep private names distinct.
Graph checks cover every actual enabled successor.
Computed ranks reject reachable dead ends and cycles.
Rank zero means endpoint receipt and both completed local plans.
Each positive-rank recorded cut has an actual supported canonical action.
One service contract bounds persistent demands across the recorded prefix.
The result does not construct a global scheduler.

`CheckedExecution.completion` is the first recorded joint completion cut.
It lies within the actual report and the deadline `initialRank * serviceBound`.
A short trace can pass the finite service check without a complete service window.
The public constructor still requires recorded completion and rejects such an incomplete trace.
It does not pad missing slots.

## Checked native case

The [tests](../NetlibTest/FederatedPacket.lean) replay seven native hops and four local updates, followed by endpoint receipt.
Each operator first adds a new relay while retaining the old relay's drain route.
Its later revision removes the old relay after the receiver fence clears.
The internal anchor moves from the old relay to the new relay.

| Measurement | Value |
| --- | --- |
| Literal actions and first completion cut | `19` |
| Initial computed rank | `19` |
| Service bound and deadline | `12`, `228` |
| Bounded-idle actions and first completion | `38`, with the same bound and deadline. |
| States, edges, and reachable states per selected graph | `225`, `518`, `156` |
| Selected source-port representatives | `4096`, `50001`, `53001` |
| Full joint partition cells | `324` |
| Stored static admission total | `601032821` |
| Original work budget | `1000000000` |

Send slot `5` uses campus revision `1` and its old relay.
At cut `7`, campus revision `2` has removed that sender, but its flight remains pending.
Arrival slot `7` consumes the original stamp and reaches the recorded receiver.
The history also visits both native PEPs and preserves management isolation.
A separate case receives at cut `18` and completes its final update at cut `19`.
Receipt alone does not complete a pending local plan.

Tests reject receiver deletion, projection jumps, stranded headers, drain cycles, forged observations, repeated arrivals, skipped updates, starvation, and truncated completion.
Budget tests cover context, class generation, graph analysis, and replay.
The complete admission estimate includes native inputs, fences, selected classes, successor generation, rank checks, and replay/service checks.
Staged guards run before their corresponding expensive work.
`profile.limits.cells` bounds the selected common cells.
The embedded deployment limits keep their existing meaning.
This estimate is not a formal runtime or processor-cycle bound.

## Model boundary

The profile models selected unfragmented IPv4 forwarding with main-table routes.
It has one packet, one fixed header, no loss, no copies, no NAT, and atomic model updates.
Endpoint receipt is a model operation.
The result does not prove wire bytes, checksums, TTL evolution, TCP behavior, application delivery, or physical delivery time.
Live kernel behavior and native update commands require separate correspondence evidence.

Node identities, principal identities, topology, border links, port bindings, and source authenticity are supplied evidence.
Cryptographic signatures, contract negotiation, and topology privacy remain outside this result.
The packet model does not establish service competition or reservation safety for multiple packets.
