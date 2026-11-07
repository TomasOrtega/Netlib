# Finite packets through shared updates

A cohort is a fixed group of packets admitted at the start.
Netlib checks that group across two independent native update plans.
The packets share finite receiver buffers and FIFO queues.
One report records all packet actions, shared updates, and idle slots.

The [single-packet result](FEDERATED_PACKETS.md) supplies each packet's native checks and computed ranks.
The [static federation result](FEDERATION.md) supplies native certificates for every local revision pair.
The cohort adds shared buffer guards, complete joint successor checks, and whole-group progress.

## Public entry points

[`Netlib.Federation.Cohort.checkJson`](../Netlib/Check/FederatedCohortCompletion.lean) accepts raw JSON text.
It returns the parsed bundle, its class certificate, and its checked execution.
`checkBundle` accepts the typed bundle.
`certify input profile` constructs the reusable certificate for all accepted header tuples.
`checkExecution` checks a literal action list and a positive service bound against that certificate.
These functions do not issue native update commands.

The [native example](../examples/federation/packet-cohorts.json) uses schema `1` and scope `two-domain-packet-cohorts`.
The strict schema requires these fields:

| Object | Fields |
| --- | --- |
| Root | `schema`, `scope`, `deployment`, `profile`, `headers`, `actions`, `serviceBound` |
| Cohort profile | `packets`, `capacities`, `limits` |
| Cohort limits | `classes`, `states`, `edges`, `work` |
| Capacity row | `node`, `slots` |
| Tagged native node | `side`, `node`; side is `left` or `right`. |
| Packet profile | `query`, `packetID`, `fences`, `limits` |
| Packet fences | `left`, `right`; each has one node-name list per local update. |
| Packet limits | `cells`, `work` |
| Observation | `packetID`, `header`, `node` |
| Header | `source`, `destination`, `protocol`, `sourcePort`, `destinationPort` |

The embedded deployment uses the [federation schema](FEDERATION.md#entry-points-and-input).
Packet profiles and actions use the [single-packet schema](FEDERATED_PACKETS.md#public-entry-points).
Addresses use dotted IPv4 text.
Protocol and port values must fit their fields.
Unknown fields, missing fields, duplicate keys, and unsupported native input cause errors.

## Identities and initial admission

Each packet profile selects a checked reach query and a nonempty external packet ID.
Packet IDs must be unique within the cohort.
Equal headers can belong to distinct packet IDs.
The header list has one entry per packet profile, in the same order.
Each header stays fixed throughout the report.

Capacity rows cover the tagged union of all native revision inventories exactly once.
They reject missing nodes, unknown nodes, and repeated nodes.
Left and right nodes remain distinct when their private names are equal.
The initial queues follow packet-profile order at each source.
Initial held packets must fit the supplied capacities.

The cohort size has no fixed packet-count cap.
The declared class, state, edge, and work limits still constrain admission.
An empty cohort still checks the native plans and must finish both update plans.

## FIFO queues and receiver reservations

A held packet occurs exactly once in its node's queue.
A flight occurs in no held queue and reserves one slot at its receiver.
A received packet occurs in neither a queue nor a reservation.
Every queue entry names the matching held packet.
At each node, held queue length plus incoming reservations stays within capacity.
The fixed packet vector preserves the cohort's identities across all actions.

Only the queue head can send or receive.
A send checks the actual native next hop and receiver capacity.
It removes the sender's head entry and reserves the receiver slot atomically.
Capacity uses the state after that removal, including when source and receiver are equal.

Arrival consumes the packet's existing reservation and appends its ID to the receiver queue.
It needs no additional free receiver slot.
FIFO order follows actual arrival order at that queue.
The model makes no network send-order delivery claim.
Endpoint receipt removes only the matching target queue head.

Shared updates check every packet's held node or pending receiver.
Those checks include queue tails and all receiver reservations.
Each occupied node must remain known, keep its public projection, and clear the update's fence.
Endpoint, ingress, and egress anchors stay fixed across the native plans.

## Exact histories and old send indices

Only an actual send creates a flight stamp.
The stamp retains the packet ID, header, source, receiver, sender cursors, and global send index.
Arrival must match that exact stamp and index.
The source record remains an earlier event in the same global report.
Its old native route, filter decision, or declared border justifies the send after sender retirement.

Each packet projection retains every global slot.
An action for another packet becomes a literal idle action in that projection.
Shared updates remain actual updates in every projection.
Thus packet histories, receipt indices, and old send indices use the same global clock.

[`Cohort.Safety`](../Netlib/Check/FederatedCohortSafety.lean) proves common public histories for each packet and every trace prefix.
Each history vertex has a held-state witness in the actual global execution.
Matched isolation queries exclude their target.
Matched mediation queries retain separate native PEP visits for each operator and the exact gateway preimage.
Another packet's visit or receipt cannot satisfy these facts.

[`Cohort.Control`](../Netlib/Check/FederatedCohortFacts.lean) exposes queue membership, capacity bounds, and exact FIFO effects.
`send_fifo`, `arrival_fifo`, and `receive_fifo` identify the actual queue changes.
`Safety.flight_origin`, `arrival_origin`, and `delivery_origin` identify actual global events and packet data.

## All header tuples and sparse progress checks

Each packet keeps its own complete single-packet partition.
That partition includes the native route and filter boundaries from every revision on both sides.
It also includes that packet's selector.
The cohort checks the complete Cartesian product of the packets' selected representative lists.
For class counts `H₁, …, Hₖ`, the tuple count is `H₁ * … * Hₖ`.
Each packet keeps its own class throughout a joint graph.
Proved successor equality extends stored tables to every accepted actual header tuple.

Each packet profile constructs its component certificate once.
Tuple checks reuse those stored component proofs and rows.
[`Sharing.signature`](../Netlib/Check/FederatedCohortSharing.lean) retains every component key and its complete successor row, including unreachable keys.
Equal full signatures permit reuse only through a kernel proof of complete joint successor equality.
That equality covers every joint key and preserves the checked table and live-row facts.
Every independent header tuple still has a certificate entry, including unequal header choices.

The joint key contains the shared cursors, every packet phase, and every FIFO order.
Sparse discovery starts at the actual initial queues.
It checks every enabled successor of each reachable key.
Each successor target must have an admitted index and a complete row.
Discovery rejects an exhausted budget and returns no partial certificate.
The live-row check rejects every reachable nonterminal state with no progress action.

The potential is derived from the stored component certificates:

```text
Phi = sum of current checked packet ranks
    + remaining left updates
    + remaining right updates
```

Component positions have proved key equality and checked-graph reachability before their ranks are read.
Every packet move or shared update strictly lowers `Phi`.
Literal idle preserves the full joint key and demand.
The update terms handle an empty cohort.
Zero means that every packet has an actual endpoint receipt and both plans are final.

At each positive-potential cut, the joint row selects a currently enabled move.
The model constructs a successful canonical action from that actual state.
One finite service check bounds persistent joint demands.
A packet demand names the exact packet identity and operation.
An action for another packet does not serve that demand.
The modeled deadline is `Phi(initial) * serviceBound`.
This is a bound in global action slots, not physical time or a separate service bound for each packet.

`CheckedExecution.completion` is the first actual whole-cohort completion cut.
It lies within both the recorded prefix and the modeled deadline.
A short trace can have no complete service window.
The public constructor still requires recorded completion and rejects an incomplete trace.
It adds no missing slots and supplies no global scheduler.

## Admission budgets

`classes` limits the full independent header product before tuple allocation.
`states` and `edges` limit each complete reachable joint graph.
`work` is one aggregate budget for the whole cohort certificate and replay.
It includes native checks, packet profiles, input rows, header tuples, all joint graphs, and replay service checks.
Each graph consumes the remaining aggregate budget before the next graph starts.
The native deployment and component certificates retain their supplied limits.

Every tuple is charged the full graph estimate, including a tuple that reuses a checked table.
The tuple estimate reserves signature comparison work before class checks start.
Let `H` count header tuples, `N` count tagged nodes, and `K` count packets.
Its comparison term is `(H+1)^2 * (signatureRows+1) * (N+K+1)`.
`signatureRows` sums the keys and edges in all stored component tables.
Tuple handling also adds `(H+1) * (K+1)`.

The state key includes FIFO order, so the reachable graph can grow rapidly with cohort size.
Sparse discovery does not remove that worst-case growth.
The work formulas are explicit structural estimates.
They are not formal runtime, memory, or processor-cycle bounds.

## Scope and trust boundary

The model admits one finite initial cohort with immutable identities and fixed headers.
Native revisions change atomically.
Capacity values, topology, principal identities, port bindings, and FIFO discipline are supplied model inputs.
Their correspondence with a live deployment requires separate evidence.
External packet IDs are checked labels, not cryptographic identities.

The action language has no later packet admission, loss, copies, cancellation, or NAT.
Receiver reservations model buffer competition.
They do not model link rates or in-flight link capacity.
The result does not prove wire bytes, TTL, checksums, transport recovery, TCP, or application delivery.
Physical time, kernel execution, live update commands, cryptographic source authenticity, negotiation, and topology privacy remain outside the result.
