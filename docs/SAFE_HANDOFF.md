# Safe gateway handoff with outstanding traffic

This layer separates endpoint route assignment from later gateway packet processing.
A packet keeps its assigned gateway across subsequent route changes.
The current configuration at that gateway governs processing.
The [source note](research/SAFE_GATEWAY_HANDOFF.md) records the Linux, Netfilter, and qdisc evidence.

```sh
lake exe netlib wire-safe-handoff examples/safe-handoff/replay.json --json
```

Exit zero means agreement, one means observation mismatch, and two means malformed input or an unsupported operation.
The command checks supplied evidence without changing routes, queues, or kernel state.

## Protected flow and outstanding assignments

Both kernel tables, the external cache, and outstanding work start empty.
An actual primary packet establishes a confirmed NAT record.
Staging selects that record from the computed primary prefix and fixes the protected flow.
Commitment installs its supported projection into the standby.

Each later endpoint admission has complete validated IPv4 UDP bytes and a direction in that protected flow.
The allocator gives it a fresh ticket identity.
The ticket stores its bytes, assigned gateway, direction, and operation epoch.
Later route changes preserve those fields.
The epoch identifies the actual model prefix at admission; it is not a kernel route-version field.

`Theory.Outstanding` supports arbitrary completion order without requiring equality of stored payloads.
Its proofs preserve identities, actual membership, exact retirement history, and targeted outstanding counts.
An identity cannot complete twice or appear from a future allocation.

A processing operation selects an actual outstanding identity.
It compares later gateway input with the retained admission bytes.
Observations never replace the stored input or computed tables.
Newer standby traffic can complete before an older primary ticket.

## Current forwarding and permission

`Protocol.TrackedFlow` derives ordinary attachment from any valid table containing the protected binding.
The two gateways can have different seen-reply knowledge while retaining that binding.
Processing uses the selected gateway's current classification, routes, forward policy, and late policy.

An associated reply can update seen-reply state before a current policy drops it.
The same binding then classifies a later original-direction packet as established.
Ticket completion records that gateway outcome, including a drop.
Application delivery remains a separate observation.

The service theorem proves existence of an actual emission when TTL, routing, and both current filter permits hold.
That emission has the exact protected NAT target, preserved payload, regenerated checksums, and one TTL decrement.
Those premises use the actual current classification at the assigned gateway.

`Examples.SafeHandoffDeployment` connects processing to a current certified EAP session policy.
Forwarded traffic requires an applicable intent, a valid current scope, and ready authentication under the session assumptions.
Logoff or revocation denies queued traffic when the current assigned-gateway policy matches that updated certificate.
Admission-time permission is absent from the ticket.

The synthetic EAP integration test installs a credential, queues old-route traffic, changes both routes, and then processes Logoff.
It installs the resulting deny policy before processing a queued reply and older request.
Both are denied; the reply still updates seen-reply state and retires its identity.
A stale installed allow policy remains an explicit counterexample to automatic installation coherence.
The native handoff capture uses fixed selected policies; it does not establish a wireless authentication or cryptographic implementation refinement.

## Control preconditions and arbitrary interleavings

Structural safety requires valid tables, unique ticket identities, and unfenced gateways for active routes and outstanding assignments.
Once the protected binding is staged, those gateways must also be ready.
The protected primary binding remains live in this profile.
The controller checks these operation preconditions:

- Move an endpoint route only to a ready, unfenced gateway.
- Commit only a matching cached binding with a positive timeout and fresh target keys.
- Fence a gateway only after both endpoint routes move elsewhere and every ticket assigned there retires.
- Preserve the protected binding while updating installed configurations.

`SafeHandoff.Admissible` states these conditions entirely before an operation.
The progress theorem constructs an actual successful next step and proves the resulting structural invariant.
Its proof does not assume an accepted step or a safe result.
Universal trace theorems preserve safety through every modeled admissible packet and control interleaving.
They also guarantee another step for each admissible operation at every reached prefix.

The packet direction, repetition, and placement between control operations remain unrestricted.
A ticket can use the old gateway after either endpoint route changes.
Fencing waits for those assignments rather than assuming route changes drained them.
Individual route reads, gateway executions, and configuration transitions still require the declared linearization and stable packet hooks.

## Drain and fence

The quantitative result counts outstanding assignments to a selected gateway.
Each successful processing operation there retires exactly one actual ticket, including policy-denied traffic.
Admissions to another gateway preserve that count.

The finite drain theorem constructs a completion sequence with exactly the initial target count, without a global FIFO assumption.
After both routes move away, that sequence permits the final fence.
The bound counts service operations.
Physical time bounds, fair scheduling, packet loss, and resource correspondence remain additional obligations.

A qdisc-empty observation alone does not establish the drain predicate.
A packet can already have left that queue while its gateway work remains outstanding.
The native evidence joins each selected old admission to actual gateway processing and a socket outcome or bounded absence.
It also retains the queue observations and route readbacks.

## Native evidence and replay

The saved [native example](../examples/safe-handoff/README.md) contains 20 native operations, seven datagrams, and six protected ticket identities.
Its projected replay has 20 model operations and 32 actual post-operation table observations.
The native verifier checks 84 kernel dumps, 27 Netfilter observations, 26 selected data-frame observations, and 30 synchronization frames.

A primary-bound datagram remains in an endpoint qdisc while both routes change and standby request/reply traffic completes.
It later reaches the primary, receives the current permitted processing, and completes before the primary fence.
Another standby-bound datagram remains queued through installation of deny and encounters that deny after release.
The final permitted request and reply continue through the standby.

Endpoint postrouting NFLOG supplies the early route assignment and unchanged IPv4 bytes.
Packet-socket transmission taps occur after qdisc dequeue.
NFLOG exports no checksum-readiness metadata; disabled offloads alone do not establish a complete checksum at that earlier hook.
The selected capture therefore checks every actual admission with the complete UDP codec and rejects unsupported invalid inputs.

The shared `CaptureEvidence` interface validates raw references, command intervals, observer lifetimes, joins, and complete evidence consumption.
Its legacy adapter preserves the earlier authoritative replication checker.
The safe adapter retains endpoint admission and gateway processing as distinct observations.
The protocol adapter checks fixed control arguments, ready tables, route owners, queue prefixes, and barrier ordering.

Projection retains unchanged nftables objects and their original file indices.
Fast combined packet operations have no fabricated intermediate table observation between admission and processing.
Physical qdisc operations remain checked side evidence rather than modeled queue counts.
Every served item has an actual earlier admission-prefix proof, including its bytes, assigned gateway, identity, and operation epoch.

Expiry, helpers, conflicting writers, tracker replacement, automatic failover, reliable synchronization, and complete implementation refinement remain open.
The [roadmap](ROADMAP.md) retains the complete networking and campus objectives.
