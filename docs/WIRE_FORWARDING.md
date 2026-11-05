# Forward UDP bytes through NAT

The wire-forwarding model carries a checked IPv4/UDP datagram through the existing tracked lifecycle.
It derives the lookup tuple from those bytes, preserves the UDP payload, decrements TTL, and updates both checksums.
The [wire guide](WIRE.md) defines the selected untagged, unfragmented input profile.

```sh
lake exe netlib wire-forward examples/wire-nat/replay.json --json
lake exe netlib session-firewall examples/wire-nat/session.json --json
```

The first command compares a computed packet execution with native byte, hook, and table observations.
The second checks the four EAP-derived firewall snapshots.
Exit code zero means agreement, one means observation mismatch, and two means invalid input or unsupported execution.
Neither command installs policies or sends packets.

## Processing order

Each packet follows these stages:

1. Validate its decoded IPv4 and UDP fields and checksums.
2. Attach one existing conntrack record or prepare a fresh unconfirmed candidate.
3. Apply destination translation and select the destination route.
4. If a route exists and TTL is at most one, produce no selected UDP transit output.
5. Otherwise, use the existing forward filter, source translation, late filter, and confirmation stages.
6. Encode permitted output with the translated tuple and decremented TTL.

TTL expiry keeps the prepared state.
A fresh candidate remains unconfirmed.
A reply can set seen-reply on an existing record before expiring.
No route causes the existing route-drop result before the TTL branch.
The model does not generate or verify ICMP errors.
The native capture retains those packets separately.
The [source note](research/WIRE_NAT_FORWARDING.md) records exact Linux ordering and RFC requirements.

The packet rewriter preserves TOS, identification, DF, UDP payload, and IPv4 total length.
It discards old link padding.
The output IPv4 checksum is recomputed for the new header.
A present UDP checksum is recomputed for translated addresses and ports.
An omitted UDP checksum remains zero.
A computed UDP zero is transmitted as `0xffff`.

Encoding cannot fail after successful modeled forwarding.
The input bounds and unchanged payload establish output bounds before the total certified rewrite is used.
Ordinary confirmation can still reject a tuple collision under the existing lifecycle profile.

## Replay schema 1

The root contains `schema`, `routing`, `configs`, `initial`, and `events`.
Routing, configuration, and table snapshot formats reuse the [lifecycle importer](LIFECYCLE.md).
`initial` is a supported native conntrack dump, or null for a declared empty initial table.
Each configuration contains `id`, `forward`, `late`, and `nat`.
The late filter follows source NAT and precedes confirmation.

A packet event contains `type: "packet"`, `config`, `zone`, `raw`, `observed`, and `state`.
`raw` contains the captured Ethernet bytes.
Its decoded tuple controls lookup and fresh-candidate selection.
The input format cannot substitute a supplied JSON packet header.
NAT candidates are derived from the selected configuration only on a lookup miss.
Cached records retain their existing translations.

The `observed` object contains these fields:

| Field | Meaning |
| --- | --- |
| `classification` | Observed conntrack state label, or null. |
| `fresh` | Observed fresh attachment, or null. |
| `afterDestination` | Observed forward-stage tuple, or null. |
| `afterSource` | Observed post-source-NAT tuple, or null. |
| `nextHop` | Observed next node, or null. |
| `disposition` | `forwarded`, `routeDrop`, `ttlExpired`, `forwardDrop`, `lateDrop`, or null. |
| `output` | Actual egress Ethernet bytes, or null for no selected UDP egress. |

Null intermediate fields remain unobserved.
They do not disable output or table checks.
`state` contains the observed post-event native table, or null when unobserved.
Native IDs, timeout seconds, iteration order, and supported unrelated status bits retain the existing table-comparison treatment.

An administrative erase event contains `type: "erase"`, `zone`, `raw`, and `state`.
Its checked byte header selects the record key.
Erasure removes the associated record and both direction keys.
It does not process that byte string as a new network packet.

Output comparison uses the complete decoded IPv4 packet fields and UDP datagram.
It checks payload, TTL, translated tuple, IP metadata, and UDP checksum mode and value.
The wire decoder separately validates each received checksum.
Both valid IPv4 checksum zero representations are accepted.
Ethernet addresses and link padding can change between interfaces and are outside this comparison.
The native verifier checks their selected interface roles separately.

## Proof chain

`Protocol.UDPRewrite` supplies total certified transformations for valid source packets and UDP target headers.
Its certificate proves output decoding, payload preservation, header fields, TTL, metadata, length, and checksum conditions.

`Protocol.WireForwarding` reuses conntrack preparation and processing.
Its proofs connect outputs to the actual lifecycle result and filter decisions.
TTL-expiry theorems preserve reply updates, prevent fresh confirmation, and retain cached mapping keys.
The completion theorem excludes an extra encoding failure after successful lifecycle processing.

`Check.WireForwarding.Report.compliant_iff` covers every supplied observation in order.
Its trace preserves ordinary-table validity at every prefix.
`observed_output_payload` proves that every matched observed output retains the input UDP payload and decrements TTL exactly once.
Observations do not replace computed state.

`Examples.WireNATDeployment` connects the actual decoded input and emitted packet to current session enforcement.
Its output facts include byte validity, exact payload, TTL, metadata, and checksum mode.
The current-permission theorem supplies a matching post-DNAT scope, a valid credential, and current EAP method readiness.
The Logoff theorem excludes selected UDP output through arbitrary cached records under the current installed policy.

## Native evidence and limits

The [capture recipe](../examples/wire-nat/README.md) repeats the four wired EAP admission stages with two-sided NAT.
The request maps `192.0.2.2:41000 → 203.0.113.2:8080` to `203.0.113.1:40000 → 198.51.100.2:9000`.
The reply restores the service VIP and client tuple.
Complete checksums and UDP payloads are captured on both interfaces.

The first TTL-one reply changes the same cached record to seen-reply before any normal reply reaches the client.
After Logoff, the same cached flow remains visible while the updated policy denies its request.
An isolated permit suffix records targeted deletion, TTL-zero and TTL-one fresh drops, TTL-two forwarding, and preserved UDP checksum omission.
That suffix tests packet mechanics and makes no additional current-session authorization claim.

The selected path assumes sufficient MTU and no additional transformations, fragmentation, or encapsulation.
ICMP generation, transport-tracker refinement, concurrent state changes, expiry, and native collision recovery remain open.
Physical packet identity, capture-stage attribution, principal binding, current policy installation, and method cryptography remain supplied assumptions.
The [roadmap](ROADMAP.md) keeps the complete stack and campus objectives open.
