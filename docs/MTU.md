# MTU decisions and IPv4 fragmentation

The MTU profile extends [byte-derived NAT forwarding](WIRE_FORWARDING.md).
It accepts a whole IPv4 UDP input and emits a checked fragment family when required.
The route supplies an effective MTU between 68 and 65,535 bytes.
This value must include route and path constraints, rather than merely the output device's configured MTU.

```sh
lake exe netlib wire-mtu examples/mtu/replay.json --json
lake exe netlib session-firewall examples/mtu/session.json --json
```

Exit zero means observation agreement, one means mismatch, and two means invalid input or unsupported execution.
The commands read evidence without installing policy or sending packets.

## Processing order

Each selected packet follows these stages:

1. Validate the whole input, including its IPv4 and UDP checksums.
2. Prepare one conntrack attachment and apply destination translation.
3. Select the destination route.
4. Handle TTL zero or one before testing the effective MTU.
5. Reject an oversized DF packet before forward filtering, source NAT, and confirmation.
6. Otherwise, execute the existing filters, source translation, and confirmation once.
7. Fragment the permitted translated packet when its length exceeds the effective MTU.

Route failure retains the existing route-drop behavior.
TTL expiry and DF rejection retain prepared state without confirming a fresh candidate.
An existing reply can set seen-reply before either rejection.
An existing translation remains cached when a later packet exceeds the MTU.
The [source note](research/MTU_FRAGMENTATION.md) records the RFC requirements and Linux ordering.

## Fragment families

Fragmentation splits the complete IP payload, including the UDP header.
Each nonfinal payload has `floor((MTU - 20) / 8) * 8` bytes.
Only nonfinal payloads need eight-byte alignment.
The final payload may use the full MTU minus its header.
Offsets count eight-byte units, and MF identifies every nonfinal part.
A fitting packet remains one packet, preserving its DF flag.
Oversized DF packets produce no selected UDP transit output.

Each output header has a valid IPv4 checksum.
All parts preserve the translated addresses, protocol, TOS, identification, and decremented TTL.
The UDP checksum covers the whole translated datagram and is retained across the split.
An omitted checksum remains zero.
Payload reconstruction includes every byte without gaps or overlap.

The fragment codec supports IHL five, DF, MF, the 13-bit offset, and trailing link padding.
It rejects the reserved flag and inconsistent fragmentation flags.
Nonfinal payloads must be positive multiples of eight bytes.
General codec proofs reconstruct arbitrary accepted bytes, including their received checksum representation and padding.

Strict reassembly sorts by offset and requires one complete family with consistent metadata.
It rejects gaps, overlaps, duplicate parts, missing final parts, and extra parts after the final fragment.
It validates every fragment checksum and the recovered IP length.
Only then does the checker decode UDP and validate its length and checksum.
This strict evidence profile does not reproduce every native overlap-resolution policy.
Reassembly timers and resource eviction remain outside it.

## Replay schema 1

The root contains `schema`, `routing`, `mtus`, `configs`, `initial`, and `events`.
Configuration and table formats reuse the [lifecycle importer](LIFECYCLE.md).
The route snapshot retains its explicit device, gateway, and next-node bindings.
The `mtus` array has one `{ "nextHop": "service", "mtu": 600 }` entry per distinct bound next node.
Unknown, duplicate, missing, or out-of-range MTU bindings are rejected.

Packet events retain `type`, `config`, `zone`, `raw`, `observed`, and `state`.
The whole captured input bytes determine the tuple and candidate lookup.
No separately supplied header can replace them.
Administrative erase events retain the earlier byte-derived key format.

The observed metadata fields retain their earlier meanings.
`disposition` also accepts `mtuExceeded`.
`mtu` is an observed effective MTU, or null when unobserved.
TTL expiry occurs before MTU selection and therefore reports no selected MTU.

`output` is always an array of captured Ethernet fragment strings.
An empty array asserts no selected UDP output within the complete observation window.
A nonempty array must form a complete valid UDP family.
Capture order is irrelevant.
Null intermediate metadata never disables output or table comparison.

Comparison checks every normalized fragment field and the complete reassembled UDP datagram.
Ethernet adjacency, padding, and the two valid IPv4 checksum zero representations are outside equality.
Their checksums and wire encodings are still independently validated.
Observed disagreement never replaces computed state or changes later modeled execution.

## Proof chain

`Protocol.IPv4Fragment` supplies general encode/decode round trips and fragment validity.
`Protocol.IPv4Fragmentation` proves aligned contiguous layouts, size bounds, exact payload recovery, and total certified generation.
`Certified.reassembled` recovers the original packet.
`Certified.reassembled_perm` proves recovery for every permutation of its fragments.

`Protocol.MTUForwarding` places rejection before filtering and fragmentation after the existing lifecycle execution.
Its proofs preserve cached mappings, prepared reply updates, filter decisions, and confirmation effects.
Fragment encoding cannot introduce a new failure after successful confirmation.

`Check.IPv4Fragments` connects raw Ethernet fragments to checked reassembly and UDP decoding.
`Check.MTUForwarding.Report.compliant_iff` covers every supplied observation and table prefix.
`observed_output_payload` transfers observed recovery to exact input payload preservation and TTL decrement.
`observed_fragments_fit` bounds every observed part by the actual selected emission MTU.

Both forwarding checkers share `Check.Replay` execution certificates.
The generic checker proves ordered agreement and invariant preservation without trusting observed state as execution state.
`Examples.MTUDeployment` composes fragment facts with current scope credentials and EAP readiness.
Current Logoff policy excludes complete output families through arbitrary cached records.

## Native evidence and remaining scope

The [capture recipe](../examples/mtu/README.md) uses the earlier four wired EAP admission stages and two-sided NAT.
The peer path has MTU 4,096 and the service path has MTU 600.
A normal UDP socket sends 1,200 application bytes as one 1,228-byte DF-clear input packet.
Permitted forwarding produces IPv4 lengths 596, 596, and 76, with offsets 0, 576, and 1,152 bytes.
The server's normal UDP socket receives the full original payload.
A small reply returns through reverse NAT.
Denied admission stages produce no selected UDP family, including the cached flow after Logoff.

Separate probes cover cached and fresh DF rejection, TTL-before-MTU priority, exact-MTU DF forwarding, fragmentation, and UDP checksum omission.
The probe suffix restores a fixed permit policy to isolate packet mechanics.
It establishes no new current-session authorization claim.
Raw ICMP errors remain captured and checked by the independent verifier.
The Lean forwarding model does not yet generate those errors or prove their side effects.

Input fragmentation, gateway reassembly, options, PMTU discovery, GSO, rerouting, allocation failure, and full transport semantics remain open.
Concurrency, expiry, kernel implementation refinement, physical packet attribution, principal binding, and installation timing also remain separate obligations.
The [roadmap](ROADMAP.md) retains the complete stack and campus objectives.
