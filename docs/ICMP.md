# Generated ICMP errors through NAT

The ICMP profile extends [MTU forwarding](MTU.md) with Time Exceeded and Fragmentation Needed.
It connects the rejected UDP packet, quoted bytes, related NAT, output filters, and emitted error.

```sh
lake exe netlib wire-icmp examples/icmp/replay.json --json
lake exe netlib session-firewall examples/icmp/session.json --json
```

Exit zero means agreement, one means observation mismatch, and two means invalid input or unsupported execution.
The commands read evidence without changing network configuration.

## Generation and related NAT

The existing transit model selects the destination route before testing TTL and DF.
TTL expiry precedes oversized-DF rejection.
These paths stop before forward filtering, source NAT, and ordinary UDP confirmation.

The error model then performs these stages:

1. Derive the error kind and reported forward MTU from the computed transit outcome.
2. Check source, destination, and link-group suppression conditions.
3. Select the return route, initial router source address, effective return MTU, and output TTL.
4. Quote the rejected packet after destination translation.
5. Attach the error to the opposite direction of the same connection as related traffic.
6. Apply the output filter, related NAT correction, and late filter.
7. Encode the ICMP message and its outer IPv4 packet.

The selected profile disables ICMP rate limiting and assumes successful allocation and transmission.
Missing return routes and denying output filters still suppress emission.
The [source note](research/ICMP_ERRORS.md) distinguishes RFC requirements from the inspected Ubuntu implementation.

Related NAT restores the quoted tuple through the existing connection mapping.
The model performs both the destination translation and its inverse on the actual quoted bytes.
It does not assume that the final quote equals the original input.
The inverse proof establishes that equality for packet fields and the complete quoted UDP prefix.
Only equivalent IPv4 checksum zero representations can differ.

A present UDP checksum is adjusted using the changed address and port words.
The calculation requires no missing application bytes.
An omitted UDP checksum remains zero.
The general update proof establishes checksum validity, inversion, composition, and omission preservation.
The intermediate translated quote is a prefix of a whole datagram whose pseudoheader checksum is accepted.

Fresh original-direction errors do not confirm their rejected candidates.
Existing reply observations survive the error path.
Control processing preserves the transit model's resulting ordinary table.

## Quotations and wire fields

For IHL five, the quote length is:

```text
min(inputIPLength, min(returnRouteMTU, 576) - 28)
```

The return-route MTU bounds the error packet.
Fragmentation Needed reports the forward MTU that rejected the input.
Those values are independent.
For example, return MTU 68 permits a 40-byte quote while the error can report forward MTU 600.

The quote retains the original total length and UDP length even when its payload is truncated.
The quotation codec validates that prefix without requiring all declared bytes.
It preserves identification, TTL, TOS, DF, and the quoted application prefix.
UDP checksum validation occurs only when the complete datagram is quoted.
A partial quotation never establishes whole-transport checksum validity.

The selected Linux TOS rule is `(inputTos & 0x1e) | 0xc0`.
The generated packet has protocol ICMP and DF clear.
The return route supplies its TTL and initial source.
Related NAT determines any final outer-address translation from the attached mapping and direction.
Identification is an explicit nondeterministic allocator choice.
Neither the model nor the checker proves the kernel's identification allocator.

Both IPv4 and ICMP checksums cover their complete encoded data.
The codecs prove exact reconstruction of arbitrary accepted bytes, including received checksum representation and Ethernet padding.
Semantic comparison ignores validated checksum zero representation and link adjacency.

## Replay schema 1

The root retains `schema`, `routing`, `mtus`, `configs`, `initial`, and `events`, and adds `icmpProfile`.
Each configuration adds native `output` and `icmpLate` filter snapshots.
The output hook has priority zero.
The late hook follows source NAT and precedes confirmation.
Both filters evaluate the generated packet as related traffic.

The profile records output TTL, configured broadcast addresses, and the selected fixed control settings.
It requires rate-limit and rate-mask zero, inbound-address selection zero, DF-clear output, and the supported TOS and quotation rules.
Unicast return routes require explicit preferred source addresses.
The native projection derives broadcast addresses from the checked interface prefixes.

Packet observations add `icmpOutput`, an array containing zero or one captured Ethernet error frame.
An empty array asserts no selected ICMP output in the complete observation window.
The earlier `output` array still describes UDP transit fragments.
Neither array controls the computed disposition.
The error's observed identification supplies only the declared allocator choice.
Its existence, kind, quotation, addresses, TTL, TOS, DF, and filter decisions remain computed.

The checker validates Ethernet, outer IPv4, ICMP, and the quoted IPv4 UDP prefix separately.
Complete quoted UDP datagrams receive an additional checksum check.
Ordered replay uses the shared execution certificate and preserves computed state after mismatches.

## Proof chain and authorization

`Protocol.ChecksumRewrite` proves incremental checksum arithmetic and full UDP checksum preservation.
`Protocol.IPv4Quote` proves truncated-prefix parsing and source-prefix construction.
`Protocol.ICMP` proves supported error-message wire round trips.
`Protocol.ICMPNAT` proves partial quotation rewriting and its inverse.

`Protocol.ICMPForwarding` composes generation with actual MTU forwarding.
Its facts connect emitted errors to the prepared attachment, restored input quote, related filter guards, and ordinary-table effects.
They bound generated output by the return MTU and connect the reported MTU to the selected forward route.

`Check.ICMPError` packages the raw decode equations and complete-quotation checksum condition.
`Check.ICMPForwarding.Report.observed_quote` transfers compliant observed errors to the computed source-prefix and generation facts.
The report covers all supplied events in order.

`Examples.ICMPDeployment` retains current-session authorization for UDP transit.
An ICMP error does not imply application permission.
TTL and DF rejection precede the forward policy, so a logged-off sender can receive an error while its UDP transit remains denied.

## Native evidence and remaining scope

The [fresh capture](../examples/icmp/README.md) retains 43 IPv4 frames, including 12 ICMP errors, and 21 replay events.
It repeats the four EAP admission checkpoints, two-sided NAT, fragmentation, cached reply updates, and targeted erasure.
Additional probes cover full and truncated quotes, odd lengths, TOS changes, reverse-direction errors, and checksum omission.
LOCAL_OUT and postrouting traces expose related classification and NAT correction.
Native snapshots, sysctl readbacks, socket observations, and provenance remain available for independent inspection.

Packet-mechanics probes use a separate fixed permit suffix and establish no new current-session authorization claim.
The [received-error layer](RECEIVED_ICMP.md) adds received ICMP forwarding and host PMTU-cache updates.
Extensions, input fragments, IP options, rate-limit state, allocation failures, and concurrency remain open.
Routing provenance, current installation, capture attribution, source identity, and kernel implementation refinement also retain explicit assumptions.
The [roadmap](ROADMAP.md) keeps the complete networking objective active.
