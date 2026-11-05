# Received IPv4 ICMP errors and host PMTU

This note distinguishes protocol requirements, inspected Ubuntu source, and the selected forwarding and host-state model.
Received errors quote earlier UDP traffic; their outer packets remain ICMP throughout forwarding.
Tuple association establishes a relationship with cached state, without authenticating the error's sender.

## Source profile

Kernel links select `Ubuntu-6.8.0-117.117`, matching the retained kernel release lineage.
Source inspection does not prove equivalence with the running binary.
The selected path uses whole IPv4 packets, IHL five, ordinary UDP conntrack, stable routes, and established NAT mappings.
[Ubuntu tagged source][ct-error].

## Protocol requirements

Destination Unreachable uses type three; Fragmentation Needed uses code four.
Time Exceeded in transit uses type 11, code zero.
The minimum quotation contains the original IP header and eight payload bytes.
The ICMP checksum covers its entire message, including that quotation.
[RFC 792](https://www.rfc-editor.org/rfc/rfc792.html).

The next-hop MTU occupies the low 16 bits following the checksum; the preceding 16 bits remain zero.
Its value includes the IP header and excludes link headers.
A host must reduce the applicable PMTU estimate after a valid Fragmentation Needed message.
Such a message must never raise the estimate or reduce it below 68 bytes.
Zero identifies an older router without an advertised MTU.
RFC 1191 offers several fallback strategies, including plateau search, without prescribing one mandatory algorithm.
[RFC 1191, sections 3–5](https://www.rfc-editor.org/rfc/rfc1191.html#section-3).

NAT should reject invalid ICMP and embedded IP checksums.
It should not validate the embedded transport checksum, even when the entire segment is quoted.
An incomplete quote cannot establish that checksum's validity.
Matching mappings govern embedded translation and the outer destination.
The ICMP type and code remain unchanged.
Private-side error sources require suitable external translation.
These requirements permit overriding local policy.
RFC 5508's session nonrefresh requirement specifically addresses quotations of ICMP queries and responses; Linux behavior below also covers UDP quotations.
[RFC 5508, sections 4.1–4.3](https://www.rfc-editor.org/rfc/rfc5508.html#section-4.1).

Routers must suppress ICMP errors in response to ICMP errors.
Therefore, an incoming error whose own TTL expires must not cause another Time Exceeded error.
Routers should quote as much as possible without exceeding a 576-byte generated datagram.
That generation bound does not exempt received ICMP packets from ordinary output fragmentation.
[RFC 1812, sections 4.3.2.3 and 4.3.2.7](https://www.rfc-editor.org/rfc/rfc1812.html#section-4.3.2.3).

Hosts must pass applicable ICMP errors to the transport layer.
UDP must pass received ICMP errors to its application layer, subject to its specified validation rules.
[RFC 1122, sections 3.2.2 and 4.1.3.3](https://www.rfc-editor.org/rfc/rfc1122.html#section-4.1.3.3).

## Existing-connection association

`nf_conntrack_icmpv4_error` checks the ICMP header and, under the configured prerouting checksum policy, its checksum.
It delegates recognized error types to `nf_conntrack_inet_error`.
That function extracts the quoted tuple, reverses it, and performs a network-namespace and conntrack-zone lookup.
The found tuple determines the error direction: original gives `RELATED`; reply gives `RELATED_REPLY`.
Importantly, the outer destination must equal the destination of that found, reversed-quote tuple.
An outer-destination mismatch prevents attachment.
The outer source is absent from these checks.
[Error association and destination guard][ct-error].

The ordinary tuple reader rejects quoted noninitial fragments and requires accessible header and port bytes.
For UDP association, it reads four port bytes rather than validating the UDP segment.
It does not verify the embedded IP checksum, UDP checksum, or UDP length against a complete datagram.
A stricter evidence decoder therefore defines a selected subset of native acceptance.
[Quoted tuple extraction][ct-tuple].

After error attachment, `nf_conntrack_in` exits before ordinary UDP processing and reply observation.
Consequently, this path neither creates a new UDP connection nor records `IPS_SEEN_REPLY` nor refreshes its UDP timeout.
Subsequent confirmation skips the already confirmed connection.
These conclusions assume no concurrent timer expiry, deletion, helper, or administrative change.
[ICMP early return][ct-input], [confirmation guard][ct-confirm].

Inference: use a lookup result containing the existing entry and related direction, with an unchanged connection table.
Do not admit errors by outer address or ICMP type alone.
Do not infer current EAP authorization from successful cached association.

## Related NAT and forwarding order

`nf_nat_icmp_reply_translation` handles attached related ICMP separately from ordinary NAT.
For each applicable NAT status bit, it manipulates the quote using the opposite tuple and opposite manipulation direction.
It adjusts quoted UDP checksums incrementally, preserves checksum omission, and recomputes the ICMP checksum.
Its UDP rewriting requires eight quoted UDP-header bytes.
It also rewrites the selected outer address from the inverted opposite tuple.
That rewrite is unconditional once the relevant NAT status bit applies; it does not test equality with the embedded address first.
With both destination and source NAT, a downstream router's error source can consequently become the connection's VIP.
[Related translation][nat-error], [UDP manipulation][nat-udp].

Prerouting tracking and related destination translation precede route selection.
`ip_forward` then tests TTL expiry and oversized DF rejection before the forward hook.
Surviving errors receive their outer TTL decrement before forward filtering.
Postrouting source translation and confirmation precede ordinary output fragmentation.
Ordinary NAT preserves the received outer TOS and quoted TTL.
[Receive route selection][input], [forward ordering][forward], [postrouting and fragmentation][output], [address manipulation][nat-error].

For a downstream Fragmentation Needed error, the quote already contains the edge's earlier UDP TTL decrement.
The downstream router rejects oversized DF input before performing its own decrement.
Returning related NAT restores quoted addresses and ports, without restoring the original host-ingress TTL.
The outer ICMP TTL independently loses one at the edge.
[TTL and DF ordering][forward], [related translation][nat-error].

Calling `icmp_send` on a received ICMP error checks the triggering ICMP type and suppresses another error.
This applies to received-error TTL expiry and oversized-DF rejection.
[Error-on-error suppression][send].

DF-clear received errors can require fragmentation after postrouting.
A 576-byte received error can exceed a legal 68-byte egress MTU.
The model therefore returns certified fragment families, including for legal small egress MTUs.
The retained native topology uses egress MTU at least 576; smaller-MTU fragmentation is exercised by synthetic tests.
[Output fragmentation][output], [IPv4 minimum forwarding size](https://www.rfc-editor.org/rfc/rfc791.html#section-3.2).

## Linux UDP host PMTU processing

On local delivery, `icmp_unreach` obtains the reported MTU under the namespace's PMTU policy.
`icmp_socket_deliver` requires the quoted IP header plus eight transport bytes before calling the quoted protocol's error handler.
[Local error dispatch][icmp-deliver].

`__udp4_lib_err` looks up a UDP socket using the quoted addresses and ports, including applicable interface scope.
For Fragmentation Needed, it calls `ipv4_sk_update_pmtu` before reporting the socket error.
With PMTU discovery enabled, it reports `EMSGSIZE`.
`IP_RECVERR` additionally queues extended information; a connected socket can receive the hard error without that option.
This handler has no recent-send ledger, quoted payload comparison, or authentication of the ICMP outer source.
[UDP error handling][udp-error].

`IP_MTU` reads the connected socket's cached destination MTU.
The extended error records ICMP origin, type, code, errno, and advertised MTU in `ee_info`.
The local send path rejects oversized `IP_PMTUDISC_DO` datagrams with `EMSGSIZE`.
For IHL five, application payload plus 28 bytes must fit the selected PMTU.
Drain pending socket errors before attributing subsequent send results to the new size limit.
[Socket MTU and error information][sockopt], [local size rejection][send-size], [DF policy][ip-policy].

`ipv4_sk_update_pmtu` uses the socket route when available, otherwise performing an output-route lookup.
`__ip_rt_update_pmtu` rejects an advertised increase and respects a locked MTU.
Values below configured `min_pmtu` are clamped to the smaller of the current MTU and that floor, then locked.
The normal default floor is 552 bytes.
Updates populate destination exceptions attached to the selected route nexthop, rather than a per-datagram sending ledger.
The default expiry is 600 seconds; equal updates can refresh it subject to the half-expiry check.
Route changes, exception eviction, allocation failure, and expiry can affect later behavior.
[Route updates and exceptions][route-pmtu], [exception storage][route-exception], [default constants][route-defaults].

For this kernel's ordinary UDP path, MTU zero reaches the route updater as zero and is clamped to `min_pmtu`.
The inspected path does not implement RFC 1191's optional plateau search.
Selected host state must preserve the configured floor, locking behavior, and expiry when those cases are modeled.
[ICMP MTU extraction][icmp-deliver], [route update][route-pmtu].

The ordinary namespace policy accepts UDP PMTU messages after socket lookup.
`ip_no_pmtu_disc=2` discards incoming PMTU messages.
Hardened mode three requires additional transport validation and excludes ordinary UDP.
Forwarding normally ignores learned protocol PMTUs because they can be forged.
Reverse-path filtering is a separate configurable source-route check, rather than authentication of an ICMP sender.
[Ubuntu networking controls][sysctl], [effective forwarding MTU][ip-policy].

## Model and evidence boundary

The gateway transition and host PMTU transition describe separate state machines.
Gateway association and translation preserve cached conntrack state; local host processing may decrease route PMTU afterward.
For fixed routes without expiry, selected host updates must be bounded and monotonically nonincreasing.
Unmatched socket tuples and non-Fragmentation-Needed errors must leave PMTU unchanged.
Larger or equal advertised values must not increase it.
These are selected transition obligations derived from the inspected paths, rather than a model of every Linux route-cache operation.
[Error association][ct-error], [UDP update trigger][udp-error], [route reduction][route-pmtu].

Correlation does not authenticate the sender.
A forged error with a matching quote and consistent outer destination can pass the inspected association and UDP socket checks.
Under the ordinary selected host policy, a smaller admissible MTU can therefore lower PMTU.
RFC 1191 explicitly identifies false low-MTU messages as a denial-of-service mechanism.
Requiring a trusted-router identity or a recent-send ledger would describe an additional policy, not these Linux UDP checks.
[Association inputs][ct-error], [UDP socket inputs][udp-error], [RFC 1191, section 8](https://www.rfc-editor.org/rfc/rfc1191.html#section-8).

Native evidence must retain the downstream router's oversized-DF error, both edge-side ICMP frames, socket PMTU, extended error, and subsequent send results.
It must distinguish translated quoted fields from the earlier forwarded TTL and compare cached connection identity and status before and after.
The end-to-end demonstration uses a connected UDP socket with `IP_PMTUDISC_DO`, a downstream MTU of 600, and a smaller successful retry.
The experiment must retain its actual namespace settings, routes, MTUs, and packet bytes.

Excluded behavior includes IP options, ICMP extensions, input fragments, helpers, XFRM, rerouting, policy changes, and concurrent connection updates.
The native capture excludes received-error output fragmentation; the model and synthetic tests cover it.
The PMTU model excludes route replacement, exception sharing across sockets, eviction, allocation failure, and optional legacy plateau search.
Linux source and captured metadata remain external evidence; model proofs do not establish kernel C refinement or authenticate captured packets.

[ct-error]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_proto_icmp.c?h=Ubuntu-6.8.0-117.117#n115
[ct-tuple]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n247
[ct-input]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n1968
[ct-confirm]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/net/netfilter/nf_conntrack_core.h?h=Ubuntu-6.8.0-117.117#n55
[nat-error]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n559
[nat-udp]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n39
[input]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_input.c?h=Ubuntu-6.8.0-117.117#n317
[forward]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_forward.c?h=Ubuntu-6.8.0-117.117#n118
[output]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n295
[send]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/icmp.c?h=Ubuntu-6.8.0-117.117#n658
[icmp-deliver]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/icmp.c?h=Ubuntu-6.8.0-117.117#n840
[udp-error]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/udp.c?h=Ubuntu-6.8.0-117.117#n776
[sockopt]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_sockglue.c?h=Ubuntu-6.8.0-117.117#n412
[send-size]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n988
[ip-policy]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/net/ip.h?h=Ubuntu-6.8.0-117.117#n435
[route-pmtu]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/route.c?h=Ubuntu-6.8.0-117.117#n1029
[route-exception]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/route.c?h=Ubuntu-6.8.0-117.117#n654
[route-defaults]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/route.c?h=Ubuntu-6.8.0-117.117#n114
[sysctl]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/Documentation/networking/ip-sysctl.rst?h=Ubuntu-6.8.0-117.117#n26
