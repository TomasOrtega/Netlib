# IPv4 UDP forwarding through tracked NAT

This note supports the selected [wire profile](../WIRE.md) and [native capture](../../examples/wire-nat/native/observations.json).
Kernel citations use official Ubuntu source tagged `Ubuntu-6.8.0-117.117`.
The capture reports `6.8.0-117-generic`; matching source and release names do not prove binary equivalence.
[Captured release](../../examples/wire-nat/native/kernel.txt).
[Ubuntu source](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_forward.c?h=Ubuntu-6.8.0-117.117).

## Required lifetime and checksum behavior

RFC 1812 requires forwarding routers to decrease TTL by at least one.
Expiry requires discarding the packet and, for nonmulticast destinations, sending ICMP Time Exceeded, subject to applicable ICMP rules.
TTL checks belong to forwarding; a valid packet addressed to the router can arrive with TTL zero or one.
[RFC 1812, sections 5.3.1 and 4.2.2.9](https://www.rfc-editor.org/rfc/rfc1812.html#section-5.3.1).

RFC 791 defines an eight-bit TTL and a checksum covering only the IPv4 header.
Header changes require checksum updates; checksum calculation clears the checksum field and complements the one's-complement sum.
[RFC 791, section 3.1](https://www.rfc-editor.org/rfc/rfc791.html#section-3.1).

UDP checksum coverage includes both IP addresses, protocol, UDP length, UDP header, and payload.
A transmitted zero omits the checksum; a computed zero becomes `0xffff`.
Thus, address and port translation require checksum changes when a checksum is present.
[RFC 768](https://www.rfc-editor.org/rfc/rfc768.html).

## Ubuntu processing order

Prerouting conntrack runs at priority `-200`; destination NAT runs at `-100`.
`nf_conntrack_in` resolves the original or reply tuple and invokes the transport tracker.
After successful reply tracking, it sets `IPS_SEEN_REPLY` before returning to later prerouting hooks.
[Hook priorities](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/netfilter_ipv4.h?h=Ubuntu-6.8.0-117.117#n30).
[Conntrack registration](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_proto.c?h=Ubuntu-6.8.0-117.117#n235).
[Lookup and reply observation](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n2003).
[NAT registration](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n828).

After prerouting, `ip_rcv_finish_core` obtains the destination route using the current destination address.
Destination NAT drops an existing route when it changes that address.
The transit route selects `ip_forward`, so this route decision precedes its TTL check.
[Prerouting continuation and route lookup](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_input.c?h=Ubuntu-6.8.0-117.117#n317).
[Changed-destination route invalidation](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n649).
[Transit route](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/route.c?h=Ubuntu-6.8.0-117.117#n1896).

`ip_forward` sends TTL values zero and one to its expiry path before the forward hook.
For surviving packets, `ip_decrease_ttl` updates the IPv4 checksum and decreases TTL before `NF_INET_FORWARD`.
Therefore, forward filtering observes the decreased TTL.
[Forwarding and expiry](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_forward.c?h=Ubuntu-6.8.0-117.117#n118).
[TTL checksum update](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/net/ip.h?h=Ubuntu-6.8.0-117.117#n416).

The accepted transit path reaches postrouting through `ip_output`.
Source NAT runs there at priority `100`; conntrack confirmation runs at `INT_MAX`.
Inference: an expired UDP packet reaches neither forward filtering, source NAT, nor its postrouting confirmation.
Its earlier reply observation on an existing connection remains; expiry does not undo that shared status update.
Generated ICMP packets have separate processing, outside this UDP claim.
[Output hook](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n426).
[Source NAT registration](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n836).
[Confirmation registration](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_proto.c?h=Ubuntu-6.8.0-117.117#n248).
[Reply update](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n2042).

NAT reuses initialized connection mappings; reply-direction processing reverses the relevant source or destination translation.
IPv4 address rewriting incrementally updates the header checksum.
UDP rewriting updates the pseudoheader address and changed port when the checksum is nonzero.
It preserves an omitted checksum and converts an updated zero to `CSUM_MANGLED_0`.
[Cached and reverse translation](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_core.c?h=Ubuntu-6.8.0-117.117#n872).
[IPv4 checksum changes](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n353).
[UDP checksum changes](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n39).

## Model correspondence and comparison

`UDPRewrite.rewrite` is total for its valid-input witness and UDP target header.
It preserves payload, TOS, identification, DF, and total length, while setting the supplied tuple and TTL.
It preserves checksum omission, fully recomputes present UDP checksums, computes the IPv4 checksum, and emits no link padding.
Its certified result proves successful encoding, decoding, field preservation, and checksum validity.
[Rewriter and proofs](../../Netlib/Protocol/UDPRewrite.lean).

`WireForwarding.step` validates the decoded packet and prepares the connection attachment once.
It checks routing after destination translation before deciding TTL expiry.
Expiry retains the prepared state, including an existing reply observation, without confirming a fresh entry.
Otherwise, the existing lifecycle handles filtering, source NAT, and confirmation; forwarded output uses the certified rewriter with TTL decreased once.
[Forwarding model and proofs](../../Netlib/Protocol/WireForwarding.lean).

RFC 1624 explains the two one's-complement zero representations and the boundary difference between some incremental updates and full recomputation.
Both representations can pass sum-based checksum verification.
[RFC 1624, sections 3–5](https://www.rfc-editor.org/rfc/rfc1624.html#section-3).

The replay compares the decoded IPv4 packet and complete UDP datagram after validating both captured Ethernet envelopes.
This retains all modeled IP fields and the UDP checksum word, while excluding Ethernet adjacency, link padding, and IPv4 checksum representation.
Therefore, comparison requires checksum validity but does not require matching IPv4 checksum zero representations.
Missing intermediate observations are unchecked; missing output asserts no selected UDP egress within the supplied observation scope.
[Replay comparison and assumptions](../../Netlib/Check/WireForwarding.lean).

## Retained native observations

The four admission stages retain requests before authentication, after authentication, with the demo credential, and after Logoff.
The permitted request changes `192.0.2.2:41000 → 203.0.113.2:8080` into `203.0.113.1:40000 → 198.51.100.2:9000`.
Its normal reply restores `203.0.113.2:8080 → 192.0.2.2:41000`, with TTL decreased once in each direction.
The other admission stages have no selected UDP egress.
[Raw frames](../../examples/wire-nat/native/frames.jsonl).
[Stage and socket observations](../../examples/wire-nat/native/observations.json).

Before the normal reply, a server reply with TTL one produces no selected UDP egress.
The snapshots retain the same connection ID while status changes from `440` to `442`, adding the reply-seen bit.
The raw capture also retains the generated ICMP frame.
This observation supports the source-derived ordering; it does not establish ICMP correctness.
[Before snapshot](../../examples/wire-nat/native/before-ttl-one-reply-conntrack.json).
[After snapshot](../../examples/wire-nat/native/after-ttl-one-reply-conntrack.json).
[Status-bit definitions](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/netfilter/nf_conntrack_common.h?h=Ubuntu-6.8.0-117.117#n41).
[Raw frames](../../examples/wire-nat/native/frames.jsonl).

After Logoff, the cached flow remains recorded while its request is denied.
Targeted deletion then produces an empty snapshot.
[Cached state](../../examples/wire-nat/native/logged-off-cached-conntrack.json).
[Deletion result](../../examples/wire-nat/native/erased-conntrack.json).
[Stage observations](../../examples/wire-nat/native/observations.json).

The isolated permit-policy suffix sends fresh requests with TTL zero, one, and two.
The first two have no UDP egress and leave empty confirmed-table snapshots.
TTL two forwards as TTL one and leaves a confirmed mapping.
A later checksum-omitted request reuses that mapping and retains UDP checksum zero across both translations.
[Probe observations](../../examples/wire-nat/native/observations.json).
[TTL-zero state](../../examples/wire-nat/native/ttl-zero-after-conntrack.json).
[TTL-one state](../../examples/wire-nat/native/ttl-one-after-conntrack.json).
[TTL-two state](../../examples/wire-nat/native/ttl-two-after-conntrack.json).
[Checksum-omitted state](../../examples/wire-nat/native/udp-zero-after-conntrack.json).
[Raw frames](../../examples/wire-nat/native/frames.jsonl).

These are finite observations under retained policies, routes, and conntrack snapshots.
The profile assumes sufficient MTU, ordinary UDP tracking, stable hooks, faithful capture attribution, and the current principal-to-address binding.
It excludes fragmentation, ICMP semantics, concurrent expiry, helper behavior, and kernel implementation refinement.
The isolated probe suffix does not extend the four admission checkpoints.
[Replay assumptions](../../Netlib/Check/WireForwarding.lean).
[Earlier framing and offload analysis](IPV4_UDP_WIRE.md).
