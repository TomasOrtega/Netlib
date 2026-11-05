# IPv4 MTU decisions and fragment families

This note supports the [selected MTU profile](../MTU.md) and its [native observations](../../examples/mtu/native/observations.json).
It separates protocol requirements, inspected kernel source, and the narrower evidence model.

## Source ledger

| Source | Use |
| --- | --- |
| [RFC 791, sections 3.1–3.2](https://www.rfc-editor.org/rfc/rfc791.html#section-3.1) | IPv4 lengths, flags, offsets, fragmentation, and destination reassembly. |
| [RFC 1812, sections 4.2.2.7–4.2.2.8 and 5.2.6](https://www.rfc-editor.org/rfc/rfc1812.html#section-4.2.2.7) | Router fragmentation requirements and transit reassembly restriction. |
| [RFC 1191, sections 3–4](https://www.rfc-editor.org/rfc/rfc1191.html#section-4) | DF rejection, reported next-hop MTU, and the 68-byte floor. |
| [Ubuntu source tag `Ubuntu-6.8.0-117.117`](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_forward.c?h=Ubuntu-6.8.0-117.117) | Exact source release inspected for forwarding, hooks, effective MTU, and output fragmentation. |
| [Upstream Linux `v6.8`, `ip_forward`](https://github.com/torvalds/linux/blob/v6.8/net/ipv4/ip_forward.c#L118-L163) | Upstream comparison for the selected TTL, MTU, and forward-hook ordering. |

The capture reports host kernel `6.8.0-117-generic`; its container packages describe Alpine userland, including separately versioned kernel headers.
The Ubuntu tag matches the reported release lineage; neither that match nor upstream `v6.8` establishes runtime binary equivalence.
[Captured kernel](../../examples/mtu/native/kernel.txt).
[Container packages](../../examples/mtu/native/packages.txt).

## Protocol requirements

IPv4 Total Length includes the header and data, with a maximum of 65,535 bytes.
DF prohibits fragmentation; MF marks every fragment except the last.
The 13-bit offset counts eight-byte units relative to the original IP payload.
Every nonfinal payload ends on an eight-byte boundary; the final payload can be shorter.
Reassembly identifies a datagram through source, destination, protocol, and identification.
Every internet module must forward 68 bytes without further fragmentation.
The 68-byte requirement accommodates a maximal 60-byte header and eight payload bytes.
[RFC 791, sections 3.1–3.2](https://www.rfc-editor.org/rfc/rfc791.html#section-3.2).

Routers MUST support fragmentation, SHOULD minimize fragment count, and SHOULD send fragments in order.
Routers MUST support reassembly for local delivery and MUST NOT reassemble transit datagrams before forwarding.
[RFC 1812, sections 4.2.2.7–4.2.2.8](https://www.rfc-editor.org/rfc/rfc1812.html#section-4.2.2.7), [section 5.2.6](https://www.rfc-editor.org/rfc/rfc1812.html#section-5.2.6).

An oversized DF packet requires ICMP Destination Unreachable, code four, subject to applicable ICMP restrictions.
The error carries the next-hop MTU, including IP headers and excluding link headers.
RFC 1191 prohibits host PMTU estimates below 68 bytes and specifies no smaller next-hop MTU.
[RFC 1191, sections 3–4](https://www.rfc-editor.org/rfc/rfc1191.html#section-3), [ICMP restrictions](https://www.rfc-editor.org/rfc/rfc1812.html#section-4.3.2.7).

## Inspected Linux ordering

These statements use the Ubuntu tag above and the ordinary transit path without the exclusions listed below.

1. Prerouting finishes before route lookup; the selected transit route invokes `ip_forward`.
   [Receive continuation and routing](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_input.c?h=Ubuntu-6.8.0-117.117#n317), [transit route callback](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/route.c?h=Ubuntu-6.8.0-117.117#n1896).
2. `ip_forward` tests `TTL ≤ 1`, selects the effective MTU, and rejects oversized DF packets before `NF_INET_FORWARD`.
   Surviving packets receive the TTL decrement before that hook.
   [TTL, MTU, and forward hook](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_forward.c?h=Ubuntu-6.8.0-117.117#n118).
3. `ip_output` runs `NF_INET_POST_ROUTING` before its `ip_finish_output` continuation.
   Source NAT has priority `100`; ordinary conntrack confirmation has priority `INT_MAX`.
   [Output continuation](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n426), [NAT registration](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n836), [confirmation registration](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_proto.c?h=Ubuntu-6.8.0-117.117#n248), [priorities](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/netfilter_ipv4.h?h=Ubuntu-6.8.0-117.117#n30).
4. `__ip_finish_output` checks output size and invokes fragmentation after those postrouting hooks.
   `ip_frag_next` copies the translated header, aligns nonfinal payloads, sets offsets and MF, and recomputes each IP checksum.
   [Output fragmentation](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n295), [fragment construction](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n684).

Inference: selected TTL expiry and DF rejection precede forward filtering, source NAT, and postrouting confirmation of that UDP packet.
Successful selected fragmentation follows translation and confirmation; it does not repeat those operations for each generated fragment.
Generated ICMP follows separate processing.

Effective MTU is not necessarily device MTU.
`ip_dst_mtu_maybe_forward` considers applicable PMTU state, MTU locks, route `RTAX_MTU`, device fallback, and tunnel headroom.
Output calls the corresponding helper again; a stable route and effective MTU connect the two selected decisions.
The model receives that effective value within `68…65535`; it does not implement the kernel's selection machinery.
[Effective MTU helpers](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/net/ip.h?h=Ubuntu-6.8.0-117.117#n466).

## Selected evidence profile

The model accepts whole, unfragmented IPv4 UDP input with IHL five.
It prepares conntrack and destination translation once, then orders routing, TTL expiry, oversized DF rejection, filtering, source translation, and confirmation.
Successful translated output is fragmented afterward.
For MTU `m`, maximal nonfinal payload length is `8 * floor((m - 20) / 8)`.
Splitting covers the entire IP payload, including the UDP header, while preserving the whole translated UDP checksum or its omission.
[Forwarding model](../../Netlib/Protocol/MTUForwarding.lean), [fragment generation](../../Netlib/Protocol/IPv4Fragmentation.lean).

The family validator sorts fragments and requires consistent TOS, identification, DF, TTL, protocol, source, and destination.
It rejects gaps, overlaps, duplicates, missing final fragments, trailing fragments, invalid checksums, and reconstructed lengths above 65,535.
It validates UDP only after complete IP payload recovery.
[Strict reassembly](../../Netlib/Protocol/IPv4Fragmentation.lean), [wire checker](../../Netlib/Check/IPv4Fragments.lean).

These are deliberately strict evidence rules, not a universal native reassembly policy.
RFC 791's example reassembly procedure can replace overlapping data with later arrivals.
The codec also excludes the reserved flag, whereas RFC 1812 requires routers to pass reserved bits unchanged.
[RFC 791 reassembly discussion](https://www.rfc-editor.org/rfc/rfc791.html#section-3.2), [RFC 1812, section 5.2.5](https://www.rfc-editor.org/rfc/rfc1812.html#section-5.2.5), [selected codec](../../Netlib/Protocol/IPv4Fragment.lean).

## Native observations and limits

The fresh capture uses peer MTU 4,096 and service MTU 600, with selected transmit and segmentation offloads disabled.
An ordinary UDP socket sends 1,200 application bytes as one DF-clear, 1,228-byte input.
Permitted NAT forwarding emits IP lengths `596, 596, 76`, with byte offsets `0, 576, 1152`; the server socket receives the original payload.
The other three admission stages retain no selected UDP output, including cached forwarding after Logoff.
[Socket and stage observations](../../examples/mtu/native/observations.json), [offload state](../../examples/mtu/native/offloads.json), [captured frames](../../examples/mtu/native/frames.jsonl).

Separate probes cover cached and fresh DF rejection, TTL-one precedence, exact-MTU DF forwarding, oversized DF-clear fragmentation, and checksum-omitted fragmentation.
Their fixed permit suffix isolates packet mechanics and establishes no new current-session authorization claim.
Cached DF rejection retains its connection ID; fresh DF rejection and TTL-one rejection leave empty confirmed-table snapshots.
The TTL-one oversized DF probe produces Time Exceeded; oversized DF probes report fragmentation needed with MTU 600.
[Checked observations](../../examples/mtu/checked-evidence.json), [cached snapshots](../../examples/mtu/native/cached-df-oversize-after-conntrack.json), [fresh snapshots](../../examples/mtu/native/fresh-df-oversize-after-conntrack.json), [TTL snapshot](../../examples/mtu/native/ttl-one-df-oversize-after-conntrack.json).

Excluded behavior includes input fragment reassembly, IP options, ICMP generation and side effects, PMTU cache updates, GSO, `ignore_df`, and `frag_max_size`.
Rerouting, XFRM, BPF effects, allocation failures, partial emission, timers, resource eviction, concurrency, and kernel C refinement also remain outside the selected model.
Thus, successful confirmation does not universally guarantee native fragment delivery.
[Native exception paths](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_forward.c?h=Ubuntu-6.8.0-117.117#n43), [output exceptions and allocation](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n295), [model scope](../MTU.md).
