# Generated IPv4 ICMP forwarding errors

This note separates protocol requirements, inspected Linux source, retained observations, and the selected model boundary.
The profile covers whole IPv4 UDP input with IHL five, ordinary conntrack, and stable routing and NAT mappings.

## Protocol requirements

Time Exceeded uses type 11, code zero for transit TTL expiry.
Fragmentation Needed uses type three, code four for oversized DF input.
Both contain an eight-byte ICMP header and the original IP header plus at least eight payload bytes.
The checksum covers the complete ICMP message, with its checksum field cleared during calculation.
Unused fields are zero.
[RFC 792](https://www.rfc-editor.org/rfc/rfc792.html).

Fragmentation Needed places the next-hop MTU in the low 16 bits after the checksum.
The preceding 16 bits remain zero.
This MTU includes IP headers, excludes link headers, and cannot be below 68.
[RFC 1191, section 4](https://www.rfc-editor.org/rfc/rfc1191.html#section-4).

Routers should quote as much input as possible without exceeding 576 bytes for the complete generated datagram.
The quote preserves received bytes, except permitted forwarding changes already performed before error detection.
Generated TTL is initialized independently of the triggering TTL.
Ordinary source selection uses an address of the output interface, with the specified unnumbered-interface exception.
[RFC 1812, sections 4.3.2.2–4.3.2.4](https://www.rfc-editor.org/rfc/rfc1812.html#section-4.3.2.2).

Errors are suppressed for ICMP errors, noninitial fragments, broadcast or multicast destinations, link broadcasts, and sources that do not identify one host.
Router restrictions also cover link multicast, invalid IP headers, and required silent discards.
Restrictions take precedence over error-generation requirements.
[RFC 1122, section 3.2.2](https://www.rfc-editor.org/rfc/rfc1122.html#section-3.2.2),
[RFC 1812, section 4.3.2.7](https://www.rfc-editor.org/rfc/rfc1812.html#section-4.3.2.7).

NAT devices must generate the applicable TTL and oversized-DF errors, subject to applicable suppression rules.
For received errors, matching mappings govern embedded and outer address translation.
An incomplete quote does not establish the embedded transport checksum's validity.
RFC 5508 recommends against validating that checksum, even when the complete transport segment is available.
[RFC 5508, sections 4.1–4.2 and 7.1–7.2](https://www.rfc-editor.org/rfc/rfc5508.html#section-4.1).

## Inspected Ubuntu order

All kernel citations select tag `Ubuntu-6.8.0-117.117`.
The retained host reports `6.8.0-117-generic`.
Matching release names and inspected source do not prove equivalence with the running binary.
[Kernel observation](../../examples/mtu/native/kernel.txt), [tagged source][forward].

1. Prerouting tracking and destination translation precede the transit route and `ip_forward`.
   A tracked reply records `IPS_SEEN_REPLY` during conntrack processing.
   [Receive continuation][input], [conntrack reply update][ct-in], [hook priorities][priorities].
2. `ip_forward` tests TTL at most one before its oversized-DF check.
   Both rejection paths call `icmp_send` before decreasing TTL or invoking `NF_INET_FORWARD`.
   The rejected UDP packet does not reach postrouting source NAT or confirmation.
   [Forwarding rejection paths][forward].
3. `__icmp_send` checks eligibility, selects a reverse route, limits the quote, and builds the ICMP message.
   `icmp_glue_bits` copies the current packet bytes and calls `nf_ct_attach` for an error.
   This initial quote therefore reflects the packet after prerouting translation.
   [Error construction][send], [quote copying and attachment][glue].
4. `nf_ct_attach` reuses the triggering packet's connection, including an unconfirmed candidate.
   It attaches original-direction input as `RELATED_REPLY` and reply-direction input as `RELATED`.
   [Attachment guard][attach-guard], [direction reversal][attach].
5. Generated output traverses `LOCAL_OUT`, followed by `POST_ROUTING` on the selected ordinary route.
   Local conntrack accepts an existing nontemplate attachment without tracking a new packet.
   Destination NAT runs at priority `-100`, source NAT at `100`, and confirmation at `INT_MAX`.
   [Local output][local-out], [output continuation][output], [tracking bypass][ct-in], [NAT hooks][nat-hooks], [priorities][priorities].
6. The NAT hook handles related ICMP specially, before ordinary NAT processing.
   It rewrites the quote with the opposite connection tuple and the opposite manipulation direction.
   It updates the embedded checksums, ICMP checksum, and corresponding outer address.
   This path tests NAT status and attachment direction, without requiring connection confirmation.
   [Related ICMP translation][nat-icmp], [IPv4 and UDP rewriting][nat-rewrite].
7. Confirmation skips already confirmed connections.
   For an unconfirmed connection, reverse-direction generated errors pass without inserting the candidate.
   Generated local tracking also does not create a new reply observation.
   [Confirmation wrapper][confirm-wrapper], [direction guard][confirm], [tracking bypass][ct-in].

Inference: fresh original-direction TTL and DF rejection retain no confirmed entry through this generated-error path.
An earlier reply observation on an existing entry survives rejection.
An emitted error does not imply that forward filtering would have authorized the rejected UDP packet.

## Wire choices and model inputs

For no IP options, Linux selects the following quote length from the triggering IP packet:

```text
quoteLength = min(inputIPLength, min(reverseRouteMTU, 576) - 20 - 8)
```

The reverse-route MTU bounds generated output, independently of the forward MTU reported by Fragmentation Needed.
Linux suppresses construction when the quote budget is at most 20 bytes.
With reverse MTU at least 68 and valid whole UDP input, the quote includes at least 28 bytes.
The embedded total length and UDP length still describe the complete triggering packet.
A truncated quote must therefore use a prefix parser, rather than a complete-datagram decoder.
[Quote budget and copying][send].

Linux derives error TOS as `(inputTos & 0x1e) | 0xc0`.
It selects an initial source through local-route state, the inbound-address setting, and reverse routing.
Related NAT can subsequently replace that source with the ingress destination VIP or public address.
[TOS and initial source][send], [TOS mask][tos], [route construction][route-lookup], [NAT translation][nat-icmp].

The ICMP control socket disables path-MTU discovery, producing DF-clear output on the selected ordinary path.
Output TTL uses the socket value or the route hop limit, with the namespace default as fallback.
Identification comes from `ip_select_ident`.
These choices do not establish constant TTL 64 or a deterministic native identification sequence.
[Control socket][icmp-init], [header construction][header], [hop-limit fallback][hoplimit].

The model receives effective reverse MTU, preferred router source, output TTL, and identification as explicit environment choices.
It derives eligibility from the input addresses, link-group bit, and configured broadcast addresses.
It computes rejection kind, quoted fields, NAT restoration, checksum updates, and final addresses from its forwarding state.
The expected error outcome and ingress-quote equality are not assumptions.

Protocol eligibility and successful construction do not guarantee emission.
Linux can suppress errors through routing failure, allocation failure, transmit locking, output policy, or rate limits.
Its global and destination rate limits exempt Fragmentation Needed, while configured limits can suppress Time Exceeded.
The selected profile disables rate limiting and assumes successful allocation and transmission.
It models return-route absence and separate related output and late filters.
Other native suppression machinery remains outside it.
[Eligibility and failure paths][send], [rate-limit exemption][limits], [output hooks][local-out].

## Retained native evidence

The MTU parent capture retains these four emitted errors:

| Trigger | Type/code | Quote bytes | Outer source | Reported MTU |
| --- | --- | --- | --- | --- |
| Cached reply, TTL one | 11/0 | 66 | `203.0.113.1` | None |
| Cached request, oversized DF | 3/4 | 548 | `203.0.113.2` | 600 |
| Fresh request, oversized DF | 3/4 | 548 | `203.0.113.2` | 600 |
| Fresh request, TTL one and oversized DF | 11/0 | 548 | `203.0.113.2` | None |

Every retained quote exactly matches the corresponding ingress IP prefix, before prerouting NAT.
Every outer source equals that ingress packet's destination.
All four outer headers have TOS 192, TTL 64, and DF clear.
The large errors have total length 576.
These are checked byte observations under the captured mappings and routes.
They do not replace the model's derivation or prove a universal Linux equality rule.
[Captured frames](../../examples/mtu/native/frames.jsonl), [attributed observations](../../examples/mtu/checked-evidence.json).

The cached reply keeps its connection ID while status changes from 440 to 442, adding the reply-seen bit.
Fresh DF and TTL rejection leave empty confirmed-table snapshots.
[Before reply](../../examples/mtu/native/before-ttl-one-reply-conntrack.json),
[after reply](../../examples/mtu/native/after-ttl-one-reply-conntrack.json),
[fresh DF](../../examples/mtu/native/fresh-df-oversize-after-conntrack.json),
[fresh TTL](../../examples/mtu/native/ttl-one-df-oversize-after-conntrack.json).

The [fresh ICMP capture](../../examples/icmp/README.md) retains 12 errors across 21 replay events and 43 IP frames.
Its quotation probes cover input lengths 63, 64, 547, 548, 549, 575, 576, and 577 bytes.
Odd checksums, complete versus partial UDP quotes, omission, and reverse-direction related NAT are checked independently.
Inputs with TOS 3, 31, 171, and 126 produce the selected masked error TOS values.
Separate LOCAL_OUT and postrouting observations expose related filtering, initial router addresses, and final NAT addresses.
[Fresh bytes](../../examples/icmp/native/frames.jsonl), [checked observations](../../examples/icmp/checked-evidence.json).

The profile excludes received ICMP forwarding, ICMP extensions, IP options, input fragments, PMTU-cache updates, helpers, XFRM, rerouting, and concurrent state changes.
Capture attribution, environmental metadata, inspected C source, and executable binary behavior remain explicit trust boundaries.
Codec and transition proofs establish the selected model's properties, rather than a complete ICMP stack or kernel implementation refinement.

[forward]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_forward.c?h=Ubuntu-6.8.0-117.117#n118
[input]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_input.c?h=Ubuntu-6.8.0-117.117#n317
[priorities]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/netfilter_ipv4.h?h=Ubuntu-6.8.0-117.117#n30
[ct-in]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n1971
[send]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/icmp.c?h=Ubuntu-6.8.0-117.117#n601
[glue]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/icmp.c?h=Ubuntu-6.8.0-117.117#n356
[attach-guard]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/core.c?h=Ubuntu-6.8.0-117.117#n700
[attach]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n2146
[local-out]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n101
[output]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n426
[nat-hooks]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n836
[nat-icmp]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n559
[nat-rewrite]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_proto.c?h=Ubuntu-6.8.0-117.117#n39
[confirm-wrapper]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/net/netfilter/nf_conntrack_core.h?h=Ubuntu-6.8.0-117.117#n55
[confirm]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n1157
[tos]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/in_route.h?h=Ubuntu-6.8.0-117.117#n31
[route-lookup]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/icmp.c?h=Ubuntu-6.8.0-117.117#n487
[icmp-init]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/icmp.c?h=Ubuntu-6.8.0-117.117#n1516
[header]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n1395
[hoplimit]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/net/route.h?h=Ubuntu-6.8.0-117.117#n363
[limits]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/icmp.c?h=Ubuntu-6.8.0-117.117#n281
