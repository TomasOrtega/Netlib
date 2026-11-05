# IPv4 and UDP wire evidence

This note supports the selected [wire profile](../WIRE.md) and private [capture](../../examples/wire/README.md).
It uses protocol specifications, Linux documentation, and official Ubuntu source tagged `Ubuntu-6.8.0-117.117`.
The capture reports kernel `6.8.0-117-generic`; the source tag declares package `6.8.0-117.117`.
Source inspection does not establish equivalence with the running binary.
[Captured kernel](../../examples/wire/native/kernel.txt).
[Ubuntu source changelog](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/debian.master/changelog?h=Ubuntu-6.8.0-117.117#n1).

## IPv4 fields and profile choices

RFC 791 section 3.1 specifies version 4 and measures IHL in 32-bit words, with minimum value five.
Total Length counts the header and data in octets, up to 65535.
The reserved flag must be zero; DF controls fragmentation, MF identifies further fragments, and fragment offsets use eight-octet units.
The checksum covers only the header, with its checksum field cleared during calculation.
It complements the one's-complement sum of sixteen-bit header words.
[RFC 791, section 3.1](https://www.rfc-editor.org/rfc/rfc791.html#section-3.1).

The selected envelope uses untagged Ethernet, EtherType `0x0800`, and capture bytes without an Ethernet FCS.
Its IPv4 decoder selects IHL five, allows either DF value, and excludes options, MF, reserved flags, and nonzero fragment offsets.
It retains bytes beyond Total Length separately as link padding.
These are profile boundaries; IPv4 options and fragmentation have specified uses.
[Ethernet envelope](../../Netlib/Import/EthernetIPv4.lean).
[IPv4 decoder](../../Netlib/Protocol/IPv4.lean).
[RFC 791, section 3.1](https://www.rfc-editor.org/rfc/rfc791.html#section-3.1).

TTL is an eight-bit field that processing decreases, and a zero value requires destruction.
The decoder retains TTL without modeling this processing.
Inference: successful framing and checksum checks alone do not establish forwardability or remaining lifetime.
[RFC 791, section 3.1](https://www.rfc-editor.org/rfc/rfc791.html#section-3.1).
[IPv4 packet fields](../../Netlib/Protocol/IPv4.lean).

## UDP length and checksums

RFC 768 defines two sixteen-bit port fields; an unused source port has value zero.
UDP Length includes the eight-byte header and data, so its minimum is eight.
The checksum covers the pseudoheader, UDP header, and data, with zero padding for an odd byte count.
The pseudoheader contains both IP addresses, a zero byte, protocol 17, and UDP Length.
A transmitted zero means checksum omission.
A computed zero is transmitted as `0xffff`.
[RFC 768](https://www.rfc-editor.org/rfc/rfc768.html).

This profile requires UDP Length to equal the entire declared IPv4 payload.
The native source rejects a UDP length above available bytes or below eight.
It then calls `pskb_trim_rcsum` with UDP Length before checksum initialization.
That helper trims received bytes and adjusts checksum bookkeeping.
Inference: this receive path permits extra IPv4 payload bytes beyond UDP Length, subject to later checks.
The profile excludes such inputs without declaring them universally invalid.
[Ubuntu UDP receive path](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/udp.c?h=Ubuntu-6.8.0-117.117#n2455).
[Trim helper](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/linux/skbuff.h?h=Ubuntu-6.8.0-117.117#n3908).
[Selected UDP decoder](../../Netlib/Protocol/UDP.lean).

RFC 1071 describes adjacent-byte pairing, odd-byte zero padding, end-around carry, and verification against all-one bits.
Its status explicitly describes implementation techniques, rather than a standard.
The arithmetic preserves both one's-complement zero representations, `0x0000` and `0xffff`.
RFC 1624 explains this distinction and its effect on checksum updates.
[RFC 1071, section 1](https://www.rfc-editor.org/rfc/rfc1071.html#section-1).
[RFC 1624, section 3](https://www.rfc-editor.org/rfc/rfc1624.html#section-3).
[Checksum arithmetic](../../Netlib/Protocol/InternetChecksum.lean).

## Capture location and offload

Linux transmit offload computes the checksum later using the configured start and offset.
The existing checksum word can supply the pseudoheader contribution.
The documented transmit path always computes the IPv4 header checksum in software.
[Linux checksum-offload documentation](https://docs.kernel.org/networking/checksum-offloads.html#tx-checksum-offload).

The native AF_PACKET source maps `CHECKSUM_PARTIAL` to `TP_STATUS_CSUMNOTREADY` in auxiliary receive metadata.
Inference: packet-socket bytes can contain an incomplete transport checksum despite a nonzero checksum field.
Incoming packet sockets observe packets before kernel protocol handling.
`PACKET_OUTGOING` identifies locally originating packets looped back to a packet socket.
Therefore, a gateway egress observation does not establish final UDP socket reception.
[Ubuntu AF_PACKET metadata](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/packet/af_packet.c?h=Ubuntu-6.8.0-117.117#n3575).
[Linux packet manual](https://man7.org/linux/man-pages/man7/packet.7.html).

The seven earlier admission frames have valid IPv4 header checksums.
Their nonzero UDP checksum words equal pseudoheader sums and fail complete UDP checksum verification.
Inference: these bytes are consistent with checksum-offload intermediates.
They remain separate evidence for tuple and forwarding observations.
[Earlier raw frames](../../examples/admission/native/data-frames.jsonl).
[Independent arithmetic verifier](../../scripts/check_wire_capture.py).

The fresh recipe disables transmit checksum offload, TSO, GSO, and GRO through `SIOCETHTOOL` on all four private veth interfaces.
Retained readbacks record those features disabled before the first socket send.
All seven ordinary UDP frames have valid IPv4 checksums and complete, nonzero UDP checksums.
[Capture producer](../../examples/wire/exercise.py).
[Offload readbacks](../../examples/wire/native/offloads.json).
[Fresh raw frames](../../examples/wire/native/data-frames.jsonl).
[Offline verifier](../../scripts/check_wire_capture.py).

## Native probes and limits

The raw valid and checksum-omitted probes reach the final UDP socket.
Bad UDP checksum and declared-length-seven probes appear at gateway egress but receive no UDP socket payload within the measured window.
The bad IPv4 checksum probe appears only at ingress.
The native IPv4 source checks the header checksum before its prerouting hook.
[Probe observations](../../examples/wire/native/probe-observations.json).
[Probe frames](../../examples/wire/native/probe-frames.jsonl).
[Ubuntu IPv4 receive checks](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_input.c?h=Ubuntu-6.8.0-117.117#n511).
[Prerouting continuation](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_input.c?h=Ubuntu-6.8.0-117.117#n561).

The probe phase follows the EAP episode and explicitly installs the generated permit policy.
Its outcomes do not extend the session-admission guarantee beyond the four checked checkpoints.
These observations provide finite implementation evidence.
They do not prove cryptographic authentication, capture authenticity, universal delivery behavior, or implementation refinement.
[Probe policy and timing checks](../../scripts/check_wire_capture.py).
[Session observations](../../examples/wire/native/observations.json).
