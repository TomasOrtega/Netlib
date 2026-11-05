# Check IPv4 and UDP bytes

The wire layer derives packet-policy headers from captured bytes.
It validates the IPv4 header checksum and each present UDP pseudoheader checksum.
A zero UDP checksum remains explicitly omitted.
The checksum does not authenticate a sender or establish freshness.

```sh
lake exe netlib wire examples/wire/frame.json --json
```

Input schema 1 has exactly `schema` and `raw` fields.
`raw` contains hexadecimal Ethernet bytes without separators.
The command returns the decoded header, transport payload, link padding, checksum status, and profile assumptions.
Successful checks return exit code zero.
Malformed input, invalid checksums, and unsupported encodings return exit code two.
The command does not inspect a live interface.

## Selected wire profile

The Ethernet envelope has a fourteen-byte header and EtherType `0x0800`.
The capture excludes the Ethernet FCS.
VLAN tags and other encapsulations need separate models.
The binary envelope preserves every payload byte.

The IPv4 profile selects version 4 and IHL 5.
It retains TOS, identification, DF, TTL, protocol, both addresses, and the declared payload.
Reserved flags, MF, nonzero fragment offsets, and options are outside this profile.
The declared total length must fit the received bytes and include the twenty-byte header.
Bytes beyond that total remain separate link padding.
The decoder checks the received header checksum and preserves its original word.
[RFC 791, section 3.1](https://www.rfc-editor.org/rfc/rfc791.html#section-3.1).

UDP uses protocol 17 and an eight-byte header.
The pseudoheader includes both IPv4 addresses, protocol, and UDP length.
This profile requires the UDP length to equal the entire IPv4 payload.
It retains source port zero and checksum omission.
Checksum synthesis changes a computed zero to `0xffff`, as required for UDP.
[RFC 768](https://www.rfc-editor.org/rfc/rfc768.html).

The profile covers framing and checksum arithmetic.
It does not establish valid address use, native transport classification, route availability, delivery time, or application authorization by itself.
TTL is a retained byte; forwarding and expiration need their own semantics.
IPv4 options, fragmentation, reassembly, IPv6, and full TCP behavior remain open.

## Proof chain

`Protocol.InternetChecksum` pairs adjacent bytes in network order and pads a final odd byte with zero.
Its arithmetic keeps both representations of one's-complement zero.
General aligned-insertion theorems prove checksum synthesis for arbitrary payloads.
The UDP synthesis theorem also proves that its transmitted checksum is nonzero.
[RFC 1071, section 1](https://www.rfc-editor.org/rfc/rfc1071.html#section-1).

The IPv4 and UDP codecs prove structured encodings decode correctly.
Their converse theorems reconstruct every accepted byte sequence exactly.
IPv4 reconstruction retains the received checksum and outer padding.
UDP checksum verification uses the actual decoded addresses and transport bytes.
Changing an address, port, or payload can invalidate that checksum.

`Check.Wire.Checked` carries successful Ethernet and transport decode equations for the original input bytes.
Its policy header contains decoded source, destination, protocol, and ports.
The input format cannot replace these fields with a supplied JSON header.
The text hex parser has runtime tests; its general correctness remains unproved.

The deployment example connects this decoded header to the checked native [session firewall](SESSION_FIREWALL.md) and tracked forwarding output.
The header must describe the actual modeled forward stage after destination NAT and before source NAT.
That association and principal-to-header binding remain deployment assumptions.
The model does not yet prove checksum updates through native NAT.
The lifecycle tracks header fields; it does not prove payload preservation or TTL updates during forwarding.
The payload reconstruction theorem concerns the decoded capture.

## Native capture and offload

The [capture recipe](../examples/wire/README.md) uses a private EAP-authenticated gateway and ordinary UDP sockets.
It disables transmit checksum offload and segmentation or aggregation features on the private veth interfaces.
Retained readbacks and independent arithmetic checks establish complete checksum bytes for the selected frames.
The experiment repeats the four session admission checkpoints and retains the same cached flow after Logoff.

Separate raw probes distinguish valid UDP, omitted UDP checksums, invalid UDP checksums, invalid UDP lengths, and invalid IPv4 header checksums.
Gateway egress and final socket reception are separate observations.
A packet can pass the forward filter before the destination transport rejects it.
These probes run in a separate test phase with an explicit permit policy.
They do not extend the session-admission guarantee beyond its checked checkpoints.

Earlier [admission frames](../examples/admission/README.md) retain checksum-offload intermediates.
They remain evidence for their declared tuple and forwarding observations.
They cannot establish completed UDP checksum validity from those bytes alone.
The strict wire command rejects those nonzero partial checksums.
[Linux checksum-offload documentation](https://docs.kernel.org/networking/checksum-offloads.html).

The experiment supplies finite implementation evidence.
Authentic collection, capture location, physical link identity, cryptographic method results, and current policy installation remain assumptions.
The [roadmap](ROADMAP.md) keeps complete stack and architecture refinement open.
The [source note](research/IPV4_UDP_WIRE.md) records the exact RFC and native Linux interpretation.
