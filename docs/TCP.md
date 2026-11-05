# TCP framing and serial arithmetic

Netlib does checks of TCP segment bytes, their selected IPv4 envelope, and circular sequence arithmetic.
It also supplies certified tuple rewriting and a byte adapter for completed IPv4 reassembly.
The [receive-state model](TCP_RECEIVE.md) adds sequence tests and bounded ACK processing above these byte contracts.
They do not establish a TCP connection, transport delivery, native conntrack classification, or full implementation refinement.

## Check commands

```sh
lake exe netlib tcp-segment examples/tcp/segment.json --json
lake exe netlib tcp-wire examples/tcp/frame.json --json
lake exe netlib tcp-sequence examples/tcp/sequence.json --json
```

The segment input has this shape:

```json
{
  "schema": 1,
  "source": "192.0.2.1",
  "destination": "198.51.100.2",
  "raw": "30390050000000000000000050101000000000008312"
}
```

The addresses supply the IPv4 pseudoheader for mandatory TCP checksum verification.
The wire command instead derives those addresses from checked Ethernet and IPv4 bytes.
Its input contains `schema: 1` and a hexadecimal `raw` Ethernet frame.
The selected IPv4 codec requires IHL five and a whole datagram.
Ethernet padding remains outside the declared TCP segment.
For fragmented input, the separate adapter uses the output after IPv4 reassembly.

The sequence query contains `schema: 1`, two unsigned 32-bit words named `first` and `second`, and an interval `length`.
It reports unsigned forward distance, the two serial comparisons, equality, and left-closed interval membership.
The interval length can be `2^32`. The report identifies lengths shorter than half the sequence space.
This calculation does not decide receive-window acceptance or acknowledgment validity.

## Byte contracts

The codec preserves ports, sequence and acknowledgment words, reserved bits, all eight flags, window, urgent pointer, options, payload, and received checksum.
Data Offset selects a header between twenty and sixty bytes.
Accepted decoding consumes the entire supplied segment and reconstructs those exact bytes.
The inverse theorem decodes every encodable segment whose mandatory checksum verifies.

TCP checksum zero has no omission meaning.
The example above has a valid computed zero checksum.
Its full pseudoheader checksum still verifies.
A received `ffff` word can also verify for this arithmetic case and remains unchanged under exact re-encoding.
Recomputation emits the actual complement, which can be zero.
The TCP codec does not use the UDP rules for omitted checksums or zero substitution.

Option framing handles EOL, NOP, inclusive TLV lengths, and the forty-byte header bound.
EOL padding must be zero.
Unknown well-formed option bodies remain uninterpreted and unchanged.
The codec examines MSS length. A separate predicate permits an MSS option only in a segment with the SYN flag.
The report's `selectedOptionSemantics` does a check of only that MSS placement condition.
It does not validate every TCP option or flag combination.

The codec keeps received reserved bits.
Fresh `computed` generation clears them and supplies the mandatory checksum.
That helper does not select a valid connection state, flag combination, or negotiated option set.
Malformed construction remains possible until the encoder or decoder does a check of structural validity.

## Sequence-space laws

`TCP.Seq` has a 32-bit representation and no global ordering instance.
Serial `Before` means that unsigned forward distance lies strictly between zero and `2^31`.
Equality and an exact half-space difference are incomparable.
Translation preserves distances and comparisons.

Unrestricted transitivity is false around the circular space.
The library proves transitivity under an explicit bounded sum of forward distances.
Common-arc order laws require all coordinates to lie within one arc shorter than `2^31`.
Interval coordinates then have unique bounded offsets.
Payload consumes its byte count. SYN and FIN each consume one additional sequence position.
These facts do not establish freshness after sequence reuse.

## Composition

`TCP.DecodedIPv4.Valid` connects the segment to the actual declared IPv4 payload and protocol six.
The two layered codec directions preserve accepted bytes. These bytes include external padding.
`Check.WireTCP` derives policy headers from checked transport fields and IPv4 addresses.
Its checksum theorem remains unconditional when the received checksum word is zero.

`TCPRewrite.Certified` changes the declared endpoint tuple and caller-supplied TTL.
It preserves sequence, acknowledgment, reserved bits, flags, window, urgent pointer, options, payload, TOS, identification, and DF.
It computes the two checksums again and has no external link padding.
The `rewriteFlow` helper matches the existing bidirectional `FlowNAT` tuple algebra under its explicit well-formedness and selected-input premises.
This is tuple rewriting, without a TCP connection-state transition.

`TCP.Reassembly.Source` does a check of the bytes of a supplied completed IPv4 output.
Its segment encoding equals that output's actual packet payload.
Its source can feed certified tuple rewriting.
Fragment provenance still requires the separate reassembly arrival and `Output.Valid` proofs.
This adapter does not extend the existing UDP-only ordinary forwarding profile to TCP.

## Evidence and remaining work

The [static fixtures](../examples/tcp/fixtures.json) include accepted and rejected segment cases, wrap boundaries, intervals, and common arcs.
The independent Python oracle calculates checksum and framing results. It does not execute Lean or use a network.
The manual checker compares CLI results with expected fields and Ethernet/IPv4 frames from the independent oracle.
These are constructed conformance cases, without native capture claims.

The [source investigation](research/TCP_FOUNDATION.md) records the selected RFC clauses and checksum-zero arithmetic.
The receive-state extension supplies selected window and ACK rules under explicit seed assumptions.
Handshake provenance, send behavior, reordering, retransmission, timers, congestion control, and connection incarnation reuse remain open.
Negotiated option semantics, TCP-aware ordinary tracking, native classification, and full application-stack correspondence remain open.
All seven [research programs](ROADMAP.md) and the full campus landmark remain OPEN.
