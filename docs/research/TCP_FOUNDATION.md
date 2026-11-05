# TCP framing foundations

This note supports static TCP model fixtures and an independent Python framing oracle.
The fixtures are constructed examples, not native captures.
The oracle does not use sockets, send packets, examine the kernel, or execute Lean.
Successful checks establish finite fixture agreement with the selected model.
They do not establish transport delivery, connection state, native classification, or implementation refinement.
All seven formal-networking research programs remain open beyond their established bounded results.
[Fixtures](../../examples/tcp/fixtures.json).
[Independent oracle](../../scripts/tcp_reference.py).
[Oracle tests](../../scripts/test_tcp_reference.py).

## Standards boundary

Data Offset counts four-byte words. The TCP header has twenty fixed bytes and a maximum of forty option bytes.
The eight baseline flags are CWR, ECE, URG, ACK, PSH, RST, SYN, and FIN.
Generated reserved bits are zero; receivers ignore unsupported reserved bits.
The checksum calculation includes the IPv4 pseudoheader and all segment bytes. These bytes include options.
For an odd final byte, the checksum calculation uses one zero byte after that byte. The sender does not transmit this padding.
Checksum zero has no omission meaning.
[RFC 9293, section 3.1](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.1).

EOL and NOP occupy one byte; other options carry inclusive lengths.
EOL requires zero padding through the declared header boundary.
Receivers ignore unknown options with valid lengths.
The MSS option has length four. A sender must put this option only in SYN segments.
The receiver must detect illegal option lengths. RFC 9293 suggests a connection reset and an error log.
[RFC 9293, sections 3.1 and 3.2](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.2).

## Selected profiles

Structural acceptance requires all bytes of the fixed header, bounded Data Offset, well-formed option framing, and a valid checksum.
The raw options region, reserved bits, flags, and received checksum survive exact re-encoding.
Unknown options retain their uninterpreted bodies.
MSS length belongs to structural validation; MSS placement belongs to a separate semantic predicate.
The semantic predicate does a check of only MSS placement. It does not validate TCP state transitions.
A non-SYN MSS example therefore passes structural decoding and fails this narrow semantic predicate.
Nonzero received reserved bits pass the two predicates. Fresh generation clears them.

Option validation reports malformed lengths and nonzero EOL padding as errors.
This is a codec decision and does not simulate a connection reset or prescribe kernel behavior.
Error precedence is a local parser choice.
All fixtures with malformed options have valid checksums. These fixtures test option framing without checksum errors.

`computed_segment` sets reserved bits to zero and computes the checksum.
`rechecksum` computes the checksum again and keeps the other received fields.
These helpers can construct malformed option examples; construction alone does not establish structural validity.
`decode_segment` uses network-order field decoding and an option parser to examine the segment.
The oracle permits TCP lengths through 65535, as representable by the pseudoheader.
The IPv4 codec limits the sum of the IP header length and the TCP segment length.
The twenty-byte IPv4 header permits a maximum of 65515 TCP bytes.

## Zero checksum fixture

The `checksum-zero` fixture uses source `192.0.2.1`, destination `198.51.100.2`, and a twenty-two-byte TCP segment.
All its bytes are:

```text
30390050000000000000000050101000000000008312
```

The pseudoheader followed by the fixed header with checksum zero has ordinary word sum 163051, or `0x27ceb`.
End-around carry gives `0x7ced`. The sum of `0x7ced` and the payload word `0x8312` is `0xffff`.
The resulting computed checksum is `0x0000`, and verification includes that actual zero word.
A change to the destination port causes checksum verification to fail.
The oracle never applies UDP checksum omission or zero-to-`0xffff` substitution.

## Sequence arithmetic

TCP sequence arithmetic wraps modulo `2^32`; SYN and FIN contribute to occupied sequence length.
[RFC 9293, section 3.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4).
The unsigned forward distance defines `before(a,b)` when it lies strictly between zero and `2^31`.
RFC 7323 gives this comparison explicitly and relates it to TCP sequence numbers.
[RFC 7323, section 5.2](https://www.rfc-editor.org/rfc/rfc7323.html#section-5.2).

The oracle treats equality and exact half-space differences as unordered.
Its interval predicate uses forward distance below a length strictly smaller than `2^31`.
Static cases include wrap, half-space boundaries, empty intervals, and inclusive starts with exclusive ends.
Common-arc examples demonstrate transitivity within a short interval.
A separate example demonstrates failure of unrestricted transitivity.
These fixtures do not establish freshness across sequence reuse or replace future connection invariants.
Window scaling and timestamp processing require separate semantics.
[RFC 7323, section 2.3](https://www.rfc-editor.org/rfc/rfc7323.html#section-2.3).

## Composition and remaining work

The existing UDP codec provides the layered IPv4 wrapper and exact reconstruction pattern.
Its omitted-checksum branch and nonzero synthesis theorem do not transfer to TCP.
Tuple imports and `FlowNAT` already represent TCP protocol and ports.
Their existing results do not supply TCP byte validation or a transmission control block.
The certified rewrite keeps transport content and computes checksums for the changed addresses and ports.
The completed IPv4 reassembly boundary must precede transport decoding of all bytes.

Future work includes connection transitions, acknowledgment validity, receive windows, retransmission, ordering, timers, and connection incarnation reuse.
Native TCP classification and refinement remain separate obligations.
[RFC 9293, section 3.10](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10).
[RFC 9293, appendix A.2](https://www.rfc-editor.org/rfc/rfc9293.html#appendix-A.2).
