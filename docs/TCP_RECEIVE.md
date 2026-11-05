# TCP receive-window and ACK processing

Netlib has a bounded receive projection for a pre-established TCP endpoint.
It connects checked IPv4/TCP bytes to sequence tests, ACK processing, and receive-buffer changes.
The caller supplies the initial state and sent-byte buffer.
The caller assumes that the endpoint transmitted these buffer bytes.
The model does not prove a handshake or a transmission history.

## Command and result

```sh
lake exe netlib tcp-receive examples/tcp-receive/trace.json --json
```

The input contains schema version one, an explicit seed, and raw IPv4 packets.
The checker derives packet tuples and transport fields from those bytes.
The existing codec requires IHL five, an unfragmented datagram, and valid IP and TCP checksums.
A TCP checksum word of zero still requires verification.

The report gives each processed packet, its decision, its ACK request if present, and its resulting state.
Replay stops at the first `Unsupported` result.
The report keeps the unread byte strings.
Their IPv4 and TCP contents remain unevaluated.
Supported protocol rejection preserves the model state and permits the next replay step.

The command returns zero for a supported replay, even when the model rejects a packet.
It returns two for unsupported processing or invalid input.
An ACK request is a model effect.
Packet generation, transmission, scheduling, and rate limits require separate semantics.

## Seed contract

The seed must satisfy these conditions:

- The inbound tuple has TCP protocol.
- The receive-buffer length does not exceed local capacity.
- Local capacity does not exceed 65535 bytes.
- The assumed sent-byte buffer does not exceed 65535 bytes.
- `SND.NXT` equals `SND.UNA` plus the sent-byte count, modulo `2^32`.
- The sent-byte count plus 65535 is below `2^31`.

Local receive capacity comes from the seed.
The free receive window is capacity minus the received-byte count.
`SND.WND` updates remain outside this projection.
The buffer conditions establish cursor consistency and bounds.
They do not establish an actual earlier transmission.

## Sequence and ACK rules

After the seed and tuple tests pass, the receive projection excludes controls and options before the ordinary sequence test.
The receive-window module implements the four sequence tests:

| Occupied segment length | Local window | Sequence condition |
| --- | --- | --- |
| Zero | Zero | `SEQ = RCV.NXT` |
| Zero | Positive | The sequence position is inside the window. |
| Positive | Zero | Reject the sequence. |
| Positive | Positive | The first or last occupied position is inside the window. |

The generic sequence predicate counts SYN and FIN positions.
The receive projection leaves their control actions unsupported.
Zero-window RST and URG actions remain outside this projection.
[RFC 9293, section 3.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4).

General interval overlap is insufficient for the last row.
For example, `RCV.NXT = 100` and window ten give positions 100 through 109.
A segment at 99 with occupied length twelve contains that window, but its endpoints are 99 and 110.
The exact sequence test rejects it.
The library proves this distinction for every positive short window.

The profile selects the RFC 5961 DATA defense with fixed `MAX.SND.WND = 65535` and no scaling.
The permitted ACK arc extends from `SND.UNA − 65535` through `SND.NXT`.
An advancing ACK removes exactly the acknowledged prefix of the assumed sent bytes.
An old ACK inside the permitted arc can accompany new received data.
After the tuple, scope, sequence, and ACK-flag tests pass, an ACK outside the arc produces a challenge ACK request.
The state stays unchanged.
[RFC 5961, section 5.2](https://www.rfc-editor.org/rfc/rfc5961.html#section-5.2).

Supported data must start at `RCV.NXT`.
Its byte count must not exceed the free receive window.
Acceptance appends the exact payload and advances `RCV.NXT` by its byte count.
An accepted pure ACK can remove sent bytes without appending receive bytes.
The sent-buffer end `SND.NXT` stays unchanged.

## Proof and scope

The proofs preserve the seed bounds after each computed receive result.
Supported rejection and unsupported continuation preserve the byte buffers.
The NAT theorem rebinds the endpoint tuple and preserves the receive decision under certified TCP rewriting.
The theorem requires a valid seed, a matching source tuple, and a TCP target tuple.
The checked replay retains the actual packet bytes and the computed state history for its processed prefix.

RST, SYN, FIN, URG, congestion flags, and options are outside this receive profile.
Partial overlap, trimming, and out-of-order storage also remain unsupported.
These scope checks do not specify the full RFC action order.
PSH has no effect in this projection.
The separate [application extension](TCP_APPLICATION.md) adds checked sends, reads, and peer-window updates.
The [startup extension](TCP_HANDSHAKE.md) constructs seeds for the selected ordinary handshake.
Broader startup features, retransmission, timers, congestion control, and incarnation freshness remain open.

Endpoint processing does not discharge the Linux conntrack transport-tracker premise.
The existing tuple and `seenReply` replication proofs do not establish TCP endpoint continuity after failover.
The [research note](research/TCP_RECEIVE.md) states the selected clauses and the remaining boundaries.
The independent fixtures are static model cases.
They establish no native capture or implementation-refinement result.
All seven [research programs](ROADMAP.md) and the full campus landmark remain OPEN.
