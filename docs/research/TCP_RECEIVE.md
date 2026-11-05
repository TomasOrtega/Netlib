# A selected TCP receive projection

This note describes a static model for an endpoint that is already in the ESTABLISHED state.
The caller supplies the initial tuple, sequence cursors, receive buffer, and sent-byte buffer.
The caller assumes that the endpoint transmitted the bytes in the sent-byte buffer.
The profile uses the permitted fixed `MAX.SND.WND` value 65535, without window scaling.
These assumptions do not prove a handshake or a transmission history.

The Python oracle does not import or execute Lean.
It does not use sockets, send packets, or collect captures.
The fixtures contain constructed IPv4 packets and literal model results.
They do not establish native TCP classification, conntrack acceptance, or implementation refinement.

## Receive-sequence rules

RFC 9293 gives four cases for segment length and receive-window size.
An empty segment at a zero window requires `SEG.SEQ = RCV.NXT`.
An empty segment at a positive window requires its sequence position inside the window.
A nonempty segment requires a positive window and its first or last occupied position inside that window.
SYN and FIN each use one sequence position in addition to the payload byte count.
[RFC 9293, section 3.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4).

General interval overlap does not replace the first-or-last test.
A segment can contain every window position and fail that test.
The fixtures retain this counterexample at ordinary and circular boundaries.
The Python reference uses separate intervals on each side of sequence wrap.
It does not use the Lean forward-distance function.

## ACK range

RFC 5961 defines optional DATA protection with this inclusive range:

```text
SND.UNA - MAX.SND.WND <= SEG.ACK <= SND.NXT
```

An implementation that selects this protection must discard a segment outside the range and send an ACK.
`MAX.SND.WND` is the largest prior peer window, with window scaling where applicable.
The RFC also permits a fixed maximum window value.
[RFC 5961, section 5.2](https://www.rfc-editor.org/rfc/rfc5961.html#section-5.2).

This projection selects the permitted fixed bound `MAX.SND.WND = 65535`.
It records an ACK request instead of a packet transmission.
The Python oracle uses signed offsets from `SND.UNA`.
It permits offsets from `-65535` through the outstanding byte count, with the two limits included.
A positive offset removes that exact prefix from the sent-byte buffer.
A permitted old ACK removes no bytes and does not prevent data progress.
The sent-byte count plus 65535 must be less than half the sequence space.
The seed also limits the sent-byte count to 65535.

RFC 9293 advances `SND.UNA` for a new ACK through `SND.NXT`.
An old or duplicate ACK does not advance it.
Send-window updates have separate `SND.WL1` and `SND.WL2` conditions.
[RFC 9293, section 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4).

## Profile scope and state changes

The model first examines seed validity and tuple equality.
It then excludes RST, SYN, FIN, URG, ECE, CWR, and all nonempty option regions.
The scope gate returns `Unsupported` before ordinary sequence processing.
This order reports the limits of the model. It does not implement RFC control actions.
RFC 9293 requires control processing for RST and URG even at a zero receive window.
The scope gate prevents ordinary sequence rejection from hiding this missing processing.
[RFC 9293, section 3.4, MUST-66](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4).

Inside the supported profile, the sequence test comes before ACK processing.
The ACK flag is necessary.
The model accepts payload bytes only at `RCV.NXT`, with all bytes inside the available local capacity.
It stores all these bytes and advances the receive cursor by their count.
It does not trim overlaps or store out-of-order data.
These cases return `Unsupported` and keep the state unchanged, even when their ACK would remove a sent prefix.
PSH has no effect in this projection.
The peer's advertised window does not set local receive capacity.

There are no send events, application buffer reads, peer-window updates, retransmission queues, timers, or ACK rate limits.
ACK requests do not establish packet emission, eventual delivery, or congestion behavior.
Sequence wrap does not establish freshness across connection reuse.

## Static artifacts

`scripts/tcp_receive_reference.py` contains the independent byte, sequence, ACK, and state calculations.
`scripts/check_tcp_receive_examples.py` compares the compiled CLI with the independent expected results.
It compares decoded fields, decisions, ACK requests, step states, final state, and the stop boundary.
The unit tests do not compile or invoke Lean or the CLI.
`examples/tcp-receive/fixtures.json` contains 84 single-input cases, 32 sequence cases, 20 ACK cases, and seven replay traces.
`examples/tcp-receive/trace.json` contains one input for the guide.
Four single-input cases use invalid seeds to test the core guard.
The strict replay adapter rejects these seeds before replay; the fixtures mark them `coreOnly`.

The replay input contains `schema`, `seed`, and `packetsHex`.
The seed contains `inbound`, `receiveNext`, `capacity`, `receivedHex`, `sendUna`, `sendNext`, and `sentHex`.
The output adds the derived local window.
Each replay stops after its first `Unsupported` result.
It retains the unread packet suffix and does not decode its transport bytes.
The parser still examines the hexadecimal syntax of every entry.
An ordinary rejected input does not stop replay.

The cases include ACK prefix removal, old ACK data progress, exact buffer limits, tuple differences, and excluded controls and options.
They also include zero windows, sequence wrap, half-space differences, the lower ACK limit, and ACKs beyond `SND.NXT`.
Zero-window RST and URG data cases require `Unsupported` and stop replay.
The ordinary TCP checksum-zero and `ffff` cases use the same mandatory verification equation.
All seven research programs remain OPEN beyond these limited results.
