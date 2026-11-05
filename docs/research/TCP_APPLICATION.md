# A selected TCP application path

This note records the source rules for bounded application events and checked model outputs.
The Python oracle does not import or execute Lean.
It uses constructed byte strings and does not send packets or collect captures.
The fixtures do not prove native transmission or implementation refinement.

## Source rules

SEND divides the application buffer into segments.
RECEIVE returns queued bytes to the application.
[RFC 9293, sections 3.10.2 and 3.10.3](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.2).

The window guard requires `SND.UNA <= SEG.ACK <= SND.NXT`.
The freshness guard requires newer `SEG.SEQ`, or equal `SEG.SEQ` with `SND.WL2 <= SEG.ACK` on the selected short arc.
The sender must tolerate window shrink.
[RFC 9293, sections 3.10.7.4 and 3.8.6](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4).

Without a startup MSS option, the default IPv4 send MSS is 536.
The effective MSS also obeys the IP transmission limit.
[RFC 9293, section 3.7.1](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.7.1).

RFC 5961 permits the DATA ACK interval from `SND.UNA - MAX.SND.WND` through `SND.NXT`.
It permits fixed `MAX.SND.WND = 65535` without scaling.
[RFC 5961, section 5.2](https://www.rfc-editor.org/rfc/rfc5961.html#section-5.2).

Congestion and peer receive windows limit transmission.
[RFC 5681, sections 2 and 3.1](https://www.rfc-editor.org/rfc/rfc5681.html#section-2).

Window scaling requires offers from the two SYN segments.
The SYN window field remains unscaled.
[RFC 7323, section 2.2](https://www.rfc-editor.org/rfc/rfc7323.html#section-2.2).

Sequence values use modulo `2^32`.
Outstanding-byte bounds alone do not exclude old copies after sequence reuse.
[RFC 9293, section 3.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4).

## Selected model

The model starts with an endpoint that is already in the ESTABLISHED state.
Its initial tuple, sequence cursors, buffers, and peer-window history are explicit inputs.
An initial nonempty buffer retains its separate byte-origin assumption.
The paired application theorem uses empty initial pending and receive buffers.
Its initial outstanding buffers can be nonempty and retain their separate origin assumptions.

The effective MSS and IP size limit are explicit configuration inputs.
Their numerical bounds do not prove a startup negotiation or a path observation.
For startup without an MSS option, the caller must supply an effective MSS of at most 536.
For another startup, the caller must supply a limit consistent with the peer MSS and IP size limit.
The model does not infer startup options from a later data packet.

Application writes add bytes to bounded pending storage.
A write does not prove an output event.
A successful send selects an exact prefix from pending storage.
It emits checked IPv4/TCP bytes and adds that same prefix to outstanding storage.
Only that successful event advances `SND.NXT`.
Failed events retain the state and emit no bytes.

New sends require enough peer window, pending bytes, storage space, and segment-size allowance.
An explicit policy input permits each send.
This input does not prove congestion-control behavior.
The model does not implement retransmission, window probes, timers, or eventual delivery.

Outputs use the reverse endpoint tuple, current sequence cursors, current local receive window, and ACK.
They contain no TCP or IP options.
An ACK event reads the current state when it emits bytes.
A prior ACK request remains an intent and does not supply saved output fields.
An explicit policy input also permits ACK emission.

## Peer-window updates

The DATA ACK interval and the window-update interval serve different purposes.
A strictly old ACK can permit data processing under the selected DATA rule.
It cannot change the peer-window fields.
A duplicate ACK at `SND.UNA` can change those fields if the freshness guard permits it.

The window guard uses the state before ACK removal.
Only an accepted receive can commit a window update.
An unsupported geometry result preserves the full state, including window history.
The replay stops at its first unsupported result.
It retains the later events as an unprocessed suffix.

The state permits an outstanding-byte count above a reduced peer window.
The next new-data send then fails its window guard.
A zero peer window also prevents a new-data send.
Neither condition invalidates bytes already in outstanding storage.

Serial comparisons require separate age evidence for their intended time order.
The outstanding ACK arc does not bound the age of `SND.WL1` or `SND.WL2`.
An exact half-space difference is outside the ordered comparison domain.
Proof indices record byte positions without changing wire fields or endpoint decisions.

## Application reads and composition

A read returns an exact prefix of receive storage.
It removes those bytes and increases the local free window by their count.
It does not advance `RCV.NXT` or change peer-window history.
The trace ledger connects read results to earlier accepted payloads.

The selected paired proof needs an explicit delivery history.
Every receive event refers to an earlier successful peer output, including rejected inputs and pure ACKs.
Each accepted nonempty payload has an earlier successful send and an earlier application write.
Certified tuple rewriting can change the tuple and checksum fields on this path.
It preserves payload bytes and sequence values.
A matching tuple and valid checksum cannot establish output origin by themselves.

The first proof uses a finite epoch below half the sequence space in each direction.
The caller excludes input from older connection instances.
Byte equality alone cannot establish physical origin or connection identity.
These conditions prevent an earlier sequence cycle from supplying current application bytes.
The resulting prefix property is a safety property.
It permits loss, rejected reordering, and stopped progress.
It does not prove that the application eventually receives its data.

Fragment delivery needs a separate fragment-arrival history and reassembly output evidence.
Endpoint proofs do not prove conntrack classification or state transfer.
The selected TCP path does not extend the older UDP forwarding path.
Handshake, close, congestion, runtime refinement, and campus integration remain open.
All seven research programs remain OPEN.

## Static artifacts

`scripts/tcp_endpoint_reference.py` contains the independent application-event oracle.
It uses signed serial coordinates for ACK and window history.
Its receive-window calculation uses the earlier split-interval reference.
Its output encoder constructs the IPv4 and TCP checksum fields independently.

`examples/tcp-endpoint/fixtures.json` contains 64 single-event cases, 116 window cases, and seven traces.
Four single-event cases have invalid seeds and carry the `coreOnly` marker.
The strict CLI parser rejects these seeds before replay.
`examples/tcp-endpoint/trace.json` contains the application-buffer example.

`scripts/check_tcp_endpoint_examples.py` compares every computed report field with the oracle.
The comparisons include current output bytes, decoded input and output fields, read bytes, ACK requests, and the stop suffix.
The helper places each window case at the current receive cursor to exercise the window guard through a receive event.
The unit tests do not compile or execute Lean or the CLI.
They also test byte conservation, mandatory checksum zero, policy rejection, sequence wrap, and stale window history.
