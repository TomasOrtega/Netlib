# A checked TCP application path

The bounded endpoint adds application writes, sends, reads, and peer-window updates.
Successful sends produce checked IPv4/TCP bytes.
Application reads return exact receive-buffer prefixes.
The local trace proofs connect these results to the actual computed endpoint events.

```sh
lake exe netlib tcp-endpoint examples/tcp-endpoint/trace.json --json
```

The report gives each event, its decision, output bytes, read bytes, ACK intent, and resulting state.
An ACK intent remains separate from an output packet.
An `emitAck` event constructs a packet from the current state.
It does not copy fields from an earlier ACK intent.

## Input and limits

Schema one contains `seed` and `events`.
The seed contains a `core` receive state and these additional fields:

| Field | Meaning |
| --- | --- |
| `pendingHex`, `pendingLimit` | Pending application bytes and their storage limit. |
| `sendWindow` | The assumed initial peer receive window. |
| `sendWL1`, `sendWL2` | The assumed initial window-history sequence fields. |
| `effectiveMSS` | The maximum new-data payload size. |
| `ipSendLimit` | The maximum emitted IPv4 packet size. |

The seed must satisfy the [receive-state bounds](TCP_RECEIVE.md#seed-contract).
Pending storage and the unscaled peer window cannot exceed 65535 bytes.
The effective MSS must be positive.
Its value plus 40 must not exceed the IP size limit.
The IP size limit cannot exceed 65535 bytes.

The numerical MSS bounds do not prove startup negotiation.
The caller supplies the startup and lower-layer size evidence.
Without a startup MSS option, the caller must use an effective MSS of at most 536.
The seed also assumes an established connection and its initial window history.
The [startup extension](TCP_HANDSHAKE.md) constructs these states and their default MSS from actual checked handshake events.
The [campus extension](CAMPUS_TCP.md) connects their delivery history to actual authenticated gateway service.

Each event has one of these forms:

```json
{"kind":"write","payloadHex":"616263"}
{"kind":"send","count":3,"policyPermitted":true}
{"kind":"read","count":2}
{"kind":"emitAck","policyPermitted":true}
{"kind":"receive","rawIPv4Hex":"..."}
```

The last line shows the field name only.
Use an actual IPv4 byte string from the example for execution.
Unknown fields, duplicate fields, invalid hex syntax, and invalid seeds cause an input error.
All event syntax is parsed before replay.
IPv4 and TCP contents are decoded only in the processed event prefix.
Reported events come from the typed event values, with lowercase hex strings.

## State changes

A write appends bytes to pending storage if space is available.
A send selects an exact pending prefix.
Its count must fit the current peer window, outstanding storage, effective MSS, and IP size limit.
The window condition is `sent.length + count <= sendWindow`.
Only a successful send removes pending bytes, appends outstanding bytes, and advances `SND.NXT`.
Each output uses the reverse tuple, current cursors, local free window, ACK, and no options.
The emitted IP and TCP checksum calculations include the exact output bytes.

A read removes and returns an exact receive-buffer prefix.
It increases the local free window by the returned byte count.
It preserves `RCV.NXT`, send storage, and peer-window history.

The peer-window guard uses the state before ACK removal.
It requires a forward ACK coordinate from `SND.UNA` through `SND.NXT`, including the endpoints.
It also requires a newer `SEG.SEQ`, or equal `SEG.SEQ` with `SND.WL2 <= SEG.ACK` on the selected short arc.
A strictly old ACK can permit received data but cannot update the peer window.
A duplicate ACK equal to `SND.UNA` can update it when the freshness guard passes.

Window shrink can leave more outstanding bytes than the new peer window permits.
This state remains valid.
The next new-data send fails until sufficient space becomes available.
A zero peer window also prevents a new-data send.

Rejected events preserve the state.
Unsupported receive processing also preserves the state, including the peer-window fields.
Replay stops at the first unsupported event and retains the unprocessed suffix.
The command returns zero for supported replay, including supported rejection.
It returns two for unsupported replay or an input error.

## Proof contract

`TCP.ApplicationTrace.Chain` records the actual endpoint results in event order.
Its byte ledgers prove these conservation equations:

```text
seed.pending ++ written = emitted ++ final.pending
seed.sent ++ emitted = acknowledged ++ final.sent
seed.received ++ acceptedPayloads = readBytes ++ final.received
```

The emitted ledger includes successful new-data sends only.
Acknowledged bytes are removed outstanding bytes.
They do not establish a remote application read.
Nonempty seed buffers retain separate origin assumptions.

The paired theorem uses empty pending and receive seed buffers and matching initial cursors.
Each receive event must refer to an earlier successful peer output, including rejected inputs and pure ACKs.
Each accepted nonempty payload has an earlier successful send and an earlier application write.
The delivery evidence preserves the emitted payload and sequence value through the selected byte transformation.
Certified TCP tuple rewriting supplies one such transformation.
Valid checksums and matching tuples alone do not establish this delivery history.
The CLI does a check of one endpoint replay.
It does not construct delivery-history evidence for the paired theorem.

Ghost byte positions connect emitted and accepted data to sequence values.
The theorem bounds each finite epoch below half the sequence space.
The caller assumes that inputs represent the selected trace outputs and excludes inputs from older connection instances.
Byte equality alone cannot establish physical origin or connection identity.
Modulo injectivity then gives the same byte position for matching in-order data.
The result states that application read bytes form a prefix of peer application writes.
It permits loss, rejected reordering, and stalled progress.

Serial window-history comparisons require separate age evidence.
State validity and the outstanding-byte bound do not supply it.
An exact half-space difference is outside the ordered comparison domain.

## Evidence and remaining work

The [source investigation](research/TCP_APPLICATION.md) records the RFC rules and their selected interpretation.
An independent Python oracle supplies static cases and mixed traces.
The manual CLI helper compares actual decoded inputs, output bytes, decisions, read bytes, and state changes.
These cases use constructed bytes and do not send packets.

Policy inputs permit individual sends and ACK outputs.
They do not prove congestion control, ACK scheduling, or rate control.
Broader startup features, connection close, retransmission, timers, window probes, and long sequence-reuse periods remain open.
The proof does not establish native transmission, eventual delivery, conntrack acceptance, or failover continuity.
The full campus demonstration and all seven [research programs](ROADMAP.md) remain OPEN.
