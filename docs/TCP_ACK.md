# Checked TCP ACK reactions

The ACK profile connects receive causes to actual local packet output.
It extends [bounded recovery](TCP_RECOVERY.md) on the same endpoint and clock.
The campus report retains startup, gateway delivery, application, and transfer evidence.

```sh
lake exe netlib campus-tcp examples/tcp-ack/trace.json --json
```

The example has 153 joint events, 21 endpoint outputs, and 22 gateway services.
The client reads 3600 bytes; the server reads 1600 bytes.
Each endpoint has five ACK causes.
The server covers its first two causes with one data output.
Its four discharge outputs cover all five causes.

## Enable the profile

Each endpoint enables recovery, then enables ACK reactions before its first application send or receive:

```json
{"kind":"enableRecovery","actor":"client"}
{"kind":"enableAck","actor":"client"}
```

Activation derives RMSS from that endpoint's own checked SYN or SYN,ACK offer.
The absent-offer limit is 536 bytes.
The peer's offer continues to bound outgoing data.
Input cannot supply ACK credit, timer deadlines, offered-window state, or a replacement seed.
Late first activation is an input error, including after a rejected send or receive.

## Causes, deadlines, and output

Accepted data creates an ACK cause with an inclusive deadline of local time plus 499 ms.
This selected whole-millisecond bound is strictly below 500 ms.
The profile requests an immediate response after two RMSS-sized packets or two RMSS of data.
An unacceptable sequence requests an immediate response without adding application bytes.
A receive-window update can also create an immediate cause.

Each cause keeps its own issue time and deadline.
Coalescing preserves the oldest deadline and the full cause group.
An output must cover every pending receive cursor and required window edge.
A clock jump beyond an owed deadline stops at explicit unsupported scope.
It cannot erase an overdue cause.

```json
{"kind":"advanceClock","actor":"client","millis":499}
{"kind":"dispatchAck","actor":"client","policyPermitted":true}
```

`dispatchAck` emits a pure ACK only when a cause is due.
`emitAck` can respond earlier.
A successful data send or retry can carry the ACK and discharge the group.
A pure ACK without credit is rejected.
An accepted pure ACK creates no response cause.
An unacceptable sequence can still request an immediate response.
Local policy or encoding denial retains credit, deadlines, and the last offered edge.
Only actual successful local output consumes that credit.

## Receive-window suppression

Physical free space and the offered receive window are separate values.
Ordered data release consumes the offered width while preserving its right edge.
Held future bytes use physical storage without shrinking that span.
The [receive-gap guide](TCP_RECEIVE_GAPS.md) separates physical free space from the remaining reservation.
A small application read increases free space but can leave the offered edge unchanged.
This rule applies to pure ACKs, data output, and retries.
A piggyback ACK cannot bypass the suppression rule.

The increase threshold is the smaller of half the receive capacity, rounded up, and the effective outgoing MSS.
Only a read that increases the candidate window creates a window-update cause.
A zero-byte read creates no cause.
The cause records an absolute stream edge, so later data cannot turn it into an impossible fixed-width obligation.
The new offered edge is committed only when packet output succeeds.
Receive sequence tests use the offered width, while storage checks also enforce physical free space.

## Checked evidence and scope

The optional `ackAssurance` report has scope `local-ack-generation`.
`checked` requires closed causal histories for the enabled endpoints.
`clientEnabled` and `serverEnabled` identify the selected endpoints.
Zero cause counts for a disabled endpoint do not establish its ACK duties.
`pending` retains checked prefix evidence and reports unresolved causes.
`failed` reports a failed joint or ACK-history check.
Legacy reports omit the field when both endpoints keep ACK reactions disabled.

The proof projects the actual endpoint chain into the generic timed-reaction history.
It does not run a replacement endpoint model.
Each discharge identifies its actual earlier receive or read and its actual output packet.
Packet ACK and window fields meet the owed stream position and edge.
Receive causes retain the earlier peer output, assignment, current-policy gateway service, and delivery path.
Each host keeps a separate clock context.
Equal example readings do not establish clock synchronization.

The example carries a pending cause through planned gateway transfer.
It also covers delayed ACKs, data and ACK loss, whole old duplicates, suppressed small reads, and window growth.
The separate fixtures include zero-window reopening.
After Logoff, local ACK generation can meet its deadline while the gateway correctly denies delivery.
The independent [research and evidence](research/TCP_ACK.md) checks bytes, state, causes, and timing without Lean-derived expected values.

The selected rules use RFC 9293, sections 3.8.6.2.2 and 3.8.6.3, and RFC 5681, section 4.2.
Challenge-ACK rate limiting, general scheduling, native clock correspondence, and eventual delivery remain OPEN.
Receive overlap storage, persist, fast recovery, and complete TCP conformance also remain OPEN.
All seven research programs and the full campus demonstration remain OPEN.
