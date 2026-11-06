# Bounded TCP data recovery

Data recovery connects checked startup, actual packet attempts, current campus policy, and planned gateway transfer.
A retry sends an earlier stream range again.
It does not consume pending bytes or advance `SND.NXT`.
Application reads still return a prefix of the peer's accepted writes.

```sh
lake exe netlib campus-tcp examples/tcp-recovery/trace.json --json
```

The example extends [directional MSS](TCP_MSS.md) and [planned transfer](CAMPUS_TCP_TRANSFER.md).
The selected profile bounds unique bytes in flight to one effective MSS per endpoint.
It permits at most two timer retries for one outstanding original segment.
It stops before omitted fast recovery or connection-failure processing can affect later state.
This result does not establish full TCP conformance or eventual delivery.

## Explicit local clocks

Each endpoint enables recovery with an actual event after checked startup:

```json
{"kind":"enableRecovery","actor":"client"}
{"kind":"advanceClock","actor":"client","millis":1000}
{"kind":"timeout","actor":"client","policyPermitted":true}
```

Enabling requires empty outstanding storage and derives the initial recovery state from the endpoint's actual effective MSS.
Input cannot supply a timer state, RTT sample, retry byte string, or replacement endpoint seed.
Timing-record `start` and `frontier` are byte offsets from that recovery initialization.
The actual packet sequence and application-history proof retain the full connection coordinates.
Each clock reading is an absolute number of milliseconds.
Backward clock input is rejected.
Events can have equal clock readings while their ordinal stamps retain strict causal order.

The two host clocks are separate.
An RTT sample uses one host's stored output time and later ACK receipt time.
Equal readings in the example do not prove native clock synchronization.
Gateway transfer and authentication events do not advance or reset these clocks.
Physical clock correspondence and credential-clock correspondence remain external obligations.

## Unique bytes and packet attempts

A new send moves an exact pending prefix into outstanding storage.
Its size must fit the peer window, effective MSS, IP size limit, and selected congestion bound.
A timeout selects the first actual outstanding timing record.
The retry payload is the corresponding prefix of actual unacknowledged bytes at `SND.UNA`.
The checked output uses that earlier sequence, the current ACK, and the current receive window.

The application trace counts a retry as no new stream bytes.
Its range proof derives the retry position from prior acknowledged bytes and exact byte conservation.
The proof requires empty initial outstanding storage; checked startup supplies it.
Every accepted data receipt still has an earlier actual peer output and certified gateway byte path.
Repeating an assignment or delivery of an old output remains a network copy.
It does not create a new endpoint attempt or RTT sample.

The gateway checks an exact slice of an earlier packet observation for the same entry and direction.
An arbitrary old sequence or changed payload cannot gain repeat admission from its length alone.
A repeat preserves the unique observed frontier and applies the current peer ACK and window rules.
It remains valid when the gateway has observed an ACK that the sender did not receive.

Each processed repeat adds an actual observation and advances the checkpoint cut.
Thus it makes an older cached source image stale even when the unique frontier stays equal.
An exact checkpoint copy retains the earlier range evidence for standby service.
Endpoint timer state stays at the hosts through that gateway operation.

## RTT, timer, and congestion limits

The initial RTO and its selected floor are 1000 ms.
The estimator uses exact rational SRTT and RTTVAR with coefficients 1/8 and 1/4.
Variance uses the old SRTT.
The interval rounds up to whole milliseconds after the RFC expression.
JSON rationals have signed `num` and positive `den` fields.

An idle timer starts only after a successful new output.
An advancing ACK retires the actual outstanding prefix and stops or restarts the timer.
A repeated ACK does not restart it.
Duplicate-ACK classification uses the last accepted ACK's advertised window.
That observation is separate from the peer window retained by the freshness rule.
A partial ACK clips the retained range without losing its original identity or retry flag.
Karn's rule excludes an RTT sample from a retransmitted range.
No complete network history can override that packet-profile ambiguity.

A timeout requires both its deadline and the required interval after the last attempt.
It doubles RTO and sets a new deadline only after checked retry output succeeds.
Local policy denial preserves the due timer and produces no attempt.
Gateway permission remains a separate current-policy check at service time.

The selected congestion window stays at one effective MSS.
The first timeout sets `ssthresh` from actual unique FlightSize and SMSS.
A later timeout of that same original segment keeps the threshold.
This is a conservative selected bound, without a general slow-start or congestion-avoidance implementation.
The third qualifying duplicate ACK stops for omitted fast recovery.
The third timer retry stops for omitted connection-failure handling.

## Connected evidence and limits

The campus witness uses asymmetric 800-byte and 1200-byte send limits.
It loses a data delivery, transfers the exact gateway history, and then loses an actual ACK delivery.
Retries use the installed range observations on the standby.
The receiver discards an old duplicate without adding its payload again.
Only an explicit later ACK output can acknowledge that duplicate.
ACK output scheduling remains explicit in the example.
The [ACK extension](TCP_ACK.md) adds checked local reaction deadlines and receive-window suppression.
General scheduling and eventual delivery remain OPEN.
Current Logoff denial prevents later gateway output despite a valid cached range.

The report retains exact attempts, clocks, timing records, estimator values, deadlines, and unique FlightSize.
Application and transfer assurance use the same computed global history.
The [independent evidence](research/TCP_RECOVERY.md) checks bytes and state without using Lean output as its expected result.

The timer rules follow [RFC 6298, sections 2, 3, and 5](https://www.rfc-editor.org/rfc/rfc6298.html#section-5).
The selected congestion bound uses [RFC 5681, section 3](https://www.rfc-editor.org/rfc/rfc5681.html#section-3).
Duplicate receive processing uses [RFC 9293, section 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4).

The [receive-gap extension](TCP_RECEIVE_GAPS.md) holds non-overlapping future runs and retains their actual receipt origins through planned transfer.
Fast recovery, receive overlap, persist, SYN/FIN retries, and full connection-failure handling remain OPEN.
Native TCP refinement, physical delivery, automatic gateway failure recovery, and general liveness also remain OPEN.
All seven research programs and the full campus demonstration remain OPEN.
