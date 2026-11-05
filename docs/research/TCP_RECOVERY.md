# Bounded TCP data recovery

This note connects actual packet attempts to unique stream bytes and timer history.
The Python oracle constructs static packets and calculates checksums independently.
It uses exact fractions for RTT estimates.
It does not execute Lean, send traffic, or collect captures.

## Primary rules

RFC 6298 defines the RTT estimator and retransmission timer.
The first sample sets SRTT to the sample and RTTVAR to half the sample.
Later updates use the previous SRTT when updating RTTVAR.
The recommended coefficients are one eighth and one quarter.
The interval uses SRTT plus the greater of clock granularity and four times RTTVAR.
Karn excludes samples for retransmitted data without timestamps.
The recommended timer starts on data when idle, stops after full acknowledgment, and restarts after ACK advancement.
Timeout selects the earliest unacknowledged segment, doubles RTO, and rearms.
The backoff and prevention of too-early timer retransmission are mandatory.
The suggested initial RTO and computed floor are one second.
An optional maximum must be at least sixty seconds.
[RFC 6298, sections 2, 3, and 5](https://www.rfc-editor.org/rfc/rfc6298.html#section-5).

RFC 5681 defines FlightSize as unique data sent but not cumulatively acknowledged.
New sends obey congestion and receive windows.
The first timeout sets ssthresh no higher than `max(FlightSize/2, 2*SMSS)`.
Repeated timeout of the same segment retains ssthresh.
Timeout reduces cwnd to at most one SMSS.
A qualifying duplicate ACK requires outstanding data, no payload, SYN/FIN clear, an unchanged ACK, and an unchanged advertised window.
These conditions differ from the old-ACK DATA safety check.
The window comparison uses the last incoming ACK window, including an accepted stale ACK.
It does not use the window retained by the separate freshness rule.
[RFC 5681, sections 2 and 3.1](https://www.rfc-editor.org/rfc/rfc5681.html#section-3.1).

RFC 9293 discards old duplicate data and acknowledges unacceptable sequence input with the current receive cursor, except for resets.
New cumulative ACKs advance the oldest unacknowledged cursor and retire acknowledged retransmission data.
Overlap trimming, zero-window probing, and excessive-retransmission failure handling have separate requirements.
[RFC 9293, sections 3.8.3, 3.8.6.1, and 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4).

## Selected executable boundary

Recovery is enabled from the actual established endpoint state when its sent buffer is empty.
The input supplies no replacement endpoint, RTT sample, timer, range, or retry-success field.
Each endpoint has its own monotone millisecond clock.
The global operation index still records causal order.
Matching clock readings in the example are explicit inputs.
They do not establish synchronized native clocks.

The selected initial RTO is 1000 milliseconds.
The granularity is one millisecond.
The estimator uses exact rational values, then rounds the final interval upward and applies the one-second floor.
The example has no configured maximum interval.

Unique bytes in flight are limited to one effective MSS.
The congestion window stays at that conservative bound.
The timeout threshold uses actual FlightSize and retains its value for repeated timeout of the same original segment.
This profile does not implement general slow-start growth, congestion avoidance, or fast recovery.
It stops at the third qualifying duplicate ACK.
It also stops before a third timer retry of the same original segment.
That budget does not implement the RFC connection-failure thresholds.

A clock can advance without producing a timeout packet.
The timeout operation checks the actual timer candidate first.
An early or idle candidate rejects without output.
A due candidate with denied local output permission also rejects without changing timer state.
For a permitted candidate, a selected retry beyond the current peer window stops with the persist scope result.
An enabled new send at zero peer window also stops before an omitted probe action.
Legal window-shrink state remains valid.

## Bytes, attempts, and gateway history

A successful new send consumes a pending prefix and advances the unique stream frontier.
It allocates an original-segment identity.
A retry selects the actual oldest unacknowledged slice.
It produces a new checked output at the oldest unacknowledged sequence.
It preserves pending bytes, the unique sent buffer, and the send-buffer end.

An attempt records its kind, local clock, original identity, stream start, and byte count.
The original identity is separate from global packet-output, ticket, and service identities.
Different attempts can have identical packet bytes.
A retry can also have different current ACK or window fields while retaining the same stream slice.
Repeated assignment or delivery of an older output remains network duplication.
It does not create a new timer-qualified endpoint attempt.

The gateway accepts a repeated range only from exact earlier observations for the same entry and direction.
The range must lie inside a prior observed payload with equal slice bytes.
The repeated branch preserves the unique observed frontier, updates applicable ACK/window fields, and appends its actual observation.
It can process a range already acknowledged at the gateway.
The sender can still need that range because the gateway's earlier ACK output was not delivered.

A processed repeat advances checkpoint history even when unique byte counters stay equal.
The exact checkpoint retains the observations and learned directional MSS offers.
Endpoint timers stay at the endpoints during gateway transfer.
Installation, route changes, fencing, and resume do not reset them.

The receiver's whole-old-data branch requests a cumulative ACK and appends no duplicate bytes.
That request is separate from an actual ACK output.
The example explicitly emits, assigns, serves, and delivers the recovery ACK.
Partial overlap and out-of-order storage remain outside this selected receive profile.

## Connected independent trace

[The trace](../../examples/tcp-recovery/trace.json) reuses the existing native-format campus inputs and asymmetric MSS evidence.
The client sends at most 800 bytes per segment, and the server sends at most 1200.
Application receive and pending capacities are 4096.
The trace has 171 operations, 23 endpoint outputs, and 23 gateway service results.

The first client sample is 256 milliseconds.
It gives SRTT 256, RTTVAR 128, and RTO 1000.
The first server sample is 896 milliseconds.
It gives SRTT 896, RTTVAR 448, and RTO 2688.
The long sample intervals include network delay after ACK emission and service.
The client emits these ACKs at local times 400 and 10300 before their later sender receipts.
This timing correction preserves every packet byte and RTT sample.

Each second data range is served at the primary and left undelivered.
The server's original output is queued before the pause and drained during it.
An early staged cut becomes stale after that service.
The final checkpoint has nine actual transport transitions.
It retains client range `[800,1600)` and server range `[1200,2400)`.

The client retries at local times 2400 and 4400.
Its first recovery ACK is served but left undelivered.
The second receipt is an old duplicate; the second actual ACK arrives at 4450.
The server retries at 4488 and 9864, with its second actual ACK arriving at 9914.
This ordering prevents a piggyback ACK from accidentally removing the intended outstanding range early.

The recovery ACKs retire exactly 800 and 1200 bytes.
Karn retains each earlier estimate and backed-off RTO.
A third fresh range in each direction supplies a new unambiguous sample.
The later RTTVAR values become 96 and 336.
The corresponding recomputed intervals are 1000 and 2240.

The server reads 2400 unique bytes, and the client reads 3600.
Each read spans primary and standby service.
The repeated packet payloads do not become additional application bytes.
A later 800-byte client range remains unacknowledged.
Its actual retry is queued before Logoff and current denial.
Final service emits no packet and retains the cached NAT binding.
The final source history has nine transitions, and the standby has twenty-two.
A separate trace reads the earlier received bytes after Logoff and denial.
Another trace retains stale allow rules and reports the actual retry output with a failed current-policy comparison.

## Scope regressions and comparison

[The fixtures](../../examples/tcp-recovery/fixtures.json) include one-gateway and transferred histories.
They compare independent endpoint states, timer records, attempt ranges, actual packets, and gateway observations.
The manual helper also compares application and transfer assurance results.
Its byte audit connects retry slices to earlier original sends and writes.

Delayed earlier window packets provide the zero-window and right-edge tests.
These are actual earlier peer outputs with checked gateway service.
They can shrink a valid outstanding range without acknowledging it.
A due 800-byte retry stops when the new window is zero or 400.
A window of 800 permits that retry.
Early timeout and denied output retain their specified precedence.

Other cases cover local clock reversal, missing or repeated enable, nonempty sent storage, and idle timers.
They test exact RTT rounding, partial ACK clipping, Karn ambiguity, and duplicate-ACK scope.
They also test unread bytes after an unsupported result.
Strict parser cases reject supplied state, samples, ranges, payloads, and retry-success fields.

Two old synthetic repeat-stop rows now reach their formerly unread malformed receipts and become input errors.
Separate positive duplicate rows test the new gateway support and receiver duplicate suppression.
All prior supported campus and transfer fixture inputs and expectations remain unchanged.

These tests establish finite modeled behavior.
They do not establish physical loss, timer scheduling bounds, eventual delivery, or native TCP correspondence.
ACK emission is explicit input; ACK scheduling and delayed-ACK timeliness remain outside this profile.
Zero-window probes, general reordering, overlap storage, SYN/FIN retransmission, broad congestion control,
connection-failure handling, native installation, and cryptographic refinement remain OPEN.
All seven research programs and the full campus landmark remain OPEN.
