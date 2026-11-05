# A selected TCP handshake

This note records the startup baseline before directional MSS support, at source commit `96ed34e`.
Its option limits and fixture counts describe that historical version.
The [MSS investigation](TCP_MSS.md) gives the current option semantics and fixture counts.

This note records the source rules for ordinary active and passive startup.
The Python oracle constructs static byte strings.
It does not import or execute Lean, send packets, or collect captures.
The fixtures do not establish native transmission or peer authentication.

## Source rules

An active OPEN emits SYN and enters SYN-SENT.
A passive SYN receipt enters SYN-RECEIVED and emits SYN,ACK.
[RFC 9293, sections 3.10.1 and 3.10.7.2](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.1).

The active endpoint enters ESTABLISHED after an acceptable SYN,ACK.
The passive endpoint enters ESTABLISHED after the ACK of its SYN.
SYN uses one sequence position.
[RFC 9293, sections 3.4, 3.10.7.3, and 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.3).

Without a startup MSS option, the default IPv4 send MSS is 536.
The effective MSS also obeys the IP transmission limit.
Full TCP conformance requires MSS sending and receipt.
[RFC 9293, section 3.7.1](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.7.1).

Window scaling requires offers from the two peers.
SYN window fields remain unscaled.
[RFC 7323, sections 2.2 and 2.3](https://www.rfc-editor.org/rfc/rfc7323.html#section-2.2).

### Initial window history

RFC 1122 sets `SND.WND`, `SND.WL1`, and `SND.WL2` from the accepted segment when startup enters ESTABLISHED.
[RFC 1122, section 4.2.2.20(c) and (f)](https://www.rfc-editor.org/rfc/rfc1122.html#section-4.2.2.20).

The successful active branch in RFC 9293 does not repeat these assignments.
Its alternative SYN-RECEIVED branch and its passive ESTABLISHED transition do.
The selected model uses the RFC 1122 initialization explicitly.
This comparison is not a claim of a verified new erratum.
[RFC 9293, sections 3.10.7.3 and 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.3).

### Reset scope

Verified erratum 8167 removes the SYN-SENT paragraph that imports an `RCV.NXT` reset test from RFC 5961.
RFC 5961 adds no reset rule for SYN-SENT.
[RFC 9293, erratum 8167](https://www.rfc-editor.org/errata/eid8167).

The selected profile does not process resets.
It returns an unsupported result and stops replay before a missing reset action could affect later state.
It does not reuse established-state reset rules during SYN-SENT.

## Selected exchange

Local configuration supplies the local socket, ISS, receive capacity, pending-storage limit, and IP send limit.
Active OPEN also supplies a remote socket.
The passive listener learns its remote socket from the checked SYN after the local destination test.
A matching socket does not authenticate the peer.

Let `a` be the active local ISS and `b` the passive local ISS.
The selected exchange uses these generated outputs:

```text
active -> passive: SYN      SEQ=a      ACK=0
passive -> active: SYN,ACK  SEQ=b      ACK=a+1
active -> passive: ACK      SEQ=a+1    ACK=b+1
```

All sequence additions use modulo `2^32`.
The generated flags are 2, 18, and 16.
The messages contain no payload or options.
The first SYN's ACK field has no acknowledgment meaning because its ACK flag is clear.

SYN advances a control sequence cursor by one.
It adds no application byte to pending, sent, received, or read storage.
The final ACK acknowledges the actual passive SYN output.
Three matching input strings alone do not establish that output history.

## Derived application state

The active application state becomes available after valid SYN,ACK receipt.
It does not wait for passive receipt of the final ACK.
The passive application state remains absent until that final receipt succeeds.
Loss of the final ACK leaves this distinction visible.

The active send cursor and oldest unacknowledged cursor become `a+1`.
Its receive cursor becomes `b+1`.
Its peer window comes from the accepted SYN,ACK.
Its `SND.WL1` is `b`, and its `SND.WL2` is `a+1`.

The passive send cursor and oldest unacknowledged cursor become `b+1`.
Its receive cursor becomes `a+1`.
Its peer window comes from the accepted final ACK.
Its `SND.WL1` is `a+1`, and its `SND.WL2` is `b+1`.

The application buffers are empty at this selected boundary.
Their capacities and storage limits remain validated local inputs.
The peer window does not set local receive capacity.

The checked startup messages have no MSS option.
The model therefore derives:

```text
peerMSS = 536
effectiveMSS = min(536, ipSendLimit - 40)
```

The fixed later IPv4 and TCP headers each use 20 bytes.
Local configuration requires `40 < ipSendLimit <= 65535`.
The derived effective MSS is positive and obeys the existing endpoint size bounds.
The peer packet does not supply this local IP limit.
Local receive capability remains a separate input.

## Delivery and proof limits

Each successful startup receipt needs an earlier actual output from the opposite role.
The selected byte path uses exact direct bytes or a certified tuple rewrite.
The rewrite preserves sequence, ACK, flags, options, payload, and advertised window.
It updates checksum fields for changed tuples.

The delivery history and the selected connection instance remain environment assumptions.
Byte equality alone does not establish physical origin or connection identity.
The tuple path does not prove routing, TTL forwarding, or conntrack classification.
Local ISS selection also remains an explicit local choice.
The proof does not establish its randomness, security, or safety after connection reuse.

The application prefix theorem can use the derived endpoint states.
It still requires its later application delivery histories and finite data epochs.
Startup success does not prove future packet delivery.
An age interval that includes the peer SYN needs an extra control position in its bound.
The application data-epoch bound alone does not prove every window-history age condition.

The first profile excludes SYN data, options, simultaneous open, retransmission, timers, resets, and close processing.
SYN data and simultaneous open are valid TCP features outside this profile.
[RFC 9293, sections 3.5 and 3.10.7.3](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.5).
An omitted required response causes unsupported processing, not a supported continuation with assumed unchanged state.

MSS options need a later selected extension.
That extension must distinguish absent MSS, positive MSS, zero MSS, duplicate MSS, and illegal option length.
The default rule applies to absence and does not define a zero-to-default conversion.
The source does not select one of two MSS values.
[RFC 9293, sections 3.2 and 3.7.1](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.2).

Congestion control, authentication, native refinement, reliability, failover, and the full campus demonstration remain open.
All seven research programs remain OPEN.

## Static artifacts

`scripts/tcp_handshake_reference.py` contains the independent startup oracle and control-byte calculations.
It derives endpoint state from local configuration and checked startup messages.
It uses exact single-position ACK tests and modulo sequence addition.
The existing independent byte decoder verifies the generated IP and TCP checksum fields.

`examples/tcp-handshake/fixtures.json` contains 110 replay traces and 25 input-error cases.
The traces include 37 completed exchanges and 70 unsupported stops.
Four supported traces leave startup incomplete.
One completed exchange has a later unsupported event, so completion and supported replay remain separate results.
`examples/tcp-handshake/trace.json` contains the ordinary exchange for the guide.

The examples include sequence wrap, zero and maximum windows, reduced IP limits, and mandatory TCP checksum zero.
They also include tuple transformations, policy and tuple retries, lost final ACK, and malformed unread byte strings.
Wrong ACKs, wrong final sequence values, resets, SYN data, options, simultaneous open, and wrong phases cause unsupported stops.
Valid input syntax with a successful transition but no matching earlier output causes an input error.

`scripts/check_tcp_handshake_examples.py` compares every computed report field with the independent fixtures.
It also verifies decoded input and output fields, source event indices, exact byte paths, derived states, and establishment times.
The unit tests do not compile or execute Lean or the CLI.
The manual helper uses the compiled CLI and performs additional strict input tests.
