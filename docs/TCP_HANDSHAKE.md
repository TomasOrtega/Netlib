# Checked TCP startup and application states

Netlib constructs the bounded application states from an ordinary TCP startup history.
The input contains local configuration and events, without replacement established states.
Successful receipts must match earlier model outputs through exact checked byte paths.

```sh
lake exe netlib tcp-handshake examples/tcp-handshake/trace.json --json
```

The selected exchange uses empty SYN, SYN,ACK, and final ACK messages without options.
SYN occupies one sequence position and contributes no application byte.
The active endpoint enters ESTABLISHED when it accepts SYN,ACK.
The passive endpoint enters ESTABLISHED when it accepts the final ACK.
Loss of that ACK leaves the passive endpoint in SYN-RECEIVED.

## Configuration and events

Schema one contains `active`, `passive`, and `events`.
Each local configuration has these fields:

| Field | Meaning |
| --- | --- |
| `socket` | Local IPv4 `address` and TCP `port`. |
| `iss` | Local initial sequence choice, between zero and `2^32-1`. |
| `capacity` | Local receive capacity, at most 65535 bytes. |
| `pendingLimit` | Application pending-storage limit, at most 65535 bytes. |
| `ipSendLimit` | Local IP size limit, between 41 and 65535 bytes. |

The local sequence choice does not prove randomness, uniqueness, or security.
The caller supplies local configuration and lower-layer IP size evidence.
The passive endpoint derives its remote socket from the checked SYN.

Use these event forms:

```json
{"kind":"activeOpen","remote":{"address":"198.51.100.2","port":80},"policyPermitted":true}
{"kind":"listenSyn","rawIPv4Hex":"...","path":"direct","policyPermitted":true}
{"kind":"synSentSynAck","rawIPv4Hex":"...","path":"direct","policyPermitted":true}
{"kind":"synReceivedAck","rawIPv4Hex":"...","path":"direct"}
```

The three receipt lines show field names only.
Use actual byte strings from the example for execution.
A policy input permits the entire selected transition and its output.
Policy denial preserves the phase and produces no output.
This permission rule is an explicit model input, not full RFC socket behavior.

The wrapper selects this phase sequence:

| Successful event | Active phase | Passive phase |
| --- | --- | --- |
| Initial state | CLOSED | LISTEN |
| `activeOpen` | SYN-SENT | LISTEN |
| `listenSyn` | SYN-SENT | SYN-RECEIVED |
| `synSentSynAck` | ESTABLISHED | SYN-RECEIVED |
| `synReceivedAck` | ESTABLISHED | ESTABLISHED |

Rejected tuple or policy events preserve the current phase and permit a later event.
An event for another phase is unsupported and stops replay before transport decoding.
This phase gate limits the selected wrapper.
It does not specify the full RFC input-action order.

## Checked delivery and output

Each output contains exact tuple, sequence, ACK, flag, window, option, payload, and checksum fields.
The selected IPv4 outputs use IHL five, DF, TTL 64, and no external padding.
The SYN and SYN,ACK use a separate control-output constructor.
They do not require the established application-buffer invariant.
The final ACK uses the newly constructed active state and its current fields.

A `direct` receipt requires exact equality with its earlier output bytes.
A `rewrite` receipt uses the decoded input tuple and TTL as the selected rewrite target.
The checker computes the certified TCP tuple rewrite and requires exact output-byte equality.
It preserves payload, sequence, ACK, flags, window, and options.
The formal byte-path type also composes successive certified rewrites.

Only a successful model receipt can advance the connected history.
It must pass the selected byte-path test.
A valid checksum alone cannot supply that source relation.
A successful candidate with mismatched history causes an input error.

The report exposes output bytes, decoded receipts, source-event indices, phases, and establishment indices.
The derived active state appears after SYN,ACK receipt.
The derived passive state appears only after final ACK receipt.
`exchangeComplete` becomes true only with the checked four-event history.
This field describes the mathematical model exchange.
Byte equality cannot establish physical origin, peer identity, or the current connection instance.

## Derived application fields

Let the active and passive initial sequence choices be `a` and `b`.
The active send cursors become `a+1`, and its receive cursor becomes `b+1`.
The passive send cursors become `b+1`, and its receive cursor becomes `a+1`.
All additions use modulo `2^32`.
The new pending, outstanding, and receive buffers are empty.

The active peer window, `SND.WL1`, and `SND.WL2` come from the checked SYN,ACK.
This initialization uses the explicit interpretation in RFC 1122, section 4.2.2.20(c).
The passive fields come from the checked final ACK.
Its default peer MSS comes from the earlier checked SYN, not the final ACK.

The absence of startup options gives default IPv4 peer MSS 536.
The effective MSS is `min 536 (ipSendLimit - 40)` for later output without options.
The proofs derive the positive MSS and IP bounds required by `Endpoint.State.Valid`.
They preserve the distinction between local receive capacity and the peer window.
The [source investigation](research/TCP_HANDSHAKE.md) records the selected RFC clauses and initialization interpretation.

## Composition and limits

`HandshakeExchange.Complete` stores actual successful transition equations and the three checked delivery paths.
It derives valid endpoint states, empty buffers, complementary cursors, peer-window sources, and default MSS.
Its application theorem uses these states in the existing [application prefix proof](TCP_APPLICATION.md).
The caller supplies supported application traces, future delivery history, and finite sequence epochs.
The composed theorem also states a quiet boundary after final ACK receipt and explicit current-instance assumptions.
It does not infer those environment conditions from wire bytes.

The data-prefix theorem bounds each data epoch below half the sequence space.
A window-history arc that includes SYN needs the separate bound `1 + dataEpochBytes < Seq.halfSpace`.
The data bound alone does not prove the age of every window-history comparison.

Unsupported flags, options, startup data, ACKs, or sequence values stop replay.
These results leave omitted RFC actions for later processing.
The report retains the unprocessed suffix with canonical lowercase hex strings.
All event syntax is parsed first, but later transport contents remain unevaluated.
The command returns zero for supported replay, including rejection and an unfinished exchange.
It returns two for unsupported replay or an input error.

SYN data, simultaneous open, and startup options are valid TCP features outside this first profile.
Full MSS sending and receipt support also remains open.
Reset handling, retransmission, timers, close processing, congestion control, and long sequence reuse remain open.
Native refinement, authentication, failover continuity, and eventual delivery require further evidence.
All seven [research programs](ROADMAP.md) and the full campus demonstration remain OPEN.
