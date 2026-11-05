# Directional TCP MSS

MSS support connects actual startup bytes, endpoint send limits, gateway admission, and planned gateway transfer.
The MSS option advertises the sender's receive capability.
It limits data sent in the opposite direction.

```sh
lake exe netlib campus-tcp examples/tcp-mss/trace.json --json
```

This extends [startup](TCP_HANDSHAKE.md) and the [planned transfer](CAMPUS_TCP_TRANSFER.md).
It does not establish full TCP conformance or reliable delivery.

## Local receive evidence and peer input

Local startup configuration accepts an optional `receiveMSS` object:

```json
"receiveMSS": { "ipReceiveLimit": 1240, "value": 1200 }
```

The IP receive/reassembly limit must be between 576 and 65535 bytes.
The advertised value must be positive, fit its 16-bit field, and satisfy `40 + value ≤ ipReceiveLimit`.
These checks justify the numeric advertisement within the supplied receive capability.
The capability itself remains lower-layer evidence.
It is separate from the IP send limit, application receive capacity, and current receive window.

Omitting `receiveMSS` retains the existing option-free generated control bytes.
Positive incoming MSS support is automatic and does not depend on a local advertisement.
Each accepted peer value comes from the actual decoded option bytes.
The input cannot supply a replacement peer-MSS certificate.

The selected startup semantics accept MSS, NOP, and EOL padding.
A valid MSS option can start after NOP, without word alignment.
The full TCP header still has the codec's required alignment.
Unknown option interactions remain unsupported in this selected handshake profile.

Absence selects the IPv4 default 536.
A present positive value is retained, including a value below 536 or an explicit 536.
Zero and duplicate values remain selected unsupported semantics.
They do not silently become absence.
Malformed framing remains a codec error.
These distinctions do not claim that the cited MSS clauses mandate a particular zero or duplicate policy.

## Actual startup and sizing

The local constructor emits one canonical four-byte MSS option on SYN or SYN,ACK when an advertisement is present.
It proves the option bytes, 24-byte TCP header, 44-byte IPv4 packet, and mandatory checksums.
The actual control packet must fit the local IP send limit.
A legacy 40-byte control packet can fit a limit of 41; a control packet with MSS requires at least 44.

The final ACK has no MSS option.
The active endpoint learns its peer limit from accepted SYN,ACK bytes.
The passive endpoint retains its peer limit from the initial SYN.
The final ACK's window still supplies the passive peer-window fields, but it cannot reset MSS to 536.

For option-free IPv4 data, the effective send-data bound is:

```text
min(peer MSS or 536, local IP send limit - 40)
```

The four option bytes on SYN do not permanently reduce later option-free data by four.
The general sizing theorem subtracts the actual TCP and IP option overhead after the minimum.
For example, peer MSS 1000 and IP send limit 1500 give baseline 1000; twelve data-option bytes leave 988.
Exhausted allowance produces zero, without unsigned underflow or an invented positive budget.
Options on application data and IPv4 options remain outside this extension.

Certified NAT and TTL rewriting retains the actual startup options.
The paired exchange requires exact source and receipt option provenance.
Adding MSS to a receipt without changing its earlier generated source remains a failed history.
MSS clamping would require a separate checked option transformation.

## Gateway and checkpoint continuity

The gateway learns the client offer from SYN and the server offer from SYN,ACK.
It retains the raw offers in startup and established state.

| Data direction | Observed peer limit |
| --- | --- |
| Original, client to server | Server's SYN,ACK MSS, or 536 if absent |
| Reply, server to client | Client's initial SYN MSS, or 536 if absent |

Data admission uses that directional limit instead of a fixed 536-byte cap.
Ordinary ACK and window updates retain the learned values.
Actual admission commitment and valid later drops retain the same facts.

Checkpoint equality includes each raw offer and all earlier packet observations.
Absent MSS and explicit MSS 536 remain different state, even when their numeric limits agree.
An MSS-only source change cannot pass the exact source comparison.
The standby inherits the actual learned limits; target configuration cannot replace them.

Extended gateway diagnostics use `clientMSS` and `serverMSS` for raw offers.
`originalMSS` and `replyMSS` give the corresponding data limits.
These fields appear when a learned offer is present.
Existing absent/absent transport diagnostics and valid no-option packet bytes remain unchanged.

## Connected example and evidence

The example has these independent local capabilities:

| Endpoint | Receive MSS | IP receive limit | IP send limit | Effective outgoing MSS |
| --- | --- | --- | --- | --- |
| Client | 1200 | 1240 | 1000 | 800 |
| Server | 800 | 840 | 1500 | 1200 |

Each application receive and pending capacity is 4096.
The receive advertisement does not become a single global minimum.

The primary processes an 800-byte client segment and a 1200-byte server segment.
It also processes an actual queued server byte during the assignment pause.
The copied server epoch contains 1201 observed bytes and none acknowledged.
A deferred client ACK uses that transferred history on the standby.
The standby then processes another exact-limit segment in each direction.
The server reads 1600 bytes; the client reads 2401 bytes from service at the two gateways.

The typed demonstration derives the directional seed limits from the actual paired startup.
It connects the four large services to actual admission and commitment, copied offers, read-prefix proofs, and current Logoff denial.
Application and transfer assurance use the existing global history, without new established seeds or supplied delivery paths.

The independent [research evidence](research/TCP_MSS.md) compares bytes, limits, copied state, deferred ACKs, reads, and assurance results.
Valid old no-option fixtures remain unchanged.
Old outside-profile expectations change where positive MSS or NOP/EOL support makes their former result incorrect.
No expectation is changed to hide an unmatched source or receipt.

RFC 9293 requires MSS input/output capability and defines the IPv4 default and effective-size rules.
RFC 6691 explains fixed-header advertisement sizing; RFC 1122 distinguishes IP send and receive limits.
See [RFC 9293, sections 3.2 and 3.7.1](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.7.1),
[RFC 6691, section 2](https://www.rfc-editor.org/rfc/rfc6691.html#section-2), and
[RFC 1122, sections 3.4 and 4.2.2.6](https://www.rfc-editor.org/rfc/rfc1122.html#section-4.2.2.6).

The SYN-only MSS rule constrains sending.
It does not by itself prescribe drop or reset behavior for received non-SYN MSS.
The remaining non-SYN option stop is selected unsupported scope.
Native TCP correspondence, timers, congestion control, retransmission, reordering, other options, and full connection processing remain open.
Physical receive capability, installation, delivery, credential integrity, and cryptographic refinement require separate evidence.
All seven research programs and the full campus demonstration remain OPEN.
