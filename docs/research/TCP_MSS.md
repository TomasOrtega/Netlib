# Directional TCP MSS

This note connects selected MSS rules to startup, gateway service, and planned transfer.
The Python evidence constructs static packets and calculates checksums independently.
It does not execute Lean, send packets, or collect captures.

## Source rules

RFC 9293 requires MSS sending and receipt capability (`MUST-14`).
An absent IPv4 MSS selects 536 (`MUST-15`).
An MSS describes the option sender's receive capability.
Its output is restricted to SYN segments (`MUST-65`).
The format has kind 2, length 4, and a two-byte value.
Options can start at any byte boundary (`MUST-64`).
[RFC 9293, sections 3.2 and 3.7.1](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.7.1).

RFC 1122 separates IP receive and reassembly capability from IP transmission capability.
Its `MMS_R` bounds an advertisement, while `MMS_S` bounds outgoing transport messages.
The IP receive and reassembly size must be at least 576.
Application buffer capacity and a changing receive window have separate meanings.
[RFC 1122, sections 3.3.2, 3.4, and 4.2.2.6](https://www.rfc-editor.org/rfc/rfc1122.html#section-4.2.2.6).

An advertisement subtracts the fixed IP and TCP headers from the selected size.
Possible options do not reduce the advertisement.
Each outgoing packet must account for the options it actually carries.
[RFC 6691, section 2](https://www.rfc-editor.org/rfc/rfc6691.html#section-2).

The effective send expression is:

```text
min(SendMSS + 20, MMS_S) - TCPhdrsize - IPoptionsize
```

`TCPhdrsize` includes actual TCP options.
For the fixed IPv4 profile and IP datagram limit `L`, this becomes:

```text
min(peerMSS, L - 40) - actualTCPOptions - actualIPOptions
```

The subtraction follows the minimum.
The four MSS bytes on SYN do not reduce later data packets that have no options.
This formula is an arithmetic consequence of the source expression.
[RFC 1122, section 4.2.2.6](https://www.rfc-editor.org/rfc/rfc1122.html#section-4.2.2.6).

## Selected interpretation

The parser distinguishes absence, one positive value, zero, and duplicate values.
Positive input support is automatic.
It does not depend on a local advertisement setting.
SYN and SYN,ACK permit MSS, NOP, and EOL options with valid framing.
A positive value below 536 remains a positive offer.

Zero and duplicate MSS values return an unsupported result in this model.
The cited MSS passages specify no zero fallback or duplicate precedence rule.
These results describe selected scope.
They do not claim an RFC requirement to reject those packets.

The final ACK and application packets still require an empty option region.
This is also a scope limit.
The SYN output restriction does not establish a mandatory receiver rejection rule.
RFC 9293 separately requires reception of options in any segment (`MUST-5`).
[RFC 9293, sections 3.1 and 3.2](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.1).

Malformed option framing remains an input decoding error.
An unsupported result stops evaluation before later events.

## Local evidence and exact startup

Local configuration can contain `receiveMSS`:

```json
{"ipReceiveLimit": 1240, "value": 1200}
```

The value is positive and fits its 16-bit field.
The IP receive limit is between 576 and 65535.
The fixed forty bytes plus the value must fit that receive limit.
This declared lower-layer capability is input evidence.
It does not prove a native socket or operating-system setting.

Without this field, valid old startup output remains forty bytes with no options.
With it, SYN and SYN,ACK contain the four-byte MSS option and use forty-four bytes.
The actual control packet must fit the local IP send limit.
A legacy send limit of 41 remains valid without an advertisement.
An advertisement requires a limit of at least 44.
The final ACK contains no MSS option.

The active endpoint derives its peer MSS from the accepted SYN,ACK.
The passive endpoint retains the initial SYN offer and uses it after the final ACK.
That ACK still supplies the passive peer-window history.
It does not replace the retained MSS with the absent-option default.

A successful receipt must retain the actual earlier output's options.
Adding a valid positive MSS only to receipt bytes fails exact source validation.
NAT and TTL processing preserve the options while updating affected checksums.
Support for an option does not supply its causal source.

## Gateway and checkpoint state

The gateway learns the client offer from the actual original SYN.
It learns the server offer from the actual reply SYN,ACK.
Original-direction data uses the server offer.
Reply-direction data uses the client offer.
The default 536 applies independently to an absent offer.
Local endpoint IP send limits remain separate.

The admission phase retains the raw offers.
Its diagnostics expose their selected numeric limits when an offer is present.
Window updates preserve the offers.
Checkpoint equality includes the offers and the observed source packets.
A change to only an MSS field makes the source image stale.
An explicit offer of 536 remains distinct from absence, although their numeric limits agree.
Target policy and namespace checks remain independent of the copied transport state.

## Independent evidence

[The fixtures](../../examples/tcp-mss/fixtures.json) store selected expected results.
[The transfer trace](../../examples/tcp-mss/trace.json) has 71 events.
The client advertises 1200 with receive limit 1240 and send limit 1000.
The server advertises 800 with receive limit 840 and send limit 1500.
Each application capacity and pending limit is 4096.

The client sends 800 bytes through each gateway.
The server sends 1200 bytes through each gateway.
One additional server byte is queued at the primary before the pause.
It is served during the pause before the final checkpoint.
The checkpoint retains a server byte epoch of 1201 with no acknowledgment yet.
The first standby ACK acknowledges that epoch.

The server reads 1600 bytes, and the client reads 2401 bytes.
Each read spans service by the primary and standby gateways.
Later Logoff and current denial stop a queued packet at ingress.
The cached NAT entry remains present.
Permission applies at gateway service time; it does not erase received buffers.

The fixtures cover single-sided offers, absent defaults, small positive values, and local send limits.
They include sequence wrap, exact control fit, and lost final ACK.
They also test zero and duplicate values, malformed framing, and unmatched receipts.
Strict input cases reject supplied limits and checkpoint state.
The manual helper compares full independent steps and the existing application and transfer assurances.

The old valid no-option fixtures remain unchanged.
Six old EOL, NOP, or positive MSS injections now fail source validation after option support.
Two former option-first rows now stop on their SYN data.
The original zero, duplicate, unknown-option, and final-ACK scope limits remain explicit.

This evidence does not establish native state migration, retransmission, congestion control,
or a general TCP implementation.
All seven research programs and the full campus landmark remain OPEN.
