# An authenticated campus TCP application path

This model connects EAP session evidence, actual installed policy, tracked NAT, routing, and TCP application bytes.
Gateway execution supplies the delivery paths used by the endpoint proofs.
The input supplies no replacement established state, packet source, or forwarding target.

```sh
lake exe netlib campus-tcp examples/campus-tcp/trace.json --json
```

The example uses constructed unfragmented IPv4 bytes and one live modeled gateway.
It is a step toward the full campus demonstration.
It does not complete that demonstration or any of the seven research programs.

## Input and execution

The [example input](../examples/campus-tcp/trace.json) contains the full schema-one bundle.
It uses the existing EAP, session-intent, nftables, ingress, and iproute2 import formats.
Separate [native-format inputs](../examples/campus-tcp/) identify the permit, deny, NAT, route, guard, and interface data.
The parser rejects unknown fields, duplicate configuration, specification, and guard identities, replacement packet sources, and supplied delivery paths.

The input also declares local endpoint sockets, sequence choices, receive capacity, pending storage, and IP size limits.
These are local choices and lower-layer evidence.
They are not derived from authentication or remote packet fields.

The timeline has these operations:

| Operation | Meaning |
| --- | --- |
| `authentication` | Consume the next actual EAP observation exactly once. |
| `install` | Store the selected imported gateway configuration. |
| `stage` | Construct an ingress attachment from the current authentication prefix. |
| `installGuard` | Store the selected imported numeric ingress guard. |
| `open` | Generate a checked local SYN. |
| `write`, `send`, `read`, `emitAck` | Run the selected endpoint application operation. |
| `assign` | Allocate an immutable ticket for an earlier endpoint output. |
| `serve` | Process that stored ticket through the current gateway. |
| `deliver` | Present exact bytes from an earlier actual gateway emission to the opposite endpoint. |

Each generated output receives an output identity.
Assignment references that identity and records an actual ingress lifetime.
It cannot supply replacement bytes.
Service consumes one pending ticket by identity.
A second service of the same ticket fails.
Receiver delivery can repeat an earlier emission to represent network duplication.
The endpoint profile decides whether that receipt is supported.

`serve.observed` is either null or a supplied input/output byte observation.
A mismatched observation fails comparison and cannot replace the stored source or computed outcome.
`deliver.rawIPv4Hex` must decode and equal the selected actual emission.
A fabricated service reference or a service without output cannot supply a receipt.

All event syntax and hex syntax are parsed first.
The replay stops at its first unsupported result.
Later transport contents remain unevaluated.
Reported event fields come from typed values and use lowercase hex.

## Current policy at service

Installed configurations persist across authentication changes.
Every installation comparison and service comparison uses the actual consumed EAP prefix.
The forward checker compares the actual stored snapshot with the compiled session policy for every modeled classification and header.
An established conntrack classification does not grant permission by itself.

The ingress checker compares the actual numeric guard with current staged attachments.
An attachment records the authentication round, authentication-port lifetime, data-ingress lifetime, application scope, and header class.
Current interface lifetimes and principal/header ownership remain supplied deployment evidence.

The comparison never replaces actual installed decisions.
If stale allow rules remain installed after Logoff, the model can still emit a packet.
The report retains that computation and marks the current-policy comparison false.
It does not substitute a generated deny pipeline for the stored allow pipeline.

Early ingress denial preserves tracking and admission state.
An admitted input uses one lifecycle preparation for TCP admission and forwarding.
The prepared attachment supplies the exact NAT entry and direction.
Fresh candidates come from the current imported NAT table only when confirmed lookup misses.
Existing bindings keep their stored mapping.

Routing follows destination NAT.
A routed packet with expired TTL stops before the later filters and source NAT.
Forward and late filters use the actual stored configuration.
Successful output uses the lifecycle-selected tuple, decremented TTL, and mandatory IPv4/TCP checksum calculations.
For forwarded output, the route comparison requires the selected client or server role in the declared campus interpretation.
A forwarded packet with the wrong route remains an actual computation and fails that comparison.

## Checked TCP admission

The gateway gate starts without a TCP history.
It learns control positions from the observed SYN and SYN,ACK, then processes the final ACK and selected data.
It validates the actual decoded segment and exact lifecycle-selected entry, zone, and direction.
No caller-supplied validation Boolean enters this gate.

Application byte positions, ACK positions, outstanding spans, peer windows, and window-history ages have explicit bounds.
SYN uses a control position and contributes no application byte.
The selected no-option data profile limits each payload to 536 bytes.
Old ACKs and duplicate ACKs have distinct window-update conditions.

Admission and reply observation precede routing and later filtering.
A valid dropped reply can therefore change observed tracking state without output.
The example tests retain `seenReply` and SYN,ACK history after a late drop.
An unconfirmed fresh drop leaves no confirmed admission history.
History loss, replacement, unsupported controls, and unsupported sequence behavior stop replay.

This is a checked Lean admission model.
It does not establish Linux TCP tracker refinement.
Firewall `CTState.established` and endpoint TCP ESTABLISHED remain different states.

## Startup and application proof

The three startup messages pass through the same gateway pipeline as application data and ACKs.
Their actual receipts construct the [startup history](TCP_HANDSHAKE.md) and valid application states.
The active endpoint enters ESTABLISHED at accepted SYN,ACK receipt.
The passive endpoint enters ESTABLISHED only at accepted final ACK receipt.

Application operations begin after that final receipt in this selected quiet-boundary profile.
Later startup copies are unsupported.
Every application receive refers to an actual earlier endpoint output, immutable assignment, service result, and exact receiver bytes.
The final history checker uses actual global steps and endpoint chains to construct the delivery history.
It does not accept that history as an unexplained input certificate.

The composed property states that each endpoint's application reads form a prefix of the other endpoint's writes.
For compliant services, gateway facts establish current session permission, method readiness, ingress attachment, selected NAT mapping, route, filters, and TTL.
The [application guide](TCP_APPLICATION.md) explains the finite-epoch and byte-origin conditions.
The initial states and cursor equalities come from the checked startup, rather than caller assertions.

The concrete example sends `abc` to the server and `xyz` to the client.
Each application reads its exact bytes.
A return ACK removes the acknowledged sender prefix.
The proofs permit loss, rejection, and stalled progress.
They do not establish eventual delivery.

## Revocation boundary

The example queues another client data packet while the session permits the application.
It then consumes Logoff and installs current forward and ingress denial.
Service emits no new TCP packet, although the cached NAT binding remains present.

This guarantee concerns later gateway output.
It does not erase earlier output or receive storage.
A separate regression delivers `abc` while authorized and reads those buffered bytes after Logoff and denial.
That read remains valid.
Its permission evidence comes from the earlier gateway service, not the later read time.

## Results and remaining work

The command returns zero when all processed comparisons and applicable history checks pass.
It returns one for supported computations with failed comparisons or failed history construction.
It returns two for unsupported processing or invalid input.
The report retains each actual decision, byte output, service comparison, and unprocessed suffix.
Each event row includes separate `supported` and `passed` values.
An accepted installation can store a configuration while its current-policy comparison fails.
`compliant` concerns the processed finite prefix.
It does not require startup completion or consumption of every supplied authentication observation.

`applicationAssurance.status` is `pendingStartup`, `checked`, or `failed`.
`checked` requires completed startup and successful construction of the composed application proof.
Its byte and receive counts come from the actual final endpoint histories.
An empty or partial startup can pass its comparisons without an application assurance result.

The independent [oracle and fixtures](research/CAMPUS_TCP.md) compare exact bytes, state changes, policy decisions, NAT, routing, receipts, and reads.
These are constructed tests, without a new native capture claim.

EAP method acceptance and credential integrity remain supplied evidence.
TLS cryptography, authentic capture, faithful native installation, physical delivery, and real Wi-Fi enforcement require separate arguments.
The interface/node interpretation and principal/header ownership also remain deployment assumptions.

The selected path has one gateway and one bounded ordinary TCP connection.
It does not extend the UDP-only replication profile to TCP.
TCP replication, failure recovery, safe upgrade, reordering, retransmission, options, timers, and long sequence reuse remain open.
All seven [research programs](ROADMAP.md) and the full campus demonstration remain OPEN.
