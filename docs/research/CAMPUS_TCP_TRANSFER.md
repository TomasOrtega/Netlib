# A reachable TCP checkpoint and planned transfer

This note records the constructed evidence for transfer between two modeled gateways.
The endpoints retain one connection and their actual application histories.
No native experiment or new traffic capture supplies this evidence.

## Source rules and model limits

TCP sequence positions identify stream bytes across a connection.
Gateway replacement does not create a new endpoint stream.
The selected profile retains the existing no-option startup limit.
Full TCP requires MSS input/output support, retransmission timers, and congestion control.
[RFC 9293, sections 3.4, 3.7.1, and 3.8](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4).

Linux TCP tracking has internal sequence/window fields beyond the state, scales, and flags exported as TCP protoinfo.
Thus, a modeled tracker/admission copy is not a general certificate for native TCP tracker reconstruction.
[Linux v6.8 TCP tracking](https://raw.githubusercontent.com/torvalds/linux/v6.8/net/netfilter/nf_conntrack_proto_tcp.c),
[internal TCP state](https://raw.githubusercontent.com/torvalds/linux/v6.8/include/linux/netfilter/nf_conntrack_tcp.h).

The conntrack-tools manual distinguishes its cache from the kernel table.
Receiving cache data alone does not establish target installation.
[Official conntrack-tools manual](https://conntrack-tools.netfilter.org/manual.html).

The new module uses actual checked Lean packet computations.
It preserves the existing UDP-only replication profile.
It supplies no native TCP synchronization or installation claim.

## Reachable state

The source transport history starts with empty tracker and admission state.
Each processed transport transition retains actual preparation, admission, forwarding, and commitment equations.
The campus service constructs that transition from its actual stored input and pipeline.
An early ingress drop changes neither the transport pair nor its transition count.
A later route or filter drop can retain admitted observations and advance the count.

The checkpoint captures the full confirmed tracker, TCP phase, observed packets, directional sequence bases, byte counts, peer windows, and window coordinates.
It also records the actual source transition cut and global staging operation.
The executable image comparison represents equality of the transport pair.
The cut count remains a separate equality test.

An established phase with internally valid lane bounds is insufficient source evidence by itself.
The checkpoint must come from the actual reachable source history.
A copied NAT entry and `seenReply` bit cannot replace that TCP history.

Policy, authentication, ingress attachments, and namespace lifetimes remain separate from the copied transport pair.
Changing those policy inputs does not make the transport cache stale.
Each later target service must still evaluate its actual installed policy and current authentication prefix.
Copying source transport state does not grant target access.

## Controller order

Staging can occur before assignments pause.
The source can advance after an early stage, which makes that cache stale.
Installation requires an actual pause, no pending primary ticket, the exact unchanged source pair and cut, and an empty target pair.
It also verifies the supplied target namespace against the declared standby and its current guard namespace.

Successful installation seals the primary against packet service.
The client and server route owners move separately while assignments remain paused.
Fencing requires the two owners away and no primary ticket.
Resume requires installed standby ownership, primary fencing, and unchanged installed transport state.
The endpoints can then produce and receive packets through their existing histories.

Pause controls assignment only.
It does not erase earlier endpoint output, receiver storage, or actual gateway emissions.
An earlier emission can still supply its exact receipt after a later controller operation.
Each ticket retains its assigned gateway and route epoch.
Service cannot select a replacement gateway from current route ownership.

The pending set is tested against actual stored work.
This test does not establish that every TCP queue has a supported drain order.
The selected admission model still excludes missing sequence positions, retry processing, and reordering.
The example exhibits one supported drain; general progress remains open.

## Decisive constructed trace

`examples/campus-tcp-transfer/trace.json` contains 71 operations.
It consumes shared EAP/session evidence, then installs and stages each gateway's policy and ingress attachments separately.
Startup runs through the primary and derives the existing endpoint states.

The client sends `abc` to the server.
The server sends `xy` to the client, then queues another server output containing `z`.
The client defers its ACK of those server bytes.

Pause is operation 38.
The first stage at operation 39 captures cut 5, with two observed server bytes and none acknowledged.
Service 40 and receipt 41 process the already assigned `z` during the pause.
The next stage at operation 42 captures cut 6, with three observed server bytes and none acknowledged.
The NAT tuple and `seenReply` remain unchanged, so copying only those fields would miss the important advance.

Installation at operation 43 copies the exact current pair to namespace 3, birth 1.
The client and server owners move at operations 44 and 45.
Primary fencing and resume occur at operations 46 and 47.

The deferred client ACK then passes through the standby.
It acknowledges the three transferred server bytes and clears the corresponding endpoint sent prefix.
The client sends `def` through the standby, and the server reads `abcdef`.
The server sends `w` through the standby, and the client reads `xyzw`.
Each read contains bytes from actual service at each gateway.

The final client output contains `ghi` and is assigned to the standby.
After Logoff and current standby forward/ingress denial, service emits no packet.
The standby retains its confirmed NAT entry and transport history.
The primary remains sealed and fenced with source cut 6; the target has nine inherited and new transport transitions.

A separate positive case stages the final cut before pause: stage 41, pause 42, install 43.
The proof needs stage before install and pause before install as separate conditions.
It must not assume pause before stage.

## Independent evidence

`scripts/campus_tcp_transfer_reference.py` reuses the independent TCP byte, serial-coordinate, EAP, native-policy, route, NAT, and admission calculations.
It calculates controller state and per-gateway histories separately.
It derives NAT status flags from the selected native translation rules.
The reference never imports Lean or reads Lean report output to set expectations.

The fixture file stores one shared constructed input and explicit path replacements.
Its 20 execution cases include source-cut staleness, early-drop cache stability, policy/authentication changes, sequence wrap, and duplicate ACK receipt.
Another case changes the fresh NAT candidate at the standby.
The latter case still uses the copied confirmed binding.
Partial cached, installed, one-owner, two-owner, and fenced prefixes remain transfer-pending until the required resume state exists.
A resumed case has empty read ledgers, so generic assurance does not assume nonempty reads.
The 71-operation witness supplies the nonempty reads separately.

The 31 input-error cases cover control order, stale or absent cache, target namespace identity/birth, and supplied state or admission certificates.
They also cover packet replacement, chosen ticket gateways, malformed unread hex, and strict standby fields.
The input language cannot construct an entry-only target copy or inject a target collision.
The module tests exercise the corresponding state guard and missing-history test.

The frozen expectations retain decisive cuts, final state, bytes, decisions, and reads.
They omit repeated rich packet histories from each saved before/after state.
`scripts/check_campus_tcp_transfer_examples.py` recalculates those histories independently and compares every per-step source packet, confirmed record, lane, cut, installation reference, gateway epoch, decision, output, and state.
It also audits the earlier write/output/assignment/service/receipt/read path.
Python unit tests do not invoke the compiled CLI.

`applicationAssurance` and `transferAssurance` have separate meanings.
The application result concerns the actual startup and byte histories.
The transfer result additionally requires the actual stage, pause, installation, route, fence, and resume lineage with preserved source state.
A failed current-policy comparison remains failed even when actual packet computation emits bytes.

## Remaining work

The model does not establish physical delivery, faithful native installation, reliable replication, kernel TCP acceptance, or route convergence.
Principal/header ownership, credential integrity, EAP method acceptance, local sequence choices, and physical namespace interpretation remain supplied evidence.
The gateway lifetimes are fixed within the selected execution.

Revocation concerns later gateway output, not erasure of previously received bytes.
MSS options, timers, congestion control, retransmission, reordering, close/reset processing, unexpected failure, and broad native correspondence remain work.
All seven research programs and the full campus demonstration remain OPEN.
