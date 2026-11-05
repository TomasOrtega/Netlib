# Native conntrack replication and gateway handoff

This example records one IPv4 UDP binding through FTFW replication, kernel commit, and an ordered two-gateway handoff.
The [source note](../../docs/research/NATIVE_STATEFUL_FAILOVER.md) identifies the exact daemon, library, kernel, and protocol behavior.

The capture uses conntrack-tools 1.4.9, libnetfilter_conntrack 1.1.1, and Ubuntu kernel `6.8.0-117-generic`.
The parent image is `netlib-received-icmp-capture:1` with ID `sha256:05d09351510c9fc2a6107d961530efdef25570cd5807506a2e20ad5883a7346b`.

## Topology and ownership

Four namespaces represent a client, primary gateway `a`, standby gateway `b`, and server.
Each endpoint has a separate link to each gateway.
The gateways also have a dedicated synchronization link on `10.10.0.0/24`.
All links have MTU 1500.

The client retains source address `192.0.2.2` across both paths.
The server retains source address `198.51.100.2` across both paths.
Explicit host routes select the active gateway independently for client requests and server replies.
The handoff changes these routes in two recorded operations, then disables both primary data interfaces.
The synchronization interfaces remain active.

The selected binding has these tuples:

| Direction | Source | Destination |
| --- | --- | --- |
| Original | `192.0.2.2:41000` | `203.0.113.2:8080` |
| Reply | `198.51.100.2:9000` | `203.0.113.1:40000` |

Both directions use conntrack zone zero.
The public translation address `203.0.113.1` remains unassigned on every actor.
Both gateways have a blackhole route for that address.
A reply without a committed binding therefore encounters that route; it cannot reach the client through an identity binding.
A committed reply restores the client destination before route selection.

## Recorded sequence

1. A real client request creates the primary's binding and reaches the server.
2. The standby's external cache receives the replica while its kernel table remains empty.
3. Separate route changes select the standby for each direction, then fence the primary's data interfaces.
4. An uncommitted reply produces no client delivery and no confirmed standby entry.
5. Explicit cache commit installs the binding into the standby kernel.
6. Current deny policy blocks a reply while its tracked entry records `SEEN_REPLY`.
7. Current established policy permits the next reply.
8. A further request and reply traverse the standby using the retained binding.

FTFW uses its external cache, `CommitTimeout 180`, and acknowledgment window 300.
Synchronization traffic is explicitly untracked and excluded from daemon state replication.
Every selected packet remains whole and below the interface MTU.

## Raw evidence

The run contains 13 events, six datagram inputs, 16 NFLOG messages, and 56 Ethernet frames.
Two separate packet-socket records describe primary interface shutdown.

`native/capture.json` retains the ordered event records, observer configuration, endpoints, and file references.
`native/commands.json` retains every synchronous command with its arguments, output, exit status, and monotonic interval.
Before and after every event, the capture exports both kernel tables, both complete rulesets, and every actor's network state.

The capture retains original Netlink messages, external cache XML, daemon logs, statistics, and complete synchronization Ethernet frames.
Cache XML exposes the original tuple but omits translated reply fields.
The verifier therefore decodes actual FTFW attributes rather than inventing a cache Netlink snapshot.
Kernel readbacks establish the committed binding independently of command success.

Early NFLOG observations retain ingress IPv4 bytes before attachment and translation.
Tracked and egress hooks retain their separate observations.
Packet sockets retain raw Ethernet observations on every data and synchronization interface.
All checksum and segmentation offloads selected by the producer are disabled and read back.

Disabling a primary data interface can return `ENETDOWN` to its packet socket.
The collector records that error and closes that socket while retaining synchronization capture.
Other collector errors fail the run.
Trace collectors end through recorded SIGTERM signals; packet and NFLOG collectors exit normally.

## Reproduce

Build the [pinned parent](../received-icmp/README.md) using its capture recipe, then run:

```sh
examples/replication/recapture.sh /tmp/netlib-replication-recapture
```

The recipe builds from the recorded producer files and uses an isolated container without external networking or host mounts.
It requires the same namespace capabilities as the earlier native captures.
The verifier requires the selected kernel release and tool versions.
Readbacks and hashes belong to the newly produced run; they do not replace the saved evidence.

## Scope

The selected stable state contains tuples, zones, NAT flags, and reply classification.
Kernel identifiers, counters, unrelated status flags, and identical remaining lifetimes are outside that equality.
The explicit commit timeout is positive; the recorded execution assumes no entry expires during transfer or forwarding.

The example records ordered replication and handoff operations.
It does not establish automatic failure detection, bounded convergence, eventual replication, split-brain prevention, or deletion propagation.
Concurrent packets, failed commits, nonempty standby replacement, TCP state, and broader protocol behavior require additional models.
