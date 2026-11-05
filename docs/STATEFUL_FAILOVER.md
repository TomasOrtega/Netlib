# Native stateful failover

This layer connects packet processing, a cached replica, kernel installation, endpoint route changes, and an explicit primary fence.
It uses two ordinary conntrack tables for a selected whole IPv4 UDP flow.
The [source note](research/NATIVE_STATEFUL_FAILOVER.md) pins the daemon, library, and kernel behavior.

```sh
lake exe netlib wire-failover examples/replication/replay.json --json
```

Exit zero means agreement, one means observation mismatch, and two means malformed input or an unsupported execution.
The command checks evidence without installing state or changing routes.

## Source, cache, and installation

Both modeled kernel tables start empty.
An actual byte-derived packet step creates the primary's confirmed record.
A stage operation selects that record by a direction key from the computed primary table.
It retains the source state and its operation epoch.
Later observations cannot replace that source or seed the standby with a chosen mapping.

`Protocol.ConntrackReplication` keeps staging and commitment separate.
Commit appends the selected record's supported projection to a valid target table after checking both direction keys.
It preserves existing records, key uniqueness, NAT lookup, inverse rewriting, and seen-reply classification.
The projection retains tuples, zones, NAT flags, and the seen-reply flag.
Native remaining timeout seconds do not become an exact copied timer.

The configured positive commit timeout is installation metadata.
This model does not evolve its lifetime or prove that a later packet precedes expiry.
The selected native execution requires live records and excludes expiry during transfer.

The daemon's external cache has its own observation format.
Received FTFW attributes identify the original tuple, NAT endpoints, zone, and seen-reply state.
An actual external cache dump establishes the corresponding cached object.
These fields do not pretend to be a kernel Netlink dump.

A transport acknowledgement can precede cache allocation failure.
A successful commit command can also hide individual installation failures.
The native evidence therefore requires the actual standby kernel record after commitment.

Colliding installation is outside the selected model.
Native conntrackd can destroy a matching kernel entry and retry creation.
An unsupported model result does not describe that native operation as a rejected or atomic transaction.

## Ordered handoff and current policy

`Protocol.StatefulFailover` retains both gateway tables, the cached selection, endpoint route owners, and fenced gateways.
The client route and server return route change through separate operations.
Fencing the primary is another operation.
A selected packet must reach the gateway chosen for its endpoint leg, and that gateway must remain unfenced.

Each packet supplies the current route, NAT, forward filter, and late filter configuration.
A cached conntrack record retains its binding and classification without retaining an earlier permission.
Replicated conntrack state conveys no authentication or authorization.

The selected demonstration uses an unassigned public source-NAT address and explicit return routes.
Both gateways have a blackhole route for that untranslated public address.
Without committed state, the reply keeps that destination and encounters the drop route.
After commitment, inverse source NAT restores the client destination before route selection.

Current deny policy still blocks an associated reply after that lookup and rewrite.
The reply observation can set seen-reply state even when filtering later drops its packet.
A subsequent permitted reply and original-direction request use the installed mapping.
Successful output preserves payload, regenerates checksums, and decrements TTL once through the existing wire-forwarding proofs.

## Replay evidence and scope

Input bytes come from immutable early Netfilter logging observations.
Output bytes come from actual Ethernet observations.
Full kernel dumps remain separate observations for each gateway.
Failed comparisons never replace the computed tables, cached record, or route ownership.

The native verifier checks complete rulesets, routes, endpoint bindings, synchronization bytes, daemon configuration, command fences, and socket results.
A projection selects unchanged objects from complete nftables exports for the existing table adapters.
Its source references retain the original file and object indices.
Other hooks remain subject to the full native evidence check.

The saved [native example](../examples/replication/README.md) retains 13 native operations and six selected datagrams.
Its 11 modeled operations compare 22 post-operation table observations; the native verifier checks 56 actual kernel dumps.
Four selected datagrams forward and two drop.
Raw evidence includes 16 Netfilter packet observations, 20 selected Ethernet observations, and 12 synchronization frames.
Recorded interface-down errors preserve packet-socket observer accounting through the primary fence.

The selected profile assumes sufficient MTU, whole UDP datagrams, zone zero, fixed NAT, and exclusive stable packet hooks.
Packets do not interleave the commands within a declared route handoff or fence operation.
Faithful capture attribution and correct implementation correspondence remain explicit premises.

The proofs do not establish automatic failure detection, eventual replication, bounded convergence, complete packet draining, split-brain prevention, or concurrent policy installation.
They do not establish complete daemon or kernel implementation refinement.
The earlier [campus model](STATEFUL.md) and the [roadmap](ROADMAP.md) retain those broader architecture obligations.
