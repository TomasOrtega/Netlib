# Interface-bound campus admission

The `attachment-campus` checker extends the [joint campus history](CAMPUS_DEPLOYMENT.md) with current ingress attachments.
It separates historical flow ownership from permission at each packet's processing prefix.
The [native experiment](../examples/attachments/README.md) adds an attacker on distinct gateway input ports.

```sh
lake exe netlib attachment-campus examples/attachments/bundle.json --json
lake exe netlib attachment-campus examples/attachments/bundle.json --budget 1000000 --json
```

## Contract

An attachment records an actual consumed EAP prefix, its authenticated subject, its round, and the declared application scope.
The controller binds that session to a namespace lifetime and input-interface lifetime.
Every accepted application packet requires the current session permission and its exact live attachment.
This check applies to cached connections and both traffic directions.

The installed guard evaluates numeric `meta iif` and the pre-NAT packet header.
The desired policy additionally checks current interface lifetimes and authentication rounds.
The equivalence checker compares both policies for every numeric index and every header.
It uses finite representatives with a completeness proof.

A stale installed allow remains an actual allow during replay.
It can execute ordinary conntrack and NAT before the checker reports the policy mismatch.
Lifetime labels do not silently change the installed rule's behavior.

The guard runs at IPv4 raw prerouting priority `-300`, before ordinary conntrack.
An early drop has no ordinary classification, translated header, forwarding outcome, or output packet.
Dropping queued work retires its actual immutable route ticket while preserving both modeled connection tables.
An allow continues through the current ordinary filter, routing, and NAT pipeline.

Initial flow ownership comes from the current permitted attachment and an actual fresh confirmed record.
Replication selects that owned source record and installs its entry on the standby.
The inherited owner retains the original authentication prefix.
Later replies and Logoff do not rewrite that historical origin.

## Observation format

The bundle retains the earlier authentication, application intent, and handoff inputs.
Additional fields declare gateway namespaces, current interfaces, attachment specifications, and actual guard exports.
The timeline stages attachments, activates observed maintenance bindings, installs guards, and marks the guarded suffix.
It also records probes, authentication events, ordinary network operations, and withdrawal.

An interface reference contains `namespace`, `ifindex`, and `birth`.
Its namespace contains `id` and `birth`.
Birth values identify controller-observed lifetimes; the kernel rule cannot inspect them.
Exported `iif` names resolve against a contemporaneous inventory from the same namespace.
The importer retains the original rules, expression indices, and log statements.
It rejects `iifname` and a late hook or priority.

Packet executions supply observed ingress metadata separately from immutable source bytes.
Queued execution uses the earlier ticket's bytes as input.
Later packet observations can confirm or contradict that source.
They cannot replace it.
Control operations cannot claim a packet ingress decision.

## Native evidence

The saved experiment has 41 native operations and 15 selected datagrams.
Its Lean replay consumes 62 steps, including 21 authentication observations and 23 network operations.
It first demonstrates successful impersonation under the header-only policy.
An explicit kernel-table flush and empty-table observations separate that unsafe prelude from the guarded suffix.
Replication starts with empty caches before the guards activate.

Eight selected datagrams receive early drops.
These include fresh spoofed requests, cached requests, forged replies, and two queued packets after Logoff.
The latter packets encounter an explicit attachment-deny installation while ordinary forward permit remains installed.
The ordinary deny installation follows both measured drops.

The evidence checker joins actual AF_PACKET frames, NFLOG ingress indices, command receipts, socket results, and full Netlink snapshots.
It checks selected tuple, ID, status, and 64-bit accounting stability during each isolated rejection interval.
Timeouts may count down; they must not show an attributable refresh.
Connection IDs can repeat across gateways or after a flush.
Origin follows the observed reset and guarded creation rather than global ID uniqueness.

The two final queued drops share one receive window.
Their order follows actual NFLOG timestamps.
Only their joint after-dump is observed; no intermediate kernel snapshot is invented.
Primary withdrawal disables every nonloopback primary interface and archives the last live primary state.

## Assumptions and remaining work

The EAP-to-data-port association, lifetime observations, installed exports, and packet attribution remain trusted evidence.
Process birth checks assume the collector and workers share the initial time namespace with unchanged zero clock offsets.
The capture does not include a separate time-namespace offset readback.
The formal input does not derive identity from a copied IP address or MAC address.
An attacker sharing the trusted data port remains indistinguishable when its packet bytes match.
Cryptographic packet provenance requires separate lower-layer protection.

Replication maintenance exceptions are checked separately and must be disjoint from protected application classes.
The selected profile covers whole IPv4 UDP datagrams on isolated routed Ethernet links.
Defragmentation can precede this guard, so fragment-state isolation remains open.
Bridges, tunnels, offload bypasses, concurrent writers, physical service bounds, and complete implementation refinement need separate arguments.

All seven [research programs](ROADMAP.md) and the complete campus landmark remain OPEN.
The [source investigation](research/INGRESS_ATTACHMENTS.md) records the kernel, nftables, and EAP evidence behind this contract.
