# Session attachments before conntrack

This experiment adds interface-bound ingress guards to the [coordinated campus capture](../campus/README.md).
It preserves the earlier producers and observations.
The runtime builds offline from the pinned campus image.

## Unsafe witness and guarded suffix

One actual EAP-TLS episode authenticates the client and precedes the local demo credential and ordinary permit policies.
An attacker namespace has separate physical ingress links to both gateways.
Its raw frames spoof the authorized IP addresses, UDP ports, and legitimate Ethernet source addresses.

The first attack runs with the ingress guard disabled.
The header-only ordinary policy forwards it to the server and creates a confirmed NAT record.
This is an explicit unsafe witness, outside the later guarded safety claim.

The controller flushes both kernel tables and retains actual empty Netlink dumps.
It then starts replication, installs current interface guards, and records a protected-phase marker with fresh table and cache readbacks.
The marker does not itself change hardware enforcement.

Fresh attacks through either unregistered ingress leave the kernel tables empty.
A legitimate primary packet then establishes the protected record.
Cached original-direction attacks and forged replies are rejected before ordinary processing at both gateways.
The selected before/after dumps preserve tuple, identity, status, and original/reply packet and byte counters.
Forged replies cannot set seen-reply or ASSURED in these intervals.
Timeouts retain their native countdown values; raw dumps are never normalized.

An old legitimate primary assignment spans both route changes while newer standby traffic overtakes it.
After draining and fencing, withdrawal disables all four primary data/synchronization interfaces, forwarding, and its replication daemon.
The standby continues legitimate request and reply service.

Both a legitimate request and reply then wait in separate endpoint qdiscs through actual EAPOL Logoff.
An explicit guard replacement removes application attachments before the packets arrive.
Both encounter the current guard and leave conntrack unchanged while the ordinary forward policy still permits the application.
Only afterward does the controller install ordinary deny.
Concurrent socket waits observe the two outcomes in one native interval.
The replay must not invent an intermediate kernel dump or a physical FIFO guarantee.

## Interface and maintenance evidence

The guard uses `meta iif` at IPv4 prerouting priority `-300`.
Its exact application matches use pre-NAT request and wire-reply tuples.
The kernel exports numeric `iif` matches as interface-name strings, including with `-nn`.
The source key remains `iif`.
Current namespace and link readbacks resolve those strings to their actual interface indices.
Namespace creation, interface creation, movement, activation, observer identity, and retirement receipts retain the selected lifetimes.

The dedicated synchronization permit uses the actual peer address, outgoing source port, destination port `3780`, and synchronization ingress index.
Conntrackd sends from an ephemeral source port.
The controller learns it from the actual daemon process, file descriptor, socket inode, and UDP socket readback.
An explicit control-only resynchronization starts that sending socket before the guarded suffix.
Maintenance permits carry no application ownership claim.

Gateway NFLOG retains separate `ATTACH_ALLOW` and `ATTACH_DROP` observations with raw pre-NAT bytes, hardware addresses, and incoming interface indices.
An early rejection has ingress and guard-drop evidence without a later ordinary tracked hook.
Packet sockets independently retain the spoofed Ethernet frames.
Conntrack accounting is enabled before the first packet; complete raw Netlink attributes retain the measured counters.

## Reproduce

Build the pinned [campus parent](../campus/README.md), configure Docker, then run:

```sh
examples/attachments/recapture.sh /tmp/netlib-attachments-recapture
```

The recipe runs without external networking or host mounts and preserves partial output if a run fails.
The inherited runtime directory remains `/tmp/netlib-safe-handoff`.
Fresh runs change certificates, process identities, socket ports, packet identifiers, timing, and hashes.

This is wired evidence for a packet adversary controlling headers and source MAC addresses on separate ingress links.
Kernel metadata, controller authority, physical attachment attribution, authentic collection, cryptography, and implementation correspondence retain explicit assumptions.
It does not establish wireless key installation or automatic hardware revocation when authentication changes.
Interface reuse, unexpected crashes, expiry, timing guarantees, and complete campus correspondence require further work.
