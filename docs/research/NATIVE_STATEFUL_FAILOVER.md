# Native conntrack replication and fenced handoff

This note covers one selected IPv4 UDP flow, fixed NAT, and conntrack zone zero.
The chosen path uses conntrackd FTFW with an external cache and an explicit kernel commit.
The handoff fences router A before router B forwards the selected traffic.
It does not establish automatic failover, split-brain prevention, expiry behavior, or general kernel refinement.

## Pinned sources

The source reads use conntrack-tools `1.4.9` and libnetfilter_conntrack `1.1.1`.
The official tags resolve to the following commits.
The release archives were downloaded from Netfilter and checked against their published SHA-256 values.
[Daemon release files](https://www.netfilter.org/pub/conntrack-tools/).
[Library releases](https://www.netfilter.org/projects/libnetfilter_conntrack/downloads.html).

| Component | Source revision | Archive SHA-256 |
| --- | --- | --- |
| conntrack-tools `1.4.9` | `4e57d5b33510b6c86f6df6ecaeb31a74907bd11f` | `c15afe488a8d408c9d6d61e97dbd19f3c591942f62c13df6453a961ca4231cae` |
| libnetfilter_conntrack `1.1.1` | `cf50fa4dd12f8b7e3567ec944ab61a51f9408311` | `769d3eaf57fa4fbdb05dd12873b6cb9a5be7844d8937e222b647381d44284820` |

Kernel reads use official Ubuntu source tagged `Ubuntu-6.8.0-117.117`.
The native environment reports `6.8.0-117-generic`.
Matching release names do not establish source-to-binary equivalence.
[Ubuntu source](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_netlink.c?h=Ubuntu-6.8.0-117.117).

## Cached replicas and kernel records

The manual distinguishes the internal cache, which represents local kernel flows, from the external cache, which represents another router's flows.
Its replication protocols are asynchronous.
The selected configuration keeps the external cache enabled with `DisableExternalCache Off`.
Disabling that cache selects direct kernel injection and changes this evidence boundary.
[Official manual](https://conntrack-tools.netfilter.org/manual.html).
[Pinned FTFW configuration](https://git.netfilter.org/conntrack-tools/tree/doc/sync/ftfw/conntrackd.conf?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n52).

Received NEW messages allocate an external cache object.
An existing matching object is deleted and replaced.
Received UPDATE messages update an existing object or allocate a missing object.
Received DELETE messages remove a matching object.
Allocation or cache insertion can fail without creating a replica.
These functions do not install kernel conntrack state.
[External handlers](https://git.netfilter.org/conntrack-tools/tree/src/external_cache.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n57).
[Cache insertion and update](https://git.netfilter.org/conntrack-tools/tree/src/cache.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n126).

FTFW tracks sequence numbers, sends ACKs and NACKs, and retains a bounded resend queue.
Its receive function runs before payload parsing and external cache insertion.
Therefore, a transport ACK does not certify successful cache insertion or kernel installation.
The HELLO path clears resend state, and a full resend queue discards its oldest queued object.
These paths prevent treating FTFW as an unconditional delivery theorem.
[FTFW receive and queue handling](https://git.netfilter.org/conntrack-tools/tree/src/sync-ftfw.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n342).
[Receive dispatch](https://git.netfilter.org/conntrack-tools/tree/src/sync-mode.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n80).

## Fields crossing the daemon channel

For IPv4 UDP, `ct2msg` sends the original addresses, original ports, protocol, and 32-bit status.
NAT attributes carry translated addresses and ports derived from the source record's reply tuple.
The receiver parses these as separate NAT attributes.
The protocol does not send a general reply tuple, kernel connection ID, packet counters, or byte counters.
[Message builder](https://git.netfilter.org/conntrack-tools/tree/src/build.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n244).
[Message parser](https://git.netfilter.org/conntrack-tools/tree/src/parse.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n50).

| Source meaning | Daemon attribute |
| --- | --- |
| Original IPv4 address pair | `NTA_IPV4` |
| Original UDP port pair | `NTA_PORT` |
| Conntrack status | `NTA_STATUS` |
| Reply destination after source NAT | `NTA_SNAT_IPV4` |
| Reply source after destination NAT | `NTA_DNAT_IPV4` |
| Reply destination port after source port translation | `NTA_SPAT_PORT` |
| Reply source port after destination port translation | `NTA_DPAT_PORT` |
| Global zone, when present | `NTA_ZONE` |

Original port groups copy the library's network-order bytes directly.
Translated port attributes instead apply `htons` to numeric getters of library ports that already use network order.
Their interpretation therefore requires the sender's byte order.
The wire decoder must check that retained producer property instead of treating all 16-bit fields alike.
[Attribute encoders](https://git.netfilter.org/conntrack-tools/tree/src/build.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n52).
[Port-group encoder](https://git.netfilter.org/conntrack-tools/tree/src/build.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n89).

The builder sends `ATTR_ZONE` only when that attribute exists.
It does not transmit the separate original-direction and reply-direction zone attributes.
The selected profile therefore requires zone zero in both directions.
The kernel parses an omitted global zone as its default zone.
[Zone builder](https://git.netfilter.org/conntrack-tools/tree/src/build.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n329).
[Kernel zone parser](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_netlink.c?h=Ubuntu-6.8.0-117.117#n1390).

## Explicit commit and failure behavior

The external commit iterates cached records and calls `nl_create_conntrack` for each record.
That function clones the replica, clears `IPS_EXPECTED`, prepares an inverse reply tuple, and requests `NFCT_Q_CREATE`.
The library builds CREATE with `NLM_F_CREATE`, `NLM_F_ACK`, and `NLM_F_EXCL`.
NAT attributes accompany the reconstructed tuple for kernel NAT setup.
[Daemon create](https://git.netfilter.org/conntrack-tools/tree/src/netlink.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n233).
[Reply reconstruction](https://git.netfilter.org/libnetfilter_conntrack/tree/src/conntrack/objopt.c?id=cf50fa4dd12f8b7e3567ec944ab61a51f9408311#n10).
[Library query flags](https://git.netfilter.org/libnetfilter_conntrack/tree/src/conntrack/api.c?id=cf50fa4dd12f8b7e3567ec944ab61a51f9408311#n805).
[Netlink attribute builder](https://git.netfilter.org/libnetfilter_conntrack/tree/src/conntrack/build_mnl.c?id=cf50fa4dd12f8b7e3567ec944ab61a51f9408311#n528).

On `EEXIST`, commit destroys the matching kernel entry and retries CREATE once.
A successful deletion or `ENOENT` permits that retry.
Other failures increment a failure counter and leave iteration running.
This is potentially destructive replacement, without transaction-wide rollback.
The selected profile excludes collisions by requiring an empty destination table before installation.
[Commit implementation](https://git.netfilter.org/conntrack-tools/tree/src/cache-ct.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n173).

Commit completion logs successful and failed entry counts, resets its state, and returns completion even after entry failures.
A concurrent commit request can also be skipped while returning local success.
The client exits successfully when its local socket request succeeds.
Thus, command exit status alone does not establish the selected record's presence.
[Commit completion](https://git.netfilter.org/conntrack-tools/tree/src/cache-ct.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n294).
[Local commit handler](https://git.netfilter.org/conntrack-tools/tree/src/sync-mode.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n551).
[Client exit behavior](https://git.netfilter.org/conntrack-tools/tree/src/main.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n335).

A positive `CommitTimeout N` supplies `N` seconds as the initial installed timeout.
The daemon then omits source timeouts from synchronization messages.
Without this option, commit estimates the remaining timeout using cache update time and can substitute 60 seconds.
Therefore, the install model needs an explicit timeout parameter instead of claiming exact timer preservation.
[Timeout calculation](https://git.netfilter.org/conntrack-tools/tree/src/cache-ct.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n179).
[Conditional timeout transmission](https://git.netfilter.org/conntrack-tools/tree/src/build.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n262).

## Kernel installation semantics

Kernel creation allocates a connection, requires a timeout, sets up NAT, marks the connection confirmed, and applies permitted status changes.
It then checks and inserts both tuple directions into the hash table.
Failures free the new object.
Tuple collisions, memory pressure, unsupported NAT, and extension changes can prevent insertion.
[Kernel create path](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_netlink.c?h=Ubuntu-6.8.0-117.117#n2236).
[Insertion checks](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n866).

`SEEN_REPLY` and `ASSURED` can be set through the status update.
They cannot be cleared through this path.
NAT and NAT-DONE bits are masked from direct status modification.
NAT setup derives those bits and the effective reply tuple.
Consequently, retaining `SEEN_REPLY` is supported; copying every source status bit is not the installation contract.
[Status rules](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n2827).
[Immutable status mask](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/netfilter/nf_conntrack_common.h?h=Ubuntu-6.8.0-117.117#n121).
[NAT tuple and bit changes](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_nat_core.c?h=Ubuntu-6.8.0-117.117#n777).

## Required observations and finite premises

External cache XML prints selected status labels, rather than the complete status word or separate NAT attributes.
The daemon also removes the timeout attribute while dumping cached entries.
Cache XML alone cannot establish exact transferred NAT state or remaining lifetime.
[Cache dump](https://git.netfilter.org/conntrack-tools/tree/src/cache-ct.c?id=4e57d5b33510b6c86f6df6ecaeb31a74907bd11f#n116).
[XML formatter](https://git.netfilter.org/libnetfilter_conntrack/tree/src/conntrack/snprintf_xml.c?id=cf50fa4dd12f8b7e3567ec944ab61a51f9408311#n395).

The finite evidence must join these observations:

1. A raw kernel dump selects the actual source record by its original and reply tuples.
2. Retained configuration selects FTFW, an enabled external cache, and a positive commit timeout.
3. Sync payload bytes expose the selected record's original tuple, status, and NAT attributes.
4. B's cache dump establishes a selected cached object before commit.
5. B's raw kernel dump is empty before commit.
6. A post-commit raw kernel dump establishes B's selected tuples, zone, NAT flags, `SEEN_REPLY`, and positive timeout.
7. Interface, route, and policy readbacks establish the selected fence and traffic path.
8. Raw traffic and socket observations establish the selected request and reply after handoff.

The model's staged record must come from the selected source table entry.
Successful installation requires an observed destination record with the supported projection and an explicit installed timeout.
The cached replica and installed record remain different states, even when their supported fields agree.
The model must not install a hand-authored replacement that merely fits later traffic.

The supported interpretation assumes whole UDP datagrams, zone zero, fixed NAT, stable policies, sufficient MTU, and faithful capture attribution.
It assumes no expiry, helper, expectation, offload, concurrent table writer, or tuple collision during the selected transition.
The fence premise excludes A forwarding selected traffic after B becomes active.
Authentication and authorization remain separate policy state; replicated conntrack state does not transfer either authority.
These finite premises do not prove reliable replication, crash recovery, complete packet draining, or automatic router election.

## Retained native observations

The retained run contains thirteen ordered events and six UDP inputs.
It retains 56 kernel table dumps, 20 selected data-frame observations, 16 NFLOG checkpoints, and 12 synchronization-frame observations.
Other Ethernet observations retain ARP traffic.
The checker consumes every selected data frame, NFLOG checkpoint, and packet trace.
[Native event manifest](../../examples/replication/native/capture.json).
[Offline checker](../../scripts/check_replication_capture.py).

The first request creates A's actual record with status `440` and the selected original and reply tuples.
An incoming FTFW NEW message transfers its status and separate NAT attributes to B.
B's external cache then exposes the original tuple while its confirmed kernel table remains empty.
These observations distinguish a cached replica from an installed connection.
[A's source table](../../examples/replication/native/establish-after-a-conntrack.json).
[Incoming synchronization frames](../../examples/replication/native/b-frames.jsonl).
[B's external cache](../../examples/replication/native/stage-b-cache-0.xml).
[B before commit](../../examples/replication/native/commit-before-b-conntrack.json).

Separate endpoint route changes select B for requests and replies.
The next operation disables both A data interfaces while leaving its synchronization interface active.
A reply before commit has no selected UDP egress and leaves B's confirmed table empty.
The retained blackhole route covers the public source-NAT address before reverse translation.
[Route and fence operations](../../examples/replication/native/commands.json).
[Fenced primary interfaces](../../examples/replication/native/fence-primary-after-a-links.json).
[Uncommitted reply trace](../../examples/replication/native/b-trace.txt).
[Standby routes](../../examples/replication/native/uncommitted-before-b-routes.json).

After explicit commit, B's raw kernel dump contains the selected tuple pair, zone zero, NAT flags, and status `440`.
Its observed remaining timeout is `179` seconds under configured `CommitTimeout 180`.
The checker requires positive lifetimes within the applicable configured bounds, without requiring identical aging across readbacks.
[Committed kernel record](../../examples/replication/native/commit-after-b-conntrack.json).
[Standby daemon configuration](../../examples/replication/native/b.conf).

A later reply encounters the current deny policy and records `SEEN_REPLY`, changing B's status to `442` without delivery.
After the established-policy installation, the next reply reaches the client with the restored service tuple.
Further request and reply inputs reuse B's binding.
Their socket results, raw frame bytes, and policy exports remain separate observations.
[Denied reply state](../../examples/replication/native/denied-after-b-conntrack.json).
[Permitted reply state](../../examples/replication/native/permitted-after-b-conntrack.json).
[Endpoint results and event references](../../examples/replication/native/capture.json).

The native UPDATE also carries a SYNPROXY attribute containing three zero words.
The decoder retains those values and rejects nonzero values under this UDP profile.
This observation does not extend the model to SYNPROXY behavior.
[Raw synchronization frames](../../examples/replication/native/b-frames.jsonl).
[Attribute decoder and regressions](../../scripts/test_check_replication_capture.py).

Primary interface shutdown produces two retained packet-socket `ENETDOWN` observations during the corresponding link-down command intervals.
The checker accepts only those selected interface errors and requires the other packet and NFLOG observers to finish successfully.
Trace observers retain their intentional termination signals.
These collector checks support the finite observation scope; they do not establish capture authenticity or universal absence of unseen packets.
[Primary packet-socket observations](../../examples/replication/native/a-frames.jsonl).
[Observer lifetimes](../../examples/replication/native/capture.json).
