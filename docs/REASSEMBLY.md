# IPv4 ingress reassembly and current policy

This layer buffers arriving IPv4 fragments before UDP attachment, NAT, routing, and session policy.
It models the selected Linux conntrack reassembly path.
The [source note](research/IPV4_INPUT_REASSEMBLY.md) records exact Ubuntu source and RFC clauses.

The [MTU layer](MTU.md) handles fragmentation of complete inputs.
The [ICMP layers](RECEIVED_ICMP.md) describe generated errors, received errors, and host PMTU feedback.
Ingress reassembly has its own state and arrival semantics.

```sh
lake exe netlib wire-reassembly examples/reassembly/replay.json --json
lake exe netlib wire-reassembly-timeouts examples/reassembly/timeout.json --json
```

Exit zero means agreement, one means observation mismatch, and two means invalid input or unsupported execution.
The command reads evidence without sending packets or installing configuration.

## Framing and fragment queues

`Protocol.IPv4InputFragment` validates complete IHL-five headers, declared payload availability, and IPv4 checksums.
Its exact reconstruction proof retains checksum representation and trailing padding.
DF, MF, fragment offsets, empty payloads, and unaligned payloads remain available to the queue transition.
Options and the reserved flag remain unsupported framing.

The older generated-fragment codec deliberately enforces stricter flag and alignment conditions.
It therefore cannot classify arbitrary ingress behavior.

Each queue key includes source, destination, protocol, identification, effective defragmentation user, and L3 master identity.
The effective user includes the conntrack zone selected before the defragmentation hook.
An ordinary ingress interface is not the L3 master identity.
Separate model instances represent separate network namespaces.

The arrival transition applies these rules:

1. Remove expired queues under the declared monotonic clock.
2. Pass a whole datagram through without consuming an existing same-key fragment queue.
3. Find or create the fragmented datagram's queue with a fixed expiry.
4. Trim an MF payload down to an eight-byte boundary.
5. Update tentative final-length information and reject inconsistent lengths.
6. Discard empty normalized payloads and destroy their queue.
7. Ignore a duplicate contained within one stored run, including different incoming bytes.
8. Destroy the queue on a genuine overlap.
9. Insert accepted data and update header, ECN, and fragment-size metadata.
10. Complete only after first, last, and complete byte coverage agree.

Linux run grouping depends on insertion history.
Appending at the current tail extends its run.
Filling an internal gap creates a separate run, even when it touches both neighbors.
Consequently, identical byte coverage can classify a later arrival differently.
The model retains this grouping instead of merging every adjacent interval.

Duplicate processing can change tentative final-length state before discarding the incoming fragment.
It does not update accepted payload, ECN, size maxima, or expiry.
It does not emit a datagram at that arrival.

The first fragment's header supplies TTL and DSCP.
Accepted fragments contribute ECN state; unsupported ECN combinations discard the completed queue.
The reconstructed DF flag depends on the largest accepted fragment and the largest accepted DF fragment.
Completion removes its queue.
Later fragments with the same key can create another queue.

The pure reassembly module performs no UDP validation or conntrack lookup.
It can describe queue effects for payloads unsupported by the selected forwarding layer.
An oversized incomplete datagram can remain buffered until completion or expiry.

## Completion selects forwarding policy

`Protocol.ReassemblyForwarding` runs UDP decoding and ordinary attachment only after reassembly emits a whole packet.
Incomplete, duplicate, and discarded fragments leave conntrack unchanged.
The completing event supplies the active NAT and filter configuration.
Earlier fragments do not retain permission from an older session snapshot.

For example, a first fragment can arrive while a credential permits traffic.
If Logoff installs deny before the remaining fragments complete, the complete datagram encounters deny.
Conversely, earlier buffering under deny does not prevent a later permitted completion.
Installation timing and correct association with the current session snapshot remain deployment premises.

The selected UDP forwarding model validates the complete transport length and checksum.
Linux can instead classify malformed UDP as invalid and continue under a permissive filter.
Such completed inputs remain unsupported by this forwarding adapter; the pure queue model still covers their reassembly.

Route selection precedes TTL and DF rejection.
TTL and DF rejection precede forward filtering and ordinary confirmation.
Surviving output preserves the application payload, applies tracked NAT, and decrements the selected TTL once.
The control projection reuses related ICMP generation for supported TTL and DF errors.

## Expiry errors and output policy

Expiry removes queues under the same clock used for arrivals.
A queue without its first fragment cannot supply the selected timeout quotation.
For the selected conntrack input path, a nonlocal original destination suppresses the timeout error.
A service VIP assigned locally can instead permit it before any destination-NAT route exists.

The timeout emitter selects the actual stored offset-zero piece.
Its ICMP type 11/code 1 quotation retains the original header, checksum, MF flag, and declared fragment length.
Only normalized accepted data supplies the quoted payload prefix.
Trimmed bytes cannot reappear in the error.
The return MTU and the 576-byte error bound constrain the result.

The selected nftables zone template survives attachment to the generated error.
Its original zone governs local-output association even if the current prerouting assignment changes.
The profile requires a bidirectional template and excludes later zone overrides.

The timeout adapter requires a reverse-quote lookup miss in that zone.
It evaluates output and late policy with invalid state and leaves conntrack and the emitted header untranslated.
A possible association returns unsupported rather than being classified as a kernel drop.
`Packet.ICMPControl` retains ICMP type/code predicates, packet predicates, state, rule order, and defaults.
Its compiler preserves that structured meaning for every modeled kind, header, and state.
The native adapter selects the named output filter while separate evidence checks the remaining observer hooks.

The combined timeout replay shares every arrival, queue, and conntrack prefix with the forwarding replay.
An explicit allocation input supplies each generated IPv4 identification.
Expiry, error existence, source bytes, routes, policy, and quotation contents are computed independently of that choice.
Observed outer checksums may use equivalent valid zero encodings; the original quoted checksum bytes remain exact.

## Re-fragmentation after NAT

A completed packet retains the maximum accepted fragment size.
Linux can fragment it again even when the reconstructed datagram fits the outgoing route MTU.
The effective output cap is the smaller of the route MTU and that retained maximum.
Whole inputs use the ordinary route MTU.

`Protocol.IPv4Refragmentation` supports size budgets down to 28 bytes.
These small legal fragment sizes are distinct from the configured IPv4 route-MTU minimum.
Its generated copying layout and checked observed layouts share payload, coverage, metadata, and size guarantees.
The checker accepts legal different boundaries and capture orders while rejecting gaps, overlaps, duplicates, and incorrect payloads.

DF behavior depends on Linux's internal fragment-list or copying path.
The contract permits only the DF choices consistent with the completed datagram's retained maxima.
It does not infer kernel buffer ownership or allocation paths from captured packets.
The semantic output contract remains explicit about that supplied implementation correspondence.

## Replay evidence and proof scope

The replay retains the existing routing, MTU, NAT, filter, and ordinary-table inputs.
It adds queue policies, an effective user base, monotonic arrival times, zones, and L3 master identifiers.
Fragment events carry actual `rawIPv4` input bytes.
Observed reassembly bytes and forwarded Ethernet families are separate observations.
Wait events advance queue time; ordinary conntrack erasure does not erase an unrelated fragment queue.
Arrival and timeout values share one clock unit.
The native projection uses monotonic nanoseconds and scales the namespace timeout from seconds.

The checker computes state from arrivals and current configuration.
Observed packets and table snapshots never replace computed conntrack or queue state.
Forwarded observations must satisfy the computed payload, header, DF, layout, and output-cap contract.

The native capture uses early and late Netfilter logging to retain packet bytes before and after reassembly.
Deferred packet-socket reads can observe shared buffers after later kernel processing changes them.
Those reads therefore require explicit provenance rather than an assumed immutable ingress view.
Raw captures remain unchanged; the selected early hook supplies the replay's ingress bytes.

The saved [native example](../examples/reassembly/README.md) contains 82 replay events, 107 Netfilter observations, and 266 packet-socket reads.
It checks 73 table observations, 22 completed packets, and two timeout errors across distinct zones.
Four EAP checkpoints bind current admission policy, including completion after Logoff and completion after permission installation.
The capture recipe, raw artifacts, verifier, and generated projections have recorded hashes.

The selected queue profile assumes successful allocation and no memory-pressure eviction.
It requires `ipfrag_max_dist = 0`; positive source-disorder heuristics have additional shared state.
Expiry uses an abstract monotonic clock.
Native readbacks and timeout counters can support observations but do not prove internal kernel scheduling.

Queue and output proofs establish bounds, normalized-byte provenance, exact emitted coverage, and retained-source relationships.
They do not equate a finite native trace with complete kernel implementation refinement.
Concurrency, options, other forwarding protocols, memory accounting, physical capture authenticity, and broader routing remain open.
The [roadmap](ROADMAP.md) retains the full networking objective.
