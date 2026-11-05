# Received ICMP and host path MTU

This layer connects received ICMP errors, confirmed NAT mappings, forwarding policy, and connected UDP host feedback.
It extends [generated ICMP errors](ICMP.md) with a distinct received-error path.

```sh
lake exe netlib wire-related examples/received-icmp/replay.json --json
lake exe netlib host-pmtu examples/received-icmp/host.json --json
lake exe netlib session-firewall examples/received-icmp/session.json --json
```

Exit zero means agreement, one means observation mismatch, and two means invalid input or unsupported execution.
These commands read evidence without installing configuration or sending packets.

## Existing-flow association

The gateway decodes the outer IPv4 packet and verifies its IPv4 and ICMP checksums.
It extracts the quoted UDP tuple, reverses it, and looks up that tuple with its conntrack zone.
The outer destination must match the destination of the found tuple.
Quoted noninitial fragments and unsupported quoted protocols remain outside the selected UDP association.

A successful association refers to an existing confirmed record.
It creates no candidate, changes no seen-reply bit, and retains the frozen table's timeout fields.
Concurrent expiry, deletion, and timeout evolution remain separate effects.
Unique table keys establish unique association, including flows sharing a public endpoint.

The quoted packet remains untrusted data.
The inspected Linux path accepts incorrect embedded IPv4 checksums, UDP checksums, and declared lengths.
The prefix parser therefore preserves them, together with raw flags and at least eight quoted transport bytes.
IHL five remains the selected header profile.
The [source note](research/RECEIVED_ICMP_PMTU.md) records the relevant Linux and RFC differences.

## Related NAT and forwarding

The gateway performs these stages:

1. Associate the quoted tuple with the confirmed record and direction.
2. Apply related destination translation to the outer destination and quoted source endpoint.
3. Select the destination route and handle outer TTL and DF/MTU rejection.
4. Evaluate the forward policy with related state.
5. Apply related source translation and the late policy.
6. Encode permitted output and fragment it when the selected MTU requires that.

TTL or DF rejection produces no further ICMP error because the input is already an error.
The outer TTL decreases exactly once on forwarding.
The quoted TTL remains unchanged.
For a downstream error, that quotation already contains the earlier UDP hop's TTL decrement.

Related NAT restores the quoted tuple to the corresponding sender's connection boundary.
Incremental updates preserve an invalid checksum's residue rather than repairing it.
UDP checksum zero retains its omission meaning.
IPv4 checksum zero participates in arithmetic and is not an omission marker.
Inactive NAT stages preserve the original quotation bytes.

The received ICMP kind and reported MTU remain unchanged.
Both outer checksums are valid after rewriting.
Certified output families fit the selected MTU and reconstruct the complete rewritten error in any fragment order.
The retained native path uses sufficiently large error-egress MTUs; smaller output MTUs are exercised by the formal model and synthetic tests.

## Host PMTU feedback

The connected host matches the quoted socket tuple and Fragmentation Needed kind.
Its PMTU model uses the configured physical route MTU, minimum PMTU, exception lifetime, and a monotonic clock.
The captured configuration uses minimum 552 and lifetime 600 seconds.

Unlocked state ignores advertised increases and accepts reductions.
Values below the configured floor, including zero, select the smaller of the current MTU and that floor, then lock the exception.
An active lock prevents later updates.
Equal early updates retain their expiry; updates after the half-lifetime threshold can refresh it.
Expired exceptions restore the physical route MTU.
Expiry can therefore increase the effective MTU across observations.

For positive lifetimes, an individual feedback update cannot increase the effective PMTU at that observation time.
Stored estimates always remain within the IPv4 interval and the configured physical route bound.
The route cache model covers one connected socket and one stable route.
Route replacement, exception eviction, allocation failure, and clock wrap remain open.

After pending socket errors are drained, a DF send with IHL five requires application length plus 28 bytes to fit the current PMTU.
The checker separately reports invalid IPv4 lengths and local `EMSGSIZE` capacity failures.
It does not model the complete socket error queue protocol.
The native verifier checks the producer's actual drain and query sequence before attributing those send observations.

Tuple association establishes a relationship with cached state.
Sender identity remains unproved.
The model proves that changing only the reporter cannot change the host feedback decision.
A matching forged quotation can lower an unlocked cached PMTU.
The controlled native forgery demonstrates that limit rather than assuming an authenticated error source.

## Replay inputs and proof chain

Gateway schema one retains `routing`, `mtus`, `configs`, `initial`, and ordered `events`.
Packet events use `type: "udp"` or `type: "icmp"`, with `config`, `zone`, `raw`, `observed`, and optional table observation `state`.
The observed object contains `forwarded` Ethernet-frame arrays and an empty `icmpOutput` array for this received-only experiment.
Administrative erase events reuse the checked UDP key format.

Output families are reassembled before ICMP and quotation comparison.
Comparison retains raw quotation fields, application bytes, UDP checksum, flags, declarations, and embedded IPv4 checksum residue.
Validated outer checksum zero representation, Ethernet adjacency, padding, and fragment capture order remain outside equality.
Mismatches never replace computed state.

Host schema one contains `route`, `policy`, `socket`, and ordered `events`.
Events receive captured errors, query PMTU, or observe drained-error send capacity.
Their `at` values use declared monotonic seconds.
The native projection derives those values from ordered producer timestamps.
Received bytes come from the same forwarded error observations as the gateway replay.

`Protocol.IPv4QuotePrefix` proves exact permissive quotation reconstruction.
`Protocol.ChecksumRewriteRaw` distinguishes header checksum arithmetic from UDP omission.
`Protocol.ICMPPrefixNAT` proves raw field preservation, inverse translation, and checksum-validity equivalence.
`Protocol.RelatedICMP` proves association, policy guards, frozen conntrack state, TTL effects, and certified fragmentation.

`Protocol.PMTU` and `Protocol.PMTUFacts` prove host bounds, update conditions, locks, refresh, expiry, and the forgery limit.
Both checkers reuse `Check.Replay` for ordered agreement and prefix invariants.
`Examples.PMTUDeployment` connects actual forwarded fragments and decoded restored quotations to host PMTU updates while conntrack remains frozen.

## Native evidence and remaining scope

The [capture recipe](../examples/received-icmp/README.md) uses four private namespaces: client, EAP/NAT edge, downstream router, and server.
It preserves the four original EAP application-admission checkpoints.
A separate fixed-policy suffix admits related errors and tests packet mechanics without establishing new current-session authorization.

The gateway replay covers 15 ingress episodes plus one administrative erase across 60 captured frames.
It compares 13 native table observations and computes all 16 state prefixes.
Post-episode snapshots are attached only to the last event they observe.
Earlier request events sharing a later reply snapshot remain explicitly unobserved at that prefix.
Every computed prefix still has a table-validity proof.

Native feedback shows PMTU 4096 becoming 600, local rejection of the next oversized DF send, and a successful 500-byte UDP exchange.
Unmatched quotations, a wrong outer destination, and TTL-one errors produce no client error delivery.
Corrupt quoted checksums are accepted under valid wrappers.
A matching forged-source error reduces the peer PMTU to 576.
Route-cache exports, error-queue origins, readbacks, and nanosecond measurement fences support these observations.
The capture does not wait for the full 600-second exception lifetime.

Full TCP and IPv6 errors, IP options, input-fragment reassembly, broader routing, concurrency, kernel refinement, and physical capture authenticity remain open.
The [roadmap](ROADMAP.md) retains the complete networking objective.
