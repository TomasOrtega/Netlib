# One checked campus deployment history

This layer connects authentication, installed policies, packet processing, and planned gateway withdrawal through one ordered replay.
The [native example](../examples/campus/README.md) supplies one coordinated wired EAP-TLS and IPv4 UDP execution.
The [source note](research/CAMPUS_DEPLOYMENT.md) records its implementation evidence and limits.

```sh
lake exe netlib campus-deployment examples/campus/bundle.json --json
lake exe netlib campus-deployment examples/campus/bundle.json --budget 100000 --json
```

Exit zero means agreement, one means a comparison or coverage failure, and two means malformed input or an unsupported operation.
The budget limits each compilation and policy comparison; it is not a total execution-time bound.
The checker reads supplied observations without changing network state.

## Shared inputs and actual prefixes

The schema contains `application`, `authentication`, `intent`, `handoff`, and `timeline`, together with `schema: 1`.
Authentication uses the existing [EAP format](EAP.md).
Packet intent uses the [session compiler format](SESSION_FIREWALL.md).
The handoff input uses the [outstanding-ticket format](SAFE_HANDOFF.md).
Every intent must name the declared application scope.

Timeline entries consume observations from those two source streams:

```json
{"type": "authentication", "event": 0}
{"type": "network", "event": 0}
{"type": "withdraw"}
```

Each numbered reference must consume its stream's next index exactly once.
A complete report consumes both entire streams and performs the guarded primary withdrawal.
Skipping or duplicating an index is unsupported.
Omitting a final observation cannot produce a compliant complete report.

Authentication state comes from the actually consumed EAP prefix.
Packets cannot select a future successful authentication or an unrelated session snapshot.
Prefix theorems count the actual earlier authentication and network findings in the same report.
The packet operation epoch counts network operations, excluding authentication and withdrawal; it is not a kernel route-version field.

## Installed policy persists

Both tables, the replication cache, and outstanding work start empty.
The initial primary and standby configurations are checked against the initial unauthenticated state.
A later authentication event changes session state without changing either installed configuration.
An explicit network installation replaces one gateway's configuration.

`Check.SessionInstallation` selects the native configuration source by its actual stored identity.
It checks that the source's compiled forward rules and fallback equal the stored pipeline.
Bidirectional refinement then compares that source against the certificate for the current consumed authentication prefix.
The comparison covers every modeled conntrack state and header at the same hook and priority.

Every installation and packet-processing operation performs this current-prefix comparison.
Processing uses the assigned gateway's stored configuration, including packets assigned before a route change.
It never restores an earlier permission from the ticket.

A stale allow policy remains the actual computed policy after Logoff until replacement.
Even matching forwarded bytes and table effects cannot make that stale policy agree with the current certificate.
The report records a policy mismatch while preserving the actual computation.
This removes the earlier caller-supplied `ForwardEquivalent` premise from the compliant deployment result.
It does not prove that a native installation command implements its exported policy.

## Packet classes, routes, and topology

Every processed packet must match a declared application class after destination NAT, including policy-denied packets.
Its imported gateway route must select the declared `server` or `client` role for the original or reply direction.
These checks are separate from agreement with packet bytes and table snapshots.
Removing the reply requirement and its native permit cannot silently turn an unsupported reply into a successful application check.
Changing a route binding to a management role likewise fails the topology check.

`Examples.CampusDuplex` supplies request and reply paths, gateway mediation, and management isolation under its declared fault model.
`Examples.CampusDirect` interprets direct client-to-gateway links without claiming physical access points.
Its stuttering refinement explicitly collapses the abstract access-point roles onto the client role.
The direct model has client, primary, standby, server, and isolated management roles.
The experiment instantiates four data namespaces and a separate wired authenticator; it supplies no native management host or Wi-Fi deployment.

For a covered header, a checked current forward permit is equivalent to duplex reachability in the session-guarded direct model.
Actual packet emission additionally requires the ordinary routing, TTL, and late-filter conditions.
Graph reachability alone does not establish socket delivery, a physical time bound, or implementation refinement.
Principal-to-header ownership and interface-to-role interpretation remain reviewed deployment assumptions.

## Planned withdrawal and archived state

`Protocol.CampusWithdrawal` wraps the protected-flow handoff model without weakening its invariant.
Withdrawal requires a staged binding, both endpoint owners on the standby, no outstanding primary ticket, and a fenced primary.
Natural-before completeness constructs the actual withdrawal step from these guards.
The wrapper then archives the primary's last modeled table.

After withdrawal, the permitted operations are assignment, service of actual standby tickets, standby installation, and cache forgetting.
Primary operations and new live primary table observations are unsupported.
Even a new primary observation equal to the archive is rejected.
The retained primary table is historical execution state, rather than a claim about the later live kernel.
Every retained pending ticket remains assigned to the standby.
When current session permission holds, its path exists in both the direct and abstract interpretations.

This is prepared withdrawal after drain.
Unexpected crashes with primary tickets outstanding, automatic detection, convergence, and recovery require additional models.
The [handoff drain theorem](SAFE_HANDOFF.md#drain-and-fence) still counts modeled operations rather than physical time.

## Output and permission proofs

`Check.CampusDeploymentFacts` connects a compliant replay to its actual earlier prefixes.
Every served ticket has a strictly earlier assignment in that same joint history.
That assignment fixes its complete source bytes, identity, assigned gateway, direction, and operation epoch.
Later observations cannot replace the ticket or computed state.

The observed-output theorem establishes the exact protected NAT output header, preserved UDP payload, valid emitted checksums, and one TTL decrement.
It also establishes current application credential validity and EAP method readiness at the actual consumed prefix.
The current direct campus interpretation has request and reply paths under those same permissions.
A denied current application scope excludes selected modeled UDP output, including queued traffic and cached bindings.

The permission theorem describes the imported forwarding semantics and supplied method evidence.
Credential signatures, TLS cryptography, header ownership, faithful installation, and authentic observation are outside these proofs.
The [proof inventory](PROOFS.md) and [specification](SPECIFICATION.md) preserve those distinctions.

## Joint native evidence

The saved run contains 26 native operations, eight datagrams, and seven protected ticket identities.
Its projection has 45 timeline operations: 21 authentication observations, 23 network operations, and one withdrawal.
The verifier checks 18 EAPOL frames, 88 live kernel dumps, 28 selected data-frame observations, 30 NFLOG observations, and 26 synchronization frames.

One actual wired EAP-TLS episode and a local demo credential precede the two permit installations.
The same UDP client establishes the primary NAT binding and participates in the route handoff.
Standby traffic overtakes an older primary-bound packet.
That older packet completes before the primary fence and physical withdrawal.
The standby then delivers another request and reply.
A later queued standby packet crosses actual Logoff and deny installation before its selected drop; a reply is denied too.

Actual withdrawal readbacks show the primary's data and synchronization links down, forwarding disabled, and its conntrack daemon absent.
Later boundaries reference its archived prefix and contain no new primary commands.
The independent verifier joins EAP producers, packet observers, commands, policy exports, sockets, and prefixes within that same execution.
Separately successful authentication and handoff captures cannot substitute for this joint history.

The finite capture advances the campus demonstration while leaving the full [research objective](ROADMAP.md) open.
Wireless enforcement, cryptographic refinement, arbitrary failures, aging, distributed synchronization guarantees, quantitative timing, and complete physical correspondence still need work.
