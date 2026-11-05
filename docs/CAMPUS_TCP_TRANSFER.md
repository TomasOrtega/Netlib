# Planned transfer of a campus TCP connection

The planned transfer keeps one connection and its actual application history across two modeled gateways.
It copies the confirmed NAT state and the full learned TCP admission state.
Existing endpoint states and sequence cursors continue without another SYN or supplied replacement seed.

```sh
lake exe netlib campus-tcp examples/campus-tcp-transfer/trace.json --json
```

This extends the [authenticated TCP path](CAMPUS_TCP.md).
It is a selected model of planned operation.
Unexpected failure, native Linux TCP state migration, and automatic recovery remain separate work.

## Gateway state and input

The primary keeps the existing schema-one deployment fields.
An optional `standby` object declares its namespace lifetime, routing, configurations, guards, ingress specifications, authentication port, and live interfaces.
The two gateway namespace lifetimes must differ.
Authentication observations, application scope, requirements, endpoint configuration, and global operation order remain shared.

`install`, `stage`, and `installGuard` accept an optional `gateway` selector.
An omitted selector means `primary`.
Each gateway keeps its own installed configuration, ingress guard, staged attachments, tracker, and admission history.
Service evaluates current permission using that gateway's actual state and the consumed authentication prefix.

Assignment still takes an earlier output identity and ingress lifetime.
It derives the gateway from the output producer's current route owner.
The immutable ticket retains that gateway and route epoch.
Service cannot replace this selection with a later route owner.
Receiver delivery still requires exact bytes from an earlier actual emission.

## Control sequence

| Operation | Required model condition and effect |
| --- | --- |
| `pause` | Stop new assignments for this connection. Existing tickets remain pending. |
| `stageCheckpoint` | Store an immutable checkpoint from the primary's actual established transport history. |
| `installCheckpoint` | Require paused assignments, no pending primary ticket, an unchanged source cut, and an empty target pair. Copy that pair and seal the source. |
| `switchRoute` | Move one endpoint's route to the installed standby while assignments remain paused. |
| `fencePrimary` | Require the two routes to select the standby and no pending primary ticket. Prohibit primary processing. |
| `resume` | Require installed standby ownership and a fenced primary. Resume assignments through the existing endpoint histories. |

`installCheckpoint.namespace` identifies the target namespace lifetime.
It must equal the declared standby lifetime and the current standby guard's namespace.
The operation accepts no caller-supplied tracker, TCP lane, endpoint state, or byte path.

Checkpoint staging alone does not establish readiness.
Staging can precede the assignment pause when the source cut stays unchanged.
An earlier cache can become stale while existing primary work is processed.
Installation compares the exact current source pair and transition cut with the cached values.
The input cannot make an old cache current with a validity flag.

After installation, primary sealing prevents further source packet processing.
Assignment remains paused while the two routes change separately.
Fencing does not discard the source history or remove earlier emissions.
Physical fencing and route convergence require separate deployment evidence.

## Exact transport history

`TCP.Checkpoint.History` starts with an empty tracker and empty admission state.
Each transition retains actual lifecycle preparation, TCP admission, forwarding, and admission commitment equations.
The campus adapter constructs these transitions from the same computations used by gateway service.
An early ingress drop preserves the pair and its transport history.

A checkpoint requires the established data phase and an actual selected confirmed TCP record.
It retains the full tracker, `seenReply`, phase, lane positions, ACK counts, peer windows, window coordinates, and packet observation history.
The executable image comparison is proved equivalent to equality of the full pair.
The target inherits the exact source history.

An entry-only copy cannot supply the missing TCP history.
An occupied target cannot receive this first selected installation.
The continuation proofs preserve selected lookup, admission behavior, and exact packet computation under their stated pipeline conditions.
Target policy remains a separate current check.
A source credential does not authorize target service.

`historyTransitions` counts the inherited checked transport transitions.
It includes admitted packets that a later route or filter drops.
It excludes early ingress drops and policy-only changes.
The target count includes the copied source prefix; it is not a native target packet counter.

The extended report exposes the two gateway pairs, exact lane fields, packet observations, cached cut, staging index, installation index, and route owners.
Inputs without `standby` retain their existing report fields and behavior.

`applicationAssurance` and `transferAssurance` have separate results.
Transfer remains `pending` until the actual routes, primary fence, and assignment resume are present.
Installation alone does not produce `checked` transfer assurance.
The completed certificate identifies the actual pause, staging, installation, route, fence, and resume operations.
It also proves final source preservation and the application read prefixes.
Generic assurance permits empty reads; the concrete example proves nonempty reads through each gateway.
`compliant` still concerns the processed finite prefix, which can end before the transfer finishes.

## Continuing application bytes

The example derives startup through the primary and sends nonempty bytes in each direction.
It queues a further server output before the pause.
The primary processes that actual pending ticket during the pause.
This advances its observed history although the NAT tuple remains unchanged.
The example stages a new checkpoint after that advance.

The installed source cut has an unacknowledged server byte epoch.
A deferred client ACK passes through the standby and acknowledges that transferred history.
New data then passes through the standby in each direction.
The server reads `abcdef`; the client reads `xyzw`.
These reads contain bytes from service at each gateway.

The final proof builder still derives startup receipts and application delivery histories from actual global operations.
It identifies each earlier output, immutable assignment, selected gateway service, and receiver input.
The paired theorem states that each read history is a prefix of the peer's write history.

The example later queues standby data, consumes Logoff, and installs current standby denial.
That queued service emits no packet while retaining the copied NAT binding.
Earlier received bytes remain readable.
Stale allow rules retain their actual output and fail current-policy comparison.

## Evidence and limits

The independent [research note](research/CAMPUS_TCP_TRANSFER.md) records the constructed tests and source references.
The oracle compares source cuts, exact state transfer, endpoint cursors, ACK removal, bytes, ticket ancestry, policy decisions, and reads.
No new native capture or traffic experiment supplies this evidence.

An empty pending set is tested against actual stored work.
This does not prove that every TCP queue has a supported drain order.
The example exhibits one successful drain.
General scheduling, loss recovery, retransmission, timers, congestion control, options, close processing, and long sequence reuse remain open.

The model has fixed declared gateway lifetimes.
It does not establish dynamic namespace replacement or native tracker reconstruction.
Native installation, reliable state synchronization, physical delivery, principal ownership, credential integrity, and cryptographic refinement remain external obligations.
The existing UDP replication profile remains restricted to UDP.
All seven research programs and the full campus demonstration remain OPEN.
