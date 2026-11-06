# Design basis for bounded campus progress

This note states the architecture target after PR 34.
It uses the source at `1816bb875fae6485966b2419ca6eb3ad922a93bf`.
No build or native experiment forms part of this research.
All seven programs and the full campus objective remain OPEN.

## Implementation status

The sparse gateway ledger is implemented.
Automatic campus packet custody now creates identities from actual output and emission results.
Assignment and delivery consume pending identities; copies and drops are explicit.
General finite and infinite bounded-service theorems are implemented in `Theory.BoundedProgress`.
The [enabled-operation extension](../TCP_ENABLED_OPERATIONS.md) derives positive endpoint and gateway operations from their preceding guards.
It also derives actual cursor chronology, ticket validity, and finite schedule slots from one checked history.
The [first bounded round](../TCP_ROUND_PROGRESS.md) now proves the concrete adapter and all nine phases for one fresh range.
It fixes local clocks and primary ownership and permits no additional copy or drop on the selected suffix.
The [recovery progress extension](../TCP_RECOVERY_PROGRESS.md) adds advancing logical clocks and two combined data-and-ACK drops for the fresh range.
The [held-gap extension](../TCP_GAP_PROGRESS.md) retains both actual two-record campus cuts with advancing clocks and two shared drops per task.
Broader copy, sparse-hole, physical-clock, and transfer results below remain OPEN.
See the [custody and service guide](../PACKET_CUSTODY.md) for the current proof boundary.
The source links below describe the earlier design basis.

## Recommendation

The architecture target is compositional bounded progress.
Sparse gateway observation admission is first for the fault model with loss and reordering before gateway service.
An ordered-ingress progress theorem is a valid separate case, but it does not cover that broader fault model.
This order is a design judgment based on the current admission restriction.
The progress theorem then needs explicit packet custody.
Packet custody means the model retains an actual packet until an explicit operation transfers or discards it.
The next theorem must cover every schedule that meets stated service, loss, clock, policy, and fault conditions.
Its conclusion must derive actual receipts, ACK retirement, and application reads.

Ingress reordering remains useful protocol work.
It does not address schedules that never assign an output, serve a ticket, deliver an emission, or read received bytes.
Likewise, more TCP semantics cannot supply an omitted scheduling condition.
This recommendation changes the next proof boundary.
It does not reduce the full objective.

## Current source boundary

`Network.Available` states graph reachability between declared source and target nodes.
It does not state that a packet receives service.
`Campus.service_survives_one_internal_failure` retains a path after one internal-node failure.
It excludes endpoint failures and independent link failures.
See [Architecture.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Network/Architecture.lean#L118) and [Failure.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Network/Failure.lean#L44).

`Transition.Trace` and `TraceRefinement.safe` transfer invariants through finite executions.
The latter explicitly excludes a progress assumption.
`Outstanding.drain_exists` constructs a finite retirement sequence.
`QueueDrain` proves clearance from sufficient actual FIFO capacity.
Neither result establishes that a native scheduler supplies those operations.
See [Transition.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/Transition.lean#L148), [Outstanding.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Theory/Outstanding.lean), and [QueueDrain.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Theory/QueueDrain.lean).

`TimedReaction.History.closed_response` requires an empty final pending list.
It proves causal output and deadline facts for that closed history.
It does not force an open history to produce a response.
The campus gap assurance has the same limit for empty final receive stores.
See [TimedReaction.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Theory/TimedReaction.lean) and [CampusTCPGapFacts.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPGapFacts.lean#L3).

The campus model retains actual endpoint outputs, immutable assignments, computed services, and exact-byte receipts.
However, `assign` can cite an old output again.
`deliver` can cite an old service again.
These operations represent network copies.
An omitted receipt has no explicit pending or lost status.
See [CampusTCPModel.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPModel.lean#L528).

## Automatic custody

Extend the existing joint state with internally allocated custody identities.
Each successful endpoint output automatically creates one ingress packet item.
This rule includes SYN packets, pure ACKs, data packets, and timer retries.
Each actual gateway emission automatically creates one receiver-link item.
A denied gateway service creates no receiver-link item.

Assignment consumes an actual ingress item and creates the existing immutable ticket.
Service consumes that ticket through the existing checked computation.
Delivery consumes an actual receiver-link item and uses its stored emission bytes.
An explicit link-drop operation consumes a pending custody identity.
It cannot supply replacement bytes or an arbitrary source.

An omitted action leaves its item pending.
The end of a finite input cannot establish loss.
Local endpoint policy denial and current gateway policy denial remain distinct outcomes.
Neither outcome consumes a link-loss allowance.
Authentication denial must continue to exclude output.

Preserve the current copy semantics explicitly.
A copy operation must cite a live or historical actual packet source.
It must allocate a fresh custody identity and retain its parent identity.
A delivery consumes one copy identity, not its historical source.
The progress profile must state a copy bound or prove a stronger condition for arbitrary copies.

The initial bounded profile can set the additional-copy allowance to zero.
That restriction must appear in its theorem and report.
The general custody interface must still represent copies.
Existing source and byte-origin proofs must retain their original strength.

## General progress interface

Use an adapter over the actual checked step relation.
Do not replay an independent endpoint or gateway model.
Read each operation result once and project its obligation changes.
`TimedReaction.Adapter` provides a useful existing pattern.

The adapter needs these components:

| Component | Required meaning |
| --- | --- |
| `execute` | This is the existing checked computation. |
| `pending` | These are actual work identities in the preceding state. |
| `demand` | This selects the next required action from the preceding state. |
| `enabled` | This checks action preconditions without its result. |
| `rank` | This measures remaining work and allowed failures. |
| `preserve` | Every allowed step retains safety and actual source evidence. |
| `advance` | Each scheduled demand executes and decreases the rank. |

`advance` must be a proved module law.
For the campus adapter, prove it by unfolding the existing endpoint and gateway functions.
An assumed successful result is not an action precondition.
A caller-supplied receipt certificate is not a service condition.

One generic theorem can use the following form:

```text
Given:
  An actual initial state s0 satisfies invariant I.
  A task q and rank R are derived from s0.
  Every allowed step preserves I and does not increase R.
  If R is positive, the preceding state exposes a persistent enabled demand.
  Each execution of that demand decreases R, unless q is already complete.
  Each persistent demand receives execution within B schedule slots.
Then:
  Every such schedule completes q within R(s0) * B slots.
```

Persistence can permit replacement by a lower-rank demand.
This permits ACK coalescing, actual link drops, and changes of processing phase.
Loss consumes a finite failure allowance before the phase can restart.
The proof must exclude fresh target work that increases the selected task rank.
Unrelated work can continue under the stated per-task service bound.

Prove sequential composition by adding local slot bounds.
Prove a product result with per-task service bounds for concurrent tasks.
At a domain boundary, a completed upstream operation must create the actual downstream obligation.
Graph reachability alone cannot discharge that condition.

## Concrete TCP theorem

First prove one complete transfer of a nonempty application range through a selected active gateway.
Use one original segment whose length fits the actual effective MSS and current receive window.
Start from the actual checked startup and current endpoint histories.
The selected range must not require unsupported overlap, trimming, persist, or control processing.
For the first lemma, require empty earlier outstanding data and no competing writes in that direction.
Exclude unresolved older packet copies from that selected epoch.
These conditions are checked state conditions, not replacement endpoint seeds.

The theorem must derive all these results:

1. The receiver obtains the actual transformed gateway bytes.
2. Ordered receive release contains the selected application range exactly once.
3. Actual local ACK output covers the resulting receive cursor.
4. An actual reverse gateway path delivers that ACK.
5. The sender retires the selected outstanding range.
6. Bounded application service reads the range.
7. Existing byte-origin and current-policy theorems still apply.

The service assumptions must constrain local actions, not state the whole conclusion.
Each pending ingress item receives assignment within its declared bound.
Each assigned ticket receives service within its declared bound.
Each receiver-link item receives either delivery or an explicit drop within its declared bound.
Each ACK cause receives local output within its actual local deadline.
Each due retry receives local dispatch within its declared bound.
An available ordered application range receives a read within its declared bound.

Require stable current permission and the matching actual gateway installation throughout the selected task.
Require actual interface and namespace lifetimes to remain live.
Require an active route owner and applicable source-to-receiver topology.
Derive the matching packet class, admission range, and emission from the current computed state.
Declare local endpoint permission separately because the endpoint model currently accepts that local decision as input.

Require sufficient offered receive space and physical storage.
For a longer stream, bounded application service must reopen space through actual read and ACK operations.
The current profile has no general zero-window persist mechanism.

### Exact loss and duplicate limits

The present recovery profile permits two timer retries for one outstanding original range.
Therefore, a fresh one-segment task can cover at most two failed rounds before its successful round.
A failed round includes either data loss or loss of its covering ACK.
Separate allowances of two data losses and two ACK losses are insufficient.
They can require four retries.

An explicit combined packet-loss allowance of two is sufficient under timely service and the selected copy restriction.
Each failed round must contain an actual discarded custody identity.
The proof must derive that fact from the custody and response rules.
Missing events do not consume the allowance.
Previously used retries reduce the available allowance.

Pure ACKs have no data-retry timer in this model.
After ACK loss, a repeated data receipt must create a new response cause.
The theorem must derive that cause and its later actual output.

The third consecutive qualifying duplicate ACK reaches unsupported fast-recovery scope.
If the preceding duplicate count is `d`, permit at most `2 - d` further qualifying duplicates before a resetting receipt.
This count must use actual endpoint classification.
An arbitrary network-copy allowance can violate this condition even without packet loss.
See [Recovery.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Recovery.lean#L127) and [Endpoint.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Endpoint.lean#L304).

The broader theorem can replace these selected limits after recovery semantics expand.
The present result must identify its limits explicitly.

### A checkable bound

Use joint operation slots first.
Physical time requires a later clock correspondence theorem.
Let `D` bound a complete data-and-ACK round after actual data output.
Compute `D` by adding assignment, gateway service, link resolution, and ACK dispatch bounds in both directions.
Include the actual delayed-ACK bound when the selected dispatcher waits.
Let `A` bound the final application read.

Let `rho` be the sender's actual RTO before the original output.
Suppose each sender-clock millisecond becomes available within `T` joint slots.
Suppose a due retry receives dispatch within `J` additional slots.
Require a clock upper bound that keeps a lossless round inside the current RTO.
This prevents spurious retries from spending the selected allowance.

For a fresh range and loss allowance `L <= 2`, use this conservative bound after original output:

```text
T * rho * (2^L - 1) + L * J + D + A
```

For two failures, the timer term is `3 * T * rho`.
The theorem must derive the doubled intervals from actual recovery updates.
It must not accept the timer sum as independent input evidence.
For an already outstanding range, calculate the first wait from its stored deadline and current clock.

The two hosts retain separate clocks.
Clock bounds relate each host to schedule slots and do not establish synchronized clock values.
Immediate ACK causes require output before that host's next clock increase.
Delayed causes require output no later than their actual inclusive deadline.
A clock jump beyond that deadline remains unsupported scope.

This bound is a proposed theorem statement.
It is not an existing Netlib result.

The universal campus theorem should have this shape:

```text
For every actual joint run from a checked reachable state:
  stable current permission
  + active checked route and gateway state
  + local action service bounds
  + independent clock bounds and timer slack
  + explicit custody-loss and copy bounds
  + supported TCP state and application service
  => a bounded prefix contains the actual receipt,
     its covering ACK delivery and sender retirement,
     and the actual application read with existing byte origins.
```

The premises contain no final receipt list or successful-output flag.
The computed run supplies the conclusion witnesses.

## Campus landmark and planned transfer

Use the existing receive-gap campus case as the required integration landmark.
It already holds 400 future bytes at the server and 600 at the client.
It later releases 800 and 1200 ordered bytes.
Its actual reads and source samples cross the planned gateway transfer.
See [TCPReceiveGapCampus.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/NetlibTest/TCPReceiveGapCampus.lean#L187).

Replace its hand-selected successful suffix with a family of admissible schedules.
Keep the actual prefix, custody identities, endpoint chains, and gateway histories.
Derive eventual gap closure, actual ACK retirement, and nonempty reads under the declared bounds.
Then retain a separate Logoff suffix that proves later output exclusion.

Prove planned transfer as an additional bounded control task.
Pause assignments, serve actual primary tickets, capture the resulting current cut, install the exact checkpoint, switch both routes, fence, and resume.
Derive each next control action from the preceding state.
A stale checkpoint must require a new capture.
Do not assume that every arbitrary TCP ticket order supports drain.

Add the proved control bound to affected packet service bounds.
Check this larger bound against the outstanding timer slack.
A long pause can consume retry capacity or reach unsupported failure handling.
A generic assertion that transfer eventually completes is insufficient.
See [CampusTCPModel.transferControl](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPModel.lean#L473) and [CampusTCPTransferFacts.lean](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPTransferFacts.lean).

Unexpected gateway failure needs a separate recovery model.
A surviving graph path does not supply its transport state, current policy, route ownership, failure detection, or convergence bound.
The present planned transfer cannot justify arbitrary single-gateway crash continuity.

## Required negative cases

| Case | Required result |
| --- | --- |
| An actual endpoint output has no later assignment. | Custody remains pending and the assignment-service bound fails. |
| An actual gateway emission has no later receipt or drop. | Custody remains pending and the link-resolution bound fails. |
| A drop cites an absent or consumed identity. | The checker rejects the operation. |
| Local output policy denies an ACK or retry. | Credit or timer work remains due without a link-loss charge. |
| Logoff removes current gateway permission. | Output remains denied and the delivery premise no longer applies. |
| Three failed rounds exhaust original output and two retries. | The next retry requires unsupported failure handling. |
| Three qualifying duplicate ACKs arrive consecutively. | The current profile stops for fast recovery. |
| A clock stops forever before a retry deadline. | The clock-progress condition fails. |
| A clock skips an owed ACK deadline. | The existing deadline stop remains visible. |
| A receiver has no usable window and no read service. | The positive-space or application-service condition fails. |
| An old checkpoint follows new primary service. | Installation fails its actual cut comparison. |
| A gateway fails without usable standby state. | Graph availability does not establish packet progress. |

## Primary literature and standards

TCP reliability combines loss detection with retransmission.
TCP does not inherently supply liveness detection.
Excessive retransmission can cause connection closure under the required failure procedure.
These facts support a conditional progress claim rather than unconditional eventual delivery.
See [RFC 9293, sections 2.2 and 3.8.3](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.8.3).

The retransmission timer cannot retransmit earlier than one RTO after the previous transmission.
Timeout processing doubles RTO and starts the next timer with that value.
These rules support the proposed geometric wait bound.
See [RFC 6298, section 5](https://www.rfc-editor.org/rfc/rfc6298.html#section-5).

Delayed ACKs have a 500 ms maximum delay.
Above-gap data and gap filling should receive immediate feedback.
These are local generation rules.
They do not establish that the network delivers a generated ACK.
See [RFC 5681, section 4.2](https://www.rfc-editor.org/rfc/rfc5681.html#section-4.2).

Lamport's alternating-bit example shows that fair sender processes can repeatedly send while the network loses every ACK.
Progress needs conditions on the specific receive actions or the loss process.
Ordinary fairness does not provide the finite service bounds proposed here.
See [The Alternating Bit Protocol, part 2](https://lamport.azurewebsites.net/tla/tutorial/session11-2.html).

Guaranteed network service requires service from every element along the path.
RFC 2212 combines local parameters into an end-to-end delay bound for conforming traffic.
Its stated guarantee assumes no component failure or route change during the flow.
This supports a later service-curve interface, with explicit arrival and fault conditions.
See [RFC 2212, Introduction and End-to-End Behavior](https://www.rfc-editor.org/rfc/rfc2212.html).

## Subsequent work

After this result, extend the progress interface to multiple outstanding segments and broader ingress reordering.
Then add persist, fast recovery, connection failure, close processing, and congestion behavior with their required conditions.
Replace selected service bounds with proved queue and scheduler contracts.
Connect native clocks, physical channels, and deployment operations through explicit correspondence proofs.
Extend domain composition so operators can expose service and fault contracts without disclosing private topology.

The bounded result provides a new guarantee under stated assumptions.
It does not complete protocol conformance, native availability, or the seven research programs.
