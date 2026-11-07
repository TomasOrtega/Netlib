# Bounded TCP progress through gateway transfer

Netlib proves a sequential exchange through one planned transfer from the primary gateway to the standby.
One actual report contains both reads, the reverse write, and all seven transfer controls.
The theorem covers every supplied trace that meets its action and persistent-service contract.
All seven programs and the full campus objective remain OPEN.

## Initial state

The task starts after the selected accepted forward write and before either original send.
`TwoWriteInitial` retains that actual writer, startup, endpoint histories, and gateway observations.
It requires two nonempty forward ranges, current endpoint guards, and sufficient MSS, window, storage, and sequence space.
The selected gateway lane has a complete earlier prefix; its history need not be empty.

The public theorem also requires these initial conditions:

- Both endpoint routes select the primary, with assignments enabled and the primary neither sealed nor fenced.
- No primary ticket is pending at the initial cut.
- The standby transport pair is empty, and its current guard namespace matches its declared deployment.
- Both gateways have the stated configuration and current native preflight, route, filter, namespace, and ingress checks.
- Both reverse ranges are nonempty and fit the initial endpoint and gateway reserves.

The reverse reserves cover pending capacity, effective MSS, send window, offered receive space, and the bounded sequence epoch.
The initial forward sender has no unread bytes.
Native comparisons use the stated budget `100000`.
The action profile retains configuration, policy, authentication, attachments, and declared gateway lifetimes.

## Transfer and recovery profile

The first forward original path that delivers or drops triggers the transfer before its ACK work.
A lower ingress drop can trigger transfer before the upper send.
The selector retains its current paths, source records, and loss credits.

The actual controls occur in this order:

```text
pause → capture → install → client route → server route → fence → resume
```

During the pause, actual pending primary tickets have service before capture and installation.
The supported profile derives at most one such ticket; it does not require an empty queue at the trigger.
Installation copies the actual current transport history and checks the target namespace.
Target policy and native permission remain separate from that copy.
The endpoints continue with their actual clocks, recovery metadata, receipt identities, and application histories.

Both original delivery orders remain possible under the path and ACK discipline.
ACK work has priority over the next ordinary data action.
One allowance `D ≤ 2` covers selected ingress and link drops of original data, retries, and ACKs in both directions.
The reverse allowance is `D - actualForwardDrops`.
Each timeout consumes a distinct earlier supported loss cause for its current head.
A dropped zero ACK uses loss allowance but supplies no timeout credit.
The suffix permits no new copies or competing application writes.
Earlier custody, copies, and unrelated work can remain in the initial history.

## One trace and one bound

Let `q > 0` bound guarded logical clock increases.
Let `B` bound service of each persistent current demand in evaluated joint slots.
One whole action check and one service check cover forward progress, transfer, the reverse write, and reverse progress.
Local service facts come from restrictions of those same stored steps.

[`CampusTCPTwoTransferExchangeBound.wholeSlots`](../Netlib/Check/CampusTCPTwoTransferExchangeBound.lean) computes the sufficient bound:

```text
N = forwardSlots(D) + B + reverseSlots(D)
```

The forward term includes transfer and derives its RTO cap for an outstanding head after at most `24 * B` slots.
The reverse term uses the initial forward receiver's RTO and estimator, with an original-stage bound of `16 * B`.
The actual reverse task uses the remaining allowance and has no larger bound.
No cap on the final retired estimator or RTO is required.

The supplied actual trace must contain at least `N` evaluated slots.
[`CampusTCPTwoTransferExchangeResult.complete_by`](../Netlib/Check/CampusTCPTwoTransferExchangeResult.lean) returns an actual prefix at `result.slot ≤ N`.
Its report is exactly the initial history followed by `steps.take result.slot`.
This result uses the same trace without another endpoint or gateway run.
Each endpoint clock is at most its initial value plus `N * q`.

## Retained results

The result identifies strictly ordered actual forward-read, reverse-write, and reverse-read slots before `N`.
Both reads return their exact selected byte lists.
The total count of timeout outputs by either actor is at most the actual selected drop count, which is at most `D`.
Those dropped custody identities are distinct.
All seven controls have actual, strictly ordered slots in the same report.
Final routing selects the installed standby.

Both endpoints have empty pending, sent, unread, held, and recovery data stores, with cleared timeout metadata.
Window ACK work created by a read can remain pending.
The result does not require every unrelated custody identity to be absent.

The [result facts](../Netlib/Check/CampusTCPTwoTransferExchangeFacts.lean) connect every read byte to its selected actual writer, output, receipt, and gateway service.
The forward writer is the selected earlier write.
The reverse writer is the operation in the same recorded reverse-write step.
Service permissions need only compliance of the initial report; the proof extends it through the same actual suffix.
Equal byte values alone do not identify a writer.

## Scope

The [fixed-owner exchange](TCP_TWO_WAY_PROGRESS.md) has a separate action profile.
The [planned transfer guide](CAMPUS_TCP_TRANSFER.md) describes the control model and native obligations.
Sparse holes, more ranges, new copies, concurrent applications, other transfer profiles, persist, and fast recovery remain open.
Logical clocks and supplied native observations do not establish physical timing, native delivery, kernel refinement, or full standards compliance.
