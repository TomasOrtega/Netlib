# TCP startup recovery through gateway transfer

Netlib proves a bounded path from cold TCP startup through both application reads and one planned gateway transfer.
The path uses one actual campus report, one action check, one service check, and one physical loss allowance.
The [RFC research note](research/TCP_STARTUP_RECOVERY.md) states the selected protocol rules and exclusions.

## Actual startup and handoff

The recovery model has separate active and passive timers.
It permits lost SYNs, lost SYN,ACKs, lost final ACKs, delayed originals, and the selected exact duplicates.
Both timers can expire after one SYN,ACK loss.
The final ACK has no independent retry timer.

Each emitted occurrence has its actual event stamp and source history.
Output, assignment, service, receipt, and custody identities remain separate.
Gateway rewriting and endpoint delivery use the actual checked bytes.
The mixed admission history preserves learned MSS offers through duplicate controls and ordinary ACK window updates.

Timers retain monotonic millisecond clocks, deadline generations, exponential backoff, and Karn sampling restrictions.
The data handoff preserves the actual clock, RTO, and estimator.
It applies the selected 3000 ms floor after an early SYN timeout and preserves a larger RTO.
An obsolete expiry cannot retransmit a canceled timer.

The actual `finishStartup` step requires completed startup and resolved startup work and packet queues.
It stores the recovery archive and the current endpoint cursors.
Both local histories and actual `sendWL1` and `sendWL2` values remain unchanged.
Five subsequent steps enable recovery and ACK handling, then perform the selected forward write.
No established seed, fresh timer, or replacement history is supplied at this boundary.

## Theorem assumptions

[`CampusTCPStartupTransferBound.complete`](../Netlib/Check/CampusTCPStartupTransferBound.lean) requires these facts:

- The raw preparation plan contains the selected authentication, configuration, attachment, and guard operations.
- The actual preparation cut has the stated fresh connection, valid tracker, native comparisons, route, filter, and ingress paths.
- Fixed primary and standby paths refer to that same cut.
- The passive endpoint configuration and selected NAT target are valid.
- Both directions contain two nonempty ranges that fit the raw endpoint, MSS, window, storage, and sequence reserves.
- The standby execution namespace matches the raw selected namespace.
- One whole Actions check and one whole persistent-demand service check accept the supplied report.
- The whole physical drop allowance satisfies `L ≤ 2`.
- The logical clock quantum satisfies `q > 0`, and the service bound satisfies `B > 0`.
- The actual report contains at least `totalSlots config B` evaluated slots.

The action profile excludes new copies and competing application writes.
It retains the fixed configuration and policy through the selected planned transfer.
The service check bounds service of each persistent current demand by `B` slots.
It covers preparation, startup, setup, both data directions, and all transfer controls.
Local service facts come from restrictions of that same check.
Native session state, current geometry, timer caps, and successful future operations are derived results.

## Sufficient horizon

The bound uses actual custody drops, independently of startup expiry counts.
Let `a` be the preparation length plus one OPEN slot.
The startup recurrence uses these definitions:

```text
e(s) = (waitSlots(q, 1000 + q*s) + 10) * B
H(0) = a + e(a)
H(k+1) = H(k) + e(H(k))
T = H(L)
S = T + (6*T + 6) * B
N = S + recoveredDataSlots(q, L, S, B)
```

[`completionBound`](../Netlib/Check/CampusTCPStartupBound.lean) computes `T`.
[`setupSlots`](../Netlib/Check/CampusTCPStartupDataEntryBound.lean) computes `S`, including the actual drain and five setup steps.
[`totalSlots`](../Netlib/Check/CampusTCPStartupTransferBound.lean) computes `N`.
The [data bound](../Netlib/Check/CampusTCPRecoveredTransferBound.lean) derives its timer capacity from the actual startup clock horizon and stored estimators.
No caller supplies a future RTO cap.

## Retained result

The result retains the actual data entry, its native checks, its recovery archive, and the complete two-way transfer result.
Both reads return their selected byte lists.
The transfer performs these seven controls:

```text
pause → capture → install → client route → server route → fence → resume
```

Checkpoint installation copies the actual mixed startup and data history.
Endpoint clocks, windows, receipt sources, and application histories continue through that transfer.

`Result.history` identifies the completed report as exactly `whole.steps.take (entrySlot + 1 + transfer.slot)`.
`Result.deadline` bounds that absolute position by `N`.
`Result.drop_ids` separates actual startup IDs from actual data IDs.
`Result.ids_disjoint` proves their separation, and `Result.whole_budget` bounds their total count by `L`.
Setup does not reset the ledger.
The data allowance is `L - actualStartupDrops`.

The result concerns this literal completed prefix.
It does not establish support for an arbitrary later tail.
Read-created window ACK work can remain pending after both data reads.
The [transfer guide](TCP_TRANSFER_PROGRESS.md) states the endpoint data-emptiness and final routing results.

## Executed example and limits

The [end-to-end test](../NetlibTest/CampusTCPStartupEndToEnd.lean) drops one startup SYN,ACK and one covering data ACK.
Both startup timers expire, and the data sender later expires its inherited timer.
Thus three actual expiries accompany two distinct physical drops.
The test preserves the actual archive, checks both reads and all seven controls, and accepts one whole `B = 12` service check.
It also rejects delivery of the old dropped startup packet after the handoff.
The executable checks this finite history directly.
The theorem covers every qualifying history with the sufficient static horizon.

The selected model excludes simultaneous open, SYN data, unsupported options, resets, aborts, close, persist, and general congestion control.
Logical clocks and native comparison inputs do not prove physical timing, kernel correspondence, peer authentication, or automatic failure detection.
The seven research programs and the full campus objective remain open.
