# One TCP session through revocation

Netlib checks cold startup, two-way transfer, and session revocation in one actual TCP report.
The [public constructor](../Netlib/Check/CampusTCPRevocationTransfer.lean),
`Netlib.Check.CampusTCPRevocation.certifyTransfer report config transferEnd triggerCut B raw`,
returns the checked shutdown result and a proved prior transfer.
It preserves the same endpoints, timers, trackers, interfaces, packet identities, and loss history.

## Checked inputs

The transfer prefix must contain both reads and all seven planned gateway-transfer controls.
[`CampusTCPStartupTransferCheck.checkReport`](../Netlib/Check/CampusTCPStartupTransferCheck.lean)
checks its native startup paths, original storage and MSS bounds, preparation, and namespace lifetime.
Both gateways and both packet directions use their actual stored sources.
`WithTransfer.history`, `.streams`, and `.controls` retain the literal prefix and its results.

The trigger consumes an actual Logoff, credential revoke, or close observation.
That consumed prefix fixes four native targets: forward and ingress policies at each gateway.
Each target must pass its source comparison.
Actual installation events establish exact stored-source equality.
The shutdown profile fixes authentication and interface lifetimes, rejects policy rollback, and excludes later packet copies.
Copies could otherwise restore a link packet from a completed parent.

One phased action check and one whole service check use the same report and positive bound `B`.
The original physical loss allowance covers startup, transfer, and shutdown.
An ingress packet, pending route ticket, and computed receiver-link packet remain distinct objects.

The action check also runs `CampusTCPRevocationEnabled.check` at every shutdown cut, including the terminal cut.
For each pending demand, it computes a supported current operation that is allowed and serves that demand.
These witnesses establish local enabledness in the supplied trace.
The result remains conditional on the selected action and bounded-service profile; it does not construct a global scheduler.

## Completion and retained data

Stale permit service before installation can emit a real packet.
Its false current-policy verdict remains in the report.
Supplied packet observations and route checks must still agree with the computed service.
After all four targets install, actual service emits no new receiver-link packet.
The remaining old link identities must be delivered or explicitly dropped within the same loss allowance.

At the selected completion cut, all targets are installed and the receiver-link frontier is empty.
`Result.future` excludes new service output and network receipts throughout the checked suffix.
`Result.whole_budget` retains the original loss bound.
Endpoint buffers and new ACK or retry ingress work can remain.
A later application read can return earlier accepted bytes;
[`CampusTCPRevocationReadOrigin`](../Netlib/Check/CampusTCPRevocationReadOrigin.lean)
locates their actual receipt before completion.

If the trigger cut is `a` and its pending link count is `K`, the sufficient absolute deadline is
`a + 4*B + (K + 4*B)*B`.
The certificate searches recorded cuts up to that deadline and can select earlier completion without padding the report.

## Checked finite case

The [fixture](../NetlibTest/CampusTCPRevocationFixture.lean) retains the exact 95-step startup and transfer prefix.
Logoff ends at cut 102; four staggered installs end at 108; the last old link arrives at 109.
The report ends at 115 and passes one whole `B = 12` contract with the original two spent losses.
It retains two distinct byte links, a false stale permit verdict, pending ACK ingress, a later read of `[101, 102]`, and denied retry service.
Tests reject missing targets, starvation, wrong cuts, copies, rollback, excess loss, and repeated delivery.

Atomic installations, supplied source and lifetime identities, and trusted method evidence remain assumptions.
Linux command execution, kernel correspondence, physical timing, cryptographic correctness, and wireless enforcement remain open.

See [startup recovery](TCP_STARTUP_RECOVERY.md), [packet custody](PACKET_CUSTODY.md), and the separate [UDP revocation result](CAMPUS_REVOCATION.md).
