# Bounded campus session revocation

Netlib proves bounded revocation for one modeled campus UDP session.
One report retains authentication, native policy comparisons, both gateway installations, actual packet processing, and FIFO delivery.
The [public interface](../Netlib/Check/CampusRevocation.lean) provides a universal completion theorem and an executable certificate.

## Actual trigger and installed policy

The selected trigger consumes an actual Logoff, credential revoke, or close observation.
Its authentication prefix determines both fixed deny targets.
Each target retains the supplied configuration identity, literal forward rules, fallback, and hook context.
Its certificate compares the compiled forward policy with the policy for the consumed authentication prefix.
The comparison covers every modeled packet header and conntrack classification.
Installation must select the exact target identity and every stored pipeline field.

One action check covers initial policy checks, raw observations, current policy before the trigger, and allowed later operations.
The selected update interval permits no later authentication change or withdrawal.
Later installations must retain the checked targets.
Stale permit processing can occur before both targets install.
Its original false verdict for the current policy remains in the report.
The existing campus compliance checker retains that verdict.

Ordinary packet calls use the selected gateway's actual stored pipeline and persistent table.
The gateway must be unfenced, and primary processing requires a primary that has not been withdrawn.
`Step.packet_available` proves these conditions for every accepted packet call.
Supplied fresh candidates cannot replace the confirmed protected binding.

## Output and delivery

The FIFO contains computed emissions with their gateway, translated header, source packet, and certified bytes.
It is separate from the outstanding route assignments in `SafeHandoff.work`.
A route ticket can exist before its packet has produced an emission.
After both deny targets install, processing an earlier ticket produces no new output.
Previously emitted datagrams can still leave the FIFO until the drain completes.

Protected route tickets use their actual retained NAT binding.
Original output is the reversed reply tuple; reply output is the reversed original tuple.
Equal headers can occur in distinct FIFO entries with different payload bytes.
The queue retains each actual occurrence.

## Universal bound

Let `a` be the cut immediately after the actual trigger.
Let `K` be the FIFO length at that same cut, and let `B > 0` be the service bound.
The sufficient deadline is:

```text
N = a + 2*B + (K + 2*B)*B
```

[`CampusRevocation.complete`](../Netlib/Check/CampusRevocation.lean) requires these facts:

- Both fixed targets pass their source comparisons at the actual trigger prefix.
- One whole action check accepts the report.
- One whole service check accepts the same report with positive bound `B` for persistent demands.
- The report contains at least `N` actual steps.

Each missing installation completes within `B` actual steps while its demand persists.
At most one emission enters the FIFO per actual step.
Thus the FIFO after both installations has at most `K + 2*B` entries.
The same service check then supplies positive delivery capacity until that FIFO drains.
Successful future installation and drain are derived results.
Actual packet selection and continued denial also follow from the recorded steps.

`Result.current` is the actual selected completion state.
`Result.history` retains exactly `report.steps.take result.slot`.
`Result.delivered_bytes` equates delivered bytes with the computed emissions from that same prefix.
Both target configurations, the consumed authentication prefix, and an existing protected binding remain available in the result.
For the checked recorded suffix, `future_arrivals` and `future_served` prove empty new output and delivery.

## Early completion and finite case

`CampusRevocation.certify` searches only recorded states between the trigger and the smaller of `N` and the report length.
It can certify an actual early completion without adding steps to meet the sufficient horizon.

The [synthetic test](../NetlibTest/CampusRevocation.lean) has 34 actual steps and a sufficient deadline of 35.
The certificate selects the actual completion cut at step 25 within that same report.
It retains three old emissions at the installation barrier, including one actual stale standby output after Logoff.
An earlier establishment emission is already in the delivered history.
Unit delivery operations drain those exact bytes.
Four cached attempts use zone zero, and four fresh attempts use zone eight.
Both gateways and both packet directions use their persistent tables.
The test also covers altered sources, missing service, policy rollback, and unavailable gateways.

## Model scope

The selected model has one declared session and application scope, with at most one protected UDP binding.
Principal ownership of the packet classes and trusted method results remain explicit deployment assumptions.
The model treats installation as an atomic state change.
Supplied export authenticity, kernel correspondence, physical timing, cryptographic correctness, and wireless enforcement remain open.
Each embedded campus operation retains its actual old step equation.
Removing packet operations does not establish an unchanged old report, because those operations update the same persistent trackers.
The [campus guide](CAMPUS_DEPLOYMENT.md) and [session policy guide](SESSION_FIREWALL.md) state the earlier model contracts.
