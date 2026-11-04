# Output exclusion through a late filter

The revocation checker proves that a selected class of output headers cannot pass a late filter.
The check covers every modeled state label and every selected header.
The lifecycle proof then excludes those outputs, including outputs produced by cached NAT bindings.
A passing replay transfers the exclusion to every supplied output observation after a declared cutover.

This is a traffic exclusion contract.
The selected header class must describe the intended restriction after NAT.
A destination-only class can quarantine requests to a backend while allowing replies in the other direction.
Identity revocation and termination of both directions require their own contracts.

## Run the retained example

```sh
lake exe netlib lifecycle examples/revocation/replay.json --json
lake exe netlib lifecycle-blocks examples/revocation/replay.json examples/revocation/forbidden.json --from 3 --json
```

The retained capture contains six UDP packets, 22 traced chain visits, and seven raw state snapshots.
Its replay has seven operations, including explicit deletion.
Before cutover, the cached established original still reaches the backend after the forward policy tightens and the NAT rules change.
After cutover, the late barrier drops that original while its confirmed record remains present.
Deletion then removes the record.
A fresh retry is denied by the tightened forward filter.
A separate fresh attempt permitted by that filter still hits the late barrier and remains unconfirmed.

The [native trace](../examples/revocation/native/trace.txt),
[socket observations](../examples/revocation/native/observations.json),
[native commands](../examples/revocation/native/commands.json), and
[checked evidence](../examples/revocation/checked-evidence.json) remain available.
The [independent verifier](../scripts/check_revocation_capture.py) checks source policies, traced headers and decisions, and raw snapshot bytes.
It compares available rule text with the supported exported expressions.
Entries that expose only a rule handle are joined to the selected configuration export.
That join assumes the correct snapshot for the recorded phase.
The [example builder](../scripts/build_revocation_example.py) projects that evidence into the Lean replay.
The [capture guide](../examples/revocation/README.md) records the producer versions, original file hashes, and reproduction commands.
This experiment supplies finite evidence for its isolated namespace and kernel.
It does not prove a native command or a general packet-drain protocol.

## Check a cutover

```sh
lake exe netlib lifecycle-blocks TRACE.json MATCH.json --from N --json
```

`TRACE.json` uses [lifecycle schema 1](LIFECYCLE.md).
`MATCH.json` uses the [traffic selection format](TRAFFIC.md).
The selection applies to the output header after both destination and source translation.
`N` is a zero-based event position, including deletion events.
The checker replays the complete prefix to compute the actual model state at that position.
It does not reset the table at cutover.

The default position is 0.
The selected suffix must be nonempty and contain a packet event.
For every packet event in that suffix, the checker certifies the selected configuration's late filter.
Deletion events need no filter certificate and preserve the exclusion guarantee.
Unused configurations are not checked.

A successful command requires both conditions:

1. Every selected late filter denies every header in the forbidden class for all five modeled state labels.
2. The complete replay agrees with every supplied packet and state observation, including observations before cutover.

The report separates `barrierCertified` from `observationsAgree`.
`compliant` is their conjunction.
Exit code 0 means both conditions hold.
Exit code 1 means a condition failed.
Exit code 2 means invalid input, an unsupported operation, or an exhausted budget.
The checker reports failures before cutover even when the barrier is valid afterward.

## Exact chain certificate

A filter blocks the forbidden class when its ordered evaluation returns deny for every selected header and every state label.
The state labels are `new`, `established`, `related`, `invalid`, and `untracked`.
The ordinary lifecycle produces only the first two labels; the chain certificate covers all five independently.

The certificate specializes the stateful chain into an ordinary ACL for each label.
It partitions headers at every policy and selection boundary.
One representative per cell suffices because each relevant match and decision is constant within that cell.
The proof covers the explicit native default and first-match rule order.

An established permit before the guard can invalidate the barrier.
A guard that denies the complete forbidden class before that permit can establish it.
A failed certificate includes a concrete state and header that the chain permits.
That header need not occur in the supplied trace.
No observed forbidden output is required to reject an incomplete barrier.

The late chain must run at postrouting after source NAT priority 100 and before confirmation priority 2147483647.
The lifecycle parser enforces that context.
The default resource budget is 100,000 partition cells across all checked packet events and all five states.
Repeated configurations are charged for each use.
Use `--budget N` after `--from N` to change the budget.
Budget exhaustion produces no exclusion answer.
The budget does not bound trace length, table size, or total execution time.

## Stateful operation guarantee

Every forwarded lifecycle output passed its selected late filter.
A certified barrier therefore excludes the selected output regardless of the attached binding, its direction, or its seen-reply state.
This argument does not require deleting the binding.
It also does not require a fresh allocation or reevaluating changed NAT rules.

The ordered operation proof covers packet calls and explicit record deletion.
Its suffix starts from the state produced by the real modeled prefix.
When each packet configuration in that suffix has the barrier, every modeled output in that suffix is outside the forbidden class.
Report agreement transfers the result to the corresponding supplied output observations.
Mismatched observations never replace the model state.

This supplies a contract for a barrier-first operational sequence:

1. Install a filter that certifies the forbidden class.
2. Keep the barrier in each configuration selected after the commit point.
3. Delete old bindings or change the remaining policies while retaining the barrier.

Deletion is cleanup in this argument.
An established-only forward policy and a NAT rule change can leave an old cached connection usable.
Static filter inclusion alone does not prove traffic exclusion for that connection.

## Deployment assumptions

The declared cutover is after the barrier has become effective for selected packets.
Packets already beyond the late hook require a separate drain or delivery boundary.
The [buffered cutover model](BUFFERING.md) supplies that distinction and a FIFO service-budget proof.
The event position is not a physical timestamp or proof that a native install command completed.

Every selected packet must traverse the declared hook sequence without bypass.
The selected configurations must cover the actual post-cutover processing intervals.
A missing configuration change or concurrent barrier removal remains outside that evidence.
The certificate does not prove that a deployment tool installs or retains the rules.

The forbidden class must cover every relevant cached and new translated endpoint.
An address or port alias outside that class remains outside its exclusion guarantee.
An application name, user, or credential has no automatic mapping to that class.

All [ordinary lifecycle assumptions](LIFECYCLE.md#model-boundary) still apply.
Transport admission, tracker reopening, expiry, concurrency, capture authenticity, complete kernel-state visibility, and kernel C correspondence remain separate obligations.
The native experiment supplies UDP evidence and does not establish full TCP behavior.
