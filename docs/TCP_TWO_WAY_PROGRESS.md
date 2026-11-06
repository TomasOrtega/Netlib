# Bounded TCP progress in both directions

Netlib proves one sequential exchange on the same actual campus report.
The forward receiver reads its two original ranges.
One actual accepted write then starts the reverse leg, whose receiver reads its two ranges.
One action selector and one persistent-service condition cover both legs and that write.
All seven programs and the full campus objective remain OPEN.

## Guarantee

The forward task starts after the selected accepted write and before either original send.
Each leg uses two nonempty ranges and permits either delivery order.
The local path and ACK discipline is the same as the [two-record result](TCP_TWO_RECORD_PROGRESS.md).
Actual data delivery creates ACK work, which resolves before the next ordinary data action.
Selected side drops remain possible while other path work is pending.

One allowance `D ≤ 2` covers selected ingress and link drops of original data, retries, and gap, partial, or full ACKs in both directions.
The reverse allowance is `D - forwardDrops`, where `forwardDrops` is the actual forward drop count.
The global log retains each consumed custody identity.
Each timeout consumes its own earlier selected loss cause.
Unused forward causes supply no reverse timeout credit.
The total timeout count is at most the actual selected drop count, which is at most `D`.

The result identifies the actual forward read, reverse write, and reverse read at strictly ordered slots:

```text
forwardRead < reverseWrite < reverseRead < N
```

Both reads return their exact selected byte lists.
The reverse selected writer is the application operation in that same actual write step.
Both final endpoints satisfy the modeled `IdleEndpoint` conditions, including empty sent data and recovery ledgers and cleared timeout metadata.
ACK reaction work and unrelated pending custody can remain.

## Initial conditions

The initial forward cut supplies the existing accepted-write, endpoint, gateway, and native environment conditions.
The reverse bytes also need primitive conditions at that same initial cut:

- The forward sender has no unread bytes.
- Reverse pending storage, effective MSS, and the initial endpoint send window fit the reverse bytes.
- The forward sender's initial offered receive space fits those bytes.
- The initial gateway peer window and bounded sequence epoch fit the reverse ranges.

The proof derives the reverse initial state from the actual completed forward history and the actual write.
The caller supplies no later accepted write, completed reverse setup, or future readiness result.
The bridge permits the write and guarded clocks.
The write retains endpoint recovery, ACK reaction work from the forward read, receipt allocation identities, and earlier histories.
The proof does not replace endpoints with new seeds.

## One service condition and one bound

Let `B` bound service of a persistent current demand in evaluated joint slots.
The whole selector chooses the current forward demand, the reverse write, or the current reverse demand.
Local service conditions are restrictions of that one whole condition on the same stored steps.
Let `q > 0` bound each logical endpoint clock increase, subject to current ACK and timer guards.

For each leg, define:

```text
H = 16 * B
C = max(initial RTO, sampleCap(initial estimator, H * q))
T = ceil((2^D * C) / q)
legSlots(D) = H + B * ((D + 1) * T + 8 * D + 7)
N = forwardSlots(D) + B + reverseSlots(D)
```

The static reverse term uses the initial forward receiver's RTO and estimator.
Its actual recovery history retains these fields through the forward leg and write, with the current clock preserved.
The actual reverse term uses the remaining allowance and is at most this static term.
The bound does not use the final adaptive RTO of the forward sender or constrain the final retired estimator.

The supplied actual trace must contain at least `N` evaluated slots and satisfy the whole action and service checks.
Each endpoint clock is at most its initial value plus `N * q`.
The returned report has exactly the initial history followed by `steps.take N`.
Unsupported input beyond the stored prefix supplies no slots.
Completion uses those same steps without another endpoint or gateway run.

## Sources and public interface

`CampusTCPTwoExchangeBounded.complete_by_checked` accepts the verified Boolean action and service checks.
`complete_by_cached` accepts the action check from one pass and the service check with cached tables of pending demands and events.
These checks are proved exactly equal to the reference checks for every input and bound, including `B = 0`.
They avoid repeated prefix folds and retain the same contract, `Result` type, sufficient bound, and test cases.
The `Result.reader_slots`, `forward_bytes`, and `reverse_bytes` methods expose the read order and bytes.
`Result.final_idle` and `budget` expose the endpoint conditions and shared loss bound.
`Result.reverse_writer_recorded` identifies the actual reverse writer.

`Result.forward_read_permissions` and `reverse_read_permissions` need only initial report compliance.
They connect each byte to its selected write, actual original or retry output, receipt, and permitted gateway service.
Reverse compliance is derived through the forward suffix and the same actual write.
Equal payload bytes alone do not identify a writer.

Both endpoint routes retain the selected primary or installed standby gateway owner.
Current native preflight comparisons, budget `100000`, and route and filter permits remain explicit initial premises.
Gateway observations and source indices remain actual retained records.
Policy, authentication, configuration, attachments, and route ownership stay fixed during this task.

## Tests and open scope

`NetlibTest.CampusTCPTwoExchangePlans` defines three continuations of the same actual report with forward/reverse drop splits `0/2`, `1/1`, and `2/0`.
Each checks one whole action and service certificate, exact read/write order, retained endpoint histories, and the shared loss log.
Two cases append actual allowed clocks at the current endpoint time to the sufficient bound of `10605` slots for `q = 10`, `B = 3`, and `D = 2`.
Their source applies the public bounded theorem to that same extended report.
These selected cases do not replace the universal proof.

More original ranges, sparse holes, extra copies, concurrent applications, gateway transfer during progress, persist, and fast recovery remain open.
Logical time and supplied native observations do not establish physical timing, native delivery, or kernel refinement.
The result does not complete broader protocol semantics, authentication composition, or the full campus objective.
