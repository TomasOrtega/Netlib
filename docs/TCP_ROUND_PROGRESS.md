# Bounded TCP round

Netlib proves completion of one nonempty client-to-server range through a fixed primary gateway.
The proof starts with actual ordinary startup, enables both endpoint ledgers, and writes the selected bytes.
It derives every packet operation from the preceding state.
It covers every schedule in the action profile below.

All seven programs and the full campus objective remain OPEN.

## Guarantee

The round has nine packet and application actions:

1. Send the client range.
2. Assign its ingress packet.
3. Serve the current gateway ticket.
4. Deliver the emitted data and release it in order.
5. Emit the server's covering ACK.
6. Assign the ACK ingress packet.
7. Serve its reverse gateway ticket.
8. Deliver the ACK and retire the sender range.
9. Read the selected bytes at the server.

If each persistent next demand has service within `B` evaluated slots, the round completes by slot `9 * B`.
The supplied prefix must contain at least that many evaluated slots.
An input tail after an unsupported stop supplies no additional slots.
The bound starts after the five setup actions.

The theorem identifies the actual read in the supplied `steps.take (9 * B)`.
The returned bytes equal the selected write.
The sender has no outstanding bytes or timer entries for this first range.
Its deadline is absent and its retry count is zero.
The full server history contains exactly one receive operation and one nonempty read.
Its released and read byte streams both equal the selected bytes.

## Initial state and environment

`CampusTCPRoundStart.Initial` retains one checked startup history and the actual setup suffix.
The past service profile has exactly the SYN, SYN-ACK, and final ACK services through primary.
`Ordinary.history_exists` derives startup delivery sources from stored joint steps.
The startup transport proof derives both NAT zones, both socket directions, the confirmed tracker record, and the initial admission lanes.
It also derives negotiated MSS values and window coordinates.
No replacement endpoint or second gateway run supplies these facts.

The five setup actions enable recovery at both endpoints, enable ACK reactions at both endpoints, and write the client bytes.
The range must fit the pending limit, effective MSS, and peer receive capacity.

`NativeEnv` supplies initial typed policy and ingress comparison evidence, budget `100000`, passing comparisons, and actual native route and filter permits.
This remains an explicit preflight boundary.
The proof does not derive those comparison results from raw configuration alone.
Primary ownership, installation, authentication, attachment lifetimes, policy, and route controls stay fixed during this suffix.
Transport changes reuse the initial checks because their environment inputs stay equal.

The initial report can contain old startup copies or pending tickets.
The result concerns the fresh selected application range.
It does not require the entire initial or final work and custody state to be empty.

## Admitted schedules

At each phase, a schedule can select the current packet or application demand, or advance either endpoint to its stored local clock value.
These clock actions are actual checked operations.
They advance the joint slot and append the actual local history while they preserve endpoint state and live packet work.
Local time remains fixed in this first profile.

The selected suffix adds no copy or drop actions, competing application operations, policy updates, or route changes.
The model still supports those actions outside this theorem.
Packet assignment and delivery consume the exact live custody identities.
Gateway service consumes the actual pending ticket and uses its current stored policy.

The service condition applies to the next action from the preceding state.
It includes assignment, both services, both deliveries, ACK output, and the read.
Omitting any one of these actions while its demand persists violates the service condition.
It is not enough to require only eventual endpoint scheduling.

## Proof interface

| Module | Result |
| --- | --- |
| `CampusTCPRoundStart` | Actual startup, setup, range bounds, and static native environment. |
| `CampusTCPRoundPhaseBase` | Immutable operation anchors, current reports, and actual clock suffixes. |
| `CampusTCPRoundPhaseForward` | The five forward phase constructors at arbitrary current cuts. |
| `CampusTCPRoundPhaseReverse` | Reverse assignment, service, ACK receipt, and read at current cuts. |
| `CampusTCPRoundProgress` | Concrete invariant, enabled demands, persistence, phase descent, and completion adapter. |
| `CampusTCPRoundMonitor` | Packet and operation references read from stored results. |
| `CampusTCPRoundServiceBound` | Executable action and service checks with exact proof meanings. |
| `CampusTCPRoundBounded` | Completion by `9 * B`, actual prefix read, and sender retirement. |
| `CampusTCPRoundPhaseHistory` | Exact release and read streams, one receive, and one nonempty read. |
| `CampusTCPRoundOrigins` | Existing typed delivery, read-byte origin, compliance, and current-permission witnesses. |

`read_by` accepts the stated action and service predicates.
`read_by_checked` accepts the corresponding verified Boolean checks.
`read_and_retirement_by` also exposes the sender state at the bound.
`completes_final` retains completion through later admitted slots.

The monitor does not execute an endpoint or gateway again.
The invariant builds each operation at its actual current cut.
Determinism identifies any matching stored operation with the derived result.
Every rank decrease therefore retains an actual output, assignment, service, receipt, ACK, or read.

The origin corollaries construct the existing `ApplicationDelivery`, `Receives`, and per-byte `ReadOrigin` witnesses directly from these records.
They do not assume a successful assurance search.
Current-permission corollaries additionally require compliance of the actual prepared report.
They extend that past compliance through each new action and clock slot.
The core completion bound does not need this additional condition on earlier checks.

## Checks and limits

Generated tests start at the actual startup cut and create new operations.
They cover normal and stalled schedules, consumed-packet rejection, and a read that creates new window ACK work.
Separate omission cases retain live work and fail each phase's service bound.
The formal test constructs actual startup and native evidence and rejects wrong tuple, zone, MSS, window, and installation conditions.

A read can create a new ACK cause.
Completion does not require discharge of that cause.

The [recovery progress extension](TCP_RECOVERY_PROGRESS.md) adds advancing logical clocks, two combined data-and-ACK drops, and actual timer retries.
Competing streams, congestion control, and planned gateway transfer remain open for this progress proof.
The existing 400-byte and 600-byte held-gap campus prefix is a later extension.
This first round does not replace or reset that prefix.
Native transmission, physical time, kernel refinement, and full protocol conformance remain external obligations.
See the [broader progress design](research/CAMPUS_PROGRESS.md), [enabled operations](TCP_ENABLED_OPERATIONS.md), and [packet custody](PACKET_CUSTODY.md).
