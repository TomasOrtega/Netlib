# 5G direct service access

This profile checks selected admission rules for a direct network-function request.
It uses TS 33.501 version 19.5.0, Release 19.
The source is clause 13.4.1.1.2, printed pages 199 through 203.
These are PDF pages 200 through 204.
Read the [pinned ETSI document](https://www.etsi.org/deliver/etsi_ts/133500_133599/133501/19.05.00_60/ts_133501v190500p.pdf).

The profile checks a consumer, producer instance, and configured authorization server.
The trace supplies identity and token integrity results.
Each admitted request must satisfy every selected guard.
A correct denial does not violate admission safety.
Availability is a separate property.

## Selected requirements

Each result preserves the source version, clause, assumptions, and event evidence.

| Result ID | Formal condition for an admitted request |
| --- | --- |
| `5G-ADMISSION` | All selected guards hold in the current session. |
| `5G-MUTUAL-AUTH` | Both peers pass the supplied identity check. |
| `5G-TOKEN` | The session contains an access token. |
| `5G-ISSUER` | The issuer matches the configured authorization server. |
| `5G-INTEGRITY` | The supplied token integrity check succeeds. |
| `5G-SUBJECT` | The subject matches the authenticated consumer. |
| `5G-AUDIENCE` | The audience matches the producer instance. |
| `5G-SCOPE` | The scope includes the requested resource and operation. |
| `5G-EXPIRATION` | The current time precedes the token expiration time. |

This selected profile requires a resource and operation scope.
It excludes producer-type audiences, slice restrictions, NF sets, service sets, and CCA claims.
The parser rejects extra fields instead of silently ignoring their security meaning.

The pinned clause permits valid token reuse.
The selected service-request procedure has no token-revocation step.
The profile therefore accepts repeated requests with the same valid token.

## Session model

The shared session module records these values:

- The peer identity result.
- The current credential.
- The current time.
- The most recent guarded admission.

Authentication starts a new context and clears the installed credential.
A token event installs the observed credential.
A request event checks the current identity, claims, and clock.
Time changes and credential changes clear the previous admission.
A close event clears the context.

The generic session module also supports local revocation.
That operation belongs to a local policy.
It clears the current credential without a persistent token blacklist.
The 5G profile does not accept a revocation event.

`Session.permits_iff` connects the Boolean guard to its independent proposition.
`Session.step_safe` and `Session.run_safe` preserve the admission invariant.
`Session.admitted_valid` proves the full guard conditions for a recorded admission.
`Session.clock_mono` proves that model transitions cannot decrease time.
`Session.policy_allows` connects the guard to the existing Zero Trust policy.

`FiveG.check_compliant_safe` connects a successful profile report to every observed admission.
The input trace must record every actual admission for this result to describe a deployment.

## Trace input

Run the checked example:

    lake exe netlib fiveg examples/5g/secure.json --json

The secure trace includes token reuse and correct denials.
It rejects a wrong operation, an expired token, and a request after session closure.

The JSON object has schema 1 and mode `direct-nf-instance`.
Its top-level fields are `consumer`, `producer`, `issuer`, and `events`.
Every event has a `type`.

| Event | Other fields |
| --- | --- |
| `authenticate` | `mutual`, a Boolean peer-check result. |
| `token` | `credential`, a complete token record. |
| `tick` | `now`, a natural-number time. |
| `request` | `resource`, `operation`, and the observed Boolean `accepted`. |
| `close` | None. |

A credential has `issuer`, `subject`, `audience`, `scopes`, `expiresAt`, and `integrity` fields.
Each scope has a `resource` and an `operation`.
The scope list must contain an entry.
The clock cannot move backward.
The trace must contain an observed request.
Unknown fields, unsupported events, and invalid field types cause input errors.

The `accepted` field records the observed service result.
It does not instruct the model to authorize a request.
An unsafe observed admission therefore produces a violation.

## Violation fixtures

The examples directory contains one fixture for each selected guard:

- `unauthenticated.json`
- `missing-token.json`
- `bad-issuer.json`
- `bad-integrity.json`
- `bad-subject.json`
- `bad-audience.json`
- `bad-scope.json`
- `expired.json`

`correct-denial.json` records rejection of an invalid token.
It satisfies the admission safety profile.
`invalid-clock.json` and `unsupported-revocation.json` must produce input errors.

## Evidence boundaries

The selected profile assumes trustworthy identity and integrity observations.
It does not validate TLS certificates, JWT syntax, signatures, or MAC values.
It does not prove token issuance policy or the complete 5G authentication procedure.
It excludes indirect communication, roaming, handover, and optional token restrictions.

`FiveG.coverage` reports the missing identity evidence, missing cryptographic evidence, and unsupported optional claims.
These results cannot count as satisfied requirements.
Use this report when the requested assurance exceeds the selected admission profile.
