# Enforce the current session with a firewall

The session compiler binds application scopes to packet classes.
It emits a permit only when the current EAP-derived session permits that scope.
All other classes are denied.
The [EAP guide](EAP.md) defines authentication and credential evidence.
The [compiler guide](COMPILER.md) defines native emission and conflict checking.

```sh
lake exe netlib compile-session examples/admission/authentication.json examples/admission/requirements.json
lake exe netlib session-firewall examples/admission/bundle.json --json
```

The first command emits a firewall for the final session state.
Use `--after N` to consume exactly the first N trace events instead.
Zero selects the initial state.
The whole supplied authentication trace must agree with its observations before emission.
For compilation, an observation mismatch or conflicting packet requirements returns exit code 1.
Malformed inputs, unsupported native matches, and exhausted budgets return exit code 2.
These commands produce and check artifacts; they do not install firewall rules.

## Scope requirements

Intent schema 1 contains `schema` and `requirements`.
Each requirement has `id`, `scope`, and `match`.
A scope contains nonempty `resource` and `operation` strings.
The match uses the [traffic-class format](TRAFFIC.md).
IDs and native match restrictions follow the packet compiler.

Several packet classes can share a scope.
The example binds one UDP request tuple and its reverse reply tuple to `campus-application/use`.
The reviewer supplies the binding from the authenticated principal to those packet classes and the ingress link.
Header fields alone do not prove identity or prevent spoofing.

Each requirement becomes a permit or hard denial according to the current scope guard.
The compiler checks every header for conflicts.
If authorized and unauthorized scopes select the same header, compilation fails with a witness.
Rule order cannot override a denied scope.

## Native snapshot checks

Bundle schema 1 contains four fields:

| Field | Meaning |
| --- | --- |
| `schema` | The integer 1. |
| `authentication` | An [EAP session trace](EAP.md). |
| `intent` | The scope requirements above. |
| `snapshots` | A nonempty array of native policy checkpoints. |

Each checkpoint contains `after` and `firewall`.
`after` counts consumed authentication events and must not exceed the event count.
Checkpoints must have strictly increasing counts.
`firewall` is a supported nftables JSON export.
The native hook and priority must equal the generated forward chain at priority zero.

The checker compares both permission directions for every modeled header and all five conntrack states.
An extra established-flow permit fails even when the observed test packets did not use it.
A missing required permit also fails.
The report retains directional packet and state counterexamples.
The snapshot command returns exit code 1 for policy or authentication observation mismatches.
Conflicting intent prevents constructing the expected policy and returns exit code 2 for this command.
The default budget is 100,000 total partition cells across compilation, both comparison directions, and all checkpoints.
The report gives the total and its compilation and comparison parts.
Use `--budget N` to set that limit.

Snapshot metadata states when a policy was installed.
The theorem does not prove the installation command, update latency, or a complete time interval between snapshots.
An accept in this chain also does not establish final native delivery through other hooks and routes.
See the [nftables verdict semantics](https://netfilter.org/projects/nftables/manpage.html#lbAO).

## Proof chain

`Compile.SessionFirewall.Certified.permits_iff` connects generated permission to a selected class with current scope permission.
`permitted_valid` adds the complete credential guard and current EAP method readiness.
`denied_requirement` excludes every header of each denied scope.
`statefulSnapshot_permits` preserves the result for every conntrack state.

`Check.SessionFirewall.Finding.correct` proves exact native snapshot equivalence.
`Report.permitted_valid` transfers native permits to the current credential and method requirements.
Every checkpoint state is computed from its EAP event prefix.
Native observations never set authorization.

`Examples.SessionFirewallDeployment.output_current_permission` connects actual modeled lifecycle output to a valid scope and current method result.
`output_matching_scope_valid` applies to each matched requirement.
The Logoff, close, and revocation theorems exclude output with arbitrary cached trackers when the current policy is installed.
They use the forward-stage header after destination NAT and before source NAT.
The buffered theorem covers new admissions.
Packets admitted under an earlier policy can remain queued; [drain proofs](BUFFERING.md) cover that separate issue.

## Native evidence and limits

The [capture recipe](../examples/admission/README.md) runs a private wired EAP-TLS link and a routed UDP service.
It records raw EAPOL frames, method producer logs, native firewall exports, conntrack rows, and independently observed packets.
The stages distinguish unauthenticated denial, authenticated denial without a credential, admitted request/reply delivery, and denial after actual EAPOL Logoff.
The last probe reuses the admitted tuple while its confirmed conntrack record remains present.

| Native checkpoint | Current EAP authorization | Modeled session credential | UDP outcome |
| --- | --- | --- | --- |
| Before authentication | False | Absent | Denied |
| After EAP-TLS | True | Absent | Denied |
| After local credential installation | True | Present | Request and reply delivered |
| After Logoff and the deny update | False | Cleared | Same cached flow denied |

The application credential is a declared local demonstration input.
Its integrity bit does not verify a signature.
The controller retains the credential file after Logoff.
The modeled session clears its credential, and the replacement firewall denies the selected classes.
The EAP method still trusts the checked producer evidence and configured certificate policy.
The capture measures selected gateway transit in an isolated namespace topology.
It does not establish physical wireless port enforcement, distributed failover, cryptographic refinement, or complete campus correspondence.
The [roadmap](ROADMAP.md) records those remaining goals.
