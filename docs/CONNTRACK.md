# Native conntrack evidence

The conntrack adapter checks reported IPv4 TCP and UDP flow tuples.
It separates a frozen tuple association from policy permission and packet admission.
It does not turn a kernel snapshot into grants in the local timed NAPT model.

## Commands

```sh
lake exe netlib conntrack SNAPSHOT INTENT.json --json
lake exe netlib conntrack-map RAW.json ZONE HEADER.json --json
```

`conntrack` detects the supported XML or JSON format.
It compiles the separate [packet intent](COMPILER.md) and audits every reported original tuple against that policy.
Its report has scope `reported-original-flow-policy`.
A passing audit establishes permission under the supplied intent for those tuples.
It does not establish how the kernel created a flow or whether it forwarded a packet.
The `--budget N` option bounds policy compilation.
A successful empty full-status capture can pass with zero reported records.
It does not establish the absence of unreported kernel state.

`conntrack-map` accepts only the full-status JSON profile.
`ZONE` is the effective 16-bit conntrack zone.
`HEADER.json` has `source`, `destination`, `protocol`, `sourcePort`, and `destinationPort` fields.
Addresses use dotted IPv4 strings; the other fields use bounded integers.
The command looks up the complete zone and header key in either direction.
A hit returns the frozen tuple projection under the checked NAT flags and endpoint conditions.
A miss means unassociated, not denied.
XML does not supply the full status needed by this command.

The audit returns exit code 0 when all reported original tuples pass, or 1 when a tuple violates the intent.
The map command returns 0 for an association or 1 for a miss.
Both commands return 2 for unsupported input or another checking error.

## XML snapshot profile

The reference producer is conntrack-tools 1.4.9 with libnetfilter_conntrack 1.1.1.
Use its IPv4 snapshot command, without labels or timestamps:

```sh
conntrack -L -f ipv4 -o xml > SNAPSHOT.xml
```

The producer can also include `id` in the output options.
The [pinned formatter source](https://www.netfilter.org/pub/libnetfilter_conntrack/libnetfilter_conntrack-1.1.1.tar.xz)
defines the supported XML fields in `src/conntrack/snprintf_xml.c`.
The [pinned command source](https://www.netfilter.org/pub/conntrack-tools/conntrack-tools-1.4.9.tar.xz)
defines snapshot framing and output choices in `src/conntrack.c`.
There is no native JSON output option in this command version.

The decoder requires one nonempty `conntrack` root and the native UTF-8 XML declaration.
Each `flow` has one original, one reply, and one independent metadata block.
It preserves both five-tuples, remaining timeout seconds, and optional zone values.
It also preserves supported TCP state, counters, mark, security mark, use count, ID, and visible status markers.
Row indices, source lines, character spans, field paths, and exact row XML remain available.

Original and reply zones use their directional value when present, then the global zone, then zero.
An explicit zero remains a supplied value.
IDs are metadata; lookup uses the effective zone and full tuple.
The decoder rejects duplicate fields or attributes, unknown elements, unsupported protocols, event rows, and out-of-range values.
It also rejects labels, security contexts, timestamps, comments, DTDs, entities, and processing instructions.
Every accepted table has unique keys across both directions.
The same public endpoint can appear in several records when their complete keys differ.

An empty successful native dump emits no XML document.
The XML decoder therefore rejects empty stdout and an empty root.
It cannot infer a successful empty table from missing bytes.
Capture status and producer version require separate evidence; the XML does not contain them.

### Partial status evidence

XML reports only the presence of `assured` and `unreplied` markers.
It does not preserve the complete kernel status mask.
Absence of `unreplied` does not independently prove that a status attribute was supplied.
TCP state and `assured` do not establish policy authorization.

The omitted flags include NAT selections, confirmation, helpers, offload, and other kernel state.
Different original and reply tuples alone do not prove that native NAT is enabled.
Caller-created tuple pairs can exist without corresponding NAT status selections.
The XML model therefore provides tuple-pair algebra, without a theorem about native NAT hooks.

## Full-status JSON capture profile

The [reviewed collector](../scripts/capture_conntrack.py) reads a raw Netlink dump in an isolated Linux namespace.
Its JSON is a Netlib capture format, not a conntrack-tools output format.
Schema 1 has these fields:

| Field | Meaning |
| --- | --- |
| `schema` | The integer `1`. |
| `family` | The integer `2`, for IPv4. |
| `entries` | Structured original and reply tuple records. |
| `messages` | Original Netlink messages as hexadecimal strings. |
| `request` | The original IPv4 dump request as a hexadecimal string. |

Each entry has `original`, `reply`, `originalZone`, `replyZone`, `remainingTTL`, and `status` fields.
It also has nullable `id`, `mark`, and `use` metadata, plus its original `raw` message.
The status field preserves the full reported mask.
The raw messages retain native attributes that have no structured field in this profile.
The collector can record a missing timeout as null.
The supported Lean profile requires a bounded reported timeout, including zero.

The collector checks message boundaries, sender, sequence, multipart framing, kernel errors, and successful dump completion.
Truncation, interruption, overruns, and exhausted capture budgets cause errors.
The Lean importer checks the structured JSON, field bounds, supported status, tuple conditions, and key uniqueness.
It retains the byte strings but does not decode them or prove that their contents agree with the JSON fields.
The collector, its execution, and the agreement of retained bytes with structured fields remain part of the evidence boundary.

The supported status profile requires confirmation.
It permits seen-reply, assured, fixed-timeout, and the supported source and destination NAT flags.
A selected NAT operation must have its corresponding NAT-done flag.
Expected-flow, sequence-adjustment, dying, template, NAT-clash, explicit-helper, offload, and unknown status bits cause errors.
Automatic helper metadata can exist without the explicit-helper bit.
Its native attributes remain opaque bytes; this profile does not detect every helper attachment.
If a NAT flag is absent, the corresponding endpoint pair must be unchanged.
The original and reply protocols must agree and must be TCP or UDP.

`Protocol.NetfilterNAT.Entry.rewrite_correct` proves the resulting endpoint rewrite under those conditions.
It is an algebraic theorem about the accepted fields and flags.
It does not prove refinement of kernel C code, hook ordering, checksum updates, or transport acceptance.

## Snapshot assumptions and limits

Remaining timeout is a reported number of seconds, not an absolute expiration time.
The kernel floors fractional seconds, so zero can describe a record with less than one second remaining.
The frozen model accepts zero and does not evolve a clock or assert liveness.

All records belong to one externally identified network namespace.
The model preserves effective direction zones and validates complete bidirectional lookup keys.
It does not impose global uniqueness of public address and port pairs.
This differs from the local endpoint-independent mapping invariant in [timed NAPT traces](STATEFUL.md).

Kernel confirmation can exclude a tentative or dropped flow from a later dump.
The kernel can also hide reply-only NAT-clash objects from normal table iteration.
Concurrent mutation can change the table during or between observations.
The supported result concerns validated reported records, not all kernel state or a complete packet history.
The relevant upstream code is in
[`nf_conntrack_core.c`](https://raw.githubusercontent.com/torvalds/linux/v6.8/net/netfilter/nf_conntrack_core.c),
[`nf_conntrack_netlink.c`](https://raw.githubusercontent.com/torvalds/linux/v6.8/net/netfilter/nf_conntrack_netlink.c), and
[`nf_nat_core.c`](https://raw.githubusercontent.com/torvalds/linux/v6.8/net/netfilter/nf_nat_core.c).
These upstream references do not establish exact correspondence with a distribution kernel.

Neither format establishes producer authenticity, table completeness, policy provenance, allocator correctness, or packet freshness.
TCP flags, sequence windows, payloads, fragmentation, and external delivery remain outside the tuple model.
A permitted original tuple does not prove that a reply was admitted or that any peer received data.
The existing [Linux forwarding bundle](LINUX.md) keeps its stateless scope.
These commands do not extend that bundle to a complete Linux NAT or firewall execution model.

## Native evidence

The repository retains a genuine isolated capture with conntrack-tools 1.4.9,
libnetfilter_conntrack 1.1.1, and nftables 1.1.3 on kernel `6.8.0-117-generic`:

- [Native XML snapshot](../examples/conntrack/native/conntrack.xml).
- [Full-status JSON and original Netlink bytes](../examples/conntrack/native/netlink.json).
- [Six matched socket observations](../examples/conntrack/native/packets.json).
- [Original client observations](../examples/conntrack/native/client.json) and [server observations](../examples/conntrack/native/server.json).
- [Loaded native rules](../examples/conntrack/native/rules.nft) and their [JSON export](../examples/conntrack/native/rules.json).
- [Kernel identity](../examples/conntrack/native/kernel.txt), [command version](../examples/conntrack/native/conntrack-version.txt),
  [library version](../examples/conntrack/native/library-version.txt), and [nftables version](../examples/conntrack/native/nftables-version.txt).
- [Producer source and captured-file hashes](../examples/conntrack/capture-provenance.json).

The dump reports two TCP and two UDP records to two remote peers.
All four use public endpoint `203.0.113.1:40000`; their full direction keys remain distinct.
The TCP rows report `ESTABLISHED` and `assured`.
The UDP rows lack `assured` despite successful application echoes.
These observations reinforce the separation between status markers and policy authority.

Runtime tests import both formats and compare every reported tuple, zone, timeout, and shared metadata field.
They also compare the frozen tuple projection with the six recorded socket exchanges.
The joined reply tuple reverses the server-observed wire tuple.
It is derived data, not an independent capture of the reply IP header before NAT.
The two additional attempts named `collision` and `postrouting-drop` had no recorded server receipt or reply.
They have no record in these reported dumps.
That observation does not establish their absence from every form of kernel state.

## Capture recipe

The [container build](../examples/conntrack/Dockerfile),
[capture recipe](../examples/conntrack/capture.sh), and
[packet exercise](../examples/conntrack/exercise.py)
prepare an isolated experiment with client, router, and server namespaces.
The recipe builds pinned producers and records their versions with the kernel identity.
It exercises TCP and UDP flows to two remote peers through an explicit source NAT rule.
The retained capture and its observed outcomes remain separate evidence from the Lean tuple proofs.

Run the recipe from the repository root:

```sh
docker build -t netlib-conntrack-capture:1.4.9 examples/conntrack
tar -cf - examples/conntrack/capture.sh examples/conntrack/exercise.py scripts/capture_conntrack.py | \
  docker run --rm --cap-add NET_ADMIN --cap-add SYS_ADMIN \
    --security-opt seccomp=unconfined --security-opt apparmor=unconfined \
    -i netlib-conntrack-capture:1.4.9 sh -c \
    'mkdir /task && tar -xf - -C /task && sh /task/examples/conntrack/capture.sh' > capture.tar
```

The extra capability and security settings permit private namespace and procfs mounts inside this disposable container.
The command uses neither host mounts nor host networking.
