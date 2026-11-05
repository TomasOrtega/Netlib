"""Check native NAT wire bytes, hook checkpoints, TTL drops, and conntrack state."""

import argparse
import json
import re
import shlex
import sys
from pathlib import Path

import check_admission_capture as admission
import check_eap_capture as eap
import check_lifecycle_capture as lifecycle
import check_wire_capture as wire

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/wire-nat"
EvidenceError = admission.EvidenceError
require = admission.require
ORIGINAL = {
    "source": "192.0.2.2",
    "destination": "203.0.113.2",
    "protocol": 17,
    "sourcePort": 41000,
    "destinationPort": 8080,
}
WIRE = {
    "source": "203.0.113.1",
    "destination": "198.51.100.2",
    "protocol": 17,
    "sourcePort": 40000,
    "destinationPort": 9000,
}
WIRE_REPLY = lifecycle.reverse(WIRE)
PEER_REPLY = lifecycle.reverse(ORIGINAL)
BASE = "/tmp/netlib-admission"


def read_json(path):
    try:
        return lifecycle.read_json(path)
    except ValueError as error:
        raise EvidenceError(str(error)) from error


def objects(document):
    rows = document["nftables"]
    require(
        rows and all(isinstance(row, dict) and len(row) == 1 for row in rows),
        "Malformed native nftables objects.",
    )
    meta = [row["metainfo"] for row in rows if "metainfo" in row]
    require(
        len(meta) == 1
        and meta[0]["version"] == "1.1.3"
        and type(meta[0]["json_schema_version"]) is int
        and meta[0]["json_schema_version"] == 1,
        "Unexpected native nftables version.",
    )
    return [
        {kind: {key: value for key, value in record.items() if key != "handle"}}
        for row in rows
        for kind, record in row.items()
        if kind != "metainfo"
    ]


def chain(table, name, kind, hook, priority, policy="accept"):
    return {
        "chain": {
            "family": "ip",
            "table": table,
            "name": name,
            "type": kind,
            "hook": hook,
            "prio": priority,
            "policy": policy,
        }
    }


def match(protocol, field, right):
    return {
        "match": {
            "op": "==",
            "left": {"payload": {"protocol": protocol, "field": field}},
            "right": right,
        }
    }


def expected_nat():
    return [
        {"table": {"family": "ip", "name": "netlib_nat"}},
        chain("netlib_nat", "destination", "nat", "prerouting", -100),
        chain("netlib_nat", "source", "nat", "postrouting", 100),
        {
            "rule": {
                "family": "ip",
                "table": "netlib_nat",
                "chain": "destination",
                "comment": "DNAT_SERVICE",
                "expr": [
                    match("ip", "daddr", "203.0.113.2"),
                    match("udp", "dport", 8080),
                    {"dnat": {"addr": "198.51.100.2", "port": 9000}},
                ],
            }
        },
        {
            "rule": {
                "family": "ip",
                "table": "netlib_nat",
                "chain": "source",
                "comment": "SNAT_PEER",
                "expr": [
                    match("ip", "saddr", {"prefix": {"addr": "192.0.2.0", "len": 24}}),
                    match("ip", "daddr", "198.51.100.2"),
                    match("udp", "dport", 9000),
                    {"snat": {"addr": "203.0.113.1", "port": 40000}},
                ],
            }
        },
    ]


def trace_objects():
    return [
        {"table": {"family": "ip", "name": "netlib_trace"}},
        chain("netlib_trace", "before", "filter", "prerouting", -301),
        chain("netlib_trace", "afterDestination", "filter", "prerouting", -90),
        chain("netlib_trace", "beforeSource", "filter", "postrouting", 90),
        chain("netlib_trace", "afterSource", "filter", "postrouting", 110),
        {
            "rule": {
                "family": "ip",
                "table": "netlib_trace",
                "chain": "before",
                "expr": [
                    {"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 17}},
                    {"mangle": {"key": {"meta": {"key": "nftrace"}}, "value": 1}},
                ],
            }
        },
    ]


def read_state(directory, record, commands):
    name = record["file"]
    require(re.fullmatch(r"[a-z0-9-]+-conntrack\.json", name), "Invalid conntrack artifact name.")
    copied_command(record["command"], commands)
    admission.successful_command(
        record["command"],
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "python3",
            "/task/capture_conntrack.py",
            "--output",
            f"{BASE}/{name}",
        ],
    )
    document = read_json(directory / name)
    require(
        type(document["schema"]) is int and type(document["family"]) is int,
        "Invalid conntrack schema.",
    )
    try:
        entries = lifecycle.decode_snapshot(document)
    except ValueError as error:
        raise EvidenceError(f"Conntrack raw evidence: {error}") from error
    require(len(entries) <= 1, "Unexpected extra visible conntrack entry.")
    for row in entries:
        require(
            row["original"] == ORIGINAL
            and row["reply"] == WIRE_REPLY
            and row["originalZone"] == row["replyZone"] == 0
            and type(row["id"]) is int
            and row["remainingTTL"] > 0
            and row["status"] in (440, 442),
            "Unexpected NAT binding tuple, zone, status, or lifetime.",
        )
    return entries


def copied_command(record, commands):
    value = {
        key: record[key]
        for key in ("command", "startNs", "endNs", "returncode", "stdout", "stderr")
    }
    require(
        sum(row == value for row in commands) == 1,
        "Observation contradicts its native command history.",
    )


def check_network(directory, observations, commands):
    profiles = {
        "peer": {"peer0": (eap.PEER, {("192.0.2.2", 24)})},
        "auth": {
            "auth0": (eap.AUTHENTICATOR, {("192.0.2.1", 24)}),
            "service0": (
                admission.SERVICE,
                {("198.51.100.1", 24), ("203.0.113.1", 32), ("203.0.113.2", 32)},
            ),
        },
        "server": {"server0": (admission.SERVER, {("198.51.100.2", 24)})},
    }
    routes = {
        "peer": {
            ("default", "peer0", "192.0.2.1", None),
            ("192.0.2.0/24", "peer0", None, "192.0.2.2"),
        },
        "auth": {
            ("192.0.2.0/24", "auth0", None, "192.0.2.1"),
            ("198.51.100.0/24", "service0", None, "198.51.100.1"),
        },
        "server": {
            ("192.0.2.0/24", "server0", "198.51.100.1", None),
            ("198.51.100.0/24", "server0", None, "198.51.100.2"),
            ("203.0.113.0/24", "server0", "198.51.100.1", None),
        },
    }
    expected_neighbors = {
        "peer": {("192.0.2.1", "peer0", eap.AUTHENTICATOR)},
        "auth": {("192.0.2.2", "auth0", eap.PEER), ("198.51.100.2", "service0", admission.SERVER)},
        "server": {("198.51.100.1", "server0", admission.SERVICE)},
    }
    exports = observations["networkExports"]
    require(
        set(exports)
        == {
            f"{namespace}-{kind}"
            for namespace in profiles
            for kind in ("links", "addresses", "routes", "neighbors")
        },
        "Missing or extra network exports.",
    )
    for namespace, interfaces in profiles.items():
        documents = {}
        for kind, arguments in (
            ("links", ["link", "show"]),
            ("addresses", ["address", "show"]),
            ("routes", ["-4", "route", "show", "table", "main"]),
            ("neighbors", ["neigh", "show"]),
        ):
            export = exports[f"{namespace}-{kind}"]
            require(
                export["file"] == f"network-{namespace}-{kind}.json",
                "Network artifact binding disagrees.",
            )
            copied_command(export["command"], commands)
            admission.successful_command(
                export["command"], ["ip", "-n", namespace, "-j", *arguments]
            )
            require(
                export["command"]["stdout"] == (directory / export["file"]).read_text(),
                "Network export stdout contradicts its saved configuration.",
            )
            require(
                export["command"]["endNs"] < observations["initial"]["command"]["startNs"],
                "Network export is later than the initial packet state.",
            )
            documents[kind] = read_json(directory / export["file"])
        links = documents["links"]
        require(
            len(links) == len(interfaces) + 1
            and {row["ifname"] for row in links} == {"lo", *interfaces},
            "Unexpected namespace link inventory.",
        )
        for row in links:
            if row["ifname"] != "lo":
                require(
                    row["address"] == interfaces[row["ifname"]][0]
                    and "UP" in row["flags"]
                    and type(row["mtu"]) is int
                    and row["mtu"] >= 1500,
                    "Interface MAC, state, or MTU disagrees.",
                )
        actual_addresses = {
            (row["ifname"], item["family"], item["local"], item["prefixlen"])
            for row in documents["addresses"]
            if row["ifname"] != "lo"
            for item in row["addr_info"]
        }
        require(
            actual_addresses
            == {
                (name, "inet", address, length)
                for name, (_, addresses) in interfaces.items()
                for address, length in addresses
            },
            "NAT interface address export disagrees.",
        )
        require(
            len(documents["routes"]) == len(routes[namespace])
            and {
                (row["dst"], row["dev"], row.get("gateway"), row.get("prefsrc"))
                for row in documents["routes"]
            }
            == routes[namespace]
            and all(
                row["flags"] == []
                and set(row) <= {"dst", "dev", "gateway", "prefsrc", "protocol", "scope", "flags"}
                for row in documents["routes"]
            ),
            "Native route profile disagrees.",
        )
        require(
            len(documents["neighbors"]) == len(expected_neighbors[namespace])
            and {(row["dst"], row["dev"], row["lladdr"]) for row in documents["neighbors"]}
            == expected_neighbors[namespace]
            and all(row["state"] == ["PERMANENT"] for row in documents["neighbors"]),
            "Native neighbor binding disagrees.",
        )
        settings = (directory / f"{namespace}-settings.txt").read_text()
        require(
            "net.ipv6.conf.all.disable_ipv6 = 1\n" in settings
            and "net.ipv6.conf.default.disable_ipv6 = 1\n" in settings
            and (namespace != "auth" or "net.ipv4.ip_forward = 1\n" in settings),
            "Native forwarding or IPv6 isolation setting disagrees.",
        )


def decode_frame(row, index):
    raw = row["hex"]
    require(
        isinstance(raw, str) and re.fullmatch(r"(?:[0-9a-fA-F]{2})+", raw),
        "Require strict hexadecimal byte pairs.",
    )
    data = bytes.fromhex(raw)
    require(len(data) >= 42 and data[12:14] == b"\x08\x00", "Unsupported captured Ethernet frame.")
    ip = data[14:34]
    size = int.from_bytes(ip[2:4], "big")
    require(
        ip[0] == 0x45
        and int.from_bytes(ip[6:8], "big") in (0, 0x4000)
        and 28 <= size <= len(data) - 14
        and wire.folded_sum(ip) == 65535,
        "Invalid captured IPv4 header, flags, or checksum.",
    )
    metadata = {
        "raw": raw,
        "source": f"frames.jsonl:{index}",
        "timeNs": row["timeNs"],
        "interface": row["interface"],
        "packetType": row["packetType"],
        "ipId": int.from_bytes(ip[4:6], "big"),
        "ipLength": size,
        "ttl": ip[8],
        "tos": ip[1],
        "dontFragment": bool(ip[6] & 0x40),
    }
    require(
        type(row["packetType"]) is int and row["interface"] in ("auth0", "service0"),
        "Invalid capture interface or packet direction.",
    )
    source, destination = data[6:12].hex(":"), data[:6].hex(":")
    if ip[9] == 17:
        decoded = wire.decode_frame(raw)
        key = (row["interface"], row["packetType"], decoded["header"])
        permitted = (
            ("auth0", 0, ORIGINAL, eap.PEER, eap.AUTHENTICATOR),
            ("service0", 4, WIRE, admission.SERVICE, admission.SERVER),
            ("service0", 0, WIRE_REPLY, admission.SERVER, admission.SERVICE),
            ("auth0", 4, PEER_REPLY, eap.AUTHENTICATOR, eap.PEER),
        )
        require(
            any(key == entry[:3] and (source, destination) == entry[3:] for entry in permitted),
            "Wire NAT tuple, MAC role, interface, or direction disagrees.",
        )
        return {
            **decoded,
            **metadata,
            "protocol": 17,
            "payload": bytes.fromhex(decoded["payloadHex"]).decode("ascii"),
        }
    require(ip[9] == 1 and row["packetType"] == 4, "Unexpected non-UDP transit frame.")
    icmp = data[34 : 14 + size]
    require(
        icmp[:2] == b"\x0b\x00" and wire.folded_sum(icmp) == 65535 and len(icmp) >= 36,
        "Expected a valid native ICMP Time Exceeded message.",
    )
    require(
        (row["interface"], source, destination)
        in (
            ("auth0", eap.AUTHENTICATOR, eap.PEER),
            ("service0", admission.SERVICE, admission.SERVER),
        ),
        "ICMP link role disagrees.",
    )
    return {
        **metadata,
        "protocol": 1,
        "icmpType": 11,
        "icmpCode": 0,
        "quotedIpId": int.from_bytes(icmp[12:14], "big"),
        "icmpHex": icmp.hex(),
    }


def parse_traces(path):
    lines = path.read_text().splitlines()
    starts = [
        index
        for index, line in enumerate(lines)
        if re.match(r"^trace id [0-9a-f]+ ip netlib_trace before packet:", line)
    ]
    require(starts and starts[0] == 0, "Trace does not begin at the selected ingress checkpoint.")
    result = []
    for begin, end in zip(starts, [*starts[1:], len(lines)]):
        try:
            parsed = lifecycle.parse_trace("\n".join(lines[begin:end]))
        except ValueError as error:
            raise EvidenceError(f"Native hook trace: {error}") from error
        require(len(parsed) == 1, "Interleaved or ambiguous native packet trace.")
        trace = parsed[0]
        trace["source"] = f"trace.txt:{begin + 1}"
        for stage in trace["stages"]:
            stage["line"] += begin
            tokens = shlex.split(lines[stage["line"] - 1])
            for key, prefix in (
                ("ttl", ["ip", "ttl"]),
                ("ipLength", ["ip", "length"]),
                ("udpLength", ["udp", "length"]),
                ("udpChecksum", ["udp", "checksum"]),
            ):
                stage[key] = int(lifecycle.tokens_value(tokens, prefix))
            for verdict in stage["verdicts"]:
                verdict["line"] += begin
        result.append(trace)
    require(len(result) == 10, "Expected ten independent selected UDP traces.")
    return result


def check_trace(trace, incoming, outgoing, disposition):
    reply = incoming["header"] == WIRE_REPLY
    translated = admission.REPLY if reply else admission.REQUEST
    stages = trace["stages"]
    by_key = {(row["table"], row["chain"]): row for row in stages}
    require(len(by_key) == len(stages), "Repeated native hook checkpoint within a packet.")
    require(
        stages[0]["packet"] == incoming["header"]
        and stages[0]["ttl"] == incoming["ttl"]
        and all(
            row["ipId"] == incoming["ipId"]
            and row["ipLength"] == incoming["ipLength"]
            and row["udpLength"] == incoming["udpLength"]
            for row in stages
        ),
        "Native hook packet identity or lengths contradict the raw ingress.",
    )
    before = by_key[("netlib_trace", "before")]
    after = by_key[("netlib_trace", "afterDestination")]
    require(
        before["packet"] == incoming["header"]
        and before["udpChecksum"] == incoming["udpChecksum"]["value"]
        and after["packet"] == translated
        and after["ttl"] == incoming["ttl"],
        "Native before/after DNAT checkpoint disagrees.",
    )
    prefix = [("netlib_trace", "before"), ("netlib_tracking", "prerouting")]
    if ("netlib_nat", "destination") in by_key:
        require(not reply, "Reply unexpectedly traverses the fresh DNAT rule.")
        prefix.append(("netlib_nat", "destination"))
    prefix.append(("netlib_trace", "afterDestination"))
    if disposition == "ttlExpired":
        require(
            [(row["table"], row["chain"]) for row in stages] == prefix
            and incoming["ttl"] <= 1
            and outgoing is None,
            "TTL-expired packet reached a later hook or selected UDP output.",
        )
        return translated, None, None
    prefix.append(("netlib", "forward"))
    forward = by_key[("netlib", "forward")]
    require(
        forward["packet"] == translated
        and forward["ttl"] == incoming["ttl"] - 1
        and forward["oif"] == ("auth0" if reply else "service0"),
        "Native forward checkpoint, decrement, or selected route disagrees.",
    )
    verdict = forward["verdicts"][-1]
    if disposition == "forwardDrop":
        require(
            [(row["table"], row["chain"]) for row in stages] == prefix
            and verdict["kind"] == "policy"
            and verdict["verdict"] == "drop"
            and outgoing is None,
            "Forward-drop trace contradicts the deny policy.",
        )
        return translated, None, "peer" if reply else "server"
    require(
        outgoing is not None and verdict["verdict"] == "accept",
        "Missing accepted native UDP output.",
    )
    prefix.append(("netlib_trace", "beforeSource"))
    if ("netlib_nat", "source") in by_key:
        require(not reply, "Reply unexpectedly traverses the fresh SNAT rule.")
        prefix.append(("netlib_nat", "source"))
    prefix += [("netlib_trace", "afterSource"), ("netlib_late", "late")]
    require(
        [(row["table"], row["chain"]) for row in stages] == prefix,
        "Unexpected forwarding hook order.",
    )
    after_source = by_key[("netlib_trace", "afterSource")]
    require(
        by_key[("netlib_trace", "beforeSource")]["packet"] == translated
        and after_source["packet"] == outgoing["header"]
        and after_source["ttl"] == outgoing["ttl"] == incoming["ttl"] - 1
        and after_source["udpChecksum"] == outgoing["udpChecksum"]["value"]
        and by_key[("netlib_late", "late")]["packet"] == outgoing["header"],
        "Native pre/post SNAT checkpoints contradict the wire output.",
    )
    require(
        outgoing["ipId"] == incoming["ipId"]
        and outgoing["payloadHex"] == incoming["payloadHex"]
        and outgoing["ipLength"] == incoming["ipLength"]
        and outgoing["udpLength"] == incoming["udpLength"],
        "Forwarding changed the datagram identity, lengths, or UDP payload.",
    )
    require(
        outgoing["tos"] == incoming["tos"] and outgoing["dontFragment"] == incoming["dontFragment"],
        "Forwarding changed preserved IPv4 metadata (TOS or flags).",
    )
    require(
        (incoming["udpChecksum"]["status"] == "omitted")
        == (outgoing["udpChecksum"]["status"] == "omitted"),
        "NAT changed UDP checksum omission.",
    )
    return translated, after_source["packet"], "peer" if reply else "server"


def verify_exports(directory, exports, commands, policy, ingress):
    require(
        set(exports) == {"firewall", "nat", "late", "ruleset"},
        "Missing or extra native configuration exports.",
    )
    documents = {}
    for kind, arguments in (
        ("firewall", ["list", "table", "ip", "netlib"]),
        ("nat", ["list", "table", "ip", "netlib_nat"]),
        ("late", ["list", "table", "ip", "netlib_late"]),
        ("ruleset", ["list", "ruleset"]),
    ):
        export = exports[kind]
        copied_command(export["command"], commands)
        admission.successful_command(
            export["command"], ["ip", "netns", "exec", "auth", "nft", "-j", "-nn", *arguments]
        )
        require(
            export["command"]["stdout"] == (directory / export["file"]).read_text(),
            "Native configuration export stdout disagrees with its artifact.",
        )
        documents[kind] = read_json(directory / export["file"])
    require(
        admission.canonical_table(documents["firewall"]) == policy
        and objects(documents["nat"]) == expected_nat(),
        "Active forward or fixed NAT policy disagrees.",
    )
    expected_late = [
        {"table": {"family": "ip", "name": "netlib_late"}},
        chain("netlib_late", "late", "filter", "postrouting", 200),
    ]
    require(
        objects(documents["late"]) == expected_late,
        "Native late output hook is not empty accept at priority 200.",
    )
    tracking = [
        {"table": {"family": "ip", "name": "netlib_tracking"}},
        chain("netlib_tracking", "prerouting", "filter", "prerouting", -199),
        {
            "rule": {
                "family": "ip",
                "table": "netlib_tracking",
                "chain": "prerouting",
                "expr": [
                    {
                        "match": {
                            "op": "==",
                            "left": {"ct": {"key": "state"}},
                            "right": {"set": [2, 8]},
                        }
                    },
                    {
                        "counter": {
                            "packets": len(ingress),
                            "bytes": sum(row["ipLength"] for row in ingress),
                        }
                    },
                ],
            }
        },
    ]
    require(
        objects(documents["ruleset"])
        == tracking
        + objects(documents["nat"])
        + expected_late
        + trace_objects()
        + objects(documents["firewall"]),
        "Complete ruleset contains an unaccounted hook, bypass, mutation, or counter disagreement.",
    )
    return documents


def check_capture(directory, *, input_directory=DIRECTORY):
    directory, input_directory = Path(directory), Path(input_directory)
    require(
        "iproute2-6.19.0" in (directory / "iproute2-version.txt").read_text()
        and (directory / "nftables-version.txt").read_text().startswith("nftables v1.1.3 "),
        "Native producer version export disagrees with the selected importer profile.",
    )
    observations = read_json(directory / "observations.json")
    require(
        type(observations["schema"]) is int
        and observations["schema"] == 1
        and observations["scope"] == "wire-nat-forwarding",
        "Invalid NAT wire capture schema.",
    )
    commands = read_json(directory / "commands.json")
    previous_end = 0
    for record in commands:
        admission.interval(record)
        require(
            record["startNs"] > previous_end
            and type(record["returncode"]) is int
            and record["returncode"] == 0,
            "Native command history is unordered or failed.",
        )
        require(
            record["stderr"] == "" or record == observations["erase"]["command"],
            "Unexpected native command stderr.",
        )
        previous_end = record["endNs"]
    require(
        sum(row["command"][:5] == ["ip", "netns", "exec", "auth", "nft"] for row in commands) == 26,
        "Unexpected extra firewall mutation or export command.",
    )
    for name in ("requirements", "deny", "permit", "demo-credential"):
        require(
            (directory / "input" / f"{name}.json").read_bytes()
            == (input_directory / f"{name}.json").read_bytes(),
            "Immutable NAT capture input disagrees.",
        )
    policies = {
        name: admission.canonical_table(read_json(directory / "input" / f"{name}.json"))
        for name in ("deny", "permit")
    }
    require(
        policies
        == {
            "deny": [],
            "permit": [{"id": "REQUEST", **admission.REQUEST}, {"id": "REPLY", **admission.REPLY}],
        },
        "Generated policy must cover the selected post-DNAT classes.",
    )
    credential = read_json(directory / "input/demo-credential.json")
    require(
        credential
        == {
            "issuer": "campus-authority",
            "subject": eap.SUBJECT,
            "audience": "campus-application",
            "scopes": [{"resource": "campus-application", "operation": "use"}],
            "expiresAt": 100,
            "integrity": True,
        }
        and (directory / "installed-demo-credential.json").read_bytes()
        == (directory / "input/demo-credential.json").read_bytes(),
        "Declared local credential installation disagrees.",
    )
    check_network(directory, observations, commands)
    eap_evidence = admission.check_eap(directory / "eap", observations["eap"])
    eap_frames = eap_evidence["phases"][0]["frames"]
    raw = eap.read_lines(directory / "frames.jsonl", observations["eap"])
    frames = [decode_frame(row, index) for index, row in enumerate(raw, 1)]
    udp, icmp = (
        [row for row in frames if row["protocol"] == 17],
        [row for row in frames if row["protocol"] == 1],
    )
    require(len(udp) == 14 and len(icmp) == 3, "Unexpected native UDP or ICMP frame count.")
    traces = parse_traces(directory / "trace.txt")
    require(
        (directory / "trace-errors.txt").read_text() == ""
        and observations["traceCommand"]
        == ["ip", "netns", "exec", "auth", "nft", "monitor", "trace"],
        "Native hook trace producer failed or changed.",
    )
    samples, used_frames, used_traces = [], set(), set()

    def sample(label, config, incoming, outgoing, disposition, state):
        matching = [
            index
            for index, trace in enumerate(traces)
            if trace["stages"][0]["ipId"] == incoming["ipId"]
            and trace["stages"][0]["packet"] == incoming["header"]
        ]
        require(
            len(matching) == 1 and matching[0] not in used_traces,
            "Raw ingress has no unique native hook episode.",
        )
        used_traces.add(matching[0])
        trace = traces[matching[0]]
        destination, source, next_hop = check_trace(trace, incoming, outgoing, disposition)
        if disposition == "ttlExpired":
            quotes = [frame for frame in icmp if frame["quotedIpId"] == incoming["ipId"]]
            require(
                len(quotes) == 1
                and quotes[0]["interface"] == incoming["interface"]
                and incoming["timeNs"] <= quotes[0]["timeNs"] < state["command"]["startNs"],
                "ICMP Time Exceeded observation is outside its selected drop interval.",
            )
        used_frames.add(incoming["source"])
        if outgoing:
            used_frames.add(outgoing["source"])
        samples.append(
            {
                "label": label,
                "config": config,
                "zone": 0,
                "raw": incoming["raw"],
                "observed": {
                    "classification": None,
                    "fresh": None,
                    "afterDestination": destination,
                    "afterSource": source,
                    "nextHop": next_hop,
                    "disposition": disposition,
                    "output": outgoing["raw"] if outgoing else None,
                },
                "stateFile": state["file"],
                "trace": trace,
                "ingress": incoming,
                "egress": outgoing,
            }
        )

    def pick(group, payload, interface, kind):
        found = [
            row
            for row in group
            if row["payload"] == payload
            and row["interface"] == interface
            and row["packetType"] == kind
        ]
        require(len(found) == 1, "Missing or duplicate selected raw datagram.")
        return found[0]

    def socket_result(record, window, expected):
        admission.interval(record, window)
        require(
            record["result"] == expected, "Native socket tuple, payload, TTL, or outcome disagrees."
        )

    def socket_header(header, payload, ttl=None):
        result = {key: value for key, value in header.items() if key != "protocol"}
        return {**result, "payload": payload, **({"ttl": ttl} if ttl is not None else {})}

    def load(record, name, policy, replace=True):
        copied_command(record, commands)
        admission.successful_command(
            record, ["ip", "netns", "exec", "auth", "nft", "-j", "-f", f"{BASE}/{name}-load.json"]
        )
        require(
            record["input"] == f"input/{policy}.json" and record["batch"] == f"{name}-load.json",
            "Misbound generated policy load.",
        )
        source = read_json(directory / record["input"])["nftables"]
        expected = (
            [source[0], {"delete": {"table": {"family": "ip", "name": "netlib"}}}, *source[1:]]
            if replace
            else source
        )
        require(
            read_json(directory / record["batch"]) == {"nftables": expected},
            "Native transaction changed the generated policy.",
        )

    stages = observations["stages"]
    require(
        [stage["stage"] for stage in stages] == list(admission.STAGES),
        "Missing or reordered authentication stage.",
    )
    require(
        not read_state(directory, observations["initial"], commands)
        and observations["initial"]["command"]["endNs"] < stages[0]["load"]["startNs"],
        "Initial visible conntrack state must be empty before the first policy load and packet.",
    )
    require(
        all(
            eap_frames[0]["timeNs"] <= source["timeNs"] < stages[1]["startNs"]
            for source in eap_evidence["phases"][0]["methodEvidence"]["source"]
        ),
        "Native TLS method evidence is outside the authenticated checkpoint.",
    )
    reports, configs, previous_end, binding = [], [], 0, None
    for index, stage in enumerate(stages):
        name, permitted = stage["stage"], index == 2
        admission.interval(stage, observations["eap"])
        require(
            stage["startNs"] > previous_end
            and stage["policy"] == ("permit" if permitted else "deny"),
            "Stage ordering or active gate disagrees.",
        )
        previous_end = stage["endNs"]
        request_payload, reply_payload = f"wire-nat:{name}:request", f"wire-nat:{name}:reply"
        socket_result(stage["sent"], stage, socket_header(ORIGINAL, request_payload, 64))
        socket_result(
            stage["server"], stage, socket_header(WIRE, request_payload) if permitted else None
        )
        socket_result(
            stage["client"], stage, socket_header(PEER_REPLY, reply_payload) if permitted else None
        )
        require(
            stage["sent"]["endNs"] <= stage["server"]["startNs"],
            "Server receive begins before native send completion.",
        )
        group = [row for row in udp if stage["startNs"] < row["timeNs"] < stage["endNs"]]
        require(
            len(group) == (5 if permitted else 1)
            and all(
                row["timeNs"] >= stage["sent"]["startNs"]
                and row["udpChecksum"]["status"] == "valid"
                for row in group
            ),
            "Unexpected main-stage raw UDP count, checksum, or timing.",
        )
        incoming = pick(group, request_payload, "auth0", 0)
        require(
            incoming["ttl"] == stage["sent"]["result"]["ttl"],
            "Native socket TTL contradicts the retained request wire bytes.",
        )
        outgoing = pick(group, request_payload, "service0", 4) if permitted else None
        state = read_state(directory, stage["state"], commands)
        admission.interval(stage["state"]["command"], stage)
        require(
            stage["client"]["endNs"] < stage["state"]["command"]["startNs"],
            "Final stage snapshot precedes the UDP result.",
        )
        if index < 2:
            require(
                not state and stage["lowTTLReply"] is None and stage["reply"] is None,
                "Denied fresh packet became a confirmed NAT flow.",
            )
            require(
                all(
                    stage[key]["endNs"] - stage[key]["startNs"] >= 200_000_000
                    for key in ("server", "client")
                ),
                "Denied fresh traffic lacks a socket timeout.",
            )
        if permitted:
            low = stage["lowTTLReply"]
            before, after = (
                read_state(directory, low["before"], commands),
                read_state(directory, low["after"], commands),
            )
            require(
                len(before) == len(after) == len(state) == 1
                and before[0]["status"] == 440
                and after[0]["status"] == state[0]["status"] == 442
                and before[0]["id"] == after[0]["id"] == state[0]["id"],
                "TTL-one reply must mark the same confirmed NAT flow seen before normal reply.",
            )
            binding = state[0]
            low_payload = f"wire-nat:{name}:ttl-one-reply"
            socket_result(low["sent"], stage, socket_header(WIRE_REPLY, low_payload, 1))
            socket_result(low["client"], stage, None)
            socket_result(stage["reply"], stage, socket_header(WIRE_REPLY, reply_payload, 64))
            require(
                stage["server"]["endNs"]
                < low["before"]["command"]["startNs"]
                < low["before"]["command"]["endNs"]
                < low["sent"]["startNs"]
                < low["sent"]["endNs"]
                <= low["client"]["startNs"]
                < low["client"]["endNs"]
                < low["after"]["command"]["startNs"]
                < low["after"]["command"]["endNs"]
                < stage["reply"]["startNs"]
                < stage["reply"]["endNs"]
                <= stage["client"]["startNs"],
                "NAT request, TTL-one reply, snapshots, and normal reply are unordered.",
            )
            require(
                low["client"]["endNs"] - low["client"]["startNs"] >= 200_000_000,
                "TTL-one reply lacks a measured client timeout.",
            )
            sample(f"{name}-request", name, incoming, outgoing, "forwarded", low["before"])
            low_in = pick(group, low_payload, "service0", 0)
            require(
                low_in["ttl"] == low["sent"]["result"]["ttl"]
                and low["sent"]["startNs"] <= low_in["timeNs"] < low["after"]["command"]["startNs"],
                "Native socket TTL or send interval contradicts the low-TTL reply wire bytes.",
            )
            sample("cached-ttl-one-reply", name, low_in, None, "ttlExpired", low["after"])
            normal_reply = pick(group, reply_payload, "service0", 0)
            require(
                normal_reply["ttl"] == stage["reply"]["result"]["ttl"]
                and normal_reply["timeNs"] >= stage["reply"]["startNs"],
                "Native socket TTL contradicts the retained normal reply wire bytes.",
            )
            sample(
                f"{name}-reply",
                name,
                normal_reply,
                pick(group, reply_payload, "auth0", 4),
                "forwarded",
                stage["state"],
            )
        else:
            if index == 3:
                require(
                    len(state) == 1
                    and binding
                    and state[0]["id"] == binding["id"]
                    and state[0]["status"] == 442,
                    "Logoff must retain the same replied NAT flow while dropping the request.",
                )
            sample(f"{name}-request", name, incoming, None, "forwardDrop", stage["state"])
        if index == 1:
            require(stage["load"] is None, "Unexpected gate change before credential installation.")
        else:
            load(stage["load"], name, stage["policy"], index != 0)
            require(
                stage["load"]["endNs"] < stage["startNs"],
                "Generated gate load is later than the packet probe.",
            )
        exports = stage["exports"]
        for export in exports.values():
            require(
                stage["client"]["endNs"]
                < export["command"]["startNs"]
                < export["command"]["endNs"]
                < stage["state"]["command"]["startNs"],
                "Native config export is outside the measured checkpoint.",
            )
        ingress = [row for row in udp if row["packetType"] == 0 and row["timeNs"] < stage["endNs"]]
        verify_exports(directory, exports, commands, policies[stage["policy"]], ingress)
        before_count = sum(frame["timeNs"] < stage["sent"]["startNs"] for frame in eap_frames)
        require(before_count == (0, 16, 16, 18)[index], "EAP prefix does not match the NAT stage.")
        configs.append(
            {
                "id": name,
                "forwardFile": exports["firewall"]["file"],
                "natFile": exports["nat"]["file"],
                "lateFile": exports["late"]["file"],
            }
        )
        reports.append(
            {
                "name": name,
                "eapFramesBeforeSend": before_count,
                "credentialInstalled": index >= 2,
                "delivered": permitted,
                "firewallFile": exports["firewall"]["file"],
                "observations": stage,
                "udpFrames": group,
                "icmpFrames": [
                    row for row in icmp if stage["startNs"] < row["timeNs"] < stage["endNs"]
                ],
            }
        )
    for key, expected in (
        (
            "credentialInstall",
            [
                "install",
                "-m",
                "0644",
                "/task/admission/input/demo-credential.json",
                "/run/netlib-admission/demo-credential.json",
            ],
        ),
        (
            "logoff",
            [
                "ip",
                "netns",
                "exec",
                "peer",
                "wpa_cli",
                "-p",
                "/run/netlib-eap/supplicant",
                "-i",
                "peer0",
                "logoff",
            ],
        ),
    ):
        copied_command(observations[key], commands)
        admission.successful_command(observations[key], expected)
    station_command = [
        "ip",
        "netns",
        "exec",
        "auth",
        "hostapd_cli",
        "-p",
        "/run/netlib-eap/hostapd",
        "-i",
        "auth0",
        "sta",
        eap.PEER,
    ]
    stations = [row for row in commands if row["command"] == station_command]
    status_command = [
        "ip",
        "netns",
        "exec",
        "peer",
        "wpa_cli",
        "-p",
        "/run/netlib-eap/supplicant",
        "-i",
        "peer0",
        "status",
    ]
    statuses = [row for row in commands if row["command"] == status_command]
    require(
        len(stations) == 2 and len(statuses) == 1,
        "Missing or duplicate native authorization status export.",
    )
    for record, filename in (
        (stations[0], "authorized-station.txt"),
        (stations[1], "logged-off-station.txt"),
        (statuses[0], "supplicant-status.txt"),
    ):
        require(
            record["stdout"] == (directory / "eap" / filename).read_text(),
            "Native status export stdout contradicts its saved authorization state.",
        )
    require(
        stations[0]["endNs"] < stages[1]["startNs"]
        and statuses[0]["endNs"] < stages[1]["startNs"]
        and observations["logoff"]["endNs"]
        < stations[1]["startNs"]
        < stations[1]["endNs"]
        < stages[3]["load"]["startNs"],
        "Native status export lies outside its authorization checkpoint.",
    )
    logoff_frame = eap_frames[eap_evidence["phases"][0]["logoffFrame"] - 1]
    require(
        observations["logoff"]["startNs"] <= logoff_frame["timeNs"] < stages[3]["load"]["startNs"],
        "Deny load does not follow the captured EAPOL Logoff.",
    )
    require(
        stages[1]["endNs"]
        < observations["credentialInstall"]["startNs"]
        < observations["credentialInstall"]["endNs"]
        < stages[2]["load"]["startNs"]
        and stages[2]["endNs"]
        < observations["logoff"]["startNs"]
        < observations["logoff"]["endNs"]
        < stages[3]["load"]["startNs"],
        "Credential or Logoff policy cutover is out of order.",
    )
    erase = observations["erase"]
    copied_command(erase["command"], commands)
    require(
        erase["command"]["command"]
        == [
            "ip",
            "netns",
            "exec",
            "auth",
            "conntrack",
            "-D",
            "-f",
            "ipv4",
            "-p",
            "udp",
            "--orig-src",
            "192.0.2.2",
            "--orig-dst",
            "203.0.113.2",
            "--sport",
            "41000",
            "--dport",
            "8080",
            "--zone",
            "0",
        ]
        and re.search(r"1 flow entries have been deleted", erase["command"]["stderr"]),
        "Administrative erase did not target exactly the selected zone-zero flow.",
    )
    require(
        stages[-1]["endNs"]
        < erase["command"]["startNs"]
        < erase["command"]["endNs"]
        < erase["state"]["command"]["startNs"]
        and not read_state(directory, erase["state"], commands),
        "Targeted erase lacks an ordered empty raw state snapshot.",
    )
    load(observations["ttlLoad"], "ttl-probes", "permit")
    ttl_probes = observations["ttlProbes"]
    require(
        [(probe["name"], probe["ttl"]) for probe in ttl_probes]
        == [("ttl-zero", 0), ("ttl-one", 1), ("ttl-two", 2), ("udp-zero", 64)],
        "Missing or reordered TTL and omission probes.",
    )
    require(
        erase["state"]["command"]["endNs"]
        < observations["ttlLoad"]["startNs"]
        < observations["ttlLoad"]["endNs"]
        < ttl_probes[0]["startNs"],
        "Isolated TTL permit phase precedes the explicit erase.",
    )
    verify_exports(
        directory,
        observations["ttlExports"],
        commands,
        policies["permit"],
        [row for row in udp if row["packetType"] == 0 and row["timeNs"] < ttl_probes[0]["startNs"]],
    )
    configs.append(
        {
            "id": "ttl-probes",
            "forwardFile": observations["ttlExports"]["firewall"]["file"],
            "natFile": observations["ttlExports"]["nat"]["file"],
            "lateFile": observations["ttlExports"]["late"]["file"],
        }
    )
    require(
        all(
            observations["ttlLoad"]["endNs"]
            < export["command"]["startNs"]
            < export["command"]["endNs"]
            < ttl_probes[0]["startNs"]
            for export in observations["ttlExports"].values()
        ),
        "TTL configuration export is outside the load-to-probe interval.",
    )
    ttl_reports, new_binding = [], None
    previous_end = observations["ttlLoad"]["endNs"]
    for index, probe in enumerate(ttl_probes):
        admission.interval(probe, observations["eap"])
        require(previous_end < probe["startNs"], "TTL probe windows overlap.")
        previous_end = probe["endNs"]
        before, after = (
            read_state(directory, probe["before"], commands),
            read_state(directory, probe["after"], commands),
        )
        source = read_json(directory / probe["input"])
        require(
            probe["input"] == f"{probe['name']}-input.json" and source["name"] == probe["name"],
            "Misbound TTL raw source.",
        )
        sent = probe["sent"]
        copied_command(sent, commands)
        admission.successful_command(
            sent,
            [
                "ip",
                "netns",
                "exec",
                "peer",
                "python3",
                "/task/wire/exercise.py",
                "raw-send",
                f"{BASE}/{probe['input']}",
            ],
        )
        sender = json.loads(sent["stdout"])
        admission.interval(sender, sent)
        require(
            sender["raw"] == source["raw"]
            and type(sender["bytesSent"]) is int
            and sender["bytesSent"] == len(bytes.fromhex(source["raw"])),
            "Raw TTL sender bytes disagree.",
        )
        require(
            probe["startNs"]
            < probe["before"]["command"]["startNs"]
            < probe["before"]["command"]["endNs"]
            < sent["startNs"]
            < sent["endNs"]
            <= probe["server"]["startNs"]
            < probe["server"]["endNs"]
            < probe["after"]["command"]["startNs"]
            < probe["after"]["command"]["endNs"]
            < probe["endNs"],
            "TTL send, socket observation, and before/after snapshots are unordered.",
        )
        group = [row for row in udp if probe["startNs"] < row["timeNs"] < probe["endNs"]]
        require(
            len(group) == (1 if index < 2 else 2),
            "TTL boundary has unexpected selected UDP egress.",
        )
        incoming = next(
            (row for row in group if row["interface"] == "auth0" and row["packetType"] == 0), None
        )
        outgoing = next(
            (row for row in group if row["interface"] == "service0" and row["packetType"] == 4),
            None,
        )
        require(
            incoming is not None
            and incoming["raw"] == source["raw"]
            and incoming["ttl"] == probe["ttl"]
            and incoming["ipId"] == 0xFC00 + index
            and incoming["udpChecksum"]["status"] == ("omitted" if index == 3 else "valid"),
            "TTL input bytes, boundary, or omission disagrees.",
        )
        if index < 2:
            require(
                not before
                and not after
                and outgoing is None
                and probe["server"]["result"] is None
                and probe["server"]["endNs"] - probe["server"]["startNs"] >= 200_000_000,
                "TTL zero/one unexpectedly confirmed or delivered the fresh packet.",
            )
        else:
            require(
                len(after) == 1
                and after[0]["status"] == 440
                and outgoing is not None
                and outgoing["ttl"] == probe["ttl"] - 1
                and probe["server"]["result"] == socket_header(WIRE, incoming["payload"]),
                "TTL-two or omission forwarding result disagrees.",
            )
            if index == 2:
                require(
                    not before and after[0]["id"] != binding["id"],
                    "TTL-two must confirm a fresh binding after explicit erase.",
                )
                new_binding = after[0]
            else:
                require(
                    len(before) == 1
                    and before[0]["id"] == after[0]["id"] == new_binding["id"]
                    and outgoing["udpChecksum"]["status"] == "omitted",
                    "Cached NAT did not preserve UDP checksum omission.",
                )
        sample(
            probe["name"],
            "ttl-probes",
            incoming,
            outgoing,
            "ttlExpired" if index < 2 else "forwarded",
            probe["after"],
        )
        ttl_reports.append(
            {
                "name": probe["name"],
                "observations": probe,
                "udpFrames": group,
                "icmpFrames": [
                    row for row in icmp if probe["startNs"] < row["timeNs"] < probe["endNs"]
                ],
            }
        )
    require(
        len(used_traces) == 10 and len(used_frames) == len(udp),
        "Unaccounted trace episode or UDP frame.",
    )
    expired = [row for row in samples if row["observed"]["disposition"] == "ttlExpired"]
    require(
        len(expired) == len(icmp) == 3
        and all(
            sum(frame["quotedIpId"] == row["ingress"]["ipId"] for frame in icmp) == 1
            for row in expired
        ),
        "TTL drops lack unique native ICMP Time Exceeded observations.",
    )
    offload_context = {"stages": [{"observations": stages[0]}]}
    settings = wire.check_offloads(directory, offload_context)
    return {
        "schema": 1,
        "scope": "checked-native-wire-nat-evidence",
        "initialFile": observations["initial"]["file"],
        "eapEvidence": eap_evidence,
        "credential": credential,
        "credentialInstall": observations["credentialInstall"],
        "logoff": observations["logoff"],
        "stages": reports,
        "routing": {
            "version": "6.19.0",
            "routesFile": "network-auth-routes.json",
            "bindings": [
                {"device": "auth0", "nextNode": "peer", "gateway": None},
                {"device": "service0", "nextNode": "server", "gateway": None},
            ],
        },
        "configs": configs,
        "packetSamples": samples,
        "erase": {
            "beforeLabel": "ttl-zero",
            "zone": 0,
            "raw": samples[2]["raw"],
            "stateFile": erase["state"]["file"],
            "command": erase["command"],
        },
        "ttlProbes": ttl_reports,
        "offloads": settings,
        "frameCount": len(frames),
        "udpFrameCount": len(udp),
        "icmpFrameCount": len(icmp),
        "icmpFrames": icmp,
        "limits": [
            "finite-private-wired-NAT-capture",
            "IHL-five-unfragmented-UDP-with-MTU-at-least1500",
            "classification-and-fresh-unasserted",
            "native-hook-checkpoints-not-fabricated-middle-wire-bytes",
            "ICMP-observed-but-not-an-ICMP-implementation-model",
            "isolated-visible-table-and-current-binding-assumptions",
            "no-TLS-cryptographic-capture-authenticity-or-kernel-refinement-proof",
        ],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture-dir", type=Path, default=DIRECTORY / "native")
    parser.add_argument("--input-dir", type=Path, default=DIRECTORY)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        evidence = check_capture(args.capture_dir, input_directory=args.input_dir)
        if args.output:
            args.output.write_text(json.dumps(evidence, indent=2) + "\n")
        print(
            f"Verified {evidence['udpFrameCount']} UDP frames, {evidence['icmpFrameCount']} ICMP observations, and ten NAT/TTL packet episodes."
        )
    except (
        ValueError,
        OSError,
        KeyError,
        TypeError,
        IndexError,
        OverflowError,
        StopIteration,
    ) as error:
        print(f"wire NAT evidence: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
