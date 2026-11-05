"""Independently check native generated ICMP bytes, NAT boundaries, and evidence."""

import argparse
import ipaddress
import json
import re
import shlex
import sys
from pathlib import Path

import check_admission_capture as admission
import check_eap_capture as eap
import check_lifecycle_capture as lifecycle
import check_mtu_capture as mtu
import check_wire_capture as wire
import check_wire_nat_capture as nat

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/icmp"
EvidenceError, require = admission.EvidenceError, admission.require
ORIGINAL, WIRE, WIRE_REPLY, PEER_REPLY = nat.ORIGINAL, nat.WIRE, nat.WIRE_REPLY, nat.PEER_REPLY
BASE, MTUS = nat.BASE, mtu.MTUS
read_json, copied_command, read_state = nat.read_json, nat.copied_command, nat.read_state
reassemble_fragments, check_links, check_network = (
    mtu.reassemble_fragments,
    mtu.check_links,
    mtu.check_network,
)
EXTRA = [
    ("quote-short-odd", 63, 0x03, False, False),
    ("quote-short-even", 64, 0x1F, False, False),
    ("quote-cap-minus-one", 547, 0xAB, False, False),
    ("quote-cap-exact", 548, 0x7E, False, False),
    ("quote-cap-plus-one", 549, 0x03, False, False),
    ("quote-ip-576", 576, 0x1F, False, False),
    ("quote-ip-577-zero", 577, 0xAB, True, False),
    ("quote-reply-odd", 575, 0x03, False, True),
]


def decode_frame(row, index):
    result = mtu.decode_frame(row, index)
    if result["protocol"] == 17:
        return result
    quote = bytes.fromhex(result["quoteHex"])
    size = int.from_bytes(quote[2:4], "big")
    udp = quote[20:]
    udp_size = int.from_bytes(udp[4:6], "big")
    value = int.from_bytes(udp[6:8], "big")
    require(
        28 <= len(quote) <= size
        and udp_size == size - 20
        and int.from_bytes(quote[6:8], "big") in (0, 0x4000),
        "Invalid quoted IPv4/UDP lengths or flags.",
    )
    complete = len(quote) == size
    pseudo = quote[12:20] + bytes((0, 17)) + udp_size.to_bytes(2, "big")
    require(
        not complete or value == 0 or wire.folded_sum(pseudo + udp) == 65535,
        "Invalid complete quoted UDP checksum.",
    )
    result.update(
        icmpChecksum="valid",
        quoteLength=len(quote),
        quoteComplete=complete,
        quotedHeader={
            "source": str(ipaddress.IPv4Address(quote[12:16])),
            "destination": str(ipaddress.IPv4Address(quote[16:20])),
            "protocol": 17,
            "sourcePort": int.from_bytes(udp[:2], "big"),
            "destinationPort": int.from_bytes(udp[2:4], "big"),
        },
        quotedIpLength=size,
        quotedUdpLength=udp_size,
        quotedUdpChecksum={
            "value": value,
            "status": "omitted" if value == 0 else "valid" if complete else "partial",
        },
        quotedIpChecksum="valid",
    )
    return result


def trace_tos(tokens):
    dscp = lifecycle.tokens_value(tokens, ["ip", "dscp"])
    dscp = int(dscp, 16) if dscp.startswith("0x") else int(dscp[2:]) * 8
    ecn = lifecycle.tokens_value(tokens, ["ip", "ecn"])
    return dscp << 2 | {"not-ect": 0, "ect1": 1, "ect0": 2, "ce": 3}[ecn]


def check_forward_trace(trace, incoming, output, disposition):
    stages = trace["stages"]
    payload = bytes.fromhex(incoming["payloadHex"])
    for stage in stages:
        header = stage["packet"]
        udp = (
            header["sourcePort"].to_bytes(2, "big")
            + header["destinationPort"].to_bytes(2, "big")
            + incoming["udpLength"].to_bytes(2, "big")
            + bytes(2)
            + payload
        )
        pseudo = (
            ipaddress.IPv4Address(header["source"]).packed
            + ipaddress.IPv4Address(header["destination"]).packed
            + bytes((0, 17))
            + len(udp).to_bytes(2, "big")
        )
        checksum = (
            0
            if incoming["udpChecksum"]["status"] == "omitted"
            else (65535 - wire.folded_sum(pseudo + udp)) or 65535
        )
        require(
            header["protocol"] == 17 and stage["udpChecksum"] == checksum,
            "Native whole UDP hook checksum disagrees with its tuple and complete payload.",
        )
        prerouting = stage["chain"] in {"before", "prerouting", "destination", "afterDestination"}
        require(
            all(stage[key] == incoming[key] for key in ("ipId", "ipLength", "udpLength", "tos"))
            and stage["ttl"] == incoming["ttl"] - (not prerouting)
            and stage["iif"] == incoming["fragments"][0]["interface"]
            and stage["oif"]
            == (
                None if prerouting else "auth0" if incoming["header"] == WIRE_REPLY else "service0"
            ),
            "Native whole UDP hook IPv4 metadata or interface disagrees.",
        )
    late = [stage for stage in stages if stage["table"] == "netlib_icmp_late"]
    require(
        len(late) == (1 if disposition == "forwarded" else 0),
        "UDP ICMP late hook must occur once after forwarding and never after an early drop.",
    )
    if late:
        require(
            late[0]["chain"] == "late"
            and late[0]["packet"] == output["header"]
            and len(late[0]["verdicts"]) == 1
            and late[0]["verdicts"][0]["kind"] == "policy"
            and late[0]["verdicts"][0]["verdict"] == "accept",
            "UDP ICMP late hook tuple or terminal verdict disagrees.",
        )
        require(
            {(stage["table"], stage["chain"]) for stage in stages[-2:]}
            == {("netlib_icmp_late", "late"), ("netlib_late", "late")},
            "UDP ICMP late hook is outside the final POSTROUTING visits.",
        )
    delegated = {
        **trace,
        "stages": [stage for stage in stages if stage["table"] != "netlib_icmp_late"],
    }
    return mtu.check_forward_trace(delegated, incoming, output, disposition)


def parse_traces(path):
    groups = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        matched = re.fullmatch(r"trace id ([0-9a-f]{8}) ip (\S+) (\S+) (.*)", line)
        require(matched is not None, f"Malformed native trace line {number}.")
        if (matched[2], matched[3]) in (
            ("netlib_trace", "before"),
            ("netlib_icmp", "outputBefore"),
        ) and matched[4].startswith("packet: "):
            groups.append((matched[1], []))
        require(groups and groups[-1][0] == matched[1], "Interleaved native packet traces.")
        groups[-1][1].append((number, line))
    udp, errors = [], []
    for episode, (identifier, lines) in enumerate(groups):
        first = lines[0][1]
        if " netlib_trace before packet: " in first:
            selected = lines
            try:
                trace = lifecycle.parse_trace("\n".join(line for _, line in selected))[0]
            except ValueError as error:
                raise EvidenceError(f"Native UDP trace: {error}") from error
            trace["source"] = f"trace.txt:{selected[0][0]}"
            for stage in trace["stages"]:
                original, line = selected[stage["line"] - 1]
                stage["line"] = original
                tokens = shlex.split(line)
                stage["tos"] = trace_tos(tokens)
                for key, prefix in (
                    ("ttl", ["ip", "ttl"]),
                    ("ipLength", ["ip", "length"]),
                    ("udpLength", ["udp", "length"]),
                    ("udpChecksum", ["udp", "checksum"]),
                ):
                    stage[key] = int(lifecycle.tokens_value(tokens, prefix))
                for verdict in stage["verdicts"]:
                    verdict["line"] = selected[verdict["line"] - 1][0]
            udp.append(trace)
        else:
            require(
                " netlib_icmp outputBefore packet: " in first, "Unaccounted native output trace."
            )
            stages = []
            for number, line in lines:
                matched = re.fullmatch(r"trace id [0-9a-f]{8} ip (\S+) (\S+) (.*)", line)
                table, chain, body = matched.groups()
                if body.startswith("packet: "):
                    tokens = shlex.split(body[8:])

                    def value(prefix):
                        return lifecycle.tokens_value(tokens, prefix)

                    stages.append(
                        {
                            "table": table,
                            "chain": chain,
                            "line": number,
                            "oif": value(["oif"]),
                            "sourceAddress": value(["ip", "saddr"]),
                            "destinationAddress": value(["ip", "daddr"]),
                            "ipId": int(value(["ip", "id"])),
                            "ipLength": int(value(["ip", "length"])),
                            "ttl": int(value(["ip", "ttl"])),
                            "tos": trace_tos(tokens),
                            "icmpRest": (int(value(["icmp", "id"])) << 16)
                            | int(value(["icmp", "sequence"])),
                            "icmpType": {"time-exceeded": 11, "destination-unreachable": 3}[
                                value(["icmp", "type"])
                            ],
                            "icmpCode": int(value(["icmp", "code"])),
                            "verdicts": [],
                        }
                    )
                else:
                    require(
                        stages and (stages[-1]["table"], stages[-1]["chain"]) == (table, chain),
                        "Orphan ICMP trace verdict.",
                    )
                    require(
                        re.fullmatch(
                            r"policy accept ?|rule .* \(verdict (?:continue|accept)\)", body
                        ),
                        "Unexpected ICMP output verdict.",
                    )
                    stages[-1]["verdicts"].append({"text": body.rstrip(), "line": number})
            require(
                episode > 0 and " netlib_trace before packet: " in groups[episode - 1][1][0][1],
                "ICMP output does not immediately follow an isolated UDP ingress episode.",
            )
            errors.append(
                {
                    "id": identifier,
                    "source": f"trace.txt:{lines[0][0]}",
                    "stages": stages,
                    "inputTraceSource": f"trace.txt:{groups[episode - 1][1][0][0]}",
                }
            )
    require(len(udp) == 20 and len(errors) == 12, "Unexpected native UDP or ICMP trace count.")
    return udp, errors


def check_settings(directory, observations, commands):
    write, read = observations["icmpSettingsWrite"], observations["icmpSettingsReadback"]
    for row in (write, read):
        copied_command(row, commands)
        require(
            row["endNs"] < observations["initial"]["command"]["startNs"],
            "ICMP sysctl readback follows traffic.",
        )
    admission.successful_command(
        write,
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "sh",
            "-c",
            "echo 0 > /tmp/netlib-proc/sys/net/ipv4/icmp_errors_use_inbound_ifaddr; "
            "echo 0 > /tmp/netlib-proc/sys/net/ipv4/icmp_ratelimit; "
            "echo 0 > /tmp/netlib-proc/sys/net/ipv4/icmp_ratemask",
        ],
    )
    admission.successful_command(
        read,
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "sysctl",
            "net.ipv4.icmp_errors_use_inbound_ifaddr",
            "net.ipv4.icmp_ratelimit",
            "net.ipv4.icmp_ratemask",
            "net.ipv4.ip_default_ttl",
        ],
    )
    expected = "net.ipv4.icmp_errors_use_inbound_ifaddr = 0\nnet.ipv4.icmp_ratelimit = 0\nnet.ipv4.icmp_ratemask = 0\nnet.ipv4.ip_default_ttl = 64\n"
    require(
        write["endNs"] < read["startNs"]
        and read["stdout"] == (directory / "icmp-settings.txt").read_text() == expected,
        "ICMP settings stdout or values disagree.",
    )
    return {
        "quoteLimit": 548,
        "outerTtl": 64,
        "outerDontFragment": False,
        "errorsUseInboundIfaddr": 0,
        "rateLimit": 0,
        "rateMask": 0,
        "tosMask": 0x1E,
        "tosPrecedence": 0xC0,
        "settingsFile": "icmp-settings.txt",
        "settingsReadback": read,
    }


def check_error(error, incoming, disposition, profile, trace):
    original = incoming["fragments"][0]
    length = min(incoming["ipLength"], min(MTUS[original["interface"]], 576) - 28)
    require(
        error["quoteLength"] == length
        and error["ipLength"] == length + 28
        and error["quotedHeader"] == incoming["header"]
        and error["quotedUdpChecksum"]["value"] == incoming["udpChecksum"]["value"]
        and error["sourceAddress"] == incoming["header"]["destination"]
        and error["destinationAddress"] == incoming["header"]["source"]
        and error["ttl"] == profile["outerTtl"]
        and error["dontFragment"] == profile["outerDontFragment"]
        and error["tos"] == (incoming["tos"] & profile["tosMask"]) | profile["tosPrecedence"],
        "Generated ICMP quote boundary, NAT addresses, TOS, TTL, or flags disagree.",
    )
    stages = trace["stages"]
    keys = [(row["table"], row["chain"]) for row in stages]
    prefix = [
        ("netlib_icmp", "outputBefore"),
        ("netlib_icmp", "outputRelated"),
        ("netlib_icmp_output", "output"),
        ("netlib_icmp", "outputAfter"),
        ("netlib_trace", "beforeSource"),
        ("netlib_trace", "afterSource"),
    ]
    require(
        keys[:6] == prefix
        and set(keys[6:]) == {("netlib_late", "late"), ("netlib_icmp_late", "late")}
        and len(keys) == 8,
        "Unexpected ICMP LOCAL_OUT/POSTROUTING hook order.",
    )
    initial_source = "192.0.2.1" if error["interface"] == "auth0" else "198.51.100.1"
    for index, stage in enumerate(stages):
        terminal = (
            "rule meta l4proto icmp ct state related accept (verdict accept)"
            if index == 2
            else "policy accept"
        )
        require(
            stage["verdicts"] and stage["verdicts"][-1]["text"] == terminal,
            "ICMP output trace lacks a terminal verdict.",
        )
        require(
            stage["sourceAddress"] == (initial_source if index < 5 else error["sourceAddress"])
            and stage["destinationAddress"] == error["destinationAddress"]
            and all(
                stage[key] == error[key]
                for key in ("ipId", "ipLength", "ttl", "tos", "icmpType", "icmpCode")
            )
            and stage["icmpRest"] == (600 if disposition == "mtuExceeded" else 0)
            and stage["oif"] == error["interface"]
            and stage["verdicts"],
            "ICMP source NAT or output hook packet metadata disagree.",
        )
    require(
        any(
            row["text"].startswith("rule ct state related counter ")
            for row in stages[1]["verdicts"]
        )
        and stages[2]["verdicts"][-1]["text"]
        == "rule meta l4proto icmp ct state related accept (verdict accept)",
        "ICMP output lacks measured RELATED classification and admission.",
    )
    error["outputTrace"] = trace


def icmp_objects(packets, size):
    chain = nat.chain
    return [
        {"table": {"family": "ip", "name": "netlib_icmp"}},
        chain("netlib_icmp", "outputBefore", "filter", "output", -301),
        chain("netlib_icmp", "outputRelated", "filter", "output", -199),
        chain("netlib_icmp", "outputAfter", "filter", "output", 1),
        {
            "rule": {
                "family": "ip",
                "table": "netlib_icmp",
                "chain": "outputBefore",
                "expr": [
                    {"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}},
                    {"mangle": {"key": {"meta": {"key": "nftrace"}}, "value": 1}},
                ],
            }
        },
        {
            "rule": {
                "family": "ip",
                "table": "netlib_icmp",
                "chain": "outputRelated",
                "comment": "ICMP_RELATED",
                "expr": [
                    {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": 4}},
                    {"counter": {"packets": packets, "bytes": size}},
                ],
            }
        },
    ]


def verify_exports(directory, exports, commands, policy, ingress):
    require(
        set(exports) == {"firewall", "nat", "late", "output", "icmpLate", "ruleset"},
        "Missing ICMP output configuration export.",
    )
    documents = {}
    tables = {
        "firewall": "netlib",
        "nat": "netlib_nat",
        "late": "netlib_late",
        "output": "netlib_icmp_output",
        "icmpLate": "netlib_icmp_late",
    }
    for kind, export in exports.items():
        copied_command(export["command"], commands)
        arguments = (
            ["list", "ruleset"] if kind == "ruleset" else ["list", "table", "ip", tables[kind]]
        )
        admission.successful_command(
            export["command"], ["ip", "netns", "exec", "auth", "nft", "-j", "-nn", *arguments]
        )
        require(
            export["command"]["stdout"] == (directory / export["file"]).read_text(),
            "ICMP configuration export stdout disagrees.",
        )
        documents[kind] = read_json(directory / export["file"])
    objects = {name: nat.objects(document) for name, document in documents.items()}
    expected_late = [
        {"table": {"family": "ip", "name": "netlib_late"}},
        nat.chain("netlib_late", "late", "filter", "postrouting", 200),
    ]
    expected_output = [
        {"table": {"family": "ip", "name": "netlib_icmp_output"}},
        nat.chain("netlib_icmp_output", "output", "filter", "output", 0, "drop"),
        {
            "rule": {
                "family": "ip",
                "table": "netlib_icmp_output",
                "chain": "output",
                "expr": [
                    {"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}},
                    {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": 4}},
                    {"accept": None},
                ],
            }
        },
    ]
    expected_icmp_late = [
        {"table": {"family": "ip", "name": "netlib_icmp_late"}},
        nat.chain("netlib_icmp_late", "late", "filter", "postrouting", 200),
    ]
    require(
        admission.canonical_table(documents["firewall"]) == policy
        and objects["nat"] == nat.expected_nat()
        and objects["late"] == expected_late
        and objects["output"] == expected_output
        and objects["icmpLate"] == expected_icmp_late,
        "Active ICMP output or forwarding policy disagrees.",
    )
    tracking = [
        {"table": {"family": "ip", "name": "netlib_tracking"}},
        nat.chain("netlib_tracking", "prerouting", "filter", "prerouting", -199),
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
    rows = [
        decode_frame(row, index)
        for index, row in enumerate(
            eap.read_lines(
                directory / "frames.jsonl", read_json(directory / "observations.json")["eap"]
            ),
            1,
        )
    ]
    errors = [
        row
        for row in rows
        if row["protocol"] == 1 and row["timeNs"] < exports["ruleset"]["command"]["startNs"]
    ]
    expected = (
        tracking
        + objects["nat"]
        + expected_late
        + nat.trace_objects()
        + icmp_objects(len(errors), sum(row["ipLength"] for row in errors))
        + expected_output
        + expected_icmp_late
        + objects["firewall"]
    )
    require(
        objects["ruleset"] == expected,
        "Complete ruleset contains an unaccounted hook, bypass, mutation, or RELATED counter disagreement.",
    )
    return documents


def check_capture(directory, *, input_directory=DIRECTORY):
    directory, input_directory = Path(directory), Path(input_directory)
    require(
        "iproute2-6.19.0" in (directory / "iproute2-version.txt").read_text()
        and (directory / "nftables-version.txt").read_text().startswith("nftables v1.1.3 "),
        "Native producer version disagrees.",
    )
    observations = read_json(directory / "observations.json")
    require(
        type(observations["schema"]) is int
        and observations["schema"] == 1
        and observations["scope"] == "icmp-error-forwarding",
        "Invalid MTU capture schema.",
    )
    commands = read_json(directory / "commands.json")
    previous_end = 0
    for record in commands:
        admission.interval(record)
        require(
            record["startNs"] > previous_end
            and type(record["returncode"]) is int
            and record["returncode"] == 0
            and (record["stderr"] == "" or record == observations["erase"]["command"]),
            "Native command history is unordered or failed.",
        )
        previous_end = record["endNs"]
    require(
        sum(row["command"][:5] == ["ip", "netns", "exec", "auth", "nft"] for row in commands) == 42,
        "Unexpected extra native firewall command.",
    )
    for name in ("requirements", "deny", "permit", "demo-credential"):
        require(
            (directory / "input" / f"{name}.json").read_bytes()
            == (input_directory / f"{name}.json").read_bytes(),
            "Immutable MTU policy input disagrees.",
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
        "Generated post-DNAT classes disagree.",
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
        "Declared local credential disagrees.",
    )
    check_network(directory, observations, commands)
    authentication = admission.check_eap(directory / "eap", observations["eap"])
    eap_frames = authentication["phases"][0]["frames"]
    frames = [
        decode_frame(row, index)
        for index, row in enumerate(
            eap.read_lines(directory / "frames.jsonl", observations["eap"]), 1
        )
    ]
    udp, icmp = (
        [row for row in frames if row["protocol"] == 17],
        [row for row in frames if row["protocol"] == 1],
    )
    require(len(udp) == 31 and len(icmp) == 12, "Unexpected captured UDP fragment or ICMP count.")
    traces, icmp_traces = parse_traces(directory / "trace.txt")
    profile = check_settings(directory, observations, commands)
    require(
        (directory / "trace-errors.txt").read_text() == ""
        and observations["traceCommand"]
        == ["ip", "netns", "exec", "auth", "nft", "monitor", "trace"],
        "Native trace producer disagrees.",
    )
    samples, used_frames, used_traces, used_icmp_traces = [], set(), set(), set()

    def family(group, interface, kind, *, payload=None, identifier=None):
        candidates = [
            row
            for row in group
            if row["interface"] == interface
            and row["packetType"] == kind
            and (identifier is None or row["ipId"] == identifier)
        ]
        families = []
        for ident in sorted({row["ipId"] for row in candidates}):
            value = reassemble_fragments([row for row in candidates if row["ipId"] == ident])
            if payload is None or value["payloadHex"] == payload.encode("ascii").hex():
                families.append(value)
        require(len(families) == 1, "Missing or ambiguous raw fragment family.")
        return families[0]

    def sample(label, config, incoming, output, disposition, state, links):
        require(
            len(incoming["fragments"]) == 1
            and not incoming["fragments"][0]["moreFragments"]
            and incoming["fragments"][0]["offsetBytes"] == 0,
            "The selected gateway input must be unfragmented.",
        )
        first = incoming["fragments"][0]
        require(
            all(
                frame["timeNs"] < state["command"]["startNs"]
                for frame in incoming["fragments"] + (output["fragments"] if output else [])
            ),
            "Selected fragment measurements extend past their post-step snapshot.",
        )
        require(
            first["ipLength"] <= MTUS[first["interface"]],
            "Input packet exceeds its measured ingress MTU.",
        )
        matching = [
            index
            for index, trace in enumerate(traces)
            if trace["stages"][0]["ipId"] == incoming["ipId"]
            and trace["stages"][0]["packet"] == incoming["header"]
            and trace["stages"][0]["ipLength"] == incoming["ipLength"]
            and trace["stages"][0]["udpChecksum"] == incoming["udpChecksum"]["value"]
        ]
        require(
            len(matching) == 1 and matching[0] not in used_traces,
            "Input lacks a unique complete hook episode.",
        )
        used_traces.add(matching[0])
        trace = traces[matching[0]]
        destination, source, next_hop = check_forward_trace(trace, incoming, output, disposition)
        quoted = [row for row in icmp if row["quotedIpId"] == incoming["ipId"]]
        if disposition in ("ttlExpired", "mtuExceeded"):
            require(
                len(quoted) == 1
                and quoted[0]["interface"] == first["interface"]
                and first["timeNs"] <= quoted[0]["timeNs"] < state["command"]["startNs"]
                and bytes.fromhex(first["raw"])[
                    14 : 14 + len(bytes.fromhex(quoted[0]["quoteHex"]))
                ].hex()
                == quoted[0]["quoteHex"],
                "ICMP quote, checksum, or measured drop interval disagrees.",
            )
            require(
                (quoted[0]["icmpType"], quoted[0]["icmpCode"])
                == ((11, 0) if disposition == "ttlExpired" else (3, 4)),
                "TTL versus MTU ICMP error priority disagrees.",
            )
            error_index = len(used_icmp_traces)
            require(
                error_index < len(icmp_traces)
                and icmp_traces[error_index]["inputTraceSource"] == trace["source"],
                "Generated ICMP lacks a distinct ordered output trace after its ingress.",
            )
            check_error(quoted[0], incoming, disposition, profile, icmp_traces[error_index])
            used_icmp_traces.add(error_index)
        else:
            require(not quoted, "Unexpected ICMP error for a forwarded or ACL-dropped datagram.")
        mtu = 600 if disposition == "mtuExceeded" else None
        if output:
            mtu = 600 if next_hop == "service" else 4096
            limit, aligned = mtu - 20, (mtu - 20) // 8 * 8
            remaining, sizes = output["udpLength"], []
            while remaining > limit:
                sizes.append(aligned)
                remaining -= aligned
            sizes.append(remaining)
            require(
                [len(bytes.fromhex(row["ipPayloadHex"])) for row in output["fragments"]] == sizes
                and all(row["ipLength"] <= mtu for row in output["fragments"]),
                "Fragment family does not match the measured MTU split boundary.",
            )
            require(
                not incoming["dontFragment"] or len(output["fragments"]) == 1,
                "DF traffic was fragmented.",
            )
        used_frames.add(first["source"])
        for row in output["fragments"] if output else []:
            used_frames.add(row["source"])
        samples.append(
            {
                "label": label,
                "config": config,
                "zone": 0,
                "raw": first["raw"],
                "observed": {
                    "icmpOutput": [row["raw"] for row in quoted],
                    "classification": None,
                    "fresh": None,
                    "afterDestination": destination,
                    "afterSource": source,
                    "nextHop": next_hop,
                    "mtu": mtu,
                    "disposition": disposition,
                    "output": [row["raw"] for row in output["fragments"]] if output else [],
                },
                "stateFile": state["file"],
                "linkMTUExports": links,
                "ingress": incoming,
                "outputFamily": output,
                "icmpObservations": quoted,
                "trace": trace,
            }
        )

    def expected_socket(header, payload, sent=False, ttl=64):
        result = {key: value for key, value in header.items() if key != "protocol"}
        return {
            **result,
            "payload": payload,
            **(
                {"ttl": ttl, "mtuDiscover": 0, "bytesSent": len(payload.encode("ascii"))}
                if sent
                else {}
            ),
        }

    def socket_record(record, window, expected):
        admission.interval(record, window)
        require(
            record["result"] == expected
            and (
                record["result"] is None
                or all(
                    type(record["result"][key]) is int
                    for key in (
                        "sourcePort",
                        "destinationPort",
                        *(["ttl", "mtuDiscover", "bytesSent"] if "ttl" in record["result"] else []),
                    )
                )
            ),
            "Native socket payload, TTL, PMTU mode, byte count, or result disagrees.",
        )

    def load(record, name, policy, replace=True):
        copied_command(record, commands)
        admission.successful_command(
            record, ["ip", "netns", "exec", "auth", "nft", "-j", "-f", f"{BASE}/{name}-load.json"]
        )
        require(
            record["input"] == f"input/{policy}.json" and record["batch"] == f"{name}-load.json",
            "Generated load is misbound.",
        )
        source = read_json(directory / record["input"])["nftables"]
        expected = (
            [source[0], {"delete": {"table": {"family": "ip", "name": "netlib"}}}, *source[1:]]
            if replace
            else source
        )
        require(
            read_json(directory / record["batch"]) == {"nftables": expected},
            "Applied transaction changed the generated policy.",
        )

    stages = observations["stages"]
    require(
        [stage["stage"] for stage in stages] == list(admission.STAGES),
        "Authentication stages are missing or reordered.",
    )
    require(
        not read_state(directory, observations["initial"], commands)
        and observations["initial"]["command"]["endNs"] < stages[0]["load"]["startNs"],
        "Initial raw conntrack state is not empty before selected traffic.",
    )
    require(
        all(
            eap_frames[0]["timeNs"] <= source["timeNs"] < stages[1]["startNs"]
            for source in authentication["phases"][0]["methodEvidence"]["source"]
        ),
        "Native method evidence is outside the authenticated checkpoint.",
    )
    reports, configs, binding, previous_end = [], [], None, 0
    for index, stage in enumerate(stages):
        name, permitted = stage["stage"], index == 2
        admission.interval(stage, observations["eap"])
        require(
            stage["startNs"] > previous_end
            and stage["policy"] == ("permit" if permitted else "deny"),
            "Native authentication gate or window disagrees.",
        )
        previous_end = stage["endNs"]
        payload = stage["sent"]["result"]["payload"]
        require(
            len(payload.encode("ascii")) == 1200 and payload.startswith(f"mtu:{name}-request|"),
            "Large native socket payload is not the selected 1200-byte request.",
        )
        socket_record(stage["sent"], stage, expected_socket(ORIGINAL, payload, True))
        socket_record(stage["server"], stage, expected_socket(WIRE, payload) if permitted else None)
        reply_payload = f"mtu:{name}:reply"
        socket_record(
            stage["client"],
            stage,
            expected_socket(PEER_REPLY, reply_payload) if permitted else None,
        )
        check_links(
            directory,
            stage["requestLinks"],
            f"{name}-request",
            commands,
            stage["startNs"],
            stage["sent"]["startNs"],
        )
        group = [row for row in udp if stage["startNs"] < row["timeNs"] < stage["endNs"]]
        require(
            len(group) == (7 if permitted else 1)
            and all(row["timeNs"] >= stage["sent"]["startNs"] for row in group),
            "Main stage has unexpected raw fragment count or timing.",
        )
        incoming = family(group, "auth0", 0, payload=payload)
        require(
            incoming["header"] == ORIGINAL
            and incoming["ipLength"] == 1228
            and incoming["ttl"] == 64
            and not incoming["dontFragment"]
            and incoming["udpChecksum"]["status"] == "valid",
            "Socket PMTU mode did not produce one complete DF-clear input.",
        )
        output = family(group, "service0", 4, identifier=incoming["ipId"]) if permitted else None
        state = read_state(directory, stage["state"], commands)
        require(
            stage["client"]["endNs"]
            < stage["state"]["command"]["startNs"]
            < stage["state"]["command"]["endNs"]
            < stage["endNs"],
            "Stage state snapshot precedes its socket result.",
        )
        if index < 2:
            require(not state, "Denied fresh traffic was confirmed.")
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
                "TTL-one reply did not mark the same fragmented-flow binding seen before the normal reply.",
            )
            binding = state[0]
            low_payload = f"mtu:{name}:ttl-one-reply"
            socket_record(low["sent"], stage, expected_socket(WIRE_REPLY, low_payload, True, 1))
            socket_record(low["client"], stage, None)
            socket_record(stage["reply"], stage, expected_socket(WIRE_REPLY, reply_payload, True))
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
                "Request, TTL reply, snapshots, and normal reply are unordered.",
            )
            check_links(
                directory,
                low["links"],
                "cached-ttl-one-reply",
                commands,
                low["before"]["command"]["endNs"],
                low["sent"]["startNs"],
            )
            check_links(
                directory,
                stage["replyLinks"],
                f"{name}-reply",
                commands,
                low["after"]["command"]["endNs"],
                stage["reply"]["startNs"],
            )
            low_input = family(group, "service0", 0, payload=low_payload)
            normal_input = family(group, "service0", 0, payload=reply_payload)
            normal_output = family(group, "auth0", 4, identifier=normal_input["ipId"])
            require(
                low_input["ttl"] == 1
                and normal_input["ttl"] == 64
                and low_input["fragments"][0]["timeNs"] >= low["sent"]["startNs"]
                and normal_input["fragments"][0]["timeNs"] >= stage["reply"]["startNs"]
                and low["client"]["endNs"] - low["client"]["startNs"] >= 200_000_000,
                "Reply socket TTL or timeout disagrees with the raw input.",
            )
            sample(
                f"{name}-request",
                name,
                incoming,
                output,
                "forwarded",
                low["before"],
                stage["requestLinks"],
            )
            sample(
                "cached-ttl-one-reply",
                name,
                low_input,
                None,
                "ttlExpired",
                low["after"],
                low["links"],
            )
            sample(
                f"{name}-reply",
                name,
                normal_input,
                normal_output,
                "forwarded",
                stage["state"],
                stage["replyLinks"],
            )
        else:
            require(
                stage["reply"] is None
                and stage["lowTTLReply"] is None
                and stage["replyLinks"] is None
                and stage["sent"]["endNs"]
                <= stage["server"]["startNs"]
                < stage["server"]["endNs"]
                <= stage["client"]["startNs"]
                and all(
                    stage[key]["endNs"] - stage[key]["startNs"] >= 200_000_000
                    for key in ("server", "client")
                ),
                "Denied large datagram lacks measured socket timeouts.",
            )
            if index == 3:
                require(
                    len(state) == 1
                    and state[0]["id"] == binding["id"]
                    and state[0]["status"] == 442,
                    "Logoff did not preserve the same cached fragmented-flow binding.",
                )
            sample(
                f"{name}-request",
                name,
                incoming,
                None,
                "forwardDrop",
                stage["state"],
                stage["requestLinks"],
            )
        if index == 1:
            require(stage["load"] is None, "Unexpected load before local credential installation.")
        else:
            load(stage["load"], name, stage["policy"], index != 0)
            require(
                stage["load"]["endNs"] < stage["startNs"], "Native gate load occurs after the send."
            )
        for export in stage["exports"].values():
            require(
                stage["client"]["endNs"]
                < export["command"]["startNs"]
                < export["command"]["endNs"]
                < stage["state"]["command"]["startNs"],
                "Native config export lies outside its measured checkpoint.",
            )
        verify_exports(
            directory,
            stage["exports"],
            commands,
            policies[stage["policy"]],
            [row for row in udp if row["packetType"] == 0 and row["timeNs"] < stage["endNs"]],
        )
        prefix = sum(frame["timeNs"] < stage["sent"]["startNs"] for frame in eap_frames)
        require(prefix == (0, 16, 16, 18)[index], "EAP prefix does not match the MTU stage.")
        configs.append(
            {
                "id": name,
                "forwardFile": stage["exports"]["firewall"]["file"],
                "natFile": stage["exports"]["nat"]["file"],
                "lateFile": stage["exports"]["late"]["file"],
                "outputFile": stage["exports"]["output"]["file"],
                "icmpLateFile": stage["exports"]["icmpLate"]["file"],
            }
        )
        reports.append(
            {
                "name": name,
                "eapFramesBeforeSend": prefix,
                "credentialInstalled": index >= 2,
                "delivered": permitted,
                "firewallFile": stage["exports"]["firewall"]["file"],
                "observations": stage,
                "udpFragments": group,
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
    require(
        stages[1]["endNs"]
        < observations["credentialInstall"]["startNs"]
        < observations["credentialInstall"]["endNs"]
        < stages[2]["load"]["startNs"]
        and stages[2]["endNs"]
        < observations["logoff"]["startNs"]
        < observations["logoff"]["endNs"]
        < stages[3]["load"]["startNs"],
        "Credential or Logoff cutover is unordered.",
    )
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
    require(len(stations) == 2 and len(statuses) == 1, "Missing or duplicate native status export.")
    for record, filename in (
        (stations[0], "authorized-station.txt"),
        (stations[1], "logged-off-station.txt"),
        (statuses[0], "supplicant-status.txt"),
    ):
        require(
            record["stdout"] == (directory / "eap" / filename).read_text(),
            "Native status stdout contradicts its saved authorization state.",
        )
    require(
        stations[0]["endNs"] < stages[1]["startNs"]
        and statuses[0]["endNs"] < stages[1]["startNs"]
        and observations["logoff"]["endNs"]
        < stations[1]["startNs"]
        < stations[1]["endNs"]
        < stages[3]["load"]["startNs"],
        "Native status export is outside its checkpoint.",
    )
    require(
        observations["logoff"]["startNs"]
        <= eap_frames[authentication["phases"][0]["logoffFrame"] - 1]["timeNs"]
        < stages[3]["load"]["startNs"],
        "Deny load precedes the captured EAPOL Logoff.",
    )
    load(observations["probeLoad"], "mtu-probes", "permit")
    probes = observations["mtuProbes"]
    specs = [
        ("cached-df-oversize", 1200, 64, True, "mtuExceeded"),
        ("fresh-df-oversize", 1200, 64, True, "mtuExceeded"),
        ("ttl-one-df-oversize", 1200, 1, True, "ttlExpired"),
        ("exact-mtu-df", 572, 64, True, "forwarded"),
        ("oversize-df-clear", 1200, 64, False, "forwarded"),
        ("udp-zero-fragments", 1200, 64, False, "forwarded"),
    ]
    specs += [(name, ip_size - 28, 1, False, "ttlExpired") for name, ip_size, _, _, _ in EXTRA]
    require(
        len(probes) == len(specs)
        and all(
            type(probe["ttl"]) is int
            and type(probe["df"]) is bool
            and type(probe["tos"]) is int
            and type(probe["reply"]) is bool
            and type(probe["payloadBytes"]) is int
            and (probe["name"], probe["payloadBytes"], probe["ttl"], probe["df"]) == spec[:4]
            for probe, spec in zip(probes, specs)
        ),
        "MTU boundary probe declarations disagree.",
    )
    require(
        stages[-1]["endNs"]
        < observations["probeLoad"]["startNs"]
        < observations["probeLoad"]["endNs"]
        < probes[0]["startNs"],
        "Isolated MTU permit phase is out of order.",
    )
    verify_exports(
        directory,
        observations["probeExports"],
        commands,
        policies["permit"],
        [row for row in udp if row["packetType"] == 0 and row["timeNs"] < probes[0]["startNs"]],
    )
    require(
        all(
            observations["probeLoad"]["endNs"]
            < export["command"]["startNs"]
            < export["command"]["endNs"]
            < probes[0]["startNs"]
            for export in observations["probeExports"].values()
        ),
        "MTU config exports lie outside activation and first probe.",
    )
    configs.append(
        {
            "id": "mtu-probes",
            "forwardFile": observations["probeExports"]["firewall"]["file"],
            "natFile": observations["probeExports"]["nat"]["file"],
            "lateFile": observations["probeExports"]["late"]["file"],
            "outputFile": observations["probeExports"]["output"]["file"],
            "icmpLateFile": observations["probeExports"]["icmpLate"]["file"],
        }
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
        and re.search(r"1 flow entries have been deleted", erase["command"]["stderr"])
        and probes[0]["endNs"]
        < erase["command"]["startNs"]
        < erase["command"]["endNs"]
        < erase["state"]["command"]["startNs"]
        < erase["state"]["command"]["endNs"]
        < probes[1]["startNs"]
        and not read_state(directory, erase["state"], commands),
        "Targeted erase is not the ordered selected zone-zero binding deletion.",
    )
    probe_reports, previous_end, new_binding = [], observations["probeLoad"]["endNs"], None
    for index, (probe, spec) in enumerate(zip(probes, specs)):
        name, size, ttl, df, disposition = spec
        admission.interval(probe, observations["eap"])
        require(previous_end < probe["startNs"], "MTU probe windows overlap.")
        previous_end = probe["endNs"]
        before, after = (
            read_state(directory, probe["before"], commands),
            read_state(directory, probe["after"], commands),
        )
        source = read_json(directory / probe["input"])
        require(
            probe["input"] == f"{name}-input.json" and source["name"] == name,
            "Misbound raw MTU input file.",
        )
        sent = probe["sent"]
        copied_command(sent, commands)
        admission.successful_command(
            sent,
            [
                "ip",
                "netns",
                "exec",
                "server" if probe["reply"] else "peer",
                "python3",
                "/task/icmp/exercise.py",
                "raw-send",
                f"{BASE}/{probe['input']}",
                "server0" if probe["reply"] else "peer0",
            ],
        )
        sender = json.loads(sent["stdout"])
        admission.interval(sender, sent)
        require(
            sender["raw"] == source["raw"]
            and type(sender["bytesSent"]) is int
            and sender["bytesSent"] == len(bytes.fromhex(source["raw"])),
            "Raw MTU sender bytes or completion disagree.",
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
            "MTU probe send and snapshots are unordered.",
        )
        check_links(
            directory,
            probe["links"],
            name,
            commands,
            probe["before"]["command"]["endNs"],
            sent["startNs"],
        )
        group = [row for row in udp if probe["startNs"] < row["timeNs"] < probe["endNs"]]
        count = 1 if index < 3 or index >= 6 else 2 if index == 3 else 4
        require(len(group) == count, "MTU probe has unexpected selected fragment count.")
        incoming = family(group, "service0" if probe["reply"] else "auth0", 0)
        require(
            incoming["fragments"][0]["raw"] == source["raw"]
            and incoming["header"] == (WIRE_REPLY if probe["reply"] else ORIGINAL)
            and incoming["ipId"] == 0xFD00 + index
            and incoming["tos"] == probe["tos"]
            and (probe["tos"], probe["reply"])
            == ((EXTRA[index - 6][2], EXTRA[index - 6][4]) if index >= 6 else (0, False))
            and incoming["ipLength"] == size + 28
            and incoming["ttl"] == ttl
            and incoming["dontFragment"] == df
            and incoming["udpChecksum"]["status"] == ("omitted" if index in (5, 12) else "valid")
            and len(bytes.fromhex(incoming["payloadHex"])) == size
            and bytes.fromhex(incoming["payloadHex"]).startswith(f"mtu:{name}|".encode())
            and all(row["timeNs"] >= sender["startNs"] for row in group),
            "Injected raw MTU boundary bytes disagree.",
        )
        output = (
            family(group, "service0", 4, identifier=incoming["ipId"])
            if disposition == "forwarded"
            else None
        )
        expected = (
            expected_socket(WIRE, bytes.fromhex(incoming["payloadHex"]).decode("ascii"))
            if output
            else None
        )
        socket_record(probe["server"], probe, expected)
        if not output:
            require(
                probe["server"]["endNs"] - probe["server"]["startNs"] >= 200_000_000,
                "MTU/TTL drop lacks a receiver timeout.",
            )
            if index == 0:
                require(
                    len(before) == len(after) == 1
                    and before[0]["id"] == after[0]["id"] == binding["id"]
                    and before[0]["status"] == after[0]["status"] == 442,
                    "Cached DF oversize did not preserve the replied binding.",
                )
            elif index < 3:
                require(
                    not before and not after, "Fresh MTU/TTL drop unexpectedly confirmed a binding."
                )
            else:
                expected_status = 442 if probe["reply"] else 440
                require(
                    len(before) == len(after) == 1
                    and before[0]["id"] == after[0]["id"] == new_binding["id"]
                    and before[0]["status"] == 440
                    and after[0]["status"] == expected_status,
                    "Cached quote probe changed the binding or reply status unexpectedly.",
                )
        else:
            require(
                len(after) == 1 and after[0]["status"] == 440,
                "Forwarded MTU probe lacks a confirmed unreplied binding.",
            )
            if index == 3:
                require(
                    not before and after[0]["id"] != binding["id"],
                    "Exact-MTU probe was not fresh after the explicit erase.",
                )
                new_binding = after[0]
            else:
                require(
                    len(before) == 1 and before[0]["id"] == after[0]["id"] == new_binding["id"],
                    "Fragmented cached probe changed the binding identity.",
                )
        sample(name, "mtu-probes", incoming, output, disposition, probe["after"], probe["links"])
        probe_reports.append(
            {
                "name": name,
                "observations": probe,
                "input": incoming,
                "outputFamily": output,
                "icmpFrames": [
                    row for row in icmp if probe["startNs"] < row["timeNs"] < probe["endNs"]
                ],
            }
        )
    require(
        len(used_traces) == 20 and len(used_frames) == len(udp),
        "Unaccounted packet trace or UDP fragment.",
    )
    require(
        len(
            [
                sample
                for sample in samples
                if sample["observed"]["disposition"] in ("ttlExpired", "mtuExceeded")
            ]
        )
        == len(icmp),
        "Unexpected ICMP side observation.",
    )
    require(
        used_icmp_traces == set(range(len(icmp_traces))) and len(icmp_traces) == len(icmp),
        "Unaccounted native ICMP output trace.",
    )
    verify_exports(
        directory,
        observations["finalExports"],
        commands,
        policies["permit"],
        [row for row in udp if row["packetType"] == 0],
    )
    require(
        all(
            probes[-1]["endNs"] < row["command"]["startNs"]
            for row in observations["finalExports"].values()
        ),
        "Final output exports precede the last probe.",
    )
    offloads = wire.check_offloads(directory, {"stages": [{"observations": stages[0]}]})
    return {
        "schema": 1,
        "scope": "checked-native-icmp-error-evidence",
        "initialFile": observations["initial"]["file"],
        "icmpProfile": profile,
        "icmpOutputTraces": icmp_traces,
        "finalExports": observations["finalExports"],
        "eapEvidence": authentication,
        "credential": credential,
        "credentialInstall": observations["credentialInstall"],
        "logoff": observations["logoff"],
        "stages": reports,
        "routing": {
            "version": "6.19.0",
            "routesFile": "network-auth-routes.json",
            "bindings": [
                {"device": "auth0", "nextNode": "peer", "gateway": None},
                {"device": "service0", "nextNode": "service", "gateway": None},
            ],
        },
        "mtus": [{"nextHop": "peer", "mtu": 4096}, {"nextHop": "service", "mtu": 600}],
        "configs": configs,
        "packetSamples": samples,
        "erase": {
            "beforeLabel": "fresh-df-oversize",
            "zone": 0,
            "raw": samples[2]["raw"],
            "stateFile": erase["state"]["file"],
            "command": erase["command"],
        },
        "mtuProbes": probe_reports,
        "offloads": offloads,
        "frameCount": len(frames),
        "udpFragmentCount": len(udp),
        "icmpFrameCount": len(icmp),
        "icmpFrames": icmp,
        "limits": [
            "finite-private-NAT-MTU-capture",
            "all-gateway-inputs-unfragmented",
            "strict-unordered-family-reassembly-is-derived-not-a-fabricated-wire-datagram",
            "UDP-checksum-only-after-complete-family-reassembly",
            "ICMP-no-options-unicast-UDP-type11-code0-and-type3-code4-only",
            "outer-ipId-is-observed-allocation-choice-not-a-deterministic-generator",
            "no-TLS-cryptographic-kernel-refinement-capture-authenticity-or-instantaneous-update-proof",
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
            f"Verified {evidence['udpFragmentCount']} UDP fragment frames, {evidence['icmpFrameCount']} ICMP errors, and twenty ICMP/MTU packet episodes."
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
        print(f"ICMP evidence: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
