"""Check real NAT fragment families, MTU errors, and native admission evidence."""

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
import check_wire_capture as wire
import check_wire_nat_capture as nat

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/mtu"
EvidenceError = admission.EvidenceError
require = admission.require
ORIGINAL, WIRE, WIRE_REPLY, PEER_REPLY = nat.ORIGINAL, nat.WIRE, nat.WIRE_REPLY, nat.PEER_REPLY
BASE = nat.BASE
MTUS = {"peer0": 4096, "auth0": 4096, "service0": 600, "server0": 600}
MACS = {
    "peer0": eap.PEER,
    "auth0": eap.AUTHENTICATOR,
    "service0": admission.SERVICE,
    "server0": admission.SERVER,
}
read_json, copied_command, read_state = nat.read_json, nat.copied_command, nat.read_state


def decode_frame(row, index):
    raw = row["hex"]
    require(
        isinstance(raw, str) and re.fullmatch(r"(?:[0-9a-fA-F]{2})+", raw),
        "Require hexadecimal byte pairs without whitespace.",
    )
    data = bytes.fromhex(raw)
    require(len(data) >= 34 and data[12:14] == b"\x08\x00", "Unsupported Ethernet IPv4 capture.")
    ip = data[14:34]
    size, flags = int.from_bytes(ip[2:4], "big"), int.from_bytes(ip[6:8], "big")
    require(
        ip[0] == 0x45
        and not flags & 0x8000
        and 20 < size <= len(data) - 14
        and wire.folded_sum(ip) == 65535,
        "Invalid captured IPv4 header, flags, length, or checksum.",
    )
    offset, more, df = (flags & 8191) * 8, bool(flags & 8192), bool(flags & 16384)
    require(not df or (not more and offset == 0), "DF cannot accompany an IPv4 fragment.")
    interface, kind = row["interface"], row["packetType"]
    require(
        type(kind) is int and interface in ("auth0", "service0") and kind in (0, 4),
        "Invalid capture interface or direction.",
    )
    source, destination = (
        str(ipaddress.IPv4Address(ip[12:16])),
        str(ipaddress.IPv4Address(ip[16:20])),
    )
    source_mac, destination_mac = data[6:12].hex(":"), data[:6].hex(":")
    roles = {
        ("auth0", 0): (eap.PEER, eap.AUTHENTICATOR),
        ("auth0", 4): (eap.AUTHENTICATOR, eap.PEER),
        ("service0", 0): (admission.SERVER, admission.SERVICE),
        ("service0", 4): (admission.SERVICE, admission.SERVER),
    }
    require(
        (source_mac, destination_mac) == roles[(interface, kind)],
        "Captured Ethernet MAC role disagrees.",
    )
    result = {
        "raw": raw,
        "source": f"frames.jsonl:{index}",
        "timeNs": row["timeNs"],
        "interface": interface,
        "packetType": kind,
        "protocol": ip[9],
        "sourceAddress": source,
        "destinationAddress": destination,
        "ipId": int.from_bytes(ip[4:6], "big"),
        "tos": ip[1],
        "ttl": ip[8],
        "dontFragment": df,
        "moreFragments": more,
        "offsetBytes": offset,
        "ipLength": size,
        "ipPayloadHex": data[34 : 14 + size].hex(),
        "paddingHex": data[14 + size :].hex(),
    }
    if ip[9] == 17:
        addresses = {
            ("auth0", 0): (ORIGINAL["source"], ORIGINAL["destination"]),
            ("auth0", 4): (PEER_REPLY["source"], PEER_REPLY["destination"]),
            ("service0", 0): (WIRE_REPLY["source"], WIRE_REPLY["destination"]),
            ("service0", 4): (WIRE["source"], WIRE["destination"]),
        }
        require(
            (source, destination) == addresses[(interface, kind)],
            "Captured fragment's translated IPv4 endpoints disagree.",
        )
        require(
            not more or (size - 20) % 8 == 0,
            "A nonfinal IPv4 fragment must have an aligned payload.",
        )
        if kind == 0:
            require(
                not more and offset == 0,
                "Gateway ingress fragmentation and reassembly are outside this capture profile.",
            )
        return result
    require(
        ip[9] == 1 and kind == 4 and not more and offset == 0, "Unexpected non-UDP transit frame."
    )
    icmp = data[34 : 14 + size]
    require(
        len(icmp) >= 36
        and wire.folded_sum(icmp) == 65535
        and icmp[:2] in (b"\x0b\x00", b"\x03\x04"),
        "Expected valid ICMP Time Exceeded or Fragmentation Needed.",
    )
    quote = icmp[8:]
    require(
        quote[0] == 0x45 and quote[9] == 17 and wire.folded_sum(quote[:20]) == 65535,
        "Malformed ICMP IPv4/UDP quote.",
    )
    result.update(
        icmpType=icmp[0],
        icmpCode=icmp[1],
        nextHopMTU=int.from_bytes(icmp[6:8], "big") if icmp[0] == 3 else None,
        quoteHex=quote.hex(),
        quotedIpId=int.from_bytes(quote[4:6], "big"),
    )
    require(
        (icmp[0] == 3 and icmp[4:6] == bytes(2) and result["nextHopMTU"] == 600)
        or (icmp[0] == 11 and icmp[4:8] == bytes(4)),
        "ICMP error code or next-hop MTU disagrees.",
    )
    return result


def reassemble_fragments(frames):
    require(
        frames and all(row["protocol"] == 17 for row in frames),
        "A UDP family must contain IPv4 UDP fragments.",
    )
    ordered = sorted(frames, key=lambda row: row["offsetBytes"])
    first = ordered[0]
    keys = (
        "sourceAddress",
        "destinationAddress",
        "protocol",
        "ipId",
        "tos",
        "ttl",
        "dontFragment",
        "interface",
        "packetType",
    )
    require(
        all(all(row[key] == first[key] for key in keys) for row in ordered),
        "Fragment family metadata disagree.",
    )
    require(
        sum(not row["moreFragments"] for row in ordered) == 1 and not ordered[-1]["moreFragments"],
        "Fragment family needs exactly one terminal fragment.",
    )
    cursor, pieces = 0, []
    for row in ordered:
        payload = bytes.fromhex(row["ipPayloadHex"])
        require(
            row["offsetBytes"] == cursor
            and payload
            and (not row["moreFragments"] or len(payload) % 8 == 0),
            "Fragment family has an overlap, gap, duplicate, or misaligned payload.",
        )
        cursor += len(payload)
        pieces.append(payload)
    require(
        cursor <= 65515 and (len(ordered) == 1 or not first["dontFragment"]),
        "Invalid reassembled IPv4 length or DF flag.",
    )
    udp = b"".join(pieces)
    require(
        len(udp) >= 8 and int.from_bytes(udp[4:6], "big") == len(udp),
        "Reassembled UDP length must cover the complete payload.",
    )
    value = int.from_bytes(udp[6:8], "big")
    pseudo = (
        ipaddress.IPv4Address(first["sourceAddress"]).packed
        + ipaddress.IPv4Address(first["destinationAddress"]).packed
        + bytes((0, 17))
        + len(udp).to_bytes(2, "big")
    )
    require(
        value == 0 or wire.folded_sum(pseudo + udp) == 65535,
        "Invalid reassembled UDP pseudoheader checksum.",
    )
    header = {
        "source": first["sourceAddress"],
        "destination": first["destinationAddress"],
        "protocol": 17,
        "sourcePort": int.from_bytes(udp[:2], "big"),
        "destinationPort": int.from_bytes(udp[2:4], "big"),
    }
    return {
        "derivedByReassembly": True,
        "header": header,
        "ipId": first["ipId"],
        "tos": first["tos"],
        "ttl": first["ttl"],
        "dontFragment": first["dontFragment"],
        "ipLength": 20 + len(udp),
        "udpLength": len(udp),
        "udpChecksum": {"value": value, "status": "omitted" if value == 0 else "valid"},
        "payloadHex": udp[8:].hex(),
        "ipPayloadHex": udp.hex(),
        "fragments": ordered,
    }


def check_links(directory, exports, name, commands, after, before):
    require(set(exports) == {"peer", "auth", "server"}, "Missing per-event link MTU export.")
    groups = {"peer": {"peer0"}, "auth": {"auth0", "service0"}, "server": {"server0"}}
    for namespace, interfaces in groups.items():
        export = exports[namespace]
        require(
            export["file"] == f"{name}-{namespace}-links.json",
            "Misbound per-event link MTU artifact.",
        )
        command = export["command"]
        copied_command(command, commands)
        admission.successful_command(command, ["ip", "-n", namespace, "-j", "link", "show"])
        require(
            after <= command["startNs"] < command["endNs"] < before
            and command["stdout"] == (directory / export["file"]).read_text(),
            "Per-event MTU export stdout or observation interval disagrees.",
        )
        rows = read_json(directory / export["file"])
        require(
            len(rows) == len(interfaces) + 1
            and {row["ifname"] for row in rows} == {"lo", *interfaces},
            "Unexpected per-event link inventory.",
        )
        for row in rows:
            if row["ifname"] != "lo":
                require(
                    type(row["mtu"]) is int
                    and row["mtu"] == MTUS[row["ifname"]]
                    and row["address"] == MACS[row["ifname"]]
                    and "UP" in row["flags"],
                    "Per-event link MTU, MAC, or state disagrees.",
                )


def check_forward_trace(trace, incoming, output, disposition):
    if disposition != "mtuExceeded":
        destination, source, next_hop = nat.check_trace(trace, incoming, output, disposition)
        return destination, source, "service" if next_hop == "server" else next_hop
    stages = trace["stages"]
    translated = admission.REPLY if incoming["header"] == WIRE_REPLY else admission.REQUEST
    expected = [("netlib_trace", "before"), ("netlib_tracking", "prerouting")]
    if any(row["table"] == "netlib_nat" and row["chain"] == "destination" for row in stages):
        expected.append(("netlib_nat", "destination"))
    expected.append(("netlib_trace", "afterDestination"))
    require(
        [(row["table"], row["chain"]) for row in stages] == expected
        and incoming["dontFragment"]
        and incoming["ttl"] > 1
        and incoming["ipLength"] > 600
        and output is None,
        "MTU-exceeded packet reached a later hook or has the wrong boundary.",
    )
    require(
        stages[0]["packet"] == incoming["header"]
        and stages[0]["udpChecksum"] == incoming["udpChecksum"]["value"]
        and stages[-1]["packet"] == translated
        and all(
            row["ipId"] == incoming["ipId"]
            and row["ipLength"] == incoming["ipLength"]
            and row["udpLength"] == incoming["udpLength"]
            and row["ttl"] == incoming["ttl"]
            for row in stages
        ),
        "MTU-drop hook packet identity or after-DNAT header disagrees.",
    )
    return translated, None, None


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
                    and row["mtu"] == MTUS[row["ifname"]],
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
        settings_command = [
            "ip",
            "netns",
            "exec",
            namespace,
            "sysctl",
            "net.ipv4.ip_forward",
            "net.ipv6.conf.all.disable_ipv6",
            "net.ipv6.conf.default.disable_ipv6",
        ]
        settings_records = [record for record in commands if record["command"] == settings_command]
        require(
            len(settings_records) == 1
            and settings_records[0]["stdout"] == settings
            and settings_records[0]["endNs"] < observations["initial"]["command"]["startNs"]
            and len(settings.splitlines()) == 3,
            "Native settings export stdout or pre-initial sysctl interval disagrees.",
        )
        require(
            "net.ipv6.conf.all.disable_ipv6 = 1\n" in settings
            and "net.ipv6.conf.default.disable_ipv6 = 1\n" in settings
            and (namespace != "auth" or "net.ipv4.ip_forward = 1\n" in settings),
            "Native forwarding or IPv6 isolation setting disagrees.",
        )


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
    require(len(result) == 12, "Expected twelve independent selected UDP traces.")
    return result


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
        and observations["scope"] == "mtu-fragment-forwarding",
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
        sum(row["command"][:5] == ["ip", "netns", "exec", "auth", "nft"] for row in commands) == 26,
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
    require(len(udp) == 23 and len(icmp) == 4, "Unexpected captured UDP fragment or ICMP count.")
    traces = parse_traces(directory / "trace.txt")
    require(
        (directory / "trace-errors.txt").read_text() == ""
        and observations["traceCommand"]
        == ["ip", "netns", "exec", "auth", "nft", "monitor", "trace"],
        "Native trace producer disagrees.",
    )
    samples, used_frames, used_traces = [], set(), set()

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
        nat.verify_exports(
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
    require(
        len(probes) == len(specs)
        and all(
            type(probe["ttl"]) is int
            and type(probe["df"]) is bool
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
    nat.verify_exports(
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
        count = 1 if index < 3 else 2 if index == 3 else 4
        require(len(group) == count, "MTU probe has unexpected selected fragment count.")
        incoming = family(group, "auth0", 0)
        require(
            incoming["fragments"][0]["raw"] == source["raw"]
            and incoming["header"] == ORIGINAL
            and incoming["ipId"] == 0xFD00 + index
            and incoming["ipLength"] == size + 28
            and incoming["ttl"] == ttl
            and incoming["dontFragment"] == df
            and incoming["udpChecksum"]["status"] == ("omitted" if index == 5 else "valid")
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
            else:
                require(
                    not before and not after, "Fresh MTU/TTL drop unexpectedly confirmed a binding."
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
        len(used_traces) == 12 and len(used_frames) == len(udp),
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
    offloads = wire.check_offloads(directory, {"stages": [{"observations": stages[0]}]})
    return {
        "schema": 1,
        "scope": "checked-native-mtu-fragment-evidence",
        "initialFile": observations["initial"]["file"],
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
            "ICMP-error-type-code-MTU-and-quote-observed-without-full-ICMP-model",
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
            f"Verified {evidence['udpFragmentCount']} UDP fragment frames, {evidence['icmpFrameCount']} ICMP errors, and twelve MTU packet episodes."
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
        print(f"MTU evidence: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
