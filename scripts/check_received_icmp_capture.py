"""Check unchanged received ICMP, NAT, conntrack, and native socket PMTU evidence."""

import argparse
import copy
import hashlib
import ipaddress
import json
import re
import shlex
import struct
from pathlib import Path

import check_admission_capture as admission
import check_icmp_capture as generated
import check_lifecycle_capture as lifecycle
import check_mtu_capture as mtu
import check_wire_capture as wire
import check_wire_nat_capture as nat

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/received-icmp"
EvidenceError, require = admission.EvidenceError, admission.require
read_json = nat.read_json
ORIGINAL, WIRE, WIRE_REPLY, PEER_REPLY = nat.ORIGINAL, nat.WIRE, nat.WIRE_REPLY, nat.PEER_REPLY
LINKS = {
    "peer": {"peer0": (4096, "192.0.2.2", "02:00:00:00:ea:02")},
    "auth": {
        "auth0": (4096, "192.0.2.1", "02:00:00:00:ea:01"),
        "service0": (1500, "198.51.101.1", "02:00:00:00:eb:01"),
    },
    "router": {
        "router0": (1500, "198.51.101.254", "02:00:00:00:eb:02"),
        "srvlink": (600, "198.51.100.254", "02:00:00:00:ec:01"),
    },
    "server": {"server0": (600, "198.51.100.2", "02:00:00:00:ec:02")},
}
PEERS = {
    "peer0": "auth0",
    "auth0": "peer0",
    "service0": "router0",
    "router0": "service0",
    "srvlink": "server0",
    "server0": "srvlink",
}
ROUTES = {
    "peer": {("default", "peer0", "192.0.2.1"), ("192.0.2.0/24", "peer0", None)},
    "auth": {
        ("192.0.2.0/24", "auth0", None),
        ("198.51.101.0/24", "service0", None),
        ("198.51.100.0/24", "service0", "198.51.101.254"),
    },
    "router": {
        ("198.51.101.0/24", "router0", None),
        ("198.51.100.0/24", "srvlink", None),
        ("192.0.2.0/24", "router0", "198.51.101.1"),
        ("203.0.113.0/24", "router0", "198.51.101.1"),
    },
    "server": {("default", "server0", "198.51.100.254"), ("198.51.100.0/24", "server0", None)},
}
INVALID = {"unmatched-quote", "wrong-outer-destination"}
RAW_NAMES = [
    "unmatched-quote",
    "wrong-outer-destination",
    "ttl-one-control",
    "full-bad-udp-checksum",
    "bad-inner-ip-checksum",
    "forged-outer-source",
]


def checksum(data):
    return 65535 - wire.folded_sum(data)


def header(data):
    return {
        "source": str(ipaddress.IPv4Address(data[12:16])),
        "destination": str(ipaddress.IPv4Address(data[16:20])),
        "protocol": data[9],
        "sourcePort": int.from_bytes(data[20:22], "big"),
        "destinationPort": int.from_bytes(data[22:24], "big"),
    }


def decode_frame(row, number, filename):
    raw = row["hex"]
    require(
        isinstance(raw, str) and re.fullmatch(r"(?:[0-9a-f]{2})+", raw),
        "Malformed raw Ethernet bytes.",
    )
    data = bytes.fromhex(raw)
    require(len(data) >= 34 and data[12:14] == b"\x08\x00", "Expected Ethernet IPv4.")
    ip = data[14:34]
    size, flags = int.from_bytes(ip[2:4], "big"), int.from_bytes(ip[6:8], "big")
    require(
        ip[0] == 0x45
        and 20 < size <= len(data) - 14
        and not flags & 0x8000
        and wire.folded_sum(ip) == 65535,
        "Invalid captured IPv4 checksum, size, or flags.",
    )
    ns, interface, kind = row["namespace"], row["interface"], row["packetType"]
    require(
        ns in LINKS and interface in LINKS[ns] and type(kind) is int and kind in (0, 4),
        "Invalid native capture interface.",
    )
    macs = {key: value[2] for links in LINKS.values() for key, value in links.items()}
    source_mac, destination_mac = (
        (macs[interface], macs[PEERS[interface]])
        if kind == 4
        else (macs[PEERS[interface]], macs[interface])
    )
    require(
        data[:6].hex(":") == destination_mac and data[6:12].hex(":") == source_mac,
        "Captured Ethernet direction disagrees.",
    )
    payload = data[34 : 14 + size]
    result = {
        "raw": raw,
        "source": f"{filename}:{number}",
        "timeNs": row["timeNs"],
        "namespace": ns,
        "interface": interface,
        "packetType": kind,
        "protocol": ip[9],
        "sourceAddress": str(ipaddress.IPv4Address(ip[12:16])),
        "destinationAddress": str(ipaddress.IPv4Address(ip[16:20])),
        "ipId": int.from_bytes(ip[4:6], "big"),
        "ipLength": size,
        "ttl": ip[8],
        "tos": ip[1],
        "dontFragment": bool(flags & 0x4000),
        "offsetBytes": (flags & 8191) * 8,
        "moreFragments": bool(flags & 8192),
        "ipPayloadHex": payload.hex(),
        "paddingHex": data[14 + size :].hex(),
    }
    require(not result["dontFragment"] or not flags & 0x3FFF, "Invalid DF fragment.")
    if ip[9] == 17:
        require(not result["moreFragments"] or len(payload) % 8 == 0, "Unaligned UDP fragment.")
        return result
    require(
        ip[9] == 1
        and not flags & 0x3FFF
        and len(payload) >= 36
        and payload[:2] == b"\x03\x04"
        and payload[4:6] == bytes(2)
        and wire.folded_sum(payload) == 65535,
        "Invalid captured ICMP error checksum or header.",
    )
    quote = payload[8:]
    require(
        quote[0] == 0x45 and quote[9] == 17 and len(quote) >= 28, "Unsupported ICMP quote prefix."
    )
    quoted_size = int.from_bytes(quote[2:4], "big")
    complete = len(quote) >= quoted_size
    udp_size = int.from_bytes(quote[24:26], "big")
    udp_checksum = int.from_bytes(quote[26:28], "big")
    pseudo = quote[12:20] + bytes((0, 17)) + udp_size.to_bytes(2, "big")
    udp_status = (
        "omitted"
        if udp_checksum == 0
        else "partial"
        if not complete
        else "valid"
        if wire.folded_sum(pseudo + quote[20:quoted_size]) == 65535
        else "invalid"
    )
    result.update(
        icmpType=3,
        icmpCode=4,
        nextHopMTU=int.from_bytes(payload[6:8], "big"),
        quoteHex=quote.hex(),
        quoteLength=len(quote),
        quoteComplete=complete,
        quotedHeader=header(quote),
        quotedIpId=int.from_bytes(quote[4:6], "big"),
        quotedIpLength=quoted_size,
        quotedIpChecksum="valid" if wire.folded_sum(quote[:20]) == 65535 else "invalid",
        quotedUdpLength=udp_size,
        quotedUdpChecksum={"value": udp_checksum, "status": udp_status},
    )
    return result


def families(frames):
    groups = {}
    for row in frames:
        if row["protocol"] == 17:
            key = tuple(
                row[key]
                for key in (
                    "namespace",
                    "interface",
                    "packetType",
                    "sourceAddress",
                    "destinationAddress",
                    "ipId",
                )
            )
            groups.setdefault(key, []).append(row)
    return [
        {
            "protocol": 17,
            "namespace": rows[0]["namespace"],
            "interface": rows[0]["interface"],
            "packetType": rows[0]["packetType"],
            **mtu.reassemble_fragments(rows),
        }
        for rows in groups.values()
    ]


def check_link_rows(rows, namespace):
    physical = {row["ifname"]: row for row in rows if row["ifname"] != "lo"}
    require(set(physical) == set(LINKS[namespace]), "Native link inventory disagrees.")
    for interface, (value, _, mac) in LINKS[namespace].items():
        row = physical[interface]
        require(
            row["mtu"] == value
            and row["address"] == mac
            and "UP" in row["flags"]
            and row["link_type"] == "ether",
            "Native link MTU, MAC, or state disagrees.",
        )


def copied(directory, record, commands):
    nat.copied_command(record["command"], commands)
    command = record["command"]
    admission.interval(command)
    require(
        command["returncode"] == 0
        and not command["stderr"]
        and (directory / record["file"]).read_text() == command["stdout"],
        "Native export differs from command stdout.",
    )
    return read_json(directory / record["file"])


def check_send_links(directory, exports, commands, prefix, after, before, consumed):
    require(
        isinstance(exports, dict) and set(exports) == set(LINKS),
        "Missing required per-send four namespace link exports.",
    )
    previous = after
    for namespace in LINKS:
        record = exports[namespace]
        command = record["command"]
        identity = (command["startNs"], command["endNs"])
        require(
            record["file"] not in consumed["files"] and identity not in consumed["commands"],
            "Native per-send link export or command is reused.",
        )
        consumed["files"].add(record["file"])
        consumed["commands"].add(identity)
        require(
            record["file"] == f"{prefix}-{namespace}-links.json",
            "Native per-send link artifact is misbound.",
        )
        admission.successful_command(command, ["ip", "-n", namespace, "-j", "link", "show"])
        rows = copied(directory, record, commands)
        check_link_rows(rows, namespace)
        require(
            previous <= command["startNs"] < command["endNs"] < before,
            "Native per-send link command is unordered or follows its send.",
        )
        previous = command["endNs"]


def check_snapshot(directory, record, commands, name, after, before, consumed):
    require(
        isinstance(record, dict) and record.get("file") == f"{name}-conntrack.json",
        "Native conntrack snapshot is misbound to its episode.",
    )
    rows = nat.read_state(directory, record, commands)
    command = record["command"]
    identity = (command["startNs"], command["endNs"])
    require(
        record["file"] not in consumed["files"] and identity not in consumed["commands"],
        "Native conntrack snapshot export or command is reused.",
    )
    consumed["files"].add(record["file"])
    consumed["commands"].add(identity)
    require(
        after < command["startNs"] < command["endNs"] < before,
        "Native conntrack snapshot is outside its measured episode boundary.",
    )
    return rows


def check_network(directory, observations, commands):
    exports = observations["networkExports"]
    require(
        set(exports)
        == {
            f"{ns}-{kind}" for ns in LINKS for kind in ("links", "addresses", "routes", "neighbors")
        },
        "Incomplete four namespace network exports.",
    )
    for ns, links in LINKS.items():
        for kind, arguments in (
            ("links", ["link", "show"]),
            ("addresses", ["address", "show"]),
            ("routes", ["-4", "route", "show", "table", "main"]),
            ("neighbors", ["neigh", "show"]),
        ):
            record = exports[f"{ns}-{kind}"]
            rows = copied(directory, record, commands)
            admission.successful_command(record["command"], ["ip", "-n", ns, "-j", *arguments])
            if kind == "links":
                check_link_rows(rows, ns)
            elif kind == "routes":
                require(
                    {(row["dst"], row["dev"], row.get("gateway")) for row in rows} == ROUTES[ns]
                    and len(rows) == len(ROUTES[ns]),
                    "Native explicit gateway routes disagree.",
                )
            elif kind == "addresses":
                actual = {
                    (row["ifname"], entry["local"], entry["prefixlen"])
                    for row in rows
                    for entry in row["addr_info"]
                    if row["ifname"] != "lo"
                }
                expected = {(name, value[1], 24) for name, value in links.items()}
                if ns == "auth":
                    expected |= {("service0", "203.0.113.1", 32), ("service0", "203.0.113.2", 32)}
                require(actual == expected, "Native interface addresses disagree.")
            else:
                macs = {
                    name: value[2]
                    for interfaces in LINKS.values()
                    for name, value in interfaces.items()
                }
                addresses = {
                    name: value[1]
                    for interfaces in LINKS.values()
                    for name, value in interfaces.items()
                }
                require(
                    len(rows) == len(links)
                    and {(r["dev"], r["dst"], r["lladdr"], tuple(r["state"])) for r in rows}
                    == {
                        (name, addresses[PEERS[name]], macs[PEERS[name]], ("PERMANENT",))
                        for name in links
                    },
                    "Native permanent neighbors disagree.",
                )
        settings = (directory / f"{ns}-settings.txt").read_text()
        candidates = [
            row
            for row in commands
            if row["command"][:5] == ["ip", "netns", "exec", ns, "sysctl"]
            and row["stdout"] == settings
        ]
        require(len(candidates) == 1, "Missing native namespace sysctl stdout.")
        values = dict(line.split(" = ") for line in settings.splitlines())
        require(
            values["net.ipv4.ip_forward"] == "1"
            and values["net.ipv6.conf.all.disable_ipv6"]
            == values["net.ipv6.conf.default.disable_ipv6"]
            == "1"
            and values["net.ipv4.route.min_pmtu"] == "552"
            and values["net.ipv4.route.mtu_expires"] == "600"
            and values["net.ipv4.ip_no_pmtu_disc"] == "0",
            "Native forwarding, IPv6, or host PMTU configuration disagrees.",
        )
    settings = observations["icmpSettingsReadback"]
    nat.copied_command(settings, commands)
    require(
        settings["stdout"] == (directory / "icmp-settings.txt").read_text()
        and dict(line.split(" = ") for line in settings["stdout"].splitlines())
        == {
            "net.ipv4.icmp_errors_use_inbound_ifaddr": "0",
            "net.ipv4.icmp_ratelimit": "0",
            "net.ipv4.icmp_ratemask": "0",
            "net.ipv4.ip_default_ttl": "64",
        },
        "Native router ICMP settings disagree.",
    )
    nat.copied_command(observations["icmpSettingsWrite"], commands)
    offloads = read_json(directory / "offloads.json")
    require(len(offloads) == 6, "Missing native offload observations.")
    seen = set()
    for row in offloads:
        key = row["namespace"], row["interface"]
        require(
            key not in seen and key[0] in LINKS and key[1] in LINKS[key[0]],
            "Repeated or unknown offload interface.",
        )
        seen.add(key)
        nat.copied_command(row["command"], commands)
        require(
            json.loads(row["command"]["stdout"])
            == {key: value for key, value in row.items() if key not in ("namespace", "command")}
            and row["after"] == {"txChecksum": 0, "tso": 0, "gso": 0, "gro": 0},
            "Native offload readback contradicts disabled checksums and segmentation.",
        )
    return exports, offloads


def parse_traces(path):
    groups = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        matched = re.fullmatch(r"trace id ([0-9a-f]{8}) ip (\S+) (\S+) (.*)", line.strip())
        require(matched is not None, "Malformed native trace line.")
        identifier, table, chain, body = matched.groups()
        if (table, chain) == ("netlib_trace", "before") and body.startswith("packet: "):
            groups.append({"id": identifier, "source": f"trace.txt:{number}", "stages": []})
        require(groups and groups[-1]["id"] == identifier, "Interleaved native trace episodes.")
        stages = groups[-1]["stages"]
        if body.startswith("packet: "):
            tokens = shlex.split(body[8:])

            def value(prefix, required=True):
                return lifecycle.tokens_value(tokens, prefix, required=required)

            protocol = 17 if "udp" in tokens else 1
            stage = {
                "table": table,
                "chain": chain,
                "line": number,
                "iif": value(["iif"]),
                "oif": value(["oif"], False),
                "sourceAddress": value(["ip", "saddr"]),
                "destinationAddress": value(["ip", "daddr"]),
                "protocol": protocol,
                "ipId": int(value(["ip", "id"])),
                "ipLength": int(value(["ip", "length"])),
                "ttl": int(value(["ip", "ttl"])),
                "tos": generated.trace_tos(tokens),
                "verdicts": [],
            }
            if protocol == 17:
                stage["packet"] = {
                    "source": stage["sourceAddress"],
                    "destination": stage["destinationAddress"],
                    "protocol": 17,
                    "sourcePort": int(value(["udp", "sport"])),
                    "destinationPort": int(value(["udp", "dport"])),
                }
                stage["udpLength"] = int(value(["udp", "length"]))
                stage["udpChecksum"] = int(value(["udp", "checksum"]))
            else:
                require(
                    value(["icmp", "type"]) == "destination-unreachable"
                    and value(["icmp", "code"]) == "4",
                    "Unexpected traced ICMP type or code.",
                )
                stage["nextHopMTU"] = (int(value(["icmp", "id"])) << 16) | int(
                    value(["icmp", "sequence"])
                )
            stages.append(stage)
        else:
            require(
                stages and (stages[-1]["table"], stages[-1]["chain"]) == (table, chain),
                "Orphan native verdict.",
            )
            found = re.fullmatch(r"(.*?) \(verdict (accept|drop|continue)\)", body)
            if found:
                text, verdict = found.groups()
                require(
                    not stages[-1]["verdicts"]
                    or stages[-1]["verdicts"][-1]["verdict"] == "continue",
                    "Trace continues after terminal verdict.",
                )
                stages[-1]["verdicts"].append({"line": number, "text": text, "verdict": verdict})
            else:
                require(body in ("policy accept", "policy drop"), "Unknown native verdict.")
                stages[-1]["verdicts"].append(
                    {"line": number, "text": body, "verdict": body.split()[1]}
                )
    return groups


def update_checksum(value, old, new, *, udp=False):
    require(len(old) == len(new) and len(old) % 2 == 0, "Checksum update requires words.")
    total = (~value) & 65535
    for offset in range(0, len(old), 2):
        total += (~int.from_bytes(old[offset : offset + 2], "big")) & 65535
        total += int.from_bytes(new[offset : offset + 2], "big")
    while total >> 16:
        total = (total & 65535) + (total >> 16)
    result = (~total) & 65535
    return (result or 65535) if udp else result


def translated_quote(raw):
    before = bytes.fromhex(raw)
    after = bytearray(before)
    new_addresses = (
        ipaddress.IPv4Address("192.0.2.2").packed + ipaddress.IPv4Address("203.0.113.2").packed
    )
    new_ports = struct.pack("!HH", 41000, 8080)
    after[10:12] = update_checksum(
        int.from_bytes(before[10:12], "big"), before[12:20], new_addresses
    ).to_bytes(2, "big")
    if int.from_bytes(before[26:28], "big"):
        after[26:28] = update_checksum(
            int.from_bytes(before[26:28], "big"),
            before[12:20] + before[20:24],
            new_addresses + new_ports,
            udp=True,
        ).to_bytes(2, "big")
    after[12:20], after[20:24] = new_addresses, new_ports
    return after.hex()


def check_icmp_translation(incoming, outgoing):
    require(
        incoming["quotedHeader"] == WIRE
        and outgoing["quotedHeader"] == ORIGINAL
        and outgoing["quoteHex"] == translated_quote(incoming["quoteHex"]),
        "Received ICMP whole quote incremental NAT disagrees.",
    )
    require(
        outgoing["sourceAddress"] == "203.0.113.2"
        and outgoing["destinationAddress"] == "192.0.2.2"
        and outgoing["ttl"] == incoming["ttl"] - 1
        and outgoing["ipId"] == incoming["ipId"]
        and outgoing["tos"] == incoming["tos"]
        and outgoing["ipLength"] == incoming["ipLength"]
        and outgoing["nextHopMTU"] == incoming["nextHopMTU"]
        and not outgoing["dontFragment"],
        "Received ICMP outer forwarding metadata disagrees.",
    )
    require(
        outgoing["quotedIpChecksum"] == incoming["quotedIpChecksum"]
        and outgoing["quotedUdpChecksum"]["status"] == incoming["quotedUdpChecksum"]["status"],
        "Received ICMP NAT repaired an invalid quoted checksum or changed completeness.",
    )


def check_trace(trace, incoming, outgoing, disposition, related, forward_handles):
    stages = trace["stages"]
    require(
        stages and (stages[0]["table"], stages[0]["chain"]) == ("netlib_trace", "before"),
        "Missing native trace start.",
    )
    protocol = incoming["protocol"]
    actual = [(row["table"], row["chain"]) for row in stages]
    expected = [
        ("netlib_trace", "before"),
        ("netlib_received", "tracked"),
        ("netlib_tracking", "prerouting"),
    ]
    fresh = ("netlib_nat", "destination") in actual
    if fresh:
        expected += [("netlib_nat", "destination")]
    expected += [("netlib_trace", "afterDestination")]
    if disposition == "local-drop":
        expected += [("netlib_received", "input")]
    elif disposition != "ttl-drop":
        expected += [("netlib", "forward")]
    if disposition == "forwarded":
        expected += [("netlib_trace", "beforeSource")]
        if ("netlib_nat", "source") in actual:
            expected += [("netlib_nat", "source")]
        expected += [("netlib_trace", "afterSource"), ("netlib_late", "late")]
    require(actual == expected, "Native hook order or complete visit set disagrees.")
    first = incoming["fragments"][0] if protocol == 17 else incoming
    for row in stages:
        chain = row["chain"]
        pre = chain in (
            "before",
            "tracked",
            "prerouting",
            "destination",
            "afterDestination",
            "input",
        )
        require(
            row["protocol"] == protocol
            and row["ipId"] == incoming["ipId"]
            and row["ipLength"] == incoming["ipLength"]
            and row["tos"] == incoming["tos"]
            and row["ttl"] == incoming["ttl"] - (not pre)
            and row["iif"] == first["interface"]
            and row["oif"]
            == (None if pre else "service0" if first["interface"] == "auth0" else "auth0"),
            "Native hook IPv4 metadata or interfaces disagree.",
        )
        before_destination = chain in ("before", "tracked", "prerouting", "destination")
        after_source = chain in ("afterSource", "late")
        if protocol == 17:
            original = incoming["header"]
            if before_destination:
                packet = original
            elif after_source:
                packet = WIRE if original == ORIGINAL else PEER_REPLY
            else:
                packet = {
                    **original,
                    "destination": "198.51.100.2" if original == ORIGINAL else "192.0.2.2",
                    "destinationPort": 9000 if original == ORIGINAL else 41000,
                }
            payload = bytes.fromhex(incoming["payloadHex"])
            udp = (
                struct.pack(
                    "!HHHH", packet["sourcePort"], packet["destinationPort"], 8 + len(payload), 0
                )
                + payload
            )
            pseudo = (
                ipaddress.IPv4Address(packet["source"]).packed
                + ipaddress.IPv4Address(packet["destination"]).packed
                + bytes((0, 17))
                + len(udp).to_bytes(2, "big")
            )
            require(
                row["packet"] == packet
                and row["udpLength"] == len(udp)
                and row["udpChecksum"]
                == ((checksum(pseudo + udp) or 65535) if incoming["udpChecksum"]["value"] else 0),
                "Native whole UDP hook checksum or tuple disagrees.",
            )
        else:
            source = "203.0.113.2" if after_source else incoming["sourceAddress"]
            destination = (
                "192.0.2.2"
                if related and not before_destination
                else incoming["destinationAddress"]
            )
            require(
                row["sourceAddress"] == source
                and row["destinationAddress"] == destination
                and row["nextHopMTU"] == incoming["nextHopMTU"],
                "Native received ICMP hook tuple or MTU disagrees.",
            )
        require(row["verdicts"], "Native hook lacks terminal evidence.")
        terminal = row["verdicts"][-1]["verdict"]
        wanted = (
            "drop"
            if row is stages[-1] and disposition in ("local-drop", "filter-drop")
            else "accept"
        )
        require(terminal == wanted, "Native hook terminal verdict disagrees.")
        if (row["table"], row["chain"]) == ("netlib", "forward"):
            rule_name = (
                "RECEIVED_CONTROL"
                if protocol == 1
                else "REQUEST"
                if incoming["header"] == ORIGINAL
                else "REPLY"
            )
            require(
                len(row["verdicts"]) == 1
                and row["verdicts"][0]["text"]
                == (
                    f"unknown rule handle {forward_handles[rule_name]}"
                    if disposition == "forwarded"
                    else "policy drop"
                ),
                "Native accepting rule handle does not resolve to the exported current rule.",
            )
    tracked = stages[1]["verdicts"]
    if protocol == 1:
        marker = "RECEIVED_RELATED" if related else "RECEIVED_INVALID"
        state = "related" if related else "invalid"
        require(
            len(tracked) == 2
            and re.fullmatch(
                rf'rule meta l4proto icmp ct state {state} counter packets [0-9]+ bytes [0-9]+ comment "{marker}"',
                tracked[0]["text"],
            )
            and tracked[0]["verdict"] == "continue"
            and tracked[1]["text"] == "policy accept",
            "Native received ICMP conntrack class trace disagrees.",
        )
    else:
        require(len(tracked) == 1, "UDP matched ICMP tracking scope.")
    if outgoing is not None and protocol == 17:
        require(
            outgoing["header"] == (WIRE if incoming["header"] == ORIGINAL else PEER_REPLY)
            and outgoing["payloadHex"] == incoming["payloadHex"]
            and outgoing["ttl"] == incoming["ttl"] - 1
            and outgoing["ipId"] == incoming["ipId"],
            "Native UDP NAT forwarding disagrees.",
        )
        require(
            all(
                outgoing[key] == incoming[key]
                for key in ("tos", "dontFragment", "ipLength", "udpLength")
            )
            and outgoing["udpChecksum"]["status"] == incoming["udpChecksum"]["status"]
            and outgoing["udpChecksum"]["value"]
            == next(row["udpChecksum"] for row in stages if row["chain"] == "afterSource"),
            "Native UDP forwarding metadata or checksum omission disagrees.",
        )


def expected_other_objects():
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
                    {"counter": {}},
                ],
            }
        },
    ]
    trace = nat.trace_objects()
    trace[-1]["rule"]["expr"][0]["match"]["right"] = {"set": [1, 17]}
    received = [
        {"table": {"family": "ip", "name": "netlib_received"}},
        nat.chain("netlib_received", "tracked", "filter", "prerouting", -199),
        nat.chain("netlib_received", "input", "filter", "input", 0, "drop"),
    ]
    for state, comment in ((4, "RECEIVED_RELATED"), (1, "RECEIVED_INVALID")):
        received.append(
            {
                "rule": {
                    "family": "ip",
                    "table": "netlib_received",
                    "chain": "tracked",
                    "comment": comment,
                    "expr": [
                        {"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}},
                        {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": state}},
                        {"counter": {}},
                    ],
                }
            }
        )
    return (
        tracking
        + nat.expected_nat()
        + [
            {"table": {"family": "ip", "name": "netlib_late"}},
            nat.chain("netlib_late", "late", "filter", "postrouting", 200),
        ]
        + trace
        + received
    )


def control_rule():
    return {
        "family": "ip",
        "table": "netlib",
        "chain": "forward",
        "comment": "RECEIVED_CONTROL",
        "expr": [
            {"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}},
            {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": 4}},
            {"accept": None},
        ],
    }


def check_exports(directory, exports, commands, policies, policy, frames, control=False):
    require(
        set(exports) == {"firewall", "nat", "late", "received", "ruleset"},
        "Incomplete exclusive native policy export.",
    )
    documents = {key: copied(directory, record, commands) for key, record in exports.items()}
    firewall = copy.deepcopy(documents["firewall"])
    if control:
        rules = [row["rule"] for row in firewall["nftables"] if "rule" in row]
        first = {key: value for key, value in rules[0].items() if key != "handle"}
        require(
            first == control_rule(),
            "Received control permission changed its explicit RELATED scope.",
        )
        firewall["nftables"] = [row for row in firewall["nftables"] if row.get("rule") != rules[0]]
    require(
        admission.canonical_table(firewall) == policies[policy],
        "Native UDP policy differs from compiled permission.",
    )
    full = documents["ruleset"]["nftables"]
    for key, table in (
        ("firewall", "netlib"),
        ("nat", "netlib_nat"),
        ("late", "netlib_late"),
        ("received", "netlib_received"),
    ):
        subset = [
            row
            for row in full
            if "metainfo" in row
            or any(
                value.get("name" if kind == "table" else "table") == table
                for kind, value in row.items()
                if kind != "metainfo"
            )
        ]
        require(
            subset == documents[key]["nftables"],
            "Complete ruleset contradicts individual native table export.",
        )
    others = [
        row
        for row in nat.objects(documents["ruleset"])
        if next(iter(row.values())).get("table", next(iter(row.values())).get("name")) != "netlib"
    ]
    time = exports["ruleset"]["command"]["startNs"]
    for row in others:
        if "rule" in row:
            rule = row["rule"]
            for expression in rule["expr"]:
                if "counter" in expression:
                    if rule["table"] == "netlib_tracking":
                        selected = [
                            f
                            for f in frames
                            if f["namespace"] == "auth"
                            and f["packetType"] == 0
                            and f["protocol"] == 17
                            and f["timeNs"] < time
                        ]
                    else:
                        invalid = rule["comment"] == "RECEIVED_INVALID"
                        selected = [
                            f
                            for f in frames
                            if f["namespace"] == "auth"
                            and f["packetType"] == 0
                            and f["protocol"] == 1
                            and f["timeNs"] < time
                            and (f["label"] in INVALID) == invalid
                        ]
                    require(
                        expression["counter"]
                        == {
                            "packets": len(selected),
                            "bytes": sum(f["ipLength"] for f in selected),
                        },
                        "Native RELATED/INVALID or UDP counters contradict complete ingress capture.",
                    )
                    expression["counter"] = {}
    require(
        others == expected_other_objects(),
        "Additional hook, policy, or rule outside the exclusive capture scope.",
    )


def check_error(row, outgoing, origin, mtu_value):
    result = row["result"]
    if origin is None:
        require(result is None, "Unexpected host socket error feedback.")
        return
    require(
        result is not None
        and len(result["ancillary"]) == 1
        and result["peer"] == ["203.0.113.2", 8080]
        and result["flags"] == 8192,
        "Missing native socket error queue record.",
    )
    ancillary = result["ancillary"][0]
    raw = bytes.fromhex(ancillary["hex"])
    require(
        len(raw) == 32 and ancillary["level"] == 0 and ancillary["type"] == 11,
        "Malformed native extended socket error.",
    )
    decoded = dict(
        zip(
            ("errno", "origin", "icmpType", "icmpCode", "pad", "info", "data"),
            struct.unpack("=IBBBBII", raw[:16]),
        )
    )
    require(
        all(ancillary[key] == value for key, value in decoded.items())
        and decoded
        == {
            "errno": 90,
            "origin": origin,
            "icmpType": 3 if origin == 2 else 0,
            "icmpCode": 4 if origin == 2 else 0,
            "pad": 0,
            "info": mtu_value,
            "data": 0,
        },
        "Native error queue raw errno, origin, ICMP code, or MTU disagrees.",
    )
    if origin == 2:
        require(
            raw[16:18] == b"\x02\x00"
            and str(ipaddress.IPv4Address(raw[20:24])) == "203.0.113.2"
            and outgoing is not None
            and result["payloadHex"] == outgoing["quoteHex"][56:],
            "Native error queue offender or quoted payload disagrees.",
        )
    else:
        require(
            not any(raw[16:]) and result["payloadHex"] == "",
            "Native local PMTU error has network offender or payload.",
        )


def check_probe_order(episode, frames):
    native = episode["origin"] == "native-host"
    keys = ("mtuBefore", "sent", "error", "mtu") if native else ("sent", "error", "mtu")
    for key in keys:
        admission.interval(episode[key], episode)
    require(
        all(
            episode[left]["endNs"] <= episode[right]["startNs"]
            for left, right in zip(keys, keys[1:])
        )
        and episode["before"]["command"]["endNs"]
        < episode["routeBefore"]["startNs"]
        < episode["routeBefore"]["endNs"]
        < episode[keys[0]]["startNs"]
        and episode["mtu"]["endNs"]
        <= episode["routeAfter"]["startNs"]
        < episode["routeAfter"]["endNs"]
        < episode["after"]["command"]["startNs"],
        "Native probe RPC and route observation order disagrees.",
    )
    host_errors = [row for row in frames if row["namespace"] == "peer" and row["protocol"] == 1]
    if host_errors:
        require(
            len(host_errors) == 1
            and episode["sent"]["startNs"]
            <= host_errors[0]["timeNs"]
            < episode["error"]["startNs"],
            "Native host-bound ICMP read is outside its send and error-queue RPC fences.",
        )
    if native:
        require(
            episode["routeAfter"]["endNs"]
            <= episode["server"]["startNs"]
            < episode["server"]["endNs"]
            < episode["after"]["command"]["startNs"],
            "Native server receive RPC order disagrees.",
        )
        if episode["reply"] is not None:
            require(
                episode["server"]["endNs"]
                <= episode["reply"]["startNs"]
                < episode["reply"]["endNs"]
                <= episode["client"]["startNs"]
                < episode["client"]["endNs"]
                < episode["after"]["command"]["startNs"],
                "Native smaller UDP reply RPC order disagrees.",
            )


def check_capture(directory, *, input_directory=DIRECTORY):
    directory, input_directory = Path(directory), Path(input_directory)
    sources = {
        "/task/admission/exercise.py": "examples/admission/exercise.py",
        "/task/wire/exercise.py": "examples/wire/exercise.py",
        "/task/eap_exercise.py": "examples/eap/exercise.py",
        "/task/capture_conntrack.py": "scripts/capture_conntrack.py",
        "/task/mtu/exercise.py": "examples/mtu/exercise.py",
        "/task/icmp/exercise.py": "examples/icmp/exercise.py",
        "/task/received-icmp/exercise.py": "examples/received-icmp/exercise.py",
    }
    captured_sources = dict(
        reversed(line.split("  "))
        for line in (directory / "helper-sha256.txt").read_text().splitlines()
    )
    require(
        captured_sources
        == {
            path: hashlib.sha256((ROOT / source).read_bytes()).hexdigest()
            for path, source in sources.items()
        },
        "Captured native producer source bytes differ from retained source hashes.",
    )
    observations = read_json(directory / "observations.json")
    require(
        observations["schema"] == 1 and observations["scope"] == "received-icmp-pmtu",
        "Unexpected received ICMP observation schema.",
    )
    commands = read_json(directory / "commands.json")
    for row in commands:
        admission.interval(row)
        require(row["returncode"] == 0, "Failed native command retained as successful evidence.")
    routing, offloads = check_network(directory, observations, commands)
    require(
        observations["traceCommand"] == ["ip", "netns", "exec", "auth", "nft", "monitor", "trace"]
        and (directory / "trace-errors.txt").read_text() == "",
        "Native trace producer failed or changed.",
    )
    policies = {
        name: admission.canonical_table(read_json(input_directory / f"{name}.json"))
        for name in ("deny", "permit")
    }
    require(
        policies["deny"] == []
        and policies["permit"]
        == [
            {
                "id": "REQUEST",
                **{**ORIGINAL, "destination": "198.51.100.2", "destinationPort": 9000},
            },
            {"id": "REPLY", **{**WIRE_REPLY, "destination": "192.0.2.2", "destinationPort": 41000}},
        ],
        "Declared UDP compiler policy scope changed.",
    )
    for name in ("deny.json", "permit.json", "requirements.json", "demo-credential.json"):
        require(
            read_json(directory / "input" / name) == read_json(input_directory / name),
            "Native generated input copy differs.",
        )
    authentication = admission.check_eap(directory / "eap", observations["eap"])
    eap_frames = authentication["phases"][0]["frames"]
    credential = read_json(directory / "installed-demo-credential.json")
    require(
        credential == read_json(input_directory / "demo-credential.json"),
        "Installed credential differs from declared compiler input.",
    )
    nat.copied_command(observations["credentialInstall"], commands)
    nat.copied_command(observations["logoff"], commands)
    stages, feedback, probes = (
        observations["stages"],
        observations["hostFeedback"],
        observations["receivedProbes"],
    )
    require(
        observations["connectedSocket"]["result"]
        == {
            "peer": ["203.0.113.2", 8080],
            "mtuDiscover": 2,
            "receiveErrors": 1,
            "initialMTU": 4096,
        },
        "Native connected socket DF, IP_RECVERR, or initial IP_MTU disagrees.",
    )
    require(
        [row["stage"] for row in stages]
        == ["unauthenticated", "authenticated-only", "credential-permitted", "logged-off-cached"]
        and [row["name"] for row in feedback]
        == ["native-df-oversize", "cached-pmtu-emsgsize", "pmtu-small-roundtrip"]
        and [row["name"] for row in probes] == RAW_NAMES,
        "Native episode sequence changed.",
    )
    episodes = stages + feedback + probes
    for index, episode in enumerate(episodes):
        admission.interval(episode)
        if index:
            require(
                episodes[index - 1]["endNs"] < episode["startNs"],
                "Native episode windows overlap or reorder.",
            )
    frames = []
    for ns in LINKS:
        filename = f"frames-{ns}.jsonl"
        rows = [json.loads(line) for line in (directory / filename).read_text().splitlines()]
        require(
            all(rows[i]["timeNs"] < rows[i + 1]["timeNs"] for i in range(len(rows) - 1)),
            "Native per-sniffer read clock is not ordered.",
        )
        for number, row in enumerate(rows, 1):
            decoded = decode_frame(row, number, filename)
            require(
                decoded["namespace"] == ns, "Native frame namespace differs from sniffer artifact."
            )
            selected = [
                episode
                for episode in episodes
                if episode["startNs"] < decoded["timeNs"] < episode["endNs"]
            ]
            require(
                len(selected) == 1,
                "Native frame is outside every uniquely assigned observation window.",
            )
            episode = selected[0]
            decoded["label"] = episode.get("name", episode.get("stage"))
            final = episode.get("state", episode.get("after"))["command"]
            require(
                episode["sent"]["startNs"] <= decoded["timeNs"] < final["startNs"],
                "Packet userspace read is outside send and post-state fences.",
            )
            frames.append(decoded)
    frames.sort(key=lambda row: row["timeNs"])
    # Both ends of every veth retain the same observed Ethernet bytes.
    for interface, opposite in (
        ("auth0", "peer0"),
        ("service0", "router0"),
        ("srvlink", "server0"),
    ):
        for kind in (0, 4):
            left = sorted(
                row["raw"]
                for row in frames
                if row["interface"] == interface and row["packetType"] == kind
            )
            right = sorted(
                row["raw"]
                for row in frames
                if row["interface"] == opposite and row["packetType"] == 4 - kind
            )
            require(left == right, "Native link endpoint captures disagree or omit a packet.")
    traces = parse_traces(directory / "trace.txt")
    incoming = sorted(
        (row for row in frames if row["namespace"] == "auth" and row["packetType"] == 0),
        key=lambda row: row["timeNs"],
    )
    require(
        len(traces) == len(incoming), "Native trace count differs from all gateway ingress packets."
    )
    traces_by_source = dict(zip((row["source"] for row in incoming), traces))
    consumed_snapshots = {"files": set(), "commands": set()}
    initial = check_snapshot(
        directory,
        observations["initial"],
        commands,
        "initial",
        0,
        stages[0]["load"]["startNs"],
        consumed_snapshots,
    )
    require(initial == [], "Native initial conntrack table is not empty.")
    reports, samples = [], []
    consumed_links = {"files": set(), "commands": set()}
    old_id = None
    for index, episode in enumerate(episodes):
        name = episode.get("name", episode.get("stage"))
        selected = [row for row in frames if row["label"] == name]
        udp = families(selected)
        errors = [row for row in selected if row["protocol"] == 1]
        for operation in ("sent", "server", "reply", "client"):
            record = episode.get(operation)
            if record is not None:
                admission.interval(record, episode)
        if index < 7 and index != 5:
            request_payload = episode["sent"]["result"]["payload"]
            require(
                all(
                    row["payloadHex"] == request_payload.encode().hex()
                    for row in udp
                    if row["header"] in (ORIGINAL, WIRE)
                ),
                "Native socket request payload differs from captured UDP.",
            )
            if episode["server"]["result"] is not None:
                require(
                    episode["server"]["result"]
                    == {"source": "203.0.113.1", "sourcePort": 40000, "payload": request_payload},
                    "Native server receive tuple or payload disagrees.",
                )
            if episode.get("reply") is not None:
                reply_payload = episode["reply"]["result"]["payload"]
                require(
                    episode["client"]["result"]
                    == {"source": "203.0.113.2", "sourcePort": 8080, "payload": reply_payload}
                    and all(
                        row["payloadHex"] == reply_payload.encode().hex()
                        for row in udp
                        if row["header"] in (WIRE_REPLY, PEER_REPLY)
                    ),
                    "Native client receive tuple or reply payload disagrees.",
                )
        if index < 4:
            require(
                episode["policy"] == ("permit" if index == 2 else "deny"),
                "Native EAP stage policy differs.",
            )
            check_exports(
                directory, episode["exports"], commands, policies, episode["policy"], frames
            )
            state = check_snapshot(
                directory,
                episode["state"],
                commands,
                name,
                episode["client"]["endNs"],
                episode["endNs"],
                consumed_snapshots,
            )
            require(
                (len(state), state[0]["status"] if state else None)
                == ((0, None) if index < 2 else (1, 442)),
                "Native four-stage conntrack confirmation disagrees.",
            )
            if index >= 2:
                require(old_id in (None, state[0]["id"]), "Native Logoff replaced the cached flow.")
                old_id = state[0]["id"]
            count = sum(frame["timeNs"] < episode["sent"]["startNs"] for frame in eap_frames)
            require(count == (0, 16, 16, 18)[index], "Native EAP stage prefix differs.")
            reports.append(
                {
                    "name": name,
                    "eapFramesBeforeSend": count,
                    "credentialInstalled": index >= 2,
                    "delivered": index == 2,
                    "firewallFile": episode["exports"]["firewall"]["file"],
                    "observations": episode,
                    "cachedRow": state[0] if state else None,
                }
            )
            require(
                not errors and len(udp) == (12 if index == 2 else 2),
                "Native EAP stage packet coverage disagrees.",
            )
            require(
                (episode["server"]["result"] is not None) == (index == 2)
                and (episode["client"]["result"] is not None) == (index == 2),
                "Native EAP UDP delivery disagrees with compiled permission.",
            )
            request_payload = episode["sent"]["result"]["payload"].encode().hex()
            require(
                episode["sent"]["result"]["bytesSent"] == 1200
                and all(
                    row["payloadHex"] == request_payload
                    for row in udp
                    if row["header"] in (ORIGINAL, WIRE)
                ),
                "Native EAP socket request differs from raw UDP.",
            )
            before = None
            if episode["load"] is not None:
                nat.copied_command(episode["load"], commands)
                batch = read_json(directory / episode["load"]["batch"])
                source = read_json(directory / episode["load"]["input"])["nftables"]
                expected = (
                    source
                    if index == 0
                    else [
                        source[0],
                        {"delete": {"table": {"family": "ip", "name": "netlib"}}},
                        *source[1:],
                    ]
                )
                require(
                    batch == {"nftables": expected}
                    and episode["load"]["endNs"] < episode["startNs"],
                    "Native policy load differs from generated transaction.",
                )
            else:
                require(index == 1, "Missing native generated policy load.")
        else:
            before = check_snapshot(
                directory,
                episode["before"],
                commands,
                f"{name}-before",
                episode["startNs"],
                episode["routeBefore"]["startNs"],
                consumed_snapshots,
            )
            state = check_snapshot(
                directory,
                episode["after"],
                commands,
                f"{name}-after",
                episode["sent"]["endNs"],
                episode["endNs"],
                consumed_snapshots,
            )
            for phase in ("Before", "After"):
                record = episode[f"route{phase}"]
                nat.copied_command(record, commands)
                admission.successful_command(
                    record, ["ip", "-n", "peer", "-j", "route", "get", "203.0.113.2"]
                )
                route = json.loads(record["stdout"])
                require(len(route) == 1, "Missing native peer route exception observation.")
                route = route[0]
                metrics = (
                    {}
                    if index == 4 and phase == "Before"
                    else {
                        "expires": route.get("expires"),
                        "metrics": [
                            {
                                "mtu": 576
                                if name == "forged-outer-source" and phase == "After"
                                else 600
                            }
                        ],
                    }
                )
                require(
                    route
                    == {
                        "dst": "203.0.113.2",
                        "gateway": "192.0.2.1",
                        "dev": "peer0",
                        "prefsrc": "192.0.2.2",
                        "flags": [],
                        "uid": 0,
                        "cache": [],
                        **metrics,
                    }
                    and (not metrics or 0 < route["expires"] <= 600)
                    and episode["startNs"]
                    < record["startNs"]
                    < record["endNs"]
                    < (
                        episode["sent"]["startNs"]
                        if phase == "Before"
                        else episode["after"]["command"]["startNs"]
                    ),
                    "Native peer PMTU exception, expiry, or route observation fence disagrees.",
                )
            expected_status = 440 if index < 6 else 442
            require(
                len(state) == 1 and state[0]["status"] == expected_status,
                "Received ICMP or local PMTU send changed seen-reply state.",
            )
            if index == 4:
                require(before == [], "Native DF experiment did not begin with a fresh flow.")
                old_id = state[0]["id"]
            else:
                require(
                    len(before) == 1 and before[0]["id"] == state[0]["id"] == old_id,
                    "Received ICMP replaced its associated cached flow.",
                )
                if index != 6:
                    require(
                        before[0]["status"] == state[0]["status"]
                        and state[0]["remainingTTL"] <= before[0]["remainingTTL"],
                        "Received ICMP refreshed or changed cached UDP state.",
                    )
            require(
                episode["before"]["command"]["endNs"]
                < episode["sent"]["startNs"]
                < episode["sent"]["endNs"]
                < episode["after"]["command"]["startNs"],
                "Native probe send and raw Netlink state fences disagree.",
            )
            if index < 7:
                require(
                    episode["origin"] == "native-host", "Native host feedback origin is mislabeled."
                )
                require(
                    episode["mtuBefore"]["result"] == {"mtu": 4096 if index == 4 else 600}
                    and episode["mtuBefore"]["endNs"] < episode["sent"]["startNs"],
                    "Native per-send host IP_MTU readback disagrees.",
                )
                require(
                    all(row["dontFragment"] for row in udp if row["header"] in (ORIGINAL, WIRE)),
                    "Native connected IP_PMTUDISC_DO request is missing DF.",
                )
                if index == 4:
                    require(
                        len(udp) == 4
                        and len(errors) == 4
                        and episode["server"]["result"] is None
                        and episode["sent"]["result"]["bytesSent"] == 1200,
                        "Native router DF error lacks complete path witnesses.",
                    )
                elif index == 5:
                    require(
                        not selected
                        and episode["sent"]["result"]["errno"] == 90
                        and episode["server"]["result"] is None,
                        "Native cached PMTU did not prevent a second wire send.",
                    )
                else:
                    require(
                        len(udp) == 12
                        and not errors
                        and episode["sent"]["result"]["bytesSent"] == 500
                        and episode["server"]["result"] is not None
                        and episode["client"]["result"] is not None,
                        "Native smaller UDP roundtrip lacks complete path witnesses.",
                    )
            else:
                require(
                    episode["origin"] == "raw-synthetic-sender" and not udp,
                    "Raw probe origin or transport scope differs.",
                )
                raw_input = read_json(directory / episode["input"])
                nat.copied_command(episode["sent"], commands)
                admission.successful_command(
                    episode["sent"],
                    [
                        "ip",
                        "netns",
                        "exec",
                        "router",
                        "python3",
                        "/task/received-icmp/exercise.py",
                        "raw-send",
                        f"/tmp/netlib-admission/{name}-input.json",
                        "router0",
                    ],
                )
                require(
                    episode["input"] == f"{name}-input.json" and raw_input["name"] == name,
                    "Raw sender input artifact is misbound.",
                )
                produced = json.loads(episode["sent"]["stdout"])
                admission.interval(produced, episode["sent"])
                require(
                    raw_input["origin"] == "raw-synthetic-sender"
                    and raw_input["raw"] == produced["raw"]
                    and produced["bytesSent"] == len(bytes.fromhex(produced["raw"]))
                    and sum(row["raw"] == produced["raw"] for row in errors) == 2,
                    "Raw probe bytes differ from unchanged native producer output.",
                )
                require(
                    len(errors) == (2 if name in INVALID or name == "ttl-one-control" else 4),
                    "Received ICMP drop or forwarding path coverage disagrees.",
                )
            outgoing_error = next(
                (row for row in errors if row["interface"] == "auth0" and row["packetType"] == 4),
                None,
            )
            origin = (
                2
                if index == 4
                or name in ("full-bad-udp-checksum", "bad-inner-ip-checksum", "forged-outer-source")
                else 1
                if index == 5
                else None
            )
            value = 576 if name == "forged-outer-source" else 600
            check_error(episode["error"], outgoing_error, origin, value)
            check_probe_order(episode, selected)
            require(
                episode["mtu"]["result"] == {"mtu": value},
                "Native connected host IP_MTU readback disagrees.",
            )
            for key in ("error", "mtu"):
                admission.interval(episode[key], episode)
                require(
                    episode[key]["endNs"] < episode["after"]["command"]["startNs"],
                    "Native host feedback follows the assigned post-state snapshot.",
                )
        links = episode.get("requestLinks") if index < 4 else episode.get("links")
        check_send_links(
            directory,
            links,
            commands,
            f"{name}-request" if index < 4 else name,
            episode["startNs"] if index < 4 else episode["routeBefore"]["endNs"],
            episode["mtuBefore"]["startNs"] if 4 <= index < 7 else episode["sent"]["startNs"],
            consumed_links,
        )
        if index == 2:
            check_send_links(
                directory,
                episode.get("replyLinks"),
                commands,
                f"{name}-reply",
                episode["server"]["endNs"],
                episode["reply"]["startNs"],
                consumed_links,
            )
        elif index < 4:
            require(
                episode.get("replyLinks") is None,
                "Unexpected per-send link export for a denied reply.",
            )
        post = episode.get("state", episode.get("after"))
        firewall = read_json(
            directory
            / (episode["exports"] if index < 4 else observations["probeExports"])["firewall"][
                "file"
            ]
        )
        forward_handles = {
            row["rule"]["comment"]: row["rule"]["handle"]
            for row in firewall["nftables"]
            if "rule" in row
        }
        edge_inputs = [
            row for row in selected if row["namespace"] == "auth" and row["packetType"] == 0
        ]
        for position, frame in enumerate(sorted(edge_inputs, key=lambda row: row["timeNs"])):
            protocol = frame["protocol"]
            if protocol == 17:
                ingress = next(row for row in udp if frame in row["fragments"])
                outputs = [
                    row
                    for row in udp
                    if row["namespace"] == "auth"
                    and row["packetType"] == 4
                    and row["payloadHex"] == ingress["payloadHex"]
                ]
                require(len(outputs) <= 1, "Multiple UDP gateway outputs for one ingress.")
                output = outputs[0] if outputs else None
                disposition = "forwarded" if output else "filter-drop"
                related = False
                label = f"{name}-{'request' if frame['interface'] == 'auth0' else 'reply'}"
            else:
                ingress = frame
                outputs = [
                    row for row in errors if row["interface"] == "auth0" and row["packetType"] == 4
                ]
                require(len(outputs) <= 1, "Multiple received ICMP outputs for one ingress.")
                output = outputs[0] if outputs else None
                related = name not in INVALID
                disposition = "forwarded" if output else "local-drop" if not related else "ttl-drop"
                label = name
                if output:
                    check_icmp_translation(ingress, output)
            trace = traces_by_source[frame["source"]]
            check_trace(trace, ingress, output, disposition, related, forward_handles)
            raw_outputs = (
                [row["raw"] for row in output["fragments"]]
                if output and protocol == 17
                else [output["raw"]]
                if output
                else []
            )
            samples.append(
                {
                    "label": label,
                    "config": name if index < 4 else "received-probes",
                    "zone": 0,
                    "raw": frame["raw"],
                    "observed": {"forwarded": raw_outputs, "icmpOutput": []},
                    "stateFile": post["file"],
                    "linkMTUExports": links,
                    "ingress": ingress,
                    "outputFamily": output,
                    "trace": trace,
                    "disposition": disposition,
                    "related": related,
                    "origin": "raw-synthetic-sender" if index >= 7 else "native-host",
                }
            )
        # Every routed UDP datagram has a separately checked downstream TTL step.
        for row in udp:
            if row["namespace"] == "router" and row["packetType"] == 0:
                outputs = [
                    candidate
                    for candidate in udp
                    if candidate["namespace"] == "router"
                    and candidate["packetType"] == 4
                    and candidate["header"] == row["header"]
                    and candidate["payloadHex"] == row["payloadHex"]
                ]
                if name == "native-df-oversize":
                    require(
                        not outputs and row["dontFragment"] and row["ipLength"] > 600,
                        "Router DF/MTU trigger disagrees.",
                    )
                    error = next(
                        candidate for candidate in errors if candidate["namespace"] == "router"
                    )
                    raw_ip = bytes.fromhex(row["fragments"][0]["raw"])[14:]
                    require(
                        error["sourceAddress"] == "198.51.101.254"
                        and error["destinationAddress"] == "203.0.113.1"
                        and error["ttl"] == 64
                        and error["tos"] == 192
                        and error["quoteHex"] == raw_ip[:548].hex()
                        and error["nextHopMTU"] == 600,
                        "Genuine downstream router ICMP error does not quote the exact SNAT wire prefix.",
                    )
                else:
                    require(
                        len(outputs) == 1
                        and outputs[0]["ttl"] == row["ttl"] - 1
                        and outputs[0]["ipId"] == row["ipId"]
                        and all(
                            outputs[0][key] == row[key]
                            for key in (
                                "tos",
                                "dontFragment",
                                "ipLength",
                                "udpLength",
                                "udpChecksum",
                            )
                        )
                        and outputs[0]["ipPayloadHex"] == row["ipPayloadHex"],
                        "Downstream router UDP forwarding, checksum, or fragment reassembly disagrees.",
                    )
    require(
        len(samples) == 15 and sum(row["ingress"]["protocol"] == 1 for row in samples) == 7,
        "Finite native gateway ingress coverage changed.",
    )
    baseline = next(
        row["ingress"]["quoteHex"] for row in samples if row["label"] == "native-df-oversize"
    )
    full_baseline = next(
        row["outputFamily"]["fragments"][0]["raw"]
        for row in samples
        if row["label"] == "pmtu-small-roundtrip-request"
    )
    full_baseline = bytes.fromhex(full_baseline)[14:]
    for raw_index, name in enumerate(RAW_NAMES):
        sample = next(row for row in samples if row["label"] == name)
        incoming = sample["ingress"]
        quote = bytearray(
            full_baseline if name == "full-bad-udp-checksum" else bytes.fromhex(baseline)
        )
        if name == "unmatched-quote":
            quote[26:28] = update_checksum(
                int.from_bytes(quote[26:28], "big"),
                (40000).to_bytes(2, "big"),
                (40001).to_bytes(2, "big"),
                udp=True,
            ).to_bytes(2, "big")
            quote[20:22] = (40001).to_bytes(2, "big")
        elif name == "full-bad-udp-checksum":
            quote[26] ^= 1
        elif name == "bad-inner-ip-checksum":
            quote[10] ^= 1
        require(
            incoming["quoteHex"] == quote.hex()
            and incoming["ipId"] == 0xED00 + raw_index
            and incoming["ttl"] == (1 if name == "ttl-one-control" else 64)
            and incoming["sourceAddress"]
            == ("198.51.100.99" if name == "forged-outer-source" else "198.51.101.254")
            and incoming["destinationAddress"]
            == ("203.0.113.2" if name == "wrong-outer-destination" else "203.0.113.1")
            and incoming["nextHopMTU"] == (576 if name == "forged-outer-source" else 600),
            "Raw sender quote mutation, tuple, TTL, or MTU differs from declared probe.",
        )
        if name == "full-bad-udp-checksum":
            require(
                incoming["quoteComplete"] and incoming["quotedUdpChecksum"]["status"] == "invalid",
                "Missing complete invalid UDP quote counterexample.",
            )
        elif name == "bad-inner-ip-checksum":
            require(
                incoming["quotedIpChecksum"] == "invalid",
                "Missing invalid IPv4 quote counterexample.",
            )
        elif name == "forged-outer-source":
            require(
                incoming["sourceAddress"] == "198.51.100.99"
                and incoming["nextHopMTU"] == 576
                and sample["disposition"] == "forwarded",
                "Missing forged outer source limitation witness.",
            )
        elif name == "wrong-outer-destination":
            require(
                incoming["quotedHeader"] == WIRE
                and incoming["destinationAddress"] == "203.0.113.2"
                and not sample["related"],
                "Missing outer destination association guard witness.",
            )
    check_exports(
        directory, observations["probeExports"], commands, policies, "permit", frames, True
    )
    check_exports(
        directory, observations["finalExports"], commands, policies, "permit", frames, True
    )
    nat.copied_command(observations["probeLoad"], commands)
    nat.copied_command(observations["relatedRule"], commands)
    admission.successful_command(
        observations["relatedRule"],
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "nft",
            "insert",
            "rule",
            "ip",
            "netlib",
            "forward",
            "meta",
            "l4proto",
            "icmp",
            "ct",
            "state",
            "related",
            "accept",
            "comment",
            '"RECEIVED_CONTROL"',
        ],
    )
    nat.copied_command(observations["erase"]["command"], commands)
    require(
        observations["erase"]["command"]["command"]
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
        and observations["erase"]["command"]["stderr"]
        == "conntrack v1.4.9 (conntrack-tools): 1 flow entries have been deleted.\n",
        "Native targeted conntrack erase command or outcome disagrees.",
    )
    require(
        check_snapshot(
            directory,
            observations["erase"]["state"],
            commands,
            "erased",
            observations["erase"]["command"]["endNs"],
            observations["connectedSocket"]["startNs"],
            consumed_snapshots,
        )
        == [],
        "Targeted flow erasure left a cached association.",
    )
    require(
        stages[1]["endNs"]
        < observations["credentialInstall"]["startNs"]
        < observations["credentialInstall"]["endNs"]
        < stages[2]["load"]["startNs"]
        and stages[2]["endNs"]
        < observations["logoff"]["startNs"]
        < observations["logoff"]["endNs"]
        < stages[3]["load"]["startNs"]
        < stages[3]["startNs"]
        < observations["probeLoad"]["startNs"]
        < observations["relatedRule"]["startNs"]
        < feedback[0]["startNs"],
        "EAP credential, Logoff, or separate received-control policy ordering disagrees.",
    )
    return {
        "schema": 1,
        "scope": "checked-native-received-icmp-pmtu",
        "eapEvidence": authentication,
        "credential": credential,
        "credentialInstall": observations["credentialInstall"],
        "logoff": observations["logoff"],
        "stages": reports,
        "routing": routing,
        "offloads": offloads,
        "initialFile": observations["initial"]["file"],
        "packetSamples": samples,
        "hostFeedback": feedback,
        "receivedProbes": probes,
        "erase": observations["erase"],
        "frameCount": len(frames),
        "icmpFrameCount": sum(row["protocol"] == 1 for row in frames),
        "udpFragmentCount": sum(row["protocol"] == 17 for row in frames),
        "eapFrameCount": len(eap_frames),
        "limits": [
            "finite-four-private-namespaces-ipv4-udp-icmp3-4",
            "native-host-and-explicitly-labeled-raw-senders",
            "related-is-tuple-association-not-source-authentication",
            "quoted-ip-and-udp-checksums-not-validated-for-association",
            "separate-fixed-related-control-policy-after-eap-stages",
            "no-capture-authenticity-linux-refinement-or-tls-cryptography-proof",
        ],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=DIRECTORY / "native")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    evidence = check_capture(args.directory)
    if args.output:
        args.output.write_text(json.dumps(evidence, indent=2) + "\n")
    print(
        f"Checked {len(evidence['packetSamples'])} gateway ingress episodes, {evidence['frameCount']} native frames, and host PMTU 600 → EMSGSIZE → smaller UDP."
    )


if __name__ == "__main__":
    main()
