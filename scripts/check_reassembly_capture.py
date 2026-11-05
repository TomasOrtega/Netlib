"""Independently decode native NFLOG IPv4 arrival and completion observations."""

import argparse
import copy
import hashlib
import ipaddress
import json
import re
import shlex
import struct
from collections import Counter
from pathlib import Path

import check_admission_capture as admission
import check_icmp_capture as generated
import check_lifecycle_capture as lifecycle
import check_wire_capture as wire
import check_wire_nat_capture as nat
from reassembly_reference import ReassemblyOracle

EvidenceError, require = admission.EvidenceError, admission.require


def decode_ipv4(raw, protocols=(17,)):
    require(
        isinstance(raw, str) and re.fullmatch(r"(?:[0-9a-f]{2})+", raw),
        "Expected unchanged hexadecimal IPv4 bytes.",
    )
    data = bytes.fromhex(raw)
    require(
        len(data) >= 20
        and data[0] == 0x45
        and int.from_bytes(data[2:4], "big") == len(data)
        and wire.folded_sum(data[:20]) == 65535,
        "Invalid native IPv4 header, length, or checksum.",
    )
    flags = int.from_bytes(data[6:8], "big")
    require(
        not flags & 0x8000 and data[9] in protocols,
        "Unsupported reserved flag or non-UDP fragment protocol.",
    )
    return {
        "raw": raw,
        "source": str(ipaddress.IPv4Address(data[12:16])),
        "destination": str(ipaddress.IPv4Address(data[16:20])),
        "protocol": data[9],
        "ipId": int.from_bytes(data[4:6], "big"),
        "ipLength": len(data),
        "tos": data[1],
        "ttl": data[8],
        "dontFragment": bool(flags & 0x4000),
        "moreFragments": bool(flags & 0x2000),
        "offsetBytes": (flags & 8191) * 8,
        "payloadHex": data[20:].hex(),
    }


def netlink_attributes(raw):
    offset, result = 0, {}
    while offset < len(raw):
        require(len(raw) - offset >= 4, "Truncated NFLOG attribute header.")
        size, kind = struct.unpack_from("=HH", raw, offset)
        aligned = (size + 3) & ~3
        require(
            4 <= size <= aligned <= len(raw) - offset and kind not in result,
            "Malformed or duplicate NFLOG attribute.",
        )
        result[kind] = raw[offset + 4 : offset + size]
        offset += aligned
    return result


def decode_timeout(packet):
    data = bytes.fromhex(packet["payloadHex"])
    require(
        packet["protocol"] == 1
        and packet["offsetBytes"] == 0
        and not packet["moreFragments"]
        and len(data) >= 36
        and data[:2] == bytes((11, 1))
        and data[4:8] == bytes(4)
        and wire.folded_sum(data) == 65535,
        "Invalid native reassembly-timeout ICMP wrapper.",
    )
    quote = data[8:]
    require(
        quote[0] == 0x45
        and quote[9] == 17
        and wire.folded_sum(quote[:20]) == 65535
        and 28 <= len(quote) <= int.from_bytes(quote[2:4], "big"),
        "Malformed native timeout IPv4 quote prefix.",
    )
    return {
        "icmpType": 11,
        "icmpCode": 1,
        "quoteHex": quote.hex(),
        "quotedIpLength": int.from_bytes(quote[2:4], "big"),
        "quotedFlags": int.from_bytes(quote[6:8], "big"),
        "quotedTTL": quote[8],
        "quotedTOS": quote[1],
        "quotedUdpLength": int.from_bytes(quote[24:26], "big"),
    }


def decode_nflog(row, line):
    require(
        row["sender"] == [0, 0] and row["flags"] == 0,
        "NFLOG message is truncated or not from the kernel.",
    )
    raw = bytes.fromhex(row["hex"])
    require(len(raw) >= 20, "Truncated NFLOG netlink message.")
    size, kind, flags, sequence, port = struct.unpack_from("=IHHII", raw)
    require(
        size == len(raw)
        and (kind, flags, sequence, port) == (0x400, 0, 0, 0)
        and raw[16:20] == bytes((2, 0, 0, 42)),
        "Unexpected NFLOG type, family, group, or envelope.",
    )
    attrs = netlink_attributes(raw[20:])
    require({1, 9, 10, 12, 13} <= set(attrs), "Missing native NFLOG packet attributes.")
    prefix = attrs[10]
    hooks = {
        b"PRE_DEFRAG\0": 0,
        b"POST_DEFRAG\0": 0,
        b"TIMEOUT_OUTPUT\0": 3,
        b"TIMEOUT_TRACKED\0": 3,
        b"TIMEOUT_EGRESS\0": 4,
    }
    require(
        prefix in hooks and attrs[1] == bytes((8, 0, hooks[prefix], 0)),
        "NFLOG hook or prefix disagrees.",
    )
    ingress = hooks[prefix] == 0
    expected = {1, 3, 4, 8, 9, 10, 12, 13, 15, 16, 17} if ingress else {1, 5, 9, 10, 12, 13}
    require(set(attrs) in (expected, expected | {2}), "Missing or extra native NFLOG attributes.")
    require(
        len(attrs[12]) == len(attrs[13]) == 4
        and (2 not in attrs or len(attrs[2]) == 4)
        and len(attrs[4 if ingress else 5]) == 4,
        "Malformed NFLOG scalar metadata.",
    )
    if ingress:
        require(
            attrs[15] == bytes.fromhex("0001")
            and attrs[17] == bytes.fromhex("000e")
            and len(attrs[16]) == 14
            and attrs[16][12:] == bytes.fromhex("0800")
            and len(attrs[3]) == 16
            and len(attrs[8]) == 12
            and attrs[8][:4] == bytes.fromhex("00060000"),
            "Malformed NFLOG Ethernet metadata.",
        )
        require(
            attrs[8][4:10] == attrs[16][6:12] and attrs[8][10:] == bytes(2),
            "NFLOG hardware source contradicts retained Ethernet metadata.",
        )
    packet = decode_ipv4(attrs[9].hex(), (17,) if ingress else (1,))
    if not ingress:
        packet.update(decode_timeout(packet))
    return {
        "source": f"nflog.jsonl:{line}",
        "timeNs": row["timeNs"],
        "localSequence": int.from_bytes(attrs[12], "big"),
        "globalSequence": int.from_bytes(attrs[13], "big"),
        "prefix": prefix[:-1].decode("ascii"),
        "hook": hooks[prefix],
        "inputIndex": int.from_bytes(attrs[4], "big") if ingress else None,
        "outputIndex": None if ingress else int.from_bytes(attrs[5], "big"),
        "mark": int.from_bytes(attrs.get(2, bytes(4)), "big"),
        "hardwareHex": attrs[16].hex() if ingress else None,
        "kernelTimestampHex": attrs[3].hex() if ingress else None,
        "packet": packet,
    }


def check_nflog_configuration(ready):
    require(
        ready["group"] == 42
        and ready["receiveBuffer"] >= 131072
        and len(ready["configuration"]) == 2,
        "Incomplete native NFLOG capture configuration.",
    )
    expected = [
        {1: bytes((3,))},
        {
            1: bytes((1,)),
            2: struct.pack("!IBB", 65531, 2, 0),
            4: struct.pack("!I", 1),
            5: struct.pack("!I", 1),
            6: struct.pack("!H", 3),
        },
    ]
    previous = 0
    for index, record in enumerate(ready["configuration"]):
        admission.interval(record)
        request = bytes.fromhex(record["request"])
        acknowledgment = bytes.fromhex(record["acknowledgment"])
        require(
            len(request) >= 20
            and struct.unpack_from("=IHHII", request)
            == (len(request), 0x401, 5, index + 1, ready["port"])
            and request[16:20] == bytes((2, 0, 0, 0 if index == 0 else 42))
            and netlink_attributes(request[20:]) == expected[index],
            "Native NFLOG binary configuration request disagrees.",
        )
        require(
            record["sender"] == [0, 0]
            and record["flags"] == 0
            and len(acknowledgment) == 36
            and struct.unpack_from("=IHHII", acknowledgment)
            == (36, 2, 256, index + 1, ready["port"])
            and acknowledgment[16:20] == bytes(4)
            and acknowledgment[20:] == request[:16]
            and previous < record["startNs"] < record["endNs"] < ready["readyNs"],
            "Native NFLOG kernel acknowledgment or timing disagrees.",
        )
        previous = record["endNs"]


ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/reassembly"
LINKS = {
    "peer": {"peer0": (600, "192.0.2.2", "02:00:00:00:ea:02")},
    "auth": {
        "auth0": (600, "192.0.2.1", "02:00:00:00:ea:01"),
        "service0": (1500, "198.51.100.1", "02:00:00:00:eb:01"),
    },
    "server": {"server0": (1500, "198.51.100.2", "02:00:00:00:eb:02")},
}
OPPOSITE = {"peer0": "auth0", "auth0": "peer0", "service0": "server0", "server0": "service0"}
ROUTES = {
    "peer": {("default", "peer0", "192.0.2.1"), ("192.0.2.0/24", "peer0", None)},
    "auth": {("192.0.2.0/24", "auth0", None), ("198.51.100.0/24", "service0", None)},
    "server": {
        ("192.0.2.0/24", "server0", "198.51.100.1"),
        ("203.0.113.0/24", "server0", "198.51.100.1"),
        ("198.51.100.0/24", "server0", None),
    },
}


def copied_export(directory, record, commands, expected_command=None):
    nat.copied_command(record["command"], commands)
    if expected_command is not None:
        admission.successful_command(record["command"], expected_command)
    require(
        (directory / record["file"]).read_text() == record["command"]["stdout"],
        "Native export differs from exact command stdout.",
    )
    return nat.read_json(directory / record["file"])


def unique_command(record, consumed, artifact=None):
    identity = (record["startNs"], record["endNs"], tuple(record["command"]))
    require(
        identity not in consumed["commands"],
        "A selected native command is reused across observation boundaries.",
    )
    consumed["commands"].add(identity)
    if artifact is not None:
        require(
            artifact not in consumed["files"],
            "A selected native artifact is reused across observation boundaries.",
        )
        consumed["files"].add(artifact)


def interface_indices(rows):
    indices = {row["ifname"]: row["ifindex"] for row in rows if row["ifname"] != "lo"}
    require(
        all(type(index) is int and index > 0 for index in indices.values())
        and len(set(indices.values())) == len(indices),
        "Native physical interface indices are invalid or duplicated.",
    )
    return indices


def check_links(rows, namespace, peer_mtu=600, *, ifindices=None):
    require(
        len({row["ifname"] for row in rows}) == len(rows),
        "Native link inventory contains duplicate interfaces.",
    )
    physical = {row["ifname"]: row for row in rows if row["ifname"] != "lo"}
    require(set(physical) == set(LINKS[namespace]), "Native namespace link inventory differs.")
    if ifindices is not None:
        require(
            interface_indices(rows) == ifindices,
            "Native per-read interface indices differ from the checked NFLOG topology.",
        )
    for interface, (mtu, _, address) in LINKS[namespace].items():
        row = physical[interface]
        mtu = peer_mtu if interface in ("peer0", "auth0") else mtu
        require(
            row["mtu"] == mtu
            and row["address"] == address
            and "UP" in row["flags"]
            and row["link_type"] == "ether"
            and "master" not in row,
            "Native MTU, MAC, link state, or selected vif-zero scope differs.",
        )


def check_network(directory, observations, commands, consumed):
    exports = observations["networkExports"]
    require(
        set(exports)
        == {
            f"{ns}-{kind}" for ns in LINKS for kind in ("links", "addresses", "routes", "neighbors")
        },
        "Missing native three-namespace network observations.",
    )
    macs = {name: values[2] for links in LINKS.values() for name, values in links.items()}
    addresses = {name: values[1] for links in LINKS.values() for name, values in links.items()}
    for namespace, links in LINKS.items():
        for kind, arguments in (
            ("links", ["link", "show"]),
            ("addresses", ["address", "show"]),
            ("routes", ["-4", "route", "show", "table", "main"]),
            ("neighbors", ["neigh", "show"]),
        ):
            record = exports[f"{namespace}-{kind}"]
            require(
                record["file"] == f"network-{namespace}-{kind}.json",
                "Misbound native network artifact.",
            )
            rows = copied_export(
                directory, record, commands, ["ip", "-n", namespace, "-j", *arguments]
            )
            unique_command(record["command"], consumed, record["file"])
            require(
                observations["fragmentSettings"]["endNs"]
                < record["command"]["startNs"]
                < record["command"]["endNs"]
                < observations["initial"]["command"]["startNs"],
                "Native network baseline readback is outside its initial configuration boundary.",
            )
            if kind == "links":
                check_links(rows, namespace)
                interface_indices(rows)
            elif kind == "addresses":
                actual = {
                    (row["ifname"], item["local"], item["prefixlen"])
                    for row in rows
                    if row["ifname"] != "lo"
                    for item in row["addr_info"]
                }
                expected = {(name, values[1], 24) for name, values in links.items()}
                if namespace == "auth":
                    expected |= {("service0", "203.0.113.1", 32), ("service0", "203.0.113.2", 32)}
                require(actual == expected, "Native interface address/VIP scope differs.")
            elif kind == "routes":
                expected_routes = []
                for destination, device, gateway in ROUTES[namespace]:
                    route = {"dst": destination, "dev": device, "flags": []}
                    if gateway is None:
                        route.update(protocol="kernel", scope="link", prefsrc=addresses[device])
                    else:
                        route["gateway"] = gateway
                    expected_routes.append(route)
                require(
                    sorted(rows, key=lambda row: row["dst"])
                    == sorted(expected_routes, key=lambda row: row["dst"]),
                    "Native routing topology or selected route semantics differ.",
                )
            else:
                require(
                    len(rows) == len(links)
                    and {
                        (row["dev"], row["dst"], row["lladdr"], tuple(row["state"])) for row in rows
                    }
                    == {
                        (name, addresses[OPPOSITE[name]], macs[OPPOSITE[name]], ("PERMANENT",))
                        for name in links
                    },
                    "Native permanent neighbor observations differ.",
                )
    record = observations["fragmentSettings"]
    nat.copied_command(record, commands)
    values = dict(line.split(" = ") for line in record["stdout"].splitlines())
    require(
        record["stdout"] == (directory / "fragment-settings.txt").read_text()
        and values
        == {
            "net.ipv4.ipfrag_max_dist": "0",
            "net.ipv4.ipfrag_time": "30",
            "net.ipv4.ipfrag_high_thresh": "4194304",
            "net.ipv4.ip_forward": "1",
            "net.ipv4.icmp_errors_use_inbound_ifaddr": "0",
            "net.ipv4.icmp_ratelimit": "0",
            "net.ipv4.icmp_ratemask": "0",
            "net.ipv4.ip_default_ttl": "64",
        },
        "Native fragment, memory, forwarding, or ICMP configuration differs.",
    )
    offloads = []
    for namespace, links in LINKS.items():
        for interface in links:
            expected = [
                "ip",
                "netns",
                "exec",
                namespace,
                "python3",
                "/task/wire/exercise.py",
                "offload",
                interface,
            ]
            selected = [row for row in commands if row["command"] == expected]
            require(len(selected) == 1, "Missing or duplicate native offload observation.")
            row = json.loads(selected[0]["stdout"])
            admission.successful_command(selected[0], expected)
            unique_command(selected[0], consumed)
            require(
                selected[0]["endNs"] < observations["initial"]["command"]["startNs"],
                "Native offload readback follows the initial packet-state boundary.",
            )
            require(
                row["interface"] == interface
                and row["after"] == {"txChecksum": 0, "tso": 0, "gso": 0, "gro": 0},
                "Native packet checksum or segmentation offload is enabled.",
            )
            offloads.append({"namespace": namespace, "command": selected[0], **row})
    return offloads


def read_state(directory, record, name, commands, after, before, consumed):
    require(
        record["file"] == f"{name}-conntrack.json",
        "Native conntrack snapshot is bound to another episode.",
    )
    command = record["command"]
    nat.copied_command(command, commands)
    admission.successful_command(
        command,
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "python3",
            "/task/capture_conntrack.py",
            "--output",
            f"/tmp/netlib-admission/{record['file']}",
        ],
    )
    unique_command(command, consumed, record["file"])
    require(
        after < command["startNs"] < command["endNs"] < before,
        "Native conntrack snapshot is outside its selected time boundary.",
    )
    try:
        rows = lifecycle.decode_snapshot(nat.read_json(directory / record["file"]))
    except ValueError as error:
        raise EvidenceError(f"Raw native conntrack evidence: {error}") from error
    require(
        len(rows) <= 3 and len({row["originalZone"] for row in rows}) == len(rows),
        "Unexpected native conntrack entries or duplicate zone.",
    )
    for row in rows:
        require(
            row["original"] == nat.ORIGINAL
            and row["reply"] == nat.WIRE_REPLY
            and row["originalZone"] == row["replyZone"]
            and row["originalZone"] in (0, 10, 20)
            and row["status"] in (440, 442)
            and isinstance(row["id"], int)
            and row["remainingTTL"] > 0,
            "Native conntrack tuple, zone, status, or lifetime differs.",
        )
    return rows


def decode_af(row, line, filename):
    raw = bytes.fromhex(row["hex"])
    namespace, interface, kind = row["namespace"], row["interface"], row["packetType"]
    require(
        namespace in LINKS
        and interface in LINKS[namespace]
        and kind in (0, 4)
        and len(raw) >= 34
        and raw[12:14] == bytes.fromhex("0800"),
        "Invalid native AF_PACKET surface or Ethernet header.",
    )
    macs = {name: value[2] for links in LINKS.values() for name, value in links.items()}
    source, destination = (
        (macs[interface], macs[OPPOSITE[interface]])
        if kind == 4
        else (macs[OPPOSITE[interface]], macs[interface])
    )
    require(
        (raw[6:12].hex(":") == source and raw[:6].hex(":") == destination)
        or (namespace, interface, kind) in (("peer", "peer0", 4), ("auth", "auth0", 0)),
        "Native AF_PACKET MAC direction differs.",
    )
    size = int.from_bytes(raw[16:18], "big")
    require(20 <= size <= len(raw) - 14, "Native AF_PACKET IPv4 length exceeds retained bytes.")
    ip = decode_ipv4(raw[14 : 14 + size].hex(), (1, 17))
    if ip["protocol"] == 1:
        ip.update(decode_timeout(ip))
    return {
        **ip,
        "rawIPv4": ip["raw"],
        "raw": row["hex"],
        "sourceRef": f"{filename}:{line}",
        "timeNs": row["timeNs"],
        "namespace": namespace,
        "interface": interface,
        "packetType": kind,
        "hardwareHex": raw[:14].hex(),
        "paddingHex": raw[14 + size :].hex(),
    }


def udp_value(ip):
    data = bytes.fromhex(ip["payloadHex"])
    require(
        ip["offsetBytes"] == 0
        and not ip["moreFragments"]
        and len(data) >= 8
        and int.from_bytes(data[4:6], "big") == len(data),
        "Completed native UDP length is invalid.",
    )
    value = int.from_bytes(data[6:8], "big")
    pseudo = (
        ipaddress.IPv4Address(ip["source"]).packed
        + ipaddress.IPv4Address(ip["destination"]).packed
        + bytes((0, 17))
        + len(data).to_bytes(2, "big")
    )
    require(
        value == 0 or wire.folded_sum(pseudo + data) == 65535,
        "Completed native UDP pseudoheader checksum is invalid.",
    )
    return {
        "header": {
            "source": ip["source"],
            "destination": ip["destination"],
            "protocol": 17,
            "sourcePort": int.from_bytes(data[:2], "big"),
            "destinationPort": int.from_bytes(data[2:4], "big"),
        },
        "udpLength": len(data),
        "udpChecksum": {"value": value, "status": "omitted" if value == 0 else "valid"},
        "dataHex": data[8:].hex(),
    }


def output_families(frames):
    groups = {}
    for row in frames:
        if row["namespace"] == "auth" and row["packetType"] == 4 and row["protocol"] == 17:
            key = tuple(row[field] for field in ("interface", "source", "destination", "ipId"))
            groups.setdefault(key, []).append(row)
    result = []
    for fragments in groups.values():
        ordered = sorted(fragments, key=lambda row: row["offsetBytes"])
        first, position, payload = ordered[0], 0, []
        for row in ordered:
            data = bytes.fromhex(row["payloadHex"])
            require(
                all(
                    row[field] == first[field]
                    for field in (
                        "source",
                        "destination",
                        "protocol",
                        "ipId",
                        "tos",
                        "ttl",
                        "dontFragment",
                        "interface",
                    )
                )
                and row["offsetBytes"] == position
                and data
                and (not row["moreFragments"] or len(data) % 8 == 0),
                "Native output fragment family has inconsistent metadata, overlap, gap, or alignment.",
            )
            position += len(data)
            payload.append(data)
        require(
            sum(not row["moreFragments"] for row in ordered) == 1
            and not ordered[-1]["moreFragments"],
            "Native output family lacks a unique final fragment.",
        )
        whole = {
            **first,
            "payloadHex": b"".join(payload).hex(),
            "offsetBytes": 0,
            "moreFragments": False,
            "ipLength": 20 + position,
        }
        result.append({**whole, **udp_value(whole), "fragments": fragments})
    return result


def parse_statistics(record):
    lines = [
        line.split()[1:] for line in record["snmp"]["stdout"].splitlines() if line.startswith("Ip:")
    ]
    require(
        len(lines) == 2 and len(lines[0]) == len(lines[1]) and len(set(lines[0])) == len(lines[0]),
        "Malformed native IPv4 SNMP observation.",
    )
    counters = dict(zip(lines[0], map(int, lines[1]), strict=True))
    frag = [
        line.split()
        for line in record["sockstat"]["stdout"].splitlines()
        if line.startswith("FRAG:")
    ]
    require(
        len(frag) == 1 and frag[0][1::2] == ["inuse", "memory"],
        "Malformed native fragment socket statistics.",
    )
    return counters, int(frag[0][2]), int(frag[0][4])


def nft_match(left, right, op="=="):
    return {"match": {"op": op, "left": left, "right": right}}


def nft_rule(table, chain, expressions, comment=None):
    value = {"family": "ip", "table": table, "chain": chain, "expr": expressions}
    if comment is not None:
        value["comment"] = comment
    return {"rule": value}


def log_expression(prefix):
    return {"log": {"prefix": prefix, "group": 42, "snaplen": 65531, "queue-threshold": 1}}


def expected_instrumentation(zone, compound):
    match_udp = nft_match({"meta": {"key": "l4proto"}}, 17)
    match_icmp = nft_match({"meta": {"key": "l4proto"}}, 1)
    trace = {"mangle": {"key": {"meta": {"key": "nftrace"}}, "value": 1}}
    zone_expression = {"mangle": {"key": {"ct": {"key": "zone"}}, "value": zone}}
    mark = {"mangle": {"key": {"meta": {"key": "mark"}}, "value": zone}}
    result = [
        {"table": {"family": "ip", "name": "netlib_tracking"}},
        nat.chain("netlib_tracking", "prerouting", "filter", "prerouting", -199),
        nft_rule(
            "netlib_tracking",
            "prerouting",
            [nft_match({"ct": {"key": "state"}}, {"set": [2, 8]}), {"counter": {}}],
        ),
        {"table": {"family": "ip", "name": "reassembly_observe"}},
    ]
    for name, hook, priority, policy in (
        ("trace", "prerouting", -452, "accept"),
        ("zone", "prerouting", -451, "accept"),
        ("before", "prerouting", -450, "accept"),
        ("after", "prerouting", -300, "accept"),
        ("afterDestination", "prerouting", -90, "accept"),
        ("beforeSource", "postrouting", 90, "accept"),
        ("afterSource", "postrouting", 110, "accept"),
        ("late", "postrouting", 210, "accept"),
        ("input", "input", 0, "drop"),
    ):
        result.append(nat.chain("reassembly_observe", name, "filter", hook, priority, policy))
    result.append(nft_rule("reassembly_observe", "trace", [match_udp, trace]))
    if compound:
        result.append(nft_rule("reassembly_observe", "zone", [zone_expression, mark]))
    else:
        result += [
            nft_rule("reassembly_observe", "zone", [zone_expression]),
            nft_rule("reassembly_observe", "zone", [mark]),
        ]
    result += [
        nft_rule("reassembly_observe", "before", [match_udp, trace]),
        nft_rule(
            "reassembly_observe",
            "before",
            [match_udp, {"counter": {}}, log_expression("PRE_DEFRAG")],
        ),
        nft_rule(
            "reassembly_observe",
            "after",
            [match_udp, {"counter": {}}, log_expression("POST_DEFRAG")],
        ),
        nft_rule("reassembly_observe", "late", [match_icmp, log_expression("TIMEOUT_EGRESS")]),
    ]
    nat_objects = nat.expected_nat()
    for row in nat_objects:
        if "rule" in row:
            row["rule"].pop("comment")
    result += nat_objects
    result += [
        {"table": {"family": "ip", "name": "netlib_late"}},
        nat.chain("netlib_late", "late", "filter", "postrouting", 200),
    ]
    result += [
        {"table": {"family": "ip", "name": "reassembly_timeout"}},
        nat.chain("reassembly_timeout", "before", "filter", "output", -301),
        nat.chain("reassembly_timeout", "tracked", "filter", "output", -199),
        nat.chain("reassembly_timeout", "output", "filter", "output", 0, "drop"),
        nft_rule("reassembly_timeout", "before", [match_icmp, trace]),
    ]
    for value in (0, 10, 20):
        result.append(
            nft_rule(
                "reassembly_timeout",
                "before",
                [match_icmp, nft_match({"ct": {"key": "zone"}}, value), {"counter": {}}],
                f"TIMEOUT_TEMPLATE_ZONE{value}",
            )
        )
    result.append(
        nft_rule("reassembly_timeout", "before", [match_icmp, log_expression("TIMEOUT_OUTPUT")])
    )
    for state, label in (
        (4, "RELATED"),
        (1, "INVALID"),
        (8, "NEW"),
        (2, "ESTABLISHED"),
        (64, "UNTRACKED"),
    ):
        result.append(
            nft_rule(
                "reassembly_timeout",
                "tracked",
                [match_icmp, nft_match({"ct": {"key": "state"}}, state, "in"), {"counter": {}}],
                f"TIMEOUT_{label}",
            )
        )
    for value in (0, 10, 20):
        result.append(
            nft_rule(
                "reassembly_timeout",
                "tracked",
                [match_icmp, nft_match({"ct": {"key": "zone"}}, value), {"counter": {}}],
                f"TIMEOUT_AFTER_ZONE{value}",
            )
        )
    result += [
        nft_rule("reassembly_timeout", "tracked", [match_icmp, log_expression("TIMEOUT_TRACKED")]),
        nft_rule(
            "reassembly_timeout",
            "output",
            [
                nat.match("icmp", "type", 11),
                nat.match("icmp", "code", 1),
                {"counter": {}},
                {"accept": None},
            ],
            "ALLOW_REASSEMBLY_TIMEOUT",
        ),
    ]
    return result


def check_exports(
    directory,
    exports,
    name,
    phase,
    zone,
    compound,
    expected_policy,
    commands,
    nflog,
    after,
    before,
    consumed,
):
    specifications = {
        "firewall": ["list", "table", "ip", "netlib"],
        "nat": ["list", "table", "ip", "netlib_nat"],
        "late": ["list", "table", "ip", "netlib_late"],
        "instrumentation": ["list", "table", "ip", "reassembly_observe"],
        "timeout": ["list", "table", "ip", "reassembly_timeout"],
        "tracking": ["list", "table", "ip", "netlib_tracking"],
        "ruleset": ["list", "ruleset"],
    }
    require(
        set(exports) == set(specifications),
        "Missing exclusive native firewall/configuration exports.",
    )
    documents = {}
    previous = after
    for kind, arguments in specifications.items():
        record = exports[kind]
        require(
            record["file"] == f"{name + '-' + phase if phase else name}-{kind}.json",
            "Native nftables export is misbound to its episode.",
        )
        document = copied_export(
            directory,
            record,
            commands,
            ["ip", "netns", "exec", "auth", "nft", "-j", "-nn", *arguments],
        )
        unique_command(record["command"], consumed, record["file"])
        require(
            previous < record["command"]["startNs"] < record["command"]["endNs"] < before,
            "Native nftables export command is outside its selected phase.",
        )
        previous = record["command"]["endNs"]
        documents[kind] = document
    require(
        admission.canonical_table(documents["firewall"]) == expected_policy,
        "Current compiled UDP policy differs at the fragment-arrival/completion boundary.",
    )
    full = documents["ruleset"]["nftables"]
    for kind, table in (
        ("firewall", "netlib"),
        ("nat", "netlib_nat"),
        ("late", "netlib_late"),
        ("instrumentation", "reassembly_observe"),
        ("timeout", "reassembly_timeout"),
        ("tracking", "netlib_tracking"),
    ):
        selected = [
            row
            for row in full
            if "metainfo" in row
            or any(
                value.get("name" if key == "table" else "table") == table
                for key, value in row.items()
                if key != "metainfo"
            )
        ]
        require(
            selected == documents[kind]["nftables"],
            "Individual native table export contradicts the complete ruleset.",
        )
    objects = [
        row
        for row in nat.objects(documents["ruleset"])
        if next(iter(row.values())).get("table", next(iter(row.values())).get("name")) != "netlib"
    ]
    observed_time = exports["ruleset"]["command"]["startNs"]
    for row in objects:
        if "rule" not in row:
            continue
        rule = row["rule"]
        for expression in rule["expr"]:
            if "counter" not in expression:
                continue
            if rule["table"] == "reassembly_observe":
                prefix = "PRE_DEFRAG" if rule["chain"] == "before" else "POST_DEFRAG"
            elif rule["table"] == "netlib_tracking":
                prefix = "POST_DEFRAG"
            elif rule["chain"] == "output":
                prefix = "TIMEOUT_EGRESS"
            else:
                prefix = "TIMEOUT_TRACKED" if rule["comment"] == "TIMEOUT_INVALID" else None
            if rule.get("comment", "").startswith("TIMEOUT_TEMPLATE_ZONE"):
                wanted_zone = int(rule["comment"].removeprefix("TIMEOUT_TEMPLATE_ZONE"))
                selected = [
                    record
                    for record in nflog
                    if record["prefix"] == "TIMEOUT_OUTPUT"
                    and record["timeNs"] < observed_time
                    and record.get("templateZone") == wanted_zone
                ]
            elif rule.get("comment", "").startswith("TIMEOUT_AFTER_ZONE"):
                selected = []
            else:
                selected = [
                    record
                    for record in nflog
                    if record["prefix"] == prefix and record["timeNs"] < observed_time
                ]
            require(
                expression["counter"]
                == {
                    "packets": len(selected),
                    "bytes": sum(record["packet"]["ipLength"] for record in selected),
                },
                "Native hook, tracking, or timeout counters contradict all retained NFLOG records.",
            )
            expression["counter"] = {}
    require(
        objects == expected_instrumentation(zone, compound),
        "Unexpected native table, hook, action, control kind, conntrack guard, or policy.",
    )
    return documents


def parse_traces(path):
    episodes = []
    for line_number, text in enumerate(path.read_text().splitlines(), 1):
        matched = re.fullmatch(r"trace id ([0-9a-f]{8}) ip (\S+) (\S+) (.*)", text.strip())
        require(matched is not None, "Malformed native nft trace line.")
        identifier, table, chain, body = matched.groups()
        if body.startswith("packet: ") and (table, chain) in (
            ("reassembly_observe", "trace"),
            ("reassembly_timeout", "before"),
        ):
            episodes.append({"id": identifier, "source": f"trace.txt:{line_number}", "stages": []})
        require(
            episodes and episodes[-1]["id"] == identifier,
            "Interleaved or orphan native trace episode.",
        )
        stages = episodes[-1]["stages"]
        if body.startswith("packet: "):
            require(
                not stages or stages[-1]["verdicts"][-1]["verdict"] != "drop",
                "Native trace continued after a drop.",
            )
            tokens = shlex.split(body[8:])

            def value(prefix, required=True):
                return lifecycle.tokens_value(tokens, prefix, required=required)

            protocol = 1 if "icmp" in tokens else 17
            result = {
                "table": table,
                "chain": chain,
                "line": line_number,
                "iif": value(["iif"], False),
                "oif": value(["oif"], False),
                "source": value(["ip", "saddr"]),
                "destination": value(["ip", "daddr"]),
                "protocol": protocol,
                "ipId": int(value(["ip", "id"])),
                "ipLength": int(value(["ip", "length"])),
                "ttl": int(value(["ip", "ttl"])),
                "tos": generated.trace_tos(tokens),
                "verdicts": [],
            }
            if protocol == 17:
                result["udpWords"] = {
                    key: int(found)
                    for key in ("sport", "dport", "length", "checksum")
                    if (found := value(["udp", key], False)) is not None
                }
            else:
                require(
                    value(["icmp", "type"]) == "time-exceeded"
                    and value(["icmp", "code"]) == "1"
                    and value(["icmp", "id"]) == value(["icmp", "sequence"]) == "0",
                    "Unexpected native traced timeout ICMP kind or reserved word.",
                )
            stages.append(result)
        else:
            require(
                stages and (stages[-1]["table"], stages[-1]["chain"]) == (table, chain),
                "Orphan native trace verdict.",
            )
            found = re.fullmatch(r"(.*?) \(verdict (continue|accept|drop)\)", body)
            if found:
                rendered, verdict = found.groups()
                mark = None
            else:
                policy = re.fullmatch(r"policy (accept|drop)(?: meta mark (0x[0-9a-f]{8}))?", body)
                require(policy is not None, "Unknown native trace verdict.")
                rendered, verdict = f"policy {policy[1]}", policy[1]
                mark = int(policy[2], 16) if policy[2] is not None else 0
            require(
                not stages[-1]["verdicts"] or stages[-1]["verdicts"][-1]["verdict"] == "continue",
                "Native trace has contradictory terminal verdicts.",
            )
            stages[-1]["verdicts"].append(
                {"line": line_number, "text": rendered, "verdict": verdict, "mark": mark}
            )
    require(
        all(stage["verdicts"] for episode in episodes for stage in episode["stages"]),
        "Native hook lacks terminal trace evidence.",
    )
    return episodes


def expected_udp_checksum(header, data, omitted):
    body = (
        struct.pack("!HHHH", header["sourcePort"], header["destinationPort"], len(data) + 8, 0)
        + data
    )
    pseudo = (
        ipaddress.IPv4Address(header["source"]).packed
        + ipaddress.IPv4Address(header["destination"]).packed
        + bytes((0, 17))
        + len(body).to_bytes(2, "big")
    )
    return 0 if omitted else (65535 - wire.folded_sum(pseudo + body)) or 65535


def check_fragment_trace(trace, before, after, output, zone, compound, documents, fresh):
    stages = trace["stages"]
    expected = [
        ("reassembly_observe", "trace"),
        ("reassembly_observe", "zone"),
        ("reassembly_observe", "before"),
    ]
    if after is not None:
        expected += [("reassembly_observe", "after"), ("netlib_tracking", "prerouting")]
        if fresh:
            expected.append(("netlib_nat", "destination"))
        expected += [("reassembly_observe", "afterDestination"), ("netlib", "forward")]
        if output is not None:
            expected.append(("reassembly_observe", "beforeSource"))
            if fresh:
                expected.append(("netlib_nat", "source"))
            expected += [
                ("reassembly_observe", "afterSource"),
                ("netlib_late", "late"),
                ("reassembly_observe", "late"),
            ]
    require(
        [(stage["table"], stage["chain"]) for stage in stages] == expected,
        "Native before/after-defrag, conntrack, NAT, or filter hook order differs.",
    )
    direction = (
        "auth0" if before["inputIndex"] == documents["inputIndices"]["auth0"] else "service0"
    )
    for index, stage in enumerate(stages):
        packet = before["packet"] if index < 3 else after["packet"]
        prerouting = stage["chain"] in (
            "trace",
            "zone",
            "before",
            "after",
            "prerouting",
            "destination",
            "afterDestination",
        )
        require(
            all(stage[key] == packet[key] for key in ("protocol", "ipId", "ipLength", "tos"))
            and stage["ttl"] == packet["ttl"] - (not prerouting)
            and stage["iif"] == direction
            and stage["oif"]
            == (None if prerouting else "service0" if direction == "auth0" else "auth0"),
            "Native fragment/completion hook IPv4 metadata or interface differs.",
        )
        if index < 3:
            require(
                stage["source"] == packet["source"]
                and stage["destination"] == packet["destination"],
                "Native pre-defrag trace contradicts authoritative NFLOG source bytes.",
            )
        else:
            source_udp = udp_value(packet)
            original = source_udp["header"]
            if stage["chain"] in ("after", "prerouting", "destination"):
                header = original
            elif stage["chain"] in ("afterSource", "late"):
                header = nat.WIRE if direction == "auth0" else nat.PEER_REPLY
            else:
                header = {
                    **original,
                    "destination": "198.51.100.2" if direction == "auth0" else "192.0.2.2",
                    "destinationPort": 9000 if direction == "auth0" else 41000,
                }
            checksum = expected_udp_checksum(
                header,
                bytes.fromhex(source_udp["dataHex"]),
                source_udp["udpChecksum"]["status"] == "omitted",
            )
            require(
                stage["source"] == header["source"]
                and stage["destination"] == header["destination"]
                and stage["udpWords"]
                == {
                    "sport": header["sourcePort"],
                    "dport": header["destinationPort"],
                    "length": source_udp["udpLength"],
                    "checksum": checksum,
                },
                "Native whole-UDP hook tuple, length, or checksum differs.",
            )
        check_rule_contract(stage, documents, 8 if fresh else 2, zone, zone if index >= 1 else 0)
        terminal = (
            "drop"
            if after is not None and output is None and index == len(stages) - 1
            else "accept"
        )
        require(
            stage["verdicts"][-1]["verdict"] == terminal,
            "Native fragment/completion hook terminal verdict differs.",
        )
    zone_stage = stages[1]
    zone_rules = [
        row["rule"]
        for row in documents["instrumentation"]["nftables"]
        if row.get("rule", {}).get("chain") == "zone"
    ]
    expected_zone = (
        [f"unknown rule handle {zone_rules[0]['handle']}"]
        if compound
        else [f"rule ct zone set {zone}", f"rule meta mark set 0x{zone:08x}"]
    )
    require(
        [row["text"] for row in zone_stage["verdicts"]] == [*expected_zone, "policy accept"],
        "Native zone-template/mark trace does not resolve to its actual exported rules.",
    )
    if after is not None:
        forward = next(stage for stage in stages if stage["table"] == "netlib")
        rule_name = "REQUEST" if direction == "auth0" else "REPLY"
        rules = [
            row["rule"]
            for row in documents["firewall"]["nftables"]
            if row.get("rule", {}).get("comment") == rule_name
        ]
        expected_verdict = f"unknown rule handle {rules[0]['handle']}" if output else "policy drop"
        require(
            len(forward["verdicts"]) == 1 and forward["verdicts"][0]["text"] == expected_verdict,
            "Native completion filter verdict is not bound to the current compiled rule handle.",
        )


def rule_matches(rule, stage, ct_state, ct_zone):
    for expression in rule["expr"]:
        if "match" not in expression:
            continue
        match = expression["match"]
        left, right = match["left"], match["right"]
        if "meta" in left:
            require(left == {"meta": {"key": "l4proto"}}, "Unsupported native meta predicate.")
            value = stage["protocol"]
        elif "ct" in left:
            value = ct_state if left["ct"]["key"] == "state" else ct_zone
        else:
            protocol, field = left["payload"]["protocol"], left["payload"]["field"]
            if protocol == "ip":
                value = stage["source" if field == "saddr" else "destination"]
            elif protocol == "udp":
                if stage["protocol"] != 17:
                    return False
                value = stage["udpWords"].get(field)
            else:
                if stage["protocol"] != 1:
                    return False
                value = 11 if field == "type" else 1
        if isinstance(right, dict) and "prefix" in right:
            prefix = right["prefix"]
            accepted = ipaddress.IPv4Address(value) in ipaddress.IPv4Network(
                f"{prefix['addr']}/{prefix['len']}"
            )
        elif isinstance(right, dict) and "set" in right:
            accepted = value in right["set"]
        else:
            accepted = value == right
        if not accepted:
            return False
    return True


def rule_pattern(rule):
    expressions = []
    for expression in rule["expr"]:
        if "match" in expression:
            left, right = expression["match"]["left"], expression["match"]["right"]
            if "meta" in left:
                text = f"meta l4proto { {1: 'icmp', 17: 'udp'}[right] }"
            elif "ct" in left:
                key = left["ct"]["key"]
                if key == "state":
                    names = {
                        1: "invalid",
                        2: "established",
                        4: "related",
                        8: "new",
                        64: "untracked",
                    }
                    rendered = (
                        "{ " + ", ".join(names[value] for value in right["set"]) + " }"
                        if isinstance(right, dict)
                        else names[right]
                    )
                else:
                    rendered = str(right)
                text = f"ct {key} {rendered}"
            else:
                protocol, field = left["payload"]["protocol"], left["payload"]["field"]
                rendered = (
                    f"{right['prefix']['addr']}/{right['prefix']['len']}"
                    if isinstance(right, dict)
                    else "time-exceeded"
                    if protocol == "icmp" and field == "type" and right == 11
                    else str(right)
                )
                text = f"{protocol} {field} {rendered}"
            expressions.append(re.escape(text))
        elif "mangle" in expression:
            value = expression["mangle"]
            if "ct" in value["key"]:
                text = f"ct zone set {value['value']}"
            else:
                key = value["key"]["meta"]["key"]
                rendered = f"0x{value['value']:08x}" if key == "mark" else str(value["value"])
                text = f"meta {key} set {rendered}"
            expressions.append(re.escape(text))
        elif "counter" in expression:
            expressions.append(r"counter packets [0-9]+ bytes [0-9]+")
        elif "log" in expression:
            value = expression["log"]
            expressions.append(
                re.escape(
                    f"log prefix {json.dumps(value['prefix'])} group {value['group']} snaplen {value['snaplen']} queue-threshold {value['queue-threshold']}"
                )
            )
        elif "accept" in expression:
            expressions.append("accept")
        else:
            kind = "dnat" if "dnat" in expression else "snat"
            value = expression[kind]
            expressions.append(re.escape(f"{kind} to {value['addr']}:{value['port']}"))
    if "comment" in rule:
        expressions.append(re.escape(f"comment {json.dumps(rule['comment'])}"))
    return "rule " + " ".join(expressions)


def check_rule_contract(stage, documents, ct_state, ct_zone, mark):
    names = {
        "netlib": "firewall",
        "netlib_nat": "nat",
        "netlib_late": "late",
        "netlib_tracking": "tracking",
        "reassembly_observe": "instrumentation",
        "reassembly_timeout": "timeout",
    }
    objects = documents[names[stage["table"]]]["nftables"]
    rules = [
        row["rule"]
        for row in objects
        if row.get("rule", {}).get("chain") == stage["chain"]
        and rule_matches(row["rule"], stage, ct_state, ct_zone)
    ]
    verdicts = stage["verdicts"]
    terminal = bool(rules) and any(
        key in rules[-1]["expr"][-1] for key in ("accept", "dnat", "snat")
    )
    require(
        len(verdicts) == len(rules) + (not terminal),
        "Native trace rule/action count does not match its actual exported chain.",
    )
    for rule, observed in zip(rules, verdicts):
        expected = (
            "accept"
            if any(key in rule["expr"][-1] for key in ("accept", "dnat", "snat"))
            else "continue"
        )
        require(
            observed["verdict"] == expected
            and (
                observed["text"] == f"unknown rule handle {rule['handle']}"
                or re.fullmatch(rule_pattern(rule), observed["text"]) is not None
            ),
            "Native trace rule text/handle/action does not resolve to the actual matching exported rule.",
        )
    if not terminal:
        chains = [
            row["chain"] for row in objects if row.get("chain", {}).get("name") == stage["chain"]
        ]
        require(
            len(chains) == 1
            and verdicts[-1]["text"] == f"policy {chains[0]['policy']}"
            and verdicts[-1]["mark"] == mark,
            "Native trace terminal policy/packet mark differs from its exported chain/context.",
        )


def check_timeout_trace(trace, packet, template_zone, documents, output_mark):
    stages = trace["stages"]
    require(
        [(stage["table"], stage["chain"]) for stage in stages]
        == [
            ("reassembly_timeout", "before"),
            ("reassembly_timeout", "tracked"),
            ("reassembly_timeout", "output"),
            ("reassembly_observe", "beforeSource"),
            ("reassembly_observe", "afterSource"),
            ("netlib_late", "late"),
            ("reassembly_observe", "late"),
        ],
        "Native timeout LOCAL_OUT/postrouting hook order differs.",
    )
    for stage in stages:
        require(
            all(
                stage[key] == packet[key]
                for key in ("source", "destination", "protocol", "ipId", "ipLength", "ttl", "tos")
            )
            and stage["iif"] is None
            and stage["oif"] == "auth0"
            and stage["verdicts"][-1]["verdict"] == "accept",
            "Native timeout output trace metadata, NAT, interface, or verdict differs.",
        )
    for stage in stages:
        before_ct = stage["table"] == "reassembly_timeout" and stage["chain"] == "before"
        check_rule_contract(
            stage,
            documents,
            8 if before_ct else 1,
            template_zone if before_ct else None,
            output_mark,
        )
    inherited = stages[0]["verdicts"]
    require(
        sum(
            bool(
                re.fullmatch(
                    rf'rule meta l4proto icmp ct zone {template_zone} counter packets [0-9]+ bytes [0-9]+ comment "TIMEOUT_TEMPLATE_ZONE{template_zone}"',
                    row["text"],
                )
            )
            for row in inherited
        )
        == 1,
        "Native timeout output did not inherit the queued fragment's BOTH-direction zone template.",
    )
    tracked = stages[1]["verdicts"]
    require(
        sum(
            bool(
                re.fullmatch(
                    r'rule meta l4proto icmp ct state invalid counter packets [0-9]+ bytes [0-9]+ comment "TIMEOUT_INVALID"',
                    row["text"],
                )
            )
            for row in tracked
        )
        == 1
        and not any("TIMEOUT_AFTER_ZONE" in row["text"] for row in tracked),
        "Native timeout post-conntrack INVALID classification differs.",
    )
    output = stages[2]["verdicts"]
    rules = [
        row["rule"]
        for row in documents["timeout"]["nftables"]
        if row.get("rule", {}).get("chain") == "output"
    ]
    require(
        len(output) == 1
        and (
            bool(
                re.fullmatch(
                    r'rule icmp type time-exceeded icmp code 1 counter packets [0-9]+ bytes [0-9]+ accept comment "ALLOW_REASSEMBLY_TIMEOUT"',
                    output[0]["text"],
                )
            )
            or output[0]["text"] == f"unknown rule handle {rules[0]['handle']}"
        ),
        "Native timeout accept is not bound to the exported type11/code1 guard.",
    )


def source_reference(row):
    filename, line = row["source"].rsplit(":", 1)
    return {
        "file": filename,
        "line": int(line),
        "localSequence": row["localSequence"],
        "globalSequence": row["globalSequence"],
    }


def frame_reference(row):
    filename, line = row["sourceRef"].rsplit(":", 1)
    return {"file": filename, "line": int(line)}


def packet_key(packet):
    return tuple(
        packet[field] for field in ("source", "destination", "protocol", "ipId", "offsetBytes")
    )


def bind_input_reads(pre, frames, outputs):
    used = set()
    aliases = []
    for record in pre:
        interface = "auth0" if record["packet"]["source"] == "192.0.2.2" else "service0"
        opposite = OPPOSITE[interface]
        original = record["hardwareHex"] + record["packet"]["raw"]
        possible_outputs = [
            row
            for row in outputs
            if row["interface"] == "service0"
            and row["ipId"] == record["packet"]["ipId"]
            and row["offsetBytes"] == record["packet"]["offsetBytes"]
        ]
        for namespace, device, kind in (
            ("auth", interface, 0),
            ("peer" if interface == "auth0" else "server", opposite, 4),
        ):
            candidates = [
                row
                for row in frames
                if row["namespace"] == namespace
                and row["interface"] == device
                and row["packetType"] == kind
                and row["sourceRef"] not in used
                and (
                    row["raw"] == original
                    or (
                        interface == "auth0"
                        and any(row["raw"] == output["raw"] for output in possible_outputs)
                    )
                )
            ]
            require(
                len(candidates) == 1,
                "Native source AF_PACKET read lacks a unique unchanged PRE snapshot or exact same-step egress-buffer alias.",
            )
            row = candidates[0]
            used.add(row["sourceRef"])
            if row["raw"] != original:
                target = next(output for output in possible_outputs if row["raw"] == output["raw"])
                aliases.append(
                    {
                        "read": frame_reference(row),
                        "pre": source_reference(record),
                        "egress": frame_reference(target),
                        "raw": row["raw"],
                    }
                )
    expected = {
        row["sourceRef"]
        for row in frames
        if (row["namespace"] == "auth" and row["packetType"] == 0)
        or (row["namespace"] in ("peer", "server") and row["packetType"] == 4)
    }
    require(used == expected, "Extra or unconsumed native ingress AF_PACKET read.")
    return aliases


def check_stat_record(record, commands, lower, upper, consumed):
    previous = lower
    for kind in ("snmp", "sockstat"):
        row = record[kind]
        nat.copied_command(row, commands)
        admission.successful_command(
            row, ["ip", "netns", "exec", "auth", "cat", f"/tmp/netlib-proc/net/{kind}"]
        )
        unique_command(row, consumed)
        require(
            previous < row["startNs"] < row["endNs"] < upper,
            "Native queue statistic read is outside its observation phase.",
        )
        previous = row["endNs"]
    return parse_statistics(record)


def normalized_state(rows):
    return {
        row["originalZone"]: {
            key: value for key, value in row.items() if key not in ("raw", "remainingTTL")
        }
        for row in rows
    }


def check_sources(directory, input_directory):
    paths = {
        "/task/admission/exercise.py": ROOT / "examples/admission/exercise.py",
        "/task/wire/exercise.py": ROOT / "examples/wire/exercise.py",
        "/task/eap_exercise.py": ROOT / "examples/eap/exercise.py",
        "/task/capture_conntrack.py": ROOT / "scripts/capture_conntrack.py",
        "/task/received-icmp/exercise.py": ROOT / "examples/received-icmp/exercise.py",
        "/task/reassembly/exercise.py": input_directory / "exercise.py",
        "/task/reassembly/nflog.py": input_directory / "nflog.py",
    }
    retained = dict(
        reversed(line.split("  "))
        for line in (directory / "helper-sha256.txt").read_text().splitlines()
    )
    require(
        retained
        == {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in paths.items()},
        "Native reassembly producer source bytes differ from captured source hashes.",
    )
    require(
        (directory / "kernel.txt").read_text().strip() == "6.8.0-117-generic"
        and (directory / "nftables-version.txt").read_text().startswith("nftables v1.1.3")
        and (directory / "iproute2-version.txt").read_text().strip()
        == "ip utility, iproute2-6.19.0",
        "Native kernel or tool version differs from the pinned selected profile.",
    )
    for name in ("deny.json", "permit.json", "requirements.json", "demo-credential.json"):
        require(
            nat.read_json(directory / "input" / name) == nat.read_json(input_directory / name),
            "Native generated policy or credential input copy differs.",
        )


def check_controls(directory, observations, commands, authentication, consumed):
    controls = observations["controls"]
    require(
        [control["kind"] for control in controls]
        == ["eap-link-mtu", "eap-link-mtu", "timeout-routes", "queue-policy"],
        "Missing, duplicate, or unexpected native control/readback epochs.",
    )
    phase = authentication["phases"][0]
    frames = phase["frames"]
    stages = observations["stages"]
    claimed = set()

    def claim(command, expected):
        nat.copied_command(command, commands)
        admission.successful_command(command, expected)
        unique_command(command, consumed)
        claimed.add((command["startNs"], command["endNs"], tuple(command["command"])))

    for key, arguments, stdout in (
        (
            "credentialInstall",
            [
                "install",
                "-m",
                "0644",
                "/task/admission/input/demo-credential.json",
                "/run/netlib-admission/demo-credential.json",
            ],
            "",
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
            "OK\n",
        ),
    ):
        claim(observations[key], arguments)
        require(
            observations[key]["stdout"] == stdout,
            "Native credential installation or Logoff response differs.",
        )

    for filename in ("instrumentation.nft", "timeout-output.nft"):
        expected = ["ip", "netns", "exec", "auth", "nft", "-f", f"/tmp/netlib-admission/{filename}"]
        matches = [command for command in commands if command["command"] == expected]
        require(len(matches) == 1, "Missing or duplicate native observer/control installation.")
        claim(matches[0], expected)
        require(
            observations["fragmentSettings"]["endNs"]
            < matches[0]["startNs"]
            < matches[0]["endNs"]
            < observations["initial"]["command"]["startNs"],
            "Native observer/control installation crosses its baseline boundary.",
        )

    for control, mtu in zip(controls[:2], (1500, 600), strict=True):
        require(
            control["mtu"] == mtu
            and len(control["writes"]) == 2
            and set(control["readbacks"]) == {"peer", "auth"},
            "Missing native temporary EAP MTU writes/readbacks.",
        )
        lower = stages[0]["endNs"] if mtu == 1500 else frames[phase["terminalFrame"] - 1]["timeNs"]
        upper = frames[0]["timeNs"] if mtu == 1500 else stages[1]["startNs"]
        previous = lower
        for command, namespace, interface in zip(
            control["writes"], ("peer", "auth"), ("peer0", "auth0"), strict=True
        ):
            claim(
                command, ["ip", "-n", namespace, "link", "set", "dev", interface, "mtu", str(mtu)]
            )
            require(
                previous < command["startNs"] < command["endNs"] < upper,
                "EAP MTU write crosses the native handshake/data boundary.",
            )
            previous = command["endNs"]
        for namespace in ("peer", "auth"):
            record = control["readbacks"][namespace]
            require(
                record["file"] == f"eap-mtu-{mtu}-{namespace}-links.json",
                "EAP MTU readback artifact is misbound.",
            )
            rows = copied_export(
                directory, record, commands, ["ip", "-n", namespace, "-j", "link", "show"]
            )
            unique_command(record["command"], consumed, record["file"])
            check_links(
                rows,
                namespace,
                mtu,
                ifindices=interface_indices(
                    nat.read_json(directory / f"network-{namespace}-links.json")
                ),
            )
            require(
                previous < record["command"]["startNs"] < record["command"]["endNs"] < upper,
                "EAP MTU native readback is outside its actual control epoch.",
            )
            previous = record["command"]["endNs"]
            if mtu == 1500:
                require(
                    (directory / "eap" / f"{namespace}-links.json").read_text()
                    == record["command"]["stdout"],
                    "EAP link evidence differs from actual handshake-MTU readback.",
                )
    short = controls[3]
    require(short["id"] == "short", "Unknown native queue-policy identifier.")
    claim(
        short["write"],
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "sh",
            "-c",
            "echo 1 > /tmp/netlib-proc/sys/net/ipv4/ipfrag_time",
        ],
    )
    claim(
        short["readback"],
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "sysctl",
            "net.ipv4.ipfrag_time",
            "net.ipv4.ipfrag_max_dist",
        ],
    )
    require(
        short["write"]["endNs"] < short["readback"]["startNs"]
        and short["readback"]["stdout"]
        == "net.ipv4.ipfrag_time = 1\nnet.ipv4.ipfrag_max_dist = 0\n",
        "Native short timeout/max-distance readback differs.",
    )
    for step in observations["steps"]:
        if step["queuePolicy"] == "normal":
            require(
                step["endNs"] < short["write"]["startNs"],
                "Native normal queue policy is used after the short-policy cutover.",
            )
        else:
            require(
                short["readback"]["endNs"] < step["startNs"],
                "Native short queue policy precedes its actual successful write/readback.",
            )
    routes = controls[2]
    for field, arguments in (
        ("input", ["203.0.113.2", "from", "192.0.2.2", "iif", "auth0", "mark", "0"]),
        ("return", ["192.0.2.2", "from", "203.0.113.2", "mark", "0"]),
    ):
        claim(
            routes[field], ["ip", "netns", "exec", "auth", "ip", "-j", "route", "get", *arguments]
        )
        require(
            observations["steps"][0]["startNs"]
            < routes[field]["startNs"]
            < routes[field]["endNs"]
            < short["write"]["startNs"],
            "Native timeout local/return route is outside the selected routing epoch.",
        )
    expected_settings = [
        "ip",
        "netns",
        "exec",
        "auth",
        "sysctl",
        "net.ipv4.ipfrag_max_dist",
        "net.ipv4.ipfrag_time",
        "net.ipv4.ipfrag_high_thresh",
        "net.ipv4.ip_forward",
        "net.ipv4.icmp_errors_use_inbound_ifaddr",
        "net.ipv4.icmp_ratelimit",
        "net.ipv4.icmp_ratemask",
        "net.ipv4.ip_default_ttl",
    ]
    claim(observations["fragmentSettings"], expected_settings)
    require(
        observations["fragmentSettings"]["endNs"] < observations["initial"]["command"]["startNs"],
        "Native baseline fragment settings were read after packet capture began.",
    )
    for filename, expected in (
        (
            "authorized-station.txt",
            [
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
                LINKS["peer"]["peer0"][2],
            ],
        ),
        (
            "logged-off-station.txt",
            [
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
                LINKS["peer"]["peer0"][2],
            ],
        ),
        (
            "supplicant-status.txt",
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
                "status",
            ],
        ),
    ):
        raw = (directory / "eap" / filename).read_text()
        selected = [
            command
            for command in commands
            if command["command"] == expected and command["stdout"] == raw
        ]
        require(
            len(selected) == 1,
            "Native EAP control status is not bound to unique actual command stdout.",
        )
        claim(selected[0], expected)
    return claimed


def check_capture(directory, *, input_directory=DIRECTORY):
    directory, input_directory = Path(directory), Path(input_directory)
    check_sources(directory, input_directory)
    observations = nat.read_json(directory / "observations.json")
    require(
        observations["schema"] == 1 and observations["scope"] == "ordered-ipv4-input-reassembly",
        "Unexpected native reassembly observation schema.",
    )
    commands = nat.read_json(directory / "commands.json")
    require(
        commands
        and all(type(row["returncode"]) is int and row["returncode"] == 0 for row in commands),
        "Failed native command in selected capture history.",
    )
    for row in commands:
        admission.interval(row)
    require(
        all(left["endNs"] < right["startNs"] for left, right in zip(commands, commands[1:])),
        "Native sequential command history overlaps or reorders.",
    )
    consumed = {"commands": set(), "files": set()}
    offloads = check_network(directory, observations, commands, consumed)
    authentication = admission.check_eap(directory / "eap", observations["eap"])
    eap_frames = authentication["phases"][0]["frames"]
    credential = nat.read_json(directory / "installed-demo-credential.json")
    require(
        credential == nat.read_json(input_directory / "demo-credential.json"),
        "Installed demo credential differs.",
    )
    nat.copied_command(observations["credentialInstall"], commands)
    nat.copied_command(observations["logoff"], commands)
    steps, stages = observations["steps"], observations["stages"]
    require(
        [stage["stage"] for stage in stages]
        == ["unauthenticated", "authenticated-only", "credential-permitted", "logged-off-cached"]
        and len({step["name"] for step in steps}) == len(steps),
        "Missing, duplicate, or reordered native admission/data episodes.",
    )
    for index, step in enumerate(steps):
        admission.interval(step)
        require(
            step["kind"] in ("socket", "raw", "wait", "erase")
            and step["queuePolicy"] in ("normal", "short")
            and type(step["zone"]) is int
            and step["zone"] in (0, 10, 20)
            and type(step["vif"]) is int
            and step["vif"] == 0
            and (index == 0 or steps[index - 1]["endNs"] < step["startNs"]),
            "Invalid native step kind, queue policy/domain, or chronological boundary.",
        )
    for stage in stages:
        require(
            sum(step == stage for step in steps) == 1,
            "Admission checkpoint is not exactly its selected native step.",
        )
    claimed_controls = check_controls(directory, observations, commands, authentication, consumed)
    policies = {
        name: admission.canonical_table(nat.read_json(input_directory / f"{name}.json"))
        for name in ("deny", "permit")
    }
    require(policies["deny"] == [], "The generated deny policy has permitting rules.")
    require(
        policies["permit"]
        == [
            {
                "id": "REQUEST",
                **{**nat.ORIGINAL, "destination": "198.51.100.2", "destinationPort": 9000},
            },
            {
                "id": "REPLY",
                **{**nat.WIRE_REPLY, "destination": "192.0.2.2", "destinationPort": 41000},
            },
        ],
        "The generated permit policy differs from the selected exact UDP flow.",
    )

    loads = []
    for stage in stages:
        if stage.get("load") is not None:
            loads.append((stage["stage"], stage["load"]))
    loads.append(("reassembly-probes", observations["probeLoad"]))
    for index, (name, record) in enumerate(loads):
        nat.copied_command(record, commands)
        admission.successful_command(
            record,
            [
                "ip",
                "netns",
                "exec",
                "auth",
                "nft",
                "-j",
                "-f",
                f"/tmp/netlib-admission/{name}-load.json",
            ],
        )
        require(
            record["batch"] == f"{name}-load.json"
            and record["input"] in ("input/deny.json", "input/permit.json"),
            "Native policy transaction source is misbound.",
        )
        original = nat.read_json(directory / record["input"])["nftables"]
        expected = (
            original
            if index == 0
            else [
                original[0],
                {"delete": {"table": {"family": "ip", "name": "netlib"}}},
                *original[1:],
            ]
        )
        require(
            nat.read_json(directory / record["batch"]) == {"nftables": expected},
            "Applied native transaction differs from immutable generated policy.",
        )
    require(
        [record["input"] for _, record in loads]
        == ["input/deny.json", "input/permit.json", "input/deny.json", "input/permit.json"],
        "Native policy cutover sequence differs.",
    )
    require(
        stages[1]["endNs"]
        < observations["credentialInstall"]["startNs"]
        < observations["credentialInstall"]["endNs"]
        < loads[1][1]["startNs"]
        and stages[2]["endNs"]
        < observations["logoff"]["startNs"]
        < observations["logoff"]["endNs"]
        < loads[2][1]["startNs"]
        < stages[3]["startNs"]
        < observations["probeLoad"]["startNs"],
        "Credential, Logoff, or fixed probe policy ordering differs.",
    )
    ready = nat.read_json(directory / observations["nflogReady"])
    check_nflog_configuration(ready)
    require(
        observations["nflogCommand"]
        == [
            "ip",
            "netns",
            "exec",
            "auth",
            "python3",
            "/task/reassembly/nflog.py",
            "/tmp/netlib-admission/nflog.jsonl",
            "42",
        ]
        and observations["traceCommand"]
        == ["ip", "netns", "exec", "auth", "nft", "monitor", "trace"]
        and (directory / "trace-errors.txt").read_text() == "",
        "Native NFLOG or nft-trace producer changed or failed.",
    )
    nflog = [
        decode_nflog(json.loads(line), index)
        for index, line in enumerate((directory / "nflog.jsonl").read_text().splitlines(), 1)
    ]
    require(
        nflog
        and all(
            row["localSequence"] == index
            and row["globalSequence"] == index + 1
            and ready["readyNs"] < row["timeNs"]
            and (index == 0 or nflog[index - 1]["timeNs"] < row["timeNs"])
            for index, row in enumerate(nflog)
        ),
        "Native NFLOG messages are missing, duplicated, reordered, or outside capture readiness.",
    )
    traces = parse_traces(directory / "trace.txt")
    starts = [row for row in nflog if row["prefix"] in ("PRE_DEFRAG", "TIMEOUT_OUTPUT")]
    require(
        len(traces) == len(starts),
        "Native trace episodes differ from every NFLOG ingress/output start.",
    )
    trace_by_source = dict(zip((row["source"] for row in starts), traces, strict=True))
    frames = []
    for namespace in LINKS:
        filename = f"frames-{namespace}.jsonl"
        rows = [json.loads(line) for line in (directory / filename).read_text().splitlines()]
        require(
            all(rows[i]["timeNs"] < rows[i + 1]["timeNs"] for i in range(len(rows) - 1)),
            "Native packet-socket read clocks are not ordered.",
        )
        for index, row in enumerate(rows, 1):
            require(
                row["namespace"] == namespace, "AF_PACKET namespace differs from its captured file."
            )
            frames.append(decode_af(row, index, filename))
    for row in [*nflog, *frames]:
        selected = [
            index
            for index, step in enumerate(steps)
            if step["startNs"] < row["timeNs"] < step["endNs"]
        ]
        require(
            len(selected) == 1, "Native packet/NFLOG read is outside a uniquely selected episode."
        )
        index = selected[0]
        row["stepIndex"] = index
        step = steps[index]
        require(
            (step["startNs"] if step["kind"] == "wait" else step["sent"]["startNs"])
            <= row["timeNs"]
            < step["after"]["command"]["startNs"],
            "Native packet userspace read violates its send/wait and post-snapshot fences.",
        )
    initial = read_state(
        directory,
        observations["initial"],
        "initial",
        commands,
        ready["readyNs"],
        loads[0][1]["startNs"],
        consumed,
    )
    require(initial == [], "Native initial conntrack table is not empty.")
    input_indices = {
        row["ifname"]: row["ifindex"]
        for row in nat.read_json(directory / "network-auth-links.json")
        if row["ifname"] != "lo"
    }
    oracle = ReassemblyOracle(user_base=2)
    events, report_steps, admissions, aliases = [], [], [], []
    step_post = {}
    current_zone, compound = 0, False
    accepted_heads = {}
    previous_state = initial
    for index, step in enumerate(steps):
        name = step["name"]
        selected = [row for row in nflog if row["stepIndex"] == index]
        surface = [row for row in frames if row["stepIndex"] == index]
        pre = [row for row in selected if row["prefix"] == "PRE_DEFRAG"]
        posts = [row for row in selected if row["prefix"] == "POST_DEFRAG"]
        control = [row for row in selected if row["hook"] != 0]
        before = read_state(
            directory,
            step["before"],
            f"{name}-before",
            commands,
            step["startNs"],
            step["statsBefore"]["snmp"]["startNs"],
            consumed,
        )
        require(
            normalized_state(before) == normalized_state(previous_state),
            "Native state changed between selected packet/administrative episodes.",
        )
        stats_before, live_before, memory_before = check_stat_record(
            step["statsBefore"],
            commands,
            step["before"]["command"]["endNs"],
            step["exportsBefore"]["firewall"]["command"]["startNs"],
            consumed,
        )
        require(
            live_before == len(oracle.queues)
            and (memory_before == 0) == (live_before == 0)
            and 0 <= memory_before < 4194304,
            "Native pre-step fragment queue count or memory scope differs from derived arrival history.",
        )
        if current_zone != step["zone"]:
            record = step["zoneLoad"]
            require(
                record is not None and record["file"] == f"zone-{index}-{step['zone']}.nft",
                "Missing native queue-zone transition transaction.",
            )
            nat.copied_command(record["command"], commands)
            admission.successful_command(
                record["command"],
                [
                    "ip",
                    "netns",
                    "exec",
                    "auth",
                    "nft",
                    "-f",
                    f"/tmp/netlib-admission/{record['file']}",
                ],
            )
            require(
                (directory / record["file"]).read_text()
                == f"flush chain ip reassembly_observe zone\nadd rule ip reassembly_observe zone ct zone set {step['zone']} meta mark set {step['zone']}\n"
                and (steps[index - 1]["endNs"] if index else ready["readyNs"])
                < record["command"]["startNs"]
                < record["command"]["endNs"]
                < step["startNs"],
                "Native BOTH-direction zone-template/mark transition differs.",
            )
            current_zone, compound = step["zone"], True
        else:
            require(
                step["zoneLoad"] is None,
                "Unexpected native zone transaction without a domain change.",
            )
        latest = [
            (phase, record) for phase, record in loads if record["endNs"] < step["sent"]["startNs"]
        ][-1]
        require(
            step["config"] == latest[0]
            or (
                name == "authenticated-only"
                and step["config"] == "authenticated-only"
                and latest[0] == "unauthenticated"
            ),
            "Fragment policy config is not the actual latest successful load.",
        )
        policy = "permit" if latest[1]["input"] == "input/permit.json" else "deny"
        expected_rows = policies[policy]
        links = step["links"]
        require(
            isinstance(links, dict) and set(links) == set(LINKS),
            "Missing required per-send native namespace link observations.",
        )
        previous = step["exportsBefore"]["ruleset"]["command"]["endNs"]
        for namespace in LINKS:
            record = links[namespace]
            require(
                record["file"] == f"{name}-{namespace}-links.json",
                "Per-send native link artifact is misbound.",
            )
            rows = copied_export(
                directory, record, commands, ["ip", "-n", namespace, "-j", "link", "show"]
            )
            unique_command(record["command"], consumed, record["file"])
            check_links(
                rows,
                namespace,
                ifindices=interface_indices(
                    nat.read_json(directory / f"network-{namespace}-links.json")
                ),
            )
            require(
                previous
                < record["command"]["startNs"]
                < record["command"]["endNs"]
                < step["sent"]["startNs"],
                "Native per-send MTU read is reordered or follows its sender.",
            )
            previous = record["command"]["endNs"]
        admission.interval(step["sent"], step)
        require(
            all(key in step for key in ("server", "reply", "client")),
            "Missing native endpoint RPC observations.",
        )
        if step["kind"] in ("raw", "socket"):
            require(isinstance(step["server"], dict), "Missing required native server receive RPC.")
            admission.interval(step["server"], step)
            require(
                step["sent"]["endNs"] <= step["server"]["startNs"],
                "Native server receive RPC precedes its sender.",
            )
        else:
            require(
                step["server"] is step["reply"] is step["client"] is None,
                "Unexpected endpoint RPC for a native wait/erase control.",
            )
        if step["kind"] == "socket":
            require(isinstance(step["client"], dict), "Missing required native client receive RPC.")
            admission.interval(step["client"], step)
            if name == "credential-permitted":
                require(
                    isinstance(step["reply"], dict), "Missing required native reply sender RPC."
                )
                admission.interval(step["reply"], step)
                require(
                    step["server"]["endNs"]
                    <= step["reply"]["startNs"]
                    < step["reply"]["endNs"]
                    <= step["client"]["startNs"],
                    "Native reply/client RPC order differs.",
                )
            else:
                require(
                    step["reply"] is None
                    and step["client"]["result"] is None
                    and step["server"]["endNs"] <= step["client"]["startNs"]
                    and step["client"]["endNs"] - step["client"]["startNs"] >= 80_000_000,
                    "Denied native socket lacks its client timeout RPC.",
                )
        elif step["kind"] == "raw":
            require(
                step["reply"] is step["client"] is None,
                "Unexpected reply/client RPC for a raw sender.",
            )
        if step["kind"] == "raw":
            require(
                step["origin"] == "raw-synthetic-sender"
                and step["input"] == f"{name}-input.json"
                and len(pre) == 1,
                "Raw synthetic sender label/input/arrival count differs.",
            )
            native_input = nat.read_json(directory / step["input"])
            sent = step["sent"]
            nat.copied_command(sent, commands)
            admission.successful_command(
                sent,
                [
                    "ip",
                    "netns",
                    "exec",
                    "peer",
                    "python3",
                    "/task/reassembly/exercise.py",
                    "raw-send",
                    f"/tmp/netlib-admission/{name}-input.json",
                    "peer0",
                ],
            )
            emitted = json.loads(sent["stdout"])
            admission.interval(emitted, sent)
            require(
                native_input["origin"] == "raw-synthetic-sender"
                and emitted["raw"]
                == native_input["raw"]
                == pre[0]["hardwareHex"] + pre[0]["packet"]["raw"]
                and emitted["bytesSent"] == len(bytes.fromhex(emitted["raw"])),
                "Actual kernel PRE snapshot differs from raw sender bytes or source stdout.",
            )
            require(
                all(row["timeNs"] >= emitted["startNs"] for row in [*selected, *surface]),
                "Native packet observation precedes its actual raw sender emission.",
            )
        elif step["kind"] == "socket":
            require(
                step["sent"]["result"]["bytesSent"] == 1200
                and len(pre) == (4 if name == "credential-permitted" else 3),
                "Native ordinary fragmenting UDP socket result or arrival count differs.",
            )
            reply_reads = [
                row for row in selected if row.get("inputIndex") == input_indices["service0"]
            ] + [
                row
                for row in surface
                if (row["namespace"], row["interface"], row["packetType"])
                in (
                    ("server", "server0", 4),
                    ("auth", "service0", 0),
                    ("auth", "auth0", 4),
                    ("peer", "peer0", 0),
                )
            ]
            require(
                not reply_reads
                or (
                    step["reply"] is not None
                    and all(row["timeNs"] >= step["reply"]["startNs"] for row in reply_reads)
                ),
                "Native reply observation precedes its actual reply sender RPC.",
            )
        else:
            require(
                not pre and not posts,
                "Wait/erase administrative episode unexpectedly contains UDP arrivals.",
            )
        families = output_families(surface)
        output_frames = [
            row
            for row in surface
            if row["namespace"] == "auth" and row["packetType"] == 4 and row["protocol"] == 17
        ]
        step_aliases = bind_input_reads(pre, surface, output_frames)
        aliases.extend(step_aliases)
        used_families, used_posts = set(), set()
        expected_state = {
            zone: copy.deepcopy(row) for zone, row in normalized_state(before).items()
        }
        touched = set()
        counters = Counter()
        expired = []
        step_events = []
        for position, record in enumerate(pre):
            require(
                record["inputIndex"] in input_indices.values()
                and record["mark"] == step["zone"]
                and record["hardwareHex"]
                == (
                    "02000000ea0102000000ea020800"
                    if record["inputIndex"] == input_indices["auth0"]
                    else "02000000eb0102000000eb020800"
                ),
                "Native pre-defrag interface, actual zone mark, or Ethernet role differs.",
            )
            arrival = oracle.arrive(
                record["packet"]["raw"],
                record["timeNs"],
                zone=step["zone"],
                vif=0,
                timeout=(1 if step["queuePolicy"] == "short" else 30) * 1_000_000_000,
            )
            require(
                not arrival.expired,
                "Unexpected queue expiry interleaved with this selected fragment arrival.",
            )
            if arrival.status == "buffered" and record["packet"]["offsetBytes"] == 0:
                packet = record["packet"]
                key = (
                    2 + step["zone"],
                    0,
                    int(ipaddress.IPv4Address(packet["source"])),
                    int(ipaddress.IPv4Address(packet["destination"])),
                    17,
                    packet["ipId"],
                )
                queue = oracle.queues[key]
                require(
                    queue.first is not None and queue.first.ip.raw.hex() == packet["raw"],
                    "Buffered fragment zero differs from its accepted queue head.",
                )
                accepted_heads[(key, queue.expires)] = record
            counters["ReasmReqds"] += int(
                record["packet"]["moreFragments"] or record["packet"]["offsetBytes"] != 0
            )
            counters["ReasmOKs"] += int(arrival.reassembled)
            counters["ReasmFails"] += int(
                arrival.status
                in ("inconsistentLength", "empty", "overlap", "invalidECN", "tooLarge")
            )
            cursor = nflog.index(record)
            post = (
                nflog[cursor + 1]
                if cursor + 1 < len(nflog) and nflog[cursor + 1]["prefix"] == "POST_DEFRAG"
                else None
            )
            require(
                (arrival.packet.hex() if arrival.packet is not None else None)
                == (post["packet"]["raw"] if post else None),
                "Actual completed packet differs from source-derived ordered fragment queue transition.",
            )
            output = None
            fresh = False
            if post:
                require(
                    post["stepIndex"] == index
                    and post["mark"] == step["zone"]
                    and post["inputIndex"] == record["inputIndex"],
                    "POST completion crossed native episode, zone, or input interface.",
                )
                used_posts.add(post["source"])
                step_post[name] = post
                whole = udp_value(post["packet"])
                require(
                    whole["header"] in (nat.ORIGINAL, nat.WIRE_REPLY),
                    "Completed native UDP tuple is outside the selected request/reply flow.",
                )
                request = whole["header"] == nat.ORIGINAL
                fresh = request and step["zone"] not in expected_state
                touched.add(step["zone"])
                expected_header = nat.WIRE if request else nat.PEER_REPLY
                candidates = [
                    family
                    for family in families
                    if family["header"] == expected_header
                    and family["dataHex"] == whole["dataHex"]
                    and family["ipId"] == post["packet"]["ipId"]
                ]
                require(
                    len(candidates) == (1 if policy == "permit" else 0),
                    "Actual NAT forwarding differs from current policy at queue completion.",
                )
                if candidates:
                    output = candidates[0]
                    require(
                        id(output) not in used_families,
                        "Native forwarded family is attributed to multiple completions.",
                    )
                    used_families.add(id(output))
                    budget = min(
                        1500 if request else 600, arrival.max_size or (1500 if request else 600)
                    )
                    require(
                        output["ttl"] == post["packet"]["ttl"] - 1
                        and output["tos"] == post["packet"]["tos"]
                        and output["ipLength"] == post["packet"]["ipLength"]
                        and output["udpChecksum"]["status"] == whole["udpChecksum"]["status"]
                        and all(fragment["ipLength"] <= budget for fragment in output["fragments"])
                        and (not output["dontFragment"] or post["packet"]["dontFragment"]),
                        "Native forwarded family violates computed TTL, TOS, payload length, DF allowance, checksum omission, or fragment-size budget.",
                    )
                    if not arrival.reassembled and post["packet"]["ipLength"] <= (
                        1500 if request else 600
                    ):
                        require(
                            len(output["fragments"]) == 1
                            and not output["fragments"][0]["moreFragments"]
                            and output["fragments"][0]["offsetBytes"] == 0
                            and output["dontFragment"] == post["packet"]["dontFragment"],
                            "Unreassembled fitting native whole UDP packet was fragmented or changed DF.",
                        )
                    if step["zone"] not in expected_state:
                        expected_state[step["zone"]] = {"status": 440}
                    if not request:
                        expected_state[step["zone"]]["status"] = 442
            step_events.append(
                {
                    "type": "fragment",
                    "label": name if len(pre) == 1 else f"{name}:{position}",
                    "stepName": name,
                    "stepIndex": index,
                    "namespace": "auth",
                    "at": record["timeNs"],
                    "config": step["config"],
                    "queuePolicy": step["queuePolicy"],
                    "zone": step["zone"],
                    "vif": 0,
                    "rawIPv4": record["packet"]["raw"],
                    "observed": {
                        "reassembled": post["packet"]["raw"] if post else None,
                        "forwarded": [row["raw"] for row in output["fragments"]] if output else [],
                    },
                    "stateFile": step["after"]["file"] if position + 1 == len(pre) else None,
                    "source": {
                        "pre": source_reference(record),
                        "post": source_reference(post) if post else None,
                        "forwarded": [frame_reference(row) for row in output["fragments"]]
                        if output
                        else [],
                    },
                    "derived": {
                        "status": arrival.status,
                        "maxSize": arrival.max_size,
                        "maxDFSize": arrival.max_df_size,
                        "reassembled": arrival.reassembled,
                    },
                    "timeoutEmissions": [],
                    "expired": [],
                    "outputPolicyFile": step["exportsAfter"]["timeout"]["file"],
                    "latePolicyFile": step["exportsAfter"]["late"]["file"],
                }
            )
        require(
            used_posts == {row["source"] for row in posts} and len(used_families) == len(families),
            "Extra, missing, or multiply attributed native POST/forwarded family.",
        )
        if step["kind"] == "wait":
            require(
                step["sent"]["seconds"] == 1.5
                and step["sent"]["endNs"] - step["sent"]["startNs"] >= 1_500_000_000,
                "Native expiry wait lacks its declared elapsed duration.",
            )
            expired = oracle.advance(step["sent"]["endNs"])
            counters["ReasmTimeout"] += len(expired)
            counters["ReasmFails"] += len(expired)
            step_events = [
                {
                    "type": "wait",
                    "label": name,
                    "stepName": name,
                    "stepIndex": index,
                    "namespace": "auth",
                    "at": step["sent"]["endNs"],
                    "stateFile": step["after"]["file"],
                    "source": {},
                    "expired": [],
                    "timeoutEmissions": [],
                    "outputPolicyFile": step["exportsAfter"]["timeout"]["file"],
                    "latePolicyFile": step["exportsAfter"]["late"]["file"],
                }
            ]
        elif step["kind"] == "erase":
            nat.copied_command(step["sent"], commands)
            require(
                step["sent"]["command"]
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
                and step["sent"]["stderr"]
                == "conntrack v1.4.9 (conntrack-tools): 1 flow entries have been deleted.\n",
                "Native administrative erase tuple/zone or success differs.",
            )
            key_source = step_post.get(step["keySource"])
            require(
                key_source is not None
                and udp_value(key_source["packet"])["header"] == nat.ORIGINAL,
                "Native erase lacks its actual earlier completed whole-UDP key source.",
            )
            expected_state.pop(0)
            step_events = [
                {
                    "type": "erase",
                    "label": name,
                    "stepName": name,
                    "stepIndex": index,
                    "namespace": "auth",
                    "at": step["sent"]["endNs"],
                    "zone": 0,
                    "rawIPv4": key_source["packet"]["raw"],
                    "source": source_reference(key_source),
                    "stateFile": step["after"]["file"],
                    "expired": [],
                    "timeoutEmissions": [],
                    "outputPolicyFile": step["exportsAfter"]["timeout"]["file"],
                    "latePolicyFile": step["exportsAfter"]["late"]["file"],
                }
            ]
        require(
            len(control) == 3 * len(expired),
            "Native timeout output count differs from expired eligible queues.",
        )
        for timeout_index, queue in enumerate(expired):
            require(
                queue.first is not None, "Selected native expiry unexpectedly lacks fragment zero."
            )
            first = accepted_heads.get((queue.key, queue.expires))
            require(
                first is not None
                and first["packet"]["raw"] == queue.first.ip.raw.hex()
                and first["mark"] == queue.key[0] - 2,
                "Expired queue's accepted first fragment lacks its queue-generation-specific PRE source.",
            )
            before_error, tracked_error, egress_error = control[
                timeout_index * 3 : timeout_index * 3 + 3
            ]
            require(
                [row["prefix"] for row in (before_error, tracked_error, egress_error)]
                == ["TIMEOUT_OUTPUT", "TIMEOUT_TRACKED", "TIMEOUT_EGRESS"]
                and before_error["packet"]["raw"]
                == tracked_error["packet"]["raw"]
                == egress_error["packet"]["raw"],
                "Native timeout output was dropped, NAT-rewritten, duplicated, or reordered.",
            )
            packet = egress_error["packet"]
            require(
                packet["source"] == "203.0.113.2"
                and packet["destination"] == "192.0.2.2"
                and packet["ttl"] == 64
                and packet["tos"] == ((first["packet"]["tos"] & 0x1E) | 0xC0)
                and not packet["dontFragment"]
                and packet["ipLength"] == 576
                and packet["quoteHex"]
                == queue.first.ip.raw[:20].hex() + queue.first.data[:528].hex(),
                "Native timeout source, TTL/TOS/DF, quote cap, or exact retained first-fragment prefix differs.",
            )
            for row in (before_error, tracked_error, egress_error):
                row["templateZone"] = queue.key[0] - 2
                require(
                    row["outputIndex"] == input_indices["auth0"]
                    and queue.expires <= row["timeNs"] < step["sent"]["endNs"],
                    "Native timeout output is outside its inherited-zone deadline/wait or route observation.",
                )
            actual = [
                row
                for row in surface
                if row["namespace"] == "auth"
                and row["packetType"] == 4
                and row["protocol"] == 1
                and row["rawIPv4"] == packet["raw"]
            ]
            peer_reads = [
                row
                for row in surface
                if row["namespace"] == "peer"
                and row["packetType"] == 0
                and row["protocol"] == 1
                and row["rawIPv4"] == packet["raw"]
            ]
            require(
                len(actual) == len(peer_reads) == 1 and actual[0]["raw"] == peer_reads[0]["raw"],
                "Native timeout egress and peer Ethernet reads do not match exact kernel NFLOG output.",
            )
            expired_row = {
                "zone": queue.key[0] - 2,
                "vif": queue.key[1],
                "firstRawIPv4": queue.first.ip.raw.hex(),
                "firstNormalizedPayloadHex": queue.first.data.hex(),
                "deadline": queue.expires,
                "firstSource": source_reference(first),
            }
            step_events[0]["expired"].append(expired_row)
            step_events[0]["timeoutEmissions"].append(
                {
                    "rawIPv4": packet["raw"],
                    "rawEthernet": actual[0]["raw"],
                    "identification": packet["ipId"],
                    "templateZone": queue.key[0] - 2,
                    "classification": "invalid",
                    "quotedFirstSource": source_reference(first),
                    "source": {
                        "before": source_reference(before_error),
                        "tracked": source_reference(tracked_error),
                        "egress": source_reference(egress_error),
                        "frame": frame_reference(actual[0]),
                    },
                }
            )
        before_documents = check_exports(
            directory,
            step["exportsBefore"],
            name,
            "before",
            step["zone"],
            compound,
            expected_rows,
            commands,
            nflog,
            step["statsBefore"]["sockstat"]["endNs"],
            links["peer"]["command"]["startNs"],
            consumed,
        )
        before_documents["inputIndices"] = input_indices
        check_exports(
            directory,
            step["exportsAfter"],
            name,
            "after",
            step["zone"],
            compound,
            expected_rows,
            commands,
            nflog,
            max(
                [
                    step["sent"]["endNs"],
                    *[
                        step[key]["endNs"]
                        for key in ("server", "reply", "client")
                        if step[key] is not None
                    ],
                ]
            ),
            step["statsAfter"]["snmp"]["startNs"],
            consumed,
        )
        stats_after, live_after, memory_after = check_stat_record(
            step["statsAfter"],
            commands,
            step["exportsAfter"]["ruleset"]["command"]["endNs"],
            step["after"]["command"]["startNs"],
            consumed,
        )
        require(
            live_after == len(oracle.queues)
            and (memory_after == 0) == (live_after == 0)
            and 0 <= memory_after < 4194304,
            "Native post-step fragment queue count or memory scope differs.",
        )
        require(
            all(
                stats_after[key] - stats_before[key] == counters[key]
                for key in ("ReasmReqds", "ReasmOKs", "ReasmFails", "ReasmTimeout")
            ),
            "Native SNMP reassembly/kill/expiry counters differ from ordered arrivals.",
        )
        after = read_state(
            directory,
            step["after"],
            f"{name}-after",
            commands,
            step["statsAfter"]["sockstat"]["endNs"],
            step["endNs"],
            consumed,
        )
        after_by_zone = normalized_state(after)
        require(
            set(after_by_zone) == set(expected_state)
            and all(
                after_by_zone[zone]["status"] == expected_state[zone]["status"]
                and (
                    "id" not in expected_state[zone] or after_by_zone[zone] == expected_state[zone]
                )
                for zone in expected_state
            ),
            "Native queued/completed/denied/expired flow state differs from actual forwarding and retained association.",
        )
        for row in after:
            if row["originalZone"] not in touched:
                prior = next(old for old in before if old["originalZone"] == row["originalZone"])
                require(
                    row["remainingTTL"] <= prior["remainingTTL"],
                    "Incomplete/duplicate/killed/expired fragments refreshed confirmed conntrack state.",
                )
        previous_state = after
        for record in pre:
            event = next(
                event
                for event in step_events
                if event["type"] == "fragment"
                and event["source"]["pre"] == source_reference(record)
            )
            post = next(
                (row for row in posts if event["source"]["post"] == source_reference(row)), None
            )
            family = next(
                (
                    family
                    for family in families
                    if [row["raw"] for row in family["fragments"]] == event["observed"]["forwarded"]
                ),
                None,
            )
            prefix_zones = {row["originalZone"] for row in before}
            earlier = [
                old
                for old in step_events
                if old.get("at", 0) < event["at"] and old.get("observed", {}).get("forwarded")
            ]
            prefix_zones |= {old["zone"] for old in earlier}
            fresh = (
                post is not None
                and udp_value(post["packet"])["header"] == nat.ORIGINAL
                and step["zone"] not in prefix_zones
            )
            check_fragment_trace(
                trace_by_source[record["source"]],
                record,
                post,
                family,
                step["zone"],
                compound,
                before_documents,
                fresh,
            )
        for emission in step_events[0]["timeoutEmissions"] if step_events else []:
            record = next(
                row for row in control if source_reference(row) == emission["source"]["before"]
            )
            check_timeout_trace(
                trace_by_source[record["source"]],
                record["packet"],
                emission["templateZone"],
                before_documents,
                record["mark"],
            )
        destination_reads = [
            row
            for row in surface
            if row["namespace"] in ("peer", "server")
            and row["packetType"] == 0
            and row["protocol"] == 17
        ]
        require(
            Counter(row["raw"] for row in destination_reads)
            == Counter(row["raw"] for row in output_frames),
            "Native UDP egress and destination Ethernet observations differ or omit frames.",
        )
        require(
            sum(row["protocol"] == 1 for row in surface) == 2 * len(expired),
            "Unexpected or unconsumed native ICMP frame.",
        )
        if step["server"] is not None:
            admission.interval(step["server"], step)
            requests = [family for family in families if family["header"] == nat.WIRE]
            require(
                len(requests) <= 1
                and (step["server"]["result"] is not None) == bool(requests)
                and (
                    not requests
                    or step["server"]["result"]
                    == {
                        "source": "203.0.113.1",
                        "sourcePort": 40000,
                        "payload": bytes.fromhex(requests[0]["dataHex"]).decode("ascii"),
                    }
                )
                and step["sent"]["endNs"] <= step["server"]["startNs"],
                "Native server UDP receive result/order differs from actual completed NAT output.",
            )
            if step["server"]["result"] is None:
                require(
                    step["server"]["endNs"] - step["server"]["startNs"] >= 80_000_000,
                    "Native server no-delivery result lacks its measured timeout.",
                )
        if step["reply"] is not None:
            reply_packet = [
                row for row in posts if udp_value(row["packet"])["header"] == nat.WIRE_REPLY
            ]
            reply_family = [family for family in families if family["header"] == nat.PEER_REPLY]
            result = step["reply"]["result"]
            require(
                len(reply_packet) == len(reply_family) == 1
                and isinstance(result, dict)
                and result.get("bytesSent") == len(result.get("payload", "").encode("ascii"))
                and result["payload"].encode("ascii").hex()
                == udp_value(reply_packet[0]["packet"])["dataHex"]
                == reply_family[0]["dataHex"]
                and step["client"]["result"]
                == {"source": "203.0.113.2", "sourcePort": 8080, "payload": result["payload"]},
                "Native reply sender/client payload and exact socket tuple differ from actual packet bytes.",
            )
        if step["kind"] == "socket":
            request_data = step["sent"]["result"]["payload"].encode().hex()
            completed = [row for row in posts if udp_value(row["packet"])["header"] == nat.ORIGINAL]
            require(
                len(completed) == 1
                and udp_value(completed[0]["packet"])["dataHex"] == request_data,
                "Ordinary socket payload differs from actual pre-conntrack completed packet.",
            )
        if step.get("stage") is not None:
            phase = authentication["phases"][0]
            count = sum(frame["timeNs"] < step["sent"]["startNs"] for frame in eap_frames)
            stage_index = [stage["stage"] for stage in stages].index(name)
            require(
                count
                == (0, phase["terminalFrame"], phase["terminalFrame"], len(eap_frames))[
                    stage_index
                ],
                "Native EAP admission checkpoint prefix differs.",
            )
            admissions.append(
                {
                    "name": name,
                    "eapFramesBeforeSend": count,
                    "credentialInstalled": stage_index >= 2,
                    "delivered": policy == "permit",
                    "firewallFile": step["exportsAfter"]["firewall"]["file"],
                    "observations": step,
                }
            )
        events.extend(step_events)
        report_steps.append(
            {
                "name": name,
                "index": index,
                "eventCount": len(step_events),
                "beforeFile": step["before"]["file"],
                "afterFile": step["after"]["file"],
                "queueCountBefore": live_before,
                "queueCountAfter": live_after,
                "snmpDelta": {
                    key: counters[key]
                    for key in ("ReasmReqds", "ReasmOKs", "ReasmFails", "ReasmTimeout")
                },
            }
        )
    require(
        not oracle.queues,
        "Unexpected native queues remain after the selected final completion/expiry.",
    )
    check_exports(
        directory,
        observations["finalExports"],
        "final",
        "",
        current_zone,
        compound,
        policies["permit"],
        commands,
        nflog,
        steps[-1]["endNs"],
        observations["eap"]["endNs"],
        consumed,
    )
    # The controller's input/return route queries are checked before normalization.
    route_control = [row for row in observations["controls"] if row["kind"] == "timeout-routes"]
    require(
        len(route_control) == 1, "Missing native timeout local-VIP and return route observations."
    )
    route_control = route_control[0]
    for field in ("input", "return"):
        nat.copied_command(route_control[field], commands)
    require(
        json.loads(route_control["input"]["stdout"])
        == [
            {
                "type": "local",
                "dst": "203.0.113.2",
                "from": "192.0.2.2",
                "dev": "lo",
                "flags": [],
                "cache": ["local"],
                "iif": "auth0",
            }
        ]
        and json.loads(route_control["return"]["stdout"])
        == [
            {
                "dst": "192.0.2.2",
                "from": "203.0.113.2",
                "dev": "auth0",
                "flags": [],
                "uid": 0,
                "cache": [],
            }
        ],
        "Native timeout pre-DNAT local route or return route differs.",
    )
    claimed = set(consumed["commands"]) | claimed_controls
    for _, command in loads:
        claimed.add((command["startNs"], command["endNs"], tuple(command["command"])))
    for command in (observations["credentialInstall"], observations["logoff"]):
        claimed.add((command["startNs"], command["endNs"], tuple(command["command"])))
    for step in steps:
        for record in [step["zoneLoad"]["command"]] if step["zoneLoad"] is not None else []:
            claimed.add((record["startNs"], record["endNs"], tuple(record["command"])))
        if step["kind"] in ("raw", "erase"):
            command = step["sent"]
            claimed.add((command["startNs"], command["endNs"], tuple(command["command"])))
    require(
        all(
            (command["startNs"], command["endNs"], tuple(command["command"])) in claimed
            for command in commands
            if command["startNs"] >= observations["fragmentSettings"]["startNs"]
        ),
        "Unattributed native controller command after the baseline configuration readback.",
    )
    config_steps = {
        name: next(step for step in steps if step["config"] == name)
        for name in (
            "unauthenticated",
            "authenticated-only",
            "credential-permitted",
            "logged-off-cached",
            "reassembly-probes",
        )
    }
    configs = [
        {
            "id": name,
            "forwardFile": step["exportsAfter"]["firewall"]["file"],
            "natFile": step["exportsAfter"]["nat"]["file"],
            "lateFile": step["exportsAfter"]["late"]["file"],
        }
        for name, step in config_steps.items()
    ]
    return {
        "schema": 1,
        "scope": "checked-native-ipv4-input-reassembly",
        "eapEvidence": authentication,
        "credential": credential,
        "credentialInstall": observations["credentialInstall"],
        "logoff": observations["logoff"],
        "stages": admissions,
        "routing": {
            "version": "6.19.0",
            "bindings": [
                {"device": "auth0", "nextNode": "peer", "gateway": None},
                {"device": "service0", "nextNode": "server", "gateway": None},
            ],
            "routesFile": "network-auth-routes.json",
        },
        "mtus": [{"nextHop": "peer", "mtu": 600}, {"nextHop": "server", "mtu": 1500}],
        "configs": configs,
        "userBase": 2,
        "queuePolicies": [
            {"id": "normal", "timeout": 30_000_000_000},
            {"id": "short", "timeout": 1_000_000_000},
        ],
        "initialFile": observations["initial"]["file"],
        "events": events,
        "steps": report_steps,
        "timeoutRouting": {
            "inputRoutes": [{"destination": "203.0.113.2", "local": True}],
            "returns": [
                {
                    "destination": "192.0.2.2",
                    "nextHop": "peer",
                    "source": "203.0.113.2",
                    "mtu": 600,
                    "ttl": 64,
                }
            ],
            "broadcasts": ["192.0.2.255", "198.51.100.255"],
        },
        "observationsFile": "observations.json",
        "offloads": offloads,
        "afAliases": aliases,
        "frameCount": len(frames),
        "nflogCount": len(nflog),
        "fragmentCount": sum(row["prefix"] == "PRE_DEFRAG" for row in nflog),
        "eventCount": len(events),
        "waitCount": sum(event["type"] == "wait" for event in events),
        "eraseCount": sum(event["type"] == "erase" for event in events),
        "stateObservationCount": sum(event["stateFile"] is not None for event in events),
        "timeoutEmissionCount": sum(len(event["timeoutEmissions"]) for event in events),
        "limits": [
            "one-private-auth-netns-fqdir-vif-zero-both-direction-zone-templates",
            "ihl-five-ipv4-udp-small-successful-allocation-max-dist-zero",
            "kernel-hook-order-from-nflog-sequence-userspace-nanoseconds-not-jiffy-refinement",
            "af-packet-delayed-shared-buffer-aliases-retained-with-exact-egress-byte-joins",
            "actual-forwarded-layout-witness-not-unique-linux-skb-path-derivation",
            "no-capture-authenticity-linux-c-refinement-or-tls-cryptography-proof",
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
        f"Checked {evidence['eventCount']} ordered events, {evidence['nflogCount']} native NFLOG messages, and {evidence['timeoutEmissionCount']} timeout errors."
    )


if __name__ == "__main__":
    main()
