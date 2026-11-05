"""Check selected FTFW replication, kernel installation, and fenced UDP handoff."""

import argparse
import hashlib
import ipaddress
import json
import re
import shlex
import struct
import xml.etree.ElementTree as ET
from collections import Counter
from pathlib import Path

import check_admission_capture as admission
import check_lifecycle_capture as lifecycle
import check_reassembly_capture as reassembly
import check_wire_capture as wire
import check_wire_nat_capture as nat

EvidenceError, require = lifecycle.EvidenceError, lifecycle.require
ORIGINAL, WIRE = nat.ORIGINAL, nat.WIRE
WIRE_REPLY, PEER_REPLY = nat.WIRE_REPLY, nat.PEER_REPLY
ROOT = Path(__file__).resolve().parents[1]
BASE = "/tmp/netlib-replication"
TASK = "/task/replication/exercise.py"
ACTORS = ("client", "a", "b", "server")
GATEWAYS = ("a", "b")
LINKS = {
    "client": {
        "cal": ("192.0.2.2", "02:00:00:10:00:00"),
        "cbl": ("192.0.3.2", "02:00:00:10:01:00"),
    },
    "a": {
        "car": ("192.0.2.1", "02:00:00:10:00:01"),
        "sar": ("198.51.100.1", "02:00:00:10:02:01"),
        "syncl": ("10.10.0.1", "02:00:00:10:04:00"),
    },
    "b": {
        "cbr": ("192.0.3.1", "02:00:00:10:01:01"),
        "sbr": ("198.51.101.1", "02:00:00:10:03:01"),
        "syncr": ("10.10.0.2", "02:00:00:10:04:01"),
    },
    "server": {
        "sal": ("198.51.100.2", "02:00:00:10:02:00"),
        "sbl": ("198.51.101.2", "02:00:00:10:03:00"),
    },
}
OPPOSITE = {
    "cal": "car",
    "car": "cal",
    "cbl": "cbr",
    "cbr": "cbl",
    "sal": "sar",
    "sar": "sal",
    "sbl": "sbr",
    "sbr": "sbl",
    "syncl": "syncr",
    "syncr": "syncl",
}
INTERFACES = {name: actor for actor, links in LINKS.items() for name in links}
EVENTS = (
    ("establish", "packet"),
    ("replicate", "stage"),
    ("client-route", "handoff"),
    ("server-route", "handoff"),
    ("fence-primary", "fence"),
    ("uncommitted", "packet"),
    ("commit", "commit"),
    ("install-deny", "policy"),
    ("denied", "packet"),
    ("install-permit", "policy"),
    ("permitted", "packet"),
    ("continued-original", "packet"),
    ("continued-reply", "packet"),
)


def integer(value, bound=2**64):
    lifecycle.bounded(value, bound)
    return value


def interval(row, lower=0, upper=2**64):
    start, end = integer(row["startNs"]), integer(row["endNs"])
    require(lower <= start < end <= upper, "Native evidence interval is out of order.")
    return start, end


def read_lines(path):
    return [
        json.loads(line, object_pairs_hook=lifecycle.unique_object)
        for line in path.read_text().splitlines()
    ]


def configuration(actor):
    local, remote = ("10.10.0.1", "10.10.0.2") if actor == "a" else ("10.10.0.2", "10.10.0.1")
    interface = "syncl" if actor == "a" else "syncr"
    return f"""Sync {{
 Mode FTFW {{ CommitTimeout 180 DisableExternalCache Off ACKWindowSize 300 }}
 UDP {{ IPv4_address {local} IPv4_Destination_Address {remote} Port 3780 Interface {interface} Checksum on }}
}}
General {{
 HashSize 1024 HashLimit 4096
 LogFile {BASE}/{actor}.log
 LockFile {BASE}/{actor}.lock
 UNIX {{ Path {BASE}/{actor}.ctl }}
 Filter From Userspace {{ Protocol Accept {{ UDP }} Address Ignore {{ IPv4_address 10.10.0.0/24 }} }}
}}
"""


def decode_ftfw(raw, *, byteorder):
    require(byteorder in ("little", "big"), "Missing daemon producer byte order.")
    require(
        isinstance(raw, str) and re.fullmatch(r"(?:[0-9a-f]{2})+", raw),
        "Invalid FTFW hexadecimal payload.",
    )
    data, offset, result = bytes.fromhex(raw), 0, []
    while offset < len(data):
        require(len(data) - offset >= 8, "Truncated FTFW header.")
        tag, flags, size, sequence = struct.unpack_from("!BBHI", data, offset)
        version, kind = tag >> 4, tag & 15
        require(
            version == 1 and 8 <= size <= len(data) - offset and size % 4 == 0,
            "Invalid FTFW version or record length.",
        )
        packet = data[offset : offset + size]
        row = {
            "raw": packet.hex(),
            "version": version,
            "flags": flags,
            "length": size,
            "sequence": sequence,
        }
        if kind == 10:
            controls = flags & 30
            require(
                flags & ~126 == 0 and controls in (2, 4, 8, 16),
                "Unsupported FTFW control flags.",
            )
            names = {2: "resync", 4: "nack", 8: "ack", 16: "alive"}
            row["type"] = names[controls]
            require(size == (8 if controls == 16 else 16), "Invalid FTFW control length.")
            if size == 16:
                row["fromSequence"], row["toSequence"] = struct.unpack_from("!II", packet, 8)
        else:
            require(kind in (0, 1, 2) and flags & ~96 == 0, "Unsupported FTFW data record.")
            row["type"] = ("new", "update", "delete")[kind]
            row["attributes"] = decode_ftfw_attributes(packet[8:], byteorder=byteorder)
        result.append(row)
        offset += size
    return result


def decode_ftfw_attributes(data, *, byteorder):
    sizes = {0: 8, 2: 1, 3: 4, 5: 4, 6: 4, 7: 4, 12: 4, 13: 4, 14: 2, 15: 2, 31: 12, 32: 2}
    fields, offset = {}, 0
    while offset < len(data):
        require(len(data) - offset >= 4, "Truncated FTFW attribute header.")
        size, kind = struct.unpack_from("!HH", data, offset)
        aligned = (size + 3) & ~3
        require(
            kind in sizes
            and kind not in fields
            and size == 4 + sizes[kind]
            and aligned <= len(data) - offset,
            "Malformed, duplicate, or unsupported FTFW attribute.",
        )
        require(
            data[offset + size : offset + aligned] == bytes(aligned - size),
            "Nonzero FTFW attribute padding.",
        )
        fields[kind] = data[offset + 4 : offset + size]
        offset += aligned
    require({0, 2, 3, 5} <= set(fields), "Missing required FTFW UDP attributes.")
    require(fields[2] == b"\x11", "Expected selected UDP FTFW state.")
    addresses, ports = fields[0], fields[3]
    result = {
        "original": {
            "source": str(ipaddress.IPv4Address(addresses[:4])),
            "destination": str(ipaddress.IPv4Address(addresses[4:])),
            "protocol": 17,
            "sourcePort": int.from_bytes(ports[:2], "big"),
            "destinationPort": int.from_bytes(ports[2:], "big"),
        },
        "status": int.from_bytes(fields[5], "big"),
    }
    for kind, name in ((6, "remainingTTL"), (7, "mark"), (32, "zone")):
        if kind in fields:
            result[name] = int.from_bytes(fields[kind], "big")
    for kind, name in ((12, "sourceNAT"), (13, "destinationNAT")):
        if kind in fields:
            result[name] = str(ipaddress.IPv4Address(fields[kind]))
    # NAT port attributes re-encode library ports that already use network order.
    for kind, name in ((14, "sourceNATPort"), (15, "destinationNATPort")):
        if kind in fields:
            result[name] = int.from_bytes(fields[kind], byteorder)
    if 31 in fields:
        require(fields[31] == bytes(12), "Unsupported nonzero SYNPROXY replication extension.")
        result["synproxy"] = list(struct.unpack("!III", fields[31]))
    return result


def decode_cache_xml(text):
    require(isinstance(text, str) and "<!" not in text, "Unsupported cache XML declaration.")
    try:
        root = ET.fromstring(f"<flows>{text}</flows>")
    except ET.ParseError as error:
        raise EvidenceError("Malformed external cache XML.") from error
    rows = []
    for flow in root:
        require(flow.tag == "flow" and not flow.attrib, "Unsupported cache flow element.")
        metas = {meta.get("direction"): meta for meta in flow}
        require(
            len(flow) == 3
            and set(metas) == {"original", "reply", "independent"}
            and all(meta.tag == "meta" and set(meta.attrib) == {"direction"} for meta in flow),
            "Missing or duplicate cache tuple metadata.",
        )
        original, reply = metas["original"], metas["reply"]
        require(
            [layer.tag for layer in original] == ["layer3", "layer4"]
            and original[0].attrib == {"protonum": "2", "protoname": "ipv4"}
            and original[1].attrib == {"protonum": "17", "protoname": "udp"}
            and [field.tag for field in original[0]] == ["src", "dst"]
            and [field.tag for field in original[1]] == ["sport", "dport"]
            and all(not field.attrib and not list(field) for layer in original for field in layer),
            "Invalid original cache UDP tuple.",
        )
        require(
            [layer.tag for layer in reply] == ["layer3", "layer4"]
            and all(layer.attrib == {"protonum": "0", "protoname": "unknown"} for layer in reply)
            and [field.tag for field in reply[0]] == ["src", "dst"]
            and all(not field.attrib and not list(field) and not field.text for field in reply[0])
            and not list(reply[1]),
            "External cache XML unexpectedly contains a reconstructed reply tuple.",
        )
        packet = lifecycle.header(
            {
                "source": original[0][0].text,
                "destination": original[0][1].text,
                "protocol": 17,
                "sourcePort": int(original[1][0].text),
                "destinationPort": int(original[1][1].text),
            }
        )
        labels = [field.tag for field in metas["independent"]]
        require(
            set(labels) <= {"unreplied", "assured", "zone", "mark"}
            and len(labels) == len(set(labels))
            and all(not field.attrib and not list(field) for field in metas["independent"])
            and all(
                not field.text
                for field in metas["independent"]
                if field.tag not in ("zone", "mark")
            ),
            "Unsupported cache status labels.",
        )
        row = {
            "original": packet,
            "unreplied": "unreplied" in labels,
            "assured": "assured" in labels,
        }
        if "zone" in labels:
            zone = int(metas["independent"].findtext("zone"))
            lifecycle.bounded(zone, 2**16)
            row["zone"] = zone
        if "mark" in labels:
            mark = int(metas["independent"].findtext("mark"))
            lifecycle.bounded(mark, 2**32)
            row["mark"] = mark
        rows.append(row)
    return rows


def check_internal_cache(text, record):
    require(isinstance(text, str) and "<!" not in text, "Unsupported internal cache XML.")

    def tuple_xml(direction, value):
        return (
            f'<meta direction="{direction}"><layer3 protonum="2" protoname="ipv4">'
            f"<src>{value['source']}</src><dst>{value['destination']}</dst></layer3>"
            '<layer4 protonum="17" protoname="udp">'
            f"<sport>{value['sourcePort']}</sport><dport>{value['destinationPort']}</dport>"
            "</layer4></meta>"
        )

    expected = (
        "<flow>"
        + tuple_xml("original", record["original"])
        + tuple_xml("reply", record["reply"])
        + f'<meta direction="independent"><id>{record["id"]}</id><unreplied/></meta></flow>'
    )
    try:
        actual_tree, expected_tree = ET.fromstring(text), ET.fromstring(expected)
    except ET.ParseError as error:
        raise EvidenceError("Malformed internal cache XML.") from error
    require(
        ET.tostring(actual_tree) == ET.tostring(expected_tree),
        "Source internal cache differs from selected raw kernel record.",
    )


def expected_tables(policy, counters):
    result = []

    def table(name, chains):
        result.append({"table": {"family": "ip", "name": name}})
        for chain in chains:
            result.append(nat.chain(name, *chain))

    def rule(table_name, chain_name, expr, comment=None):
        value = {"family": "ip", "table": table_name, "chain": chain_name, "expr": expr}
        if comment:
            value["comment"] = comment
        result.append({"rule": value})

    def counter(name):
        packets, count = counters.get(name, (0, 0))
        return {"counter": {"packets": packets, "bytes": count}}

    def state(value):
        return {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": value}}

    table(
        "netlib_nat",
        [("prerouting", "nat", "prerouting", -100), ("postrouting", "nat", "postrouting", 100)],
    )
    rule(
        "netlib_nat",
        "prerouting",
        [
            nat.match("ip", "daddr", ORIGINAL["destination"]),
            nat.match("udp", "dport", 8080),
            {"dnat": {"addr": WIRE["destination"], "port": 9000}},
        ],
    )
    original_forward = [
        nat.match("ip", "saddr", ORIGINAL["source"]),
        nat.match("ip", "daddr", WIRE["destination"]),
        nat.match("udp", "sport", 41000),
        nat.match("udp", "dport", 9000),
    ]
    rule(
        "netlib_nat",
        "postrouting",
        original_forward + [{"snat": {"addr": WIRE["source"], "port": 40000}}],
    )
    table("netlib", [("forward", "filter", "forward", 0, "drop")])
    if policy == "initial":
        rule(
            "netlib",
            "forward",
            original_forward + [state(["established", "new"]), {"accept": None}],
        )
    if policy != "deny":
        rule("netlib", "forward", [state("established"), {"accept": None}])
    table(
        "sync_untracked",
        [("prerouting", "filter", "prerouting", -300), ("output", "filter", "output", -300)],
    )
    for name in ("prerouting", "output"):
        rule(
            "sync_untracked",
            name,
            [
                nat.match("ip", "saddr", {"prefix": {"addr": "10.10.0.0", "len": 24}}),
                nat.match("udp", "dport", 3780),
                {"notrack": None},
            ],
        )
    table("netlib_late", [("late", "filter", "postrouting", 200)])
    table(
        "replication_observe",
        [
            ("ingress", "filter", "prerouting", -450),
            ("tracked", "filter", "prerouting", -199),
            ("egress", "filter", "postrouting", 210),
        ],
    )
    selected = {
        "match": {
            "op": "!=",
            "left": {"payload": {"protocol": "udp", "field": "dport"}},
            "right": 3780,
        }
    }
    rule(
        "replication_observe",
        "ingress",
        [selected, {"mangle": {"key": {"meta": {"key": "nftrace"}}, "value": 1}}],
    )
    for chain_name, label in (("ingress", "INGRESS"), ("tracked", "TRACKED"), ("egress", "EGRESS")):
        if chain_name == "tracked":
            for label_ in ("NEW", "ESTABLISHED"):
                rule(
                    "replication_observe",
                    chain_name,
                    [selected, state(label_.lower()), counter(label_)],
                    label_,
                )
        rule(
            "replication_observe",
            chain_name,
            [
                selected,
                counter(label),
                {"log": {"prefix": label, "group": 42, "snaplen": 65531, "queue-threshold": 1}},
            ],
        )
    return result


def expected_routes(actor, owners, *, fenced=False):
    result = {
        (str(ipaddress.IPv4Network(address + "/24", strict=False)), name, None, address, None)
        for name, (address, _) in LINKS[actor].items()
        if not (fenced and actor == "a" and name in ("car", "sar"))
    }
    if actor == "client":
        router = owners["original"]
        result.add(
            (
                "203.0.113.2",
                "cal" if router == "a" else "cbl",
                "192.0.2.1" if router == "a" else "192.0.3.1",
                "192.0.2.2",
                None,
            )
        )
    elif actor == "server":
        router = owners["reply"]
        result.add(
            (
                "203.0.113.1",
                "sal" if router == "a" else "sbl",
                "198.51.100.1" if router == "a" else "198.51.101.1",
                "198.51.100.2",
                None,
            )
        )
    else:
        result.add(("203.0.113.1", None, None, None, "blackhole"))
        if actor == "b":
            result |= {
                ("192.0.2.2", "cbr", "192.0.3.2", None, None),
                ("198.51.100.2", "sbr", "198.51.101.2", None, None),
            }
    return result


def check_network(documents, owners, fenced, indices):
    require(set(documents) == set(ACTORS), "Missing namespace network readbacks.")
    for actor, documents_ in documents.items():
        links = documents_["links"]
        require(
            {row["ifname"] for row in links} == {"lo", *LINKS[actor]},
            "Unexpected namespace link inventory.",
        )
        for row in links:
            name = row["ifname"]
            if name == "lo":
                require(
                    "UP" in row["flags"] and row["link_type"] == "loopback",
                    "Loopback is unavailable.",
                )
                continue
            require(
                (row["mtu"], row["address"], row["link_type"], row["qdisc"])
                == (1500, LINKS[actor][name][1], "ether", "noqueue"),
                "Native link MTU, MAC, type, or queue disagrees.",
            )
            require(
                ("UP" in row["flags"])
                == (not (fenced and actor == "a" and name in ("car", "sar"))),
                "Native fence interface state disagrees.",
            )
            require(indices[actor][name] == row["ifindex"], "Native interface index changed.")
        addresses = set()
        for row in documents_["addresses"]:
            require(row["ifname"] in {"lo", *LINKS[actor]}, "Unexpected addressed interface.")
            for value in row["addr_info"]:
                require(value["family"] == "inet", "Unexpected IPv6 address.")
                addresses.add((row["ifname"], value["local"], value["prefixlen"]))
        require(
            addresses
            == {("lo", "127.0.0.1", 8)}
            | {(name, value[0], 24) for name, value in LINKS[actor].items()},
            "Namespace address inventory disagrees.",
        )
        routes = {
            (row["dst"], row.get("dev"), row.get("gateway"), row.get("prefsrc"), row.get("type"))
            for row in documents_["routes"]
        }
        require(
            len(routes) == len(documents_["routes"])
            and routes == expected_routes(actor, owners, fenced=fenced),
            "Per-leg route ownership or blackhole route disagrees.",
        )
        expected_objects = []
        for destination, device, gateway, preferred, kind in expected_routes(
            actor, owners, fenced=fenced
        ):
            row = {"dst": destination, "flags": []}
            if kind:
                row["type"] = kind
            else:
                row["dev"] = device
                if gateway:
                    row["gateway"] = gateway
                if preferred:
                    row["prefsrc"] = preferred
                if "/" in destination:
                    row.update(protocol="kernel", scope="link")
                    if fenced and device in ("cal", "sal"):
                        row["flags"] = ["linkdown"]
            expected_objects.append(row)
        require(
            sorted(documents_["routes"], key=lambda row: json.dumps(row, sort_keys=True))
            == sorted(expected_objects, key=lambda row: json.dumps(row, sort_keys=True)),
            "Unsupported route attributes, flags, or selectors in native readback.",
        )
        for row in documents_["neighbors"]:
            check_neighbor(row, actor)


def check_neighbor(row, actor):
    name = row["dev"]
    require(name in LINKS[actor], "Unexpected neighbor interface.")
    peer = OPPOSITE[name]
    peer_links = LINKS[INTERFACES[peer]]
    expected_mac = peer_links[peer][1]
    require(
        row["dst"] in {address for address, _ in peer_links.values()}
        and row.get("lladdr", expected_mac) == expected_mac,
        "Neighbor adjacency contradicts native topology.",
    )


def decode_nflog(row, actor, number):
    require(
        set(row) == {"timeNs", "hex", "sender", "flags"}
        and row["sender"] == [0, 0]
        and row["flags"] == 0,
        "NFLOG data is truncated or not from the kernel.",
    )
    raw = bytes.fromhex(row["hex"])
    require(
        len(raw) >= 20
        and struct.unpack_from("=IHHII", raw) == (len(raw), 0x400, 0, 0, 0)
        and raw[16:20] == bytes((2, 0, 0, 42)),
        "Unexpected NFLOG message envelope.",
    )
    fields = reassembly.netlink_attributes(raw[20:])
    require(10 in fields and fields[10].endswith(b"\0"), "Missing NFLOG prefix.")
    prefix = fields[10][:-1].decode("ascii")
    require(prefix in ("INGRESS", "TRACKED", "EGRESS"), "Unexpected NFLOG prefix.")
    expected = {1, 4, 8, 9, 10, 12, 13, 15, 16, 17} | ({5} if prefix == "EGRESS" else {3})
    require(set(fields) in (expected, expected | {2}), "Missing or extra NFLOG fields.")
    require(
        fields[1] == bytes((8, 0, 4 if prefix == "EGRESS" else 0, 0))
        and fields[15] == b"\0\1"
        and fields[17] == b"\0\x0e"
        and len(fields[16]) == 14
        and fields[16][12:] == b"\x08\0",
        "NFLOG hook or hardware metadata disagrees.",
    )
    require(
        len(fields[8]) == 12
        and fields[8][:4] == bytes.fromhex("00060000")
        and fields[8][4:10] == fields[16][6:12]
        and fields[8][10:] == bytes(2),
        "NFLOG hardware source disagrees.",
    )
    for kind in (4, 5, 12, 13, 2):
        require(kind not in fields or len(fields[kind]) == 4, "Malformed NFLOG scalar.")
    require(2 not in fields or fields[2] == bytes(4), "Unexpected selected packet mark.")
    if 3 in fields:
        require(len(fields[3]) == 16, "Malformed NFLOG kernel timestamp.")
    packet = wire.decode_frame((fields[16] + fields[9]).hex())
    require(packet["paddingHex"] == "", "Unexpected NFLOG payload padding.")
    return {
        "source": f"{actor}-nflog.jsonl:{number}",
        "actor": actor,
        "timeNs": integer(row["timeNs"]),
        "prefix": prefix,
        "inputIndex": int.from_bytes(fields[4], "big"),
        "outputIndex": int.from_bytes(fields[5], "big") if 5 in fields else None,
        "localSequence": int.from_bytes(fields[12], "big"),
        "globalSequence": int.from_bytes(fields[13], "big"),
        "hardwareHex": fields[16].hex(),
        "packet": packet,
    }


def decode_af(row, actor, number, indices, fence_commands):
    require(
        row["namespace"] == actor and row["interface"] in LINKS[actor],
        "AF_PACKET namespace or interface disagrees.",
    )
    stamp = integer(row["timeNs"])
    if "socketError" in row:
        name = row["interface"]
        require(
            set(row) == {"namespace", "interface", "timeNs", "socketError"}
            and actor == "a"
            and name in ("car", "sar")
            and type(row["socketError"]) is int
            and row["socketError"] == 100
            and fence_commands[name]["startNs"] <= stamp,
            "Unexpected AF_PACKET socket error.",
        )
        return {"error": True, "interface": name, "timeNs": stamp}
    require(
        set(row) == {"namespace", "interface", "ifindex", "timeNs", "packetType", "hex"},
        "Unsupported AF_PACKET metadata.",
    )
    require(
        row["ifindex"] == indices[actor][row["interface"]], "AF_PACKET interface index disagrees."
    )
    data = bytes.fromhex(row["hex"])
    require(
        len(data) >= 14 and type(row["packetType"]) is int and row["packetType"] in (0, 1, 4),
        "Malformed Ethernet capture envelope.",
    )
    name = row["interface"]
    own = LINKS[actor][name][1]
    peer_name = OPPOSITE[name]
    peer = LINKS[INTERFACES[peer_name]][peer_name][1]
    source, destination = data[6:12].hex(":"), data[:6].hex(":")
    require(
        (source, destination) == ((own, peer) if row["packetType"] == 4 else (peer, own))
        or (
            data[12:14] == b"\x08\x06"
            and source in (own, peer)
            and destination == "ff:ff:ff:ff:ff:ff"
        ),
        "Ethernet adjacency or packet direction disagrees.",
    )
    if data[12:14] == b"\x08\x06":
        require(
            len(data) >= 42 and data[14:20] == bytes.fromhex("000108000604"),
            "Malformed ARP envelope.",
        )
        return None
    require(
        data[12:14] == b"\x08\0" and row["packetType"] in (0, 4),
        "Unsupported captured link protocol.",
    )
    packet = wire.decode_frame(row["hex"])
    require(packet["udpChecksum"]["status"] == "valid", "Expected valid nonzero UDP checksum.")
    result = {**packet, **row, "source": f"{actor}-frames.jsonl:{number}"}
    if name.startswith("sync"):
        source_ip = "10.10.0.1" if source == LINKS["a"]["syncl"][1] else "10.10.0.2"
        destination_ip = "10.10.0.2" if source_ip == "10.10.0.1" else "10.10.0.1"
        require(
            packet["header"]["source"] == source_ip
            and packet["header"]["destination"] == destination_ip
            and packet["header"]["destinationPort"] == 3780
            and packet["ttl"] == 64,
            "Sync datagram addressing or TTL disagrees.",
        )
        result["messages"] = decode_ftfw(packet["payloadHex"], byteorder="little")
        result["sync"] = True
    else:
        require(
            packet["header"] in (ORIGINAL, WIRE, WIRE_REPLY, PEER_REPLY),
            "Unaccounted selected IPv4 UDP frame.",
        )
        result["sync"] = False
    return result


def trace_rule_tokens(rule):
    tokens = []
    for expression in rule["expr"]:
        kind, value = next(iter(expression.items()))
        if kind == "match":
            if value["left"] == {"ct": {"key": "state"}}:
                right = value["right"]
                tokens.extend(
                    ["ct", "state", ",".join(right) if isinstance(right, list) else right]
                )
            elif value["op"] == "!=":
                field = value["left"]["payload"]
                tokens.extend([field["protocol"], field["field"], "!=", str(value["right"])])
            else:
                tokens.extend(lifecycle.match_tokens(value))
        elif kind == "counter":
            tokens.extend(["counter", "packets", "0", "bytes", "0"])
        elif kind == "log":
            tokens.extend(
                [
                    "log",
                    "prefix",
                    value["prefix"],
                    "group",
                    str(value["group"]),
                    "snaplen",
                    str(value["snaplen"]),
                    "queue-threshold",
                    str(value["queue-threshold"]),
                ]
            )
        elif kind == "mangle":
            require(
                value == {"key": {"meta": {"key": "nftrace"}}, "value": 1},
                "Unexpected trace mangle.",
            )
            tokens.extend(["meta", "nftrace", "set", "1"])
        elif kind == "notrack":
            tokens.append("notrack")
        else:
            tokens.extend(lifecycle.rule_tokens({"expr": [expression]}))
    if "comment" in rule:
        tokens.extend(["comment", rule["comment"]])
    return tokens


def check_trace_rules(stage, document, state):
    chain, rules = lifecycle.native_chain(document, stage["table"], stage["chain"])
    expected = []
    for rule in rules:
        matched = True
        for expression in rule["expr"]:
            if "match" not in expression:
                continue
            value = expression["match"]
            if value["op"] == "!=":
                matched &= not lifecycle.native_match({**value, "op": "=="}, state, stage["packet"])
            else:
                matched &= lifecycle.native_match(value, state, stage["packet"])
        if not matched:
            continue
        terminal = next(iter(rule["expr"][-1]))
        verdict = (
            "accept"
            if terminal in ("dnat", "snat", "accept")
            else "drop"
            if terminal == "drop"
            else "continue"
        )
        expected.append(("rule", verdict, rule))
        if verdict != "continue":
            break
    if not expected or expected[-1][1] == "continue":
        expected.append(("policy", chain["policy"], None))
    require(len(expected) == len(stage["verdicts"]), "Native trace omits or adds a rule visit.")
    for (kind, verdict, rule), actual in zip(expected, stage["verdicts"], strict=True):
        require(
            (actual["kind"], actual["verdict"]) == (kind, verdict),
            "Trace verdict contradicts active exported rules.",
        )
        if rule:
            if actual["handle"] is not None:
                require(
                    actual["handle"] == rule["handle"],
                    "Trace rule handle contradicts active export.",
                )
            else:
                text = re.sub(
                    r"counter packets [0-9]+ bytes [0-9]+",
                    "counter packets 0 bytes 0",
                    actual["text"],
                )
                require(
                    shlex.split(text) == trace_rule_tokens(rule),
                    "Trace rule text contradicts active export.",
                )


def check_packet_trace(trace, incoming, outgoing, document, name, actor, indices):
    state = "new" if name in ("establish", "uncommitted") else "established"
    stages = trace["stages"]
    keys = [(row["table"], row["chain"]) for row in stages]
    expected = [
        ("replication_observe", "ingress"),
        ("sync_untracked", "prerouting"),
        ("replication_observe", "tracked"),
    ]
    if name in ("establish", "uncommitted"):
        expected.append(("netlib_nat", "prerouting"))
    if name != "uncommitted":
        expected.append(("netlib", "forward"))
    if outgoing:
        if name == "establish":
            expected.append(("netlib_nat", "postrouting"))
        expected.extend([("netlib_late", "late"), ("replication_observe", "egress")])
    require(keys == expected, "Unexpected selected packet hook path.")
    reply = incoming["header"] == WIRE_REPLY
    translated = admission.REPLY if reply else admission.REQUEST
    interface_in = (
        "sar" if actor == "a" and reply else "car" if actor == "a" else "sbr" if reply else "cbr"
    )
    interface_out = (
        "car" if actor == "a" and reply else "sar" if actor == "a" else "cbr" if reply else "sbr"
    )
    for stage in stages:
        late = stage["chain"] in ("late", "egress")
        forwarded = stage["chain"] == "forward" or stage["chain"] == "postrouting" or late
        expected_header = (
            outgoing["header"] if late else translated if forwarded else incoming["header"]
        )
        require(
            stage["packet"] == expected_header
            and stage["iif"] == interface_in
            and stage["oif"] == (interface_out if forwarded else None)
            and stage["ipId"] == incoming["ipId"],
            "Trace tuple, route interface, or packet identity disagrees.",
        )
        require(
            stage["ttl"] == (63 if forwarded else 64)
            and stage["ipLength"] == incoming["ipLength"]
            and stage["udpLength"] == incoming["udpLength"],
            "Trace TTL or datagram lengths disagree.",
        )
        if not forwarded:
            require(
                stage["udpChecksum"] == incoming["udpChecksum"]["value"],
                "Early trace checksum differs from ingress.",
            )
        if late:
            require(
                stage["udpChecksum"] == outgoing["udpChecksum"]["value"],
                "Late trace checksum differs from output.",
            )
        if forwarded and not late:
            require(
                stage["udpChecksum"]
                == reassembly.expected_udp_checksum(
                    expected_header, bytes.fromhex(incoming["payloadHex"]), False
                ),
                "Intermediate translated checksum contradicts actual UDP payload and tuple.",
            )
        check_trace_rules(stage, document, state)
    return state, interface_in, interface_out


def parse_traces(path):
    lines = path.read_text().splitlines()
    result = lifecycle.parse_trace("\n".join(lines))
    for trace in result:
        for stage in trace["stages"]:
            tokens = shlex.split(lines[stage["line"] - 1])
            for key, prefix in (
                ("ttl", ["ip", "ttl"]),
                ("ipLength", ["ip", "length"]),
                ("udpLength", ["udp", "length"]),
                ("udpChecksum", ["udp", "checksum"]),
            ):
                stage[key] = int(lifecycle.tokens_value(tokens, prefix))
    return result


def check_provenance(directory, commands, consumed, setup_before, shutdown_after, shutdown_before):
    require(
        re.fullmatch(
            r"Linux \S+ 6\.8\.0-117-generic .* aarch64 Linux\n",
            (directory / "kernel.txt").read_text(),
        ),
        "Unexpected native kernel release or architecture.",
    )
    versions = {
        "conntrack-version.txt": "conntrack v1.4.9 (conntrack-tools)\n",
        "conntrackd-version.txt": "Connection tracking userspace daemon v1.4.9. Licensed under GPLv2.\n(C) 2006-2009 Pablo Neira Ayuso <pablo@netfilter.org>\n",
        "nftables-version.txt": "nftables v1.1.3 (Commodore Bullmoose #4)\n",
        "iproute2-version.txt": "ip utility, iproute2-6.19.0\n",
    }
    for name, expected in versions.items():
        require((directory / name).read_text() == expected, "Native producer version disagrees.")
    helper_paths = {
        "/task/replication/exercise.py": ROOT / "examples/replication/exercise.py",
        "/task/replication/nflog.py": ROOT / "examples/replication/nflog.py",
        "/task/wire/exercise.py": ROOT / "examples/wire/exercise.py",
        "/task/capture_conntrack.py": ROOT / "scripts/capture_conntrack.py",
    }
    helpers = {}
    for line in (directory / "helper-sha256.txt").read_text().splitlines():
        digest, name = line.split("  ")
        require(
            name not in helpers
            and name in helper_paths
            and hashlib.sha256(helper_paths[name].read_bytes()).hexdigest() == digest,
            "Retained helper source digest disagrees.",
        )
        helpers[name] = digest
    require(set(helpers) == set(helper_paths), "Missing retained helper source digest.")
    producers = {}
    for line in (directory / "producer-sha256.txt").read_text().splitlines():
        digest, name = line.split("  ")
        require(
            name not in producers and re.fullmatch(r"[0-9a-f]{64}", digest),
            "Invalid producer digest manifest.",
        )
        producers[name] = digest
    require(
        set(producers)
        == {
            "/opt/netlib/sbin/conntrackd",
            "/opt/netlib/sbin/conntrack",
            "/opt/netlib/sbin/nft",
            "/opt/netlib/sbin/ip",
            "/tmp/tools.tar.xz",
            "/tmp/library.tar.xz",
        }
        and producers["/tmp/tools.tar.xz"]
        == "c15afe488a8d408c9d6d61e97dbd19f3c591942f62c13df6453a961ca4231cae"
        and producers["/tmp/library.tar.xz"]
        == "769d3eaf57fa4fbdb05dd12873b6cb9a5be7844d8937e222b647381d44284820",
        "Source archive provenance disagrees.",
    )
    setup = []
    for actor in ACTORS:
        prefix = ["ip", "netns", "exec", actor]
        setup.extend([["ip", "netns", "add", actor], prefix + ["ip", "link", "set", "lo", "up"]])
        for key, value in (
            ("net.ipv6.conf.all.disable_ipv6", 1),
            ("net.ipv6.conf.default.disable_ipv6", 1),
            ("net.ipv4.conf.all.rp_filter", 0),
            ("net.ipv4.conf.default.rp_filter", 0),
            ("net.ipv4.ip_forward", int(actor in GATEWAYS)),
        ):
            setup.append(
                prefix
                + ["sh", "-c", f"echo {value} > /tmp/netlib-proc/sys/{key.replace('.', '/')}"]
            )
    for left, right in (
        ("cal", "car"),
        ("cbl", "cbr"),
        ("sal", "sar"),
        ("sbl", "sbr"),
        ("syncl", "syncr"),
    ):
        setup.append(["ip", "link", "add", left, "type", "veth", "peer", "name", right])
        for name in (left, right):
            actor = INTERFACES[name]
            address, mac = LINKS[actor][name]
            prefix = ["ip", "netns", "exec", actor]
            setup.extend(
                [
                    ["ip", "link", "set", name, "netns", actor],
                    prefix + ["ip", "link", "set", name, "address", mac],
                    prefix + ["ip", "address", "add", address + "/24", "dev", name],
                    prefix + ["ip", "link", "set", name, "mtu", "1500", "up"],
                    prefix + ["python3", "/task/wire/exercise.py", "offload", name],
                ]
            )
    setup.extend(
        [
            [
                "ip",
                "netns",
                "exec",
                "client",
                "ip",
                "route",
                "add",
                "203.0.113.2/32",
                "via",
                "192.0.2.1",
                "dev",
                "cal",
                "src",
                "192.0.2.2",
            ],
            [
                "ip",
                "netns",
                "exec",
                "server",
                "ip",
                "route",
                "add",
                "203.0.113.1/32",
                "via",
                "198.51.100.1",
                "dev",
                "sal",
                "src",
                "198.51.100.2",
            ],
            [
                "ip",
                "netns",
                "exec",
                "b",
                "ip",
                "route",
                "add",
                "192.0.2.2/32",
                "via",
                "192.0.3.2",
                "dev",
                "cbr",
            ],
            [
                "ip",
                "netns",
                "exec",
                "b",
                "ip",
                "route",
                "add",
                "198.51.100.2/32",
                "via",
                "198.51.101.2",
                "dev",
                "sbr",
            ],
        ]
    )
    shutdown = []
    for actor in GATEWAYS:
        prefix = ["ip", "netns", "exec", actor]
        setup.extend(
            [
                prefix + ["ip", "route", "add", "blackhole", "203.0.113.1/32"],
                prefix + ["nft", "-f", f"{BASE}/{actor}-initial.nft"],
                prefix + ["conntrackd", "-C", f"{BASE}/{actor}.conf", "-d"],
                prefix + ["conntrackd", "-C", f"{BASE}/{actor}.conf", "-s", "runtime"],
            ]
        )
        shutdown.append(prefix + ["conntrackd", "-C", f"{BASE}/{actor}.conf", "-k"])
    remaining = [row for index, row in enumerate(commands) if index not in consumed]
    require(
        Counter(tuple(row["arguments"]) for row in remaining)
        == Counter(tuple(row) for row in setup + shutdown),
        "Command history contains unaccounted mutations or missing setup operations.",
    )
    for row in remaining:
        if row["arguments"] in shutdown:
            require(
                shutdown_after < row["startNs"] < row["endNs"] < shutdown_before,
                "Daemon was stopped before its final observations or after observer shutdown.",
            )
        else:
            require(
                row["endNs"] < setup_before,
                "Setup mutation occurred after initial native state observations began.",
            )
        if row["arguments"][-2:-1] == ["offload"]:
            response = json.loads(row["stdout"])
            require(
                response["interface"] == row["arguments"][-1]
                and set(response["before"]) == set(response["after"]) == set(wire.FEATURES)
                and all(
                    type(value) is int and value in (0, 1) for value in response["before"].values()
                )
                and all(type(value) is int and value == 0 for value in response["after"].values())
                and len(response["operations"]) == 12,
                "Offload producer readback remains enabled or incomplete.",
            )
            previous = row["startNs"]
            for index, (feature, (get, set_)) in enumerate(wire.FEATURES.items()):
                triple = response["operations"][3 * index : 3 * index + 3]
                require(
                    [item["command"] for item in triple] == [get, set_, get]
                    and [item["result"] for item in triple] == [response["before"][feature], 0, 0],
                    "Offload ioctl sequence contradicts readback.",
                )
                for item in triple:
                    _, previous = interval(item, previous, row["endNs"])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "directory", nargs="?", type=Path, default=ROOT / "examples/replication/native"
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        result = check_capture(args.directory)
    except (EvidenceError, ValueError, KeyError, TypeError, OSError, IndexError) as error:
        parser.exit(1, f"Replication capture rejected: {error}\n")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(
        f"Verified {result['packetCount']} packets, {result['snapshotCount']} kernel dumps, and {result['syncFrameCount']} sync frames."
    )
    return 0


def check_capture(directory):
    directory = Path(directory)
    manifest = nat.read_json(directory / "capture.json")
    commands = nat.read_json(directory / "commands.json")
    require(
        manifest["schema"] == 1
        and type(manifest["schema"]) is int
        and manifest["profile"] == "conntrackd-ftfw-udp-handoff"
        and manifest["byteorder"] == "little",
        "Unsupported replication producer profile.",
    )
    interval(manifest)
    previous = manifest["startNs"]
    for command in commands:
        require(
            set(command) == {"arguments", "startNs", "endNs", "returncode", "stdout", "stderr"}
            and isinstance(command["arguments"], list)
            and all(isinstance(value, str) for value in command["arguments"])
            and command["returncode"] == 0
            and type(command["returncode"]) is int
            and not command["stderr"],
            "Native command failed or has unsupported fields.",
        )
        _, previous = interval(command, previous, manifest["endNs"])
    require(
        [(event["id"], event["type"]) for event in manifest["events"]] == list(EVENTS),
        "Unexpected ordered event inventory.",
    )
    metadata = {
        "establish": {"gateway": "a", "leg": "original"},
        "replicate": {"source": "a", "destination": "b"},
        "client-route": {"leg": "original", "source": "a", "destination": "b"},
        "server-route": {"leg": "reply", "source": "a", "destination": "b"},
        "fence-primary": {"gateway": "a"},
        "commit": {"gateway": "b"},
        "install-deny": {"gateway": "b", "policy": "deny"},
        "install-permit": {"gateway": "b", "policy": "permit-established"},
        **{
            name: {"gateway": "b", "leg": "original" if name == "continued-original" else "reply"}
            for name in (
                "uncommitted",
                "denied",
                "permitted",
                "continued-original",
                "continued-reply",
            )
        },
    }
    for event in manifest["events"]:
        expected = metadata[event["id"]]
        require(
            set(event)
            == {
                "id",
                "type",
                "startNs",
                "endNs",
                "before",
                "after",
                "result",
                "commands",
                *expected,
            }
            and all(event[key] == value for key, value in expected.items()),
            "Event gateway, handoff leg, replication direction, or policy metadata disagrees with fixed native operation.",
        )
    consumed = set()

    def command_at(index, expected=None, lower=0, upper=2**64):
        integer(index, len(commands))
        require(index not in consumed, "Native command reference is reused.")
        consumed.add(index)
        row = commands[index]
        interval(row, lower, upper)
        if expected is not None:
            require(
                row["arguments"] == expected,
                "Native command arguments contradict their observation.",
            )
        return row

    def exported(reference, actor, args, lower=0, upper=2**64, *, as_json=True):
        name = reference["file"]
        require(
            set(reference) == {"file", "command"} and re.fullmatch(r"[a-z0-9.-]+", name),
            "Invalid native artifact reference.",
        )
        row = command_at(reference["command"], ["ip", "netns", "exec", actor, *args], lower, upper)
        require(
            (directory / name).read_text() == row["stdout"],
            "Native export contradicts exact command stdout.",
        )
        return nat.read_json(directory / name) if as_json else row["stdout"]

    indices = {}
    observers = {(row["actor"], row["kind"]): row for row in manifest["observers"]}
    require(
        len(manifest["observers"]) == len(observers) == 8
        and set(observers)
        == {(a, "packet") for a in ACTORS} | {(a, k) for a in GATEWAYS for k in ("nflog", "trace")},
        "Missing or duplicate native observer.",
    )
    first_event = manifest["events"][0]["startNs"]
    last_event = manifest["events"][-1]["endNs"]
    for (actor, kind), observer in observers.items():
        require(
            observer["runningBeforeStop"] is True
            and observer["stopSignal"] == 15
            and observer["returncode"] == (-15 if kind == "trace" else 0)
            and last_event < observer["stopNs"] < observer["endNs"] <= manifest["endNs"],
            "Observer exited early or failed during capture.",
        )
        if kind == "trace":
            expected = ["ip", "netns", "exec", actor, "nft", "monitor", "trace"]
            require(
                observer["file"] == f"{actor}-trace.txt"
                and observer["errors"] == f"{actor}-trace-errors.txt"
                and not (directory / observer["errors"]).read_text(),
                "Native trace monitor reported errors.",
            )
            require(
                manifest["startNs"] < observer["startNs"] < first_event,
                "Trace monitor started too late.",
            )
        else:
            ready = observer["ready"]
            require(
                manifest["startNs"] < ready["readyNs"] < first_event,
                "Native packet observer started too late.",
            )
            if kind == "packet":
                expected = [
                    "ip",
                    "netns",
                    "exec",
                    actor,
                    "python3",
                    TASK,
                    "sniff",
                    f"{BASE}/{actor}-frames.jsonl",
                    actor,
                    *LINKS[actor],
                ]
                require(
                    observer["file"] == f"{actor}-frames.jsonl"
                    and ready["namespace"] == actor
                    and [row["interface"] for row in ready["interfaces"]] == list(LINKS[actor]),
                    "AF_PACKET observer interface binding disagrees.",
                )
                indices[actor] = {
                    row["interface"]: integer(row["ifindex"], 2**32) for row in ready["interfaces"]
                }
                require(
                    all(row["receiveBuffer"] >= 131072 for row in ready["interfaces"]),
                    "Insufficient retained AF_PACKET receive buffer.",
                )
            else:
                expected = [
                    "ip",
                    "netns",
                    "exec",
                    actor,
                    "python3",
                    "/task/replication/nflog.py",
                    f"{BASE}/{actor}-nflog.jsonl",
                    "42",
                ]
                require(
                    observer["file"] == f"{actor}-nflog.jsonl", "NFLOG artifact binding disagrees."
                )
                reassembly.check_nflog_configuration(ready)
        require(
            observer["command"] == expected,
            "Observer command contradicts selected capture profile.",
        )
    require(
        manifest["interfaces"] == {actor: list(links) for actor, links in LINKS.items()},
        "Manifest interface inventory disagrees.",
    )
    for actor in ACTORS:
        values = {
            "net.ipv4.ip_forward": int(actor in GATEWAYS),
            "net.ipv4.conf.all.rp_filter": 0,
            "net.ipv4.conf.default.rp_filter": 0,
            "net.ipv6.conf.all.disable_ipv6": 1,
            "net.ipv6.conf.default.disable_ipv6": 1,
            "net.netfilter.nf_conntrack_udp_timeout": 30,
            "net.netfilter.nf_conntrack_udp_timeout_stream": 120,
            **{f"net.ipv4.conf.{name}.rp_filter": 0 for name in LINKS[actor]},
        }
        text = exported(
            manifest["settings"][actor],
            actor,
            ["sysctl", *values],
            upper=first_event,
            as_json=False,
        )
        require(
            text == "".join(f"{key} = {value}\n" for key, value in values.items()),
            "Native namespace sysctl readback disagrees.",
        )
    for actor in GATEWAYS:
        require(
            (directory / f"{actor}.conf").read_text() == configuration(actor),
            "Daemon configuration differs from selected FTFW external cache profile.",
        )
    owners, fenced, policy = {"original": "a", "reply": "a"}, False, "initial"
    statuses, ids = {"a": None, "b": None}, {}
    counts = {actor: {} for actor in GATEWAYS}
    snapshot_count = 0

    def observations(value, label, lower, upper):
        nonlocal snapshot_count
        require(
            set(value) == {"conntrack", "tables", "networks"}
            and set(value["conntrack"]) == set(value["tables"]) == set(GATEWAYS),
            "Missing complete gateway observation.",
        )
        tables, rows, references, times = {}, {}, {}, []
        for actor in GATEWAYS:
            reference = value["conntrack"][actor]
            name = f"{label}-{actor}-conntrack.json"
            require(
                reference["file"] == name, "Conntrack snapshot belongs to another event boundary."
            )
            row = command_at(
                reference["command"],
                [
                    "ip",
                    "netns",
                    "exec",
                    actor,
                    "python3",
                    "/task/capture_conntrack.py",
                    "--output",
                    f"{BASE}/{name}",
                ],
                lower,
                upper,
            )
            require(not row["stdout"], "Unexpected conntrack snapshot producer stdout.")
            document = nat.read_json(directory / name)
            require(
                type(document["schema"]) is int and type(document["family"]) is int,
                "Invalid conntrack numeric envelope.",
            )
            decoded = lifecycle.decode_snapshot(document)
            require(
                len(decoded) == int(statuses[actor] is not None),
                "Destination or source record presence contradicts event prefix.",
            )
            for entry in decoded:
                require(
                    entry["original"] == ORIGINAL
                    and entry["reply"] == WIRE_REPLY
                    and entry["originalZone"] == entry["replyZone"] == 0
                    and entry["status"] == statuses[actor]
                    and type(entry["remainingTTL"]) is int
                    and 0
                    < entry["remainingTTL"]
                    <= (
                        30
                        if actor == "a" or entry["status"] == 442
                        else 120
                        if entry["status"] == 446
                        else 180
                    )
                    and type(entry["id"]) is int
                    and entry["mark"] == 0,
                    "Actual conntrack tuple, zone, status, lifetime, or mark disagrees.",
                )
                if actor in ids:
                    require(
                        entry["id"] == ids[actor], "Native selected kernel record changed identity."
                    )
                ids[actor] = entry["id"]
            rows[actor], references[actor] = decoded, name
            snapshot_count += 1
            times.append(row)
            reference = value["tables"][actor]
            require(
                reference["file"] == f"{label}-{actor}-nftables.json",
                "Ruleset export belongs to another event boundary.",
            )
            tables[actor] = exported(
                reference, actor, ["nft", "-j", "-a", "list", "ruleset"], lower, upper
            )
            require(
                nat.objects(tables[actor])
                == expected_tables("initial" if actor == "a" else policy, counts[actor]),
                "Full active ruleset, priorities, policy, or packet counters disagree.",
            )
            times.append(commands[reference["command"]])
        networks = {}
        for actor in ACTORS:
            records = value["networks"][actor]
            require(
                set(records) == {"links", "addresses", "routes", "neighbors", "rules"},
                "Missing full namespace network exports.",
            )
            networks[actor] = {}
            args = {
                "links": ["link", "show"],
                "addresses": ["address", "show"],
                "routes": ["-4", "route", "show", "table", "main"],
                "neighbors": ["neigh", "show"],
                "rules": ["-4", "rule", "show"],
            }
            for kind, arguments in args.items():
                reference = records[kind]
                require(
                    reference["file"] == f"{label}-{actor}-{kind}.json",
                    "Network readback belongs to another event boundary.",
                )
                networks[actor][kind] = exported(
                    reference, actor, ["ip", "-j", *arguments], lower, upper
                )
                times.append(commands[reference["command"]])
            require(
                networks[actor]["rules"]
                == [
                    {"priority": 0, "src": "all", "table": "local"},
                    {"priority": 32766, "src": "all", "table": "main"},
                    {"priority": 32767, "src": "all", "table": "default"},
                ],
                "Policy routing differs from default RPDB.",
            )
        check_network(networks, owners, fenced, indices)
        return (
            rows,
            references,
            tables,
            min(row["startNs"] for row in times),
            max(row["endNs"] for row in times),
        )

    initial, initial_refs, _, initial_start, initial_end = observations(
        manifest["initial"], "initial", manifest["startNs"], first_event
    )
    for actor in GATEWAYS:
        text = exported(
            manifest["initialCaches"][actor],
            actor,
            ["conntrackd", "-C", f"{BASE}/{actor}.conf", "-e", "-x"],
            initial_end,
            first_event,
            as_json=False,
        )
        require(decode_cache_xml(text) == [], "External cache was not initially empty.")
    report_events, operation_bounds = [], {}
    previous_event_end = initial_end
    for event in manifest["events"]:
        name, kind = event["id"], event["type"]
        interval(event, previous_event_end, manifest["endNs"])
        before, before_refs, tables, _, before_end = observations(
            event["before"], f"{name}-before", event["startNs"], event["endNs"]
        )
        entry = {
            key: event[key]
            for key in ("id", "type", "gateway", "leg", "source", "destination", "policy")
            if key in event
        }
        entry.update(before=before, snapshots={"before": before_refs})
        operations = event["commands"]
        require(
            isinstance(operations, list)
            and operations == list(range(operations[0], operations[-1] + 1))
            if operations
            else isinstance(operations, list),
            "Event command indices are not contiguous.",
        )
        if kind == "packet":
            require(
                event["gateway"] == owners[event["leg"]],
                "Packet gateway contradicts current endpoint route owner.",
            )
            require(not operations, "Packet event contains an unmodeled native command.")
            sender, receiver = event["result"]["sender"], event["result"]["receiver"]
            interval(sender, before_end, event["endNs"])
            interval(receiver, sender["endNs"], event["endNs"])
            interval(sender["response"], sender["startNs"], sender["endNs"])
            interval(receiver["response"], receiver["startNs"], receiver["endNs"])
            op_start, op_end = sender["startNs"], receiver["endNs"]
            actor = event["gateway"]
            statuses[actor] = (
                440
                if name == "establish"
                else statuses[actor]
                if name == "uncommitted"
                else 442
                if name == "denied"
                else 446
            )
            size = 28 + len(bytes.fromhex(sender["request"]["payloadHex"]))
            for key in (
                "INGRESS",
                "TRACKED",
                "NEW" if name in ("establish", "uncommitted") else "ESTABLISHED",
                *(() if name in ("uncommitted", "denied") else ("EGRESS",)),
            ):
                previous_count, previous_bytes = counts[actor].get(key, (0, 0))
                counts[actor][key] = previous_count + 1, previous_bytes + size
        elif kind == "stage":
            require(
                (event["source"], event["destination"]) == ("a", "b"),
                "Unexpected replication direction.",
            )
            attempts = event["result"]["attempts"]
            require(
                attempts and event["result"]["external"] == attempts[-1],
                "Selected cache result does not match final actual read.",
            )
            for index, reference in enumerate(attempts):
                text = exported(
                    reference,
                    "b",
                    ["conntrackd", "-C", f"{BASE}/b.conf", "-e", "-x"],
                    before_end,
                    event["endNs"],
                    as_json=False,
                )
                cached = decode_cache_xml(text)
                require(
                    cached
                    == (
                        [{"original": ORIGINAL, "unreplied": True, "assured": False}]
                        if index == len(attempts) - 1
                        else []
                    ),
                    "Actual external cache presence or status label disagrees.",
                )
            internal = event["result"]["internal"]
            text = exported(
                internal,
                "a",
                ["conntrackd", "-C", f"{BASE}/a.conf", "-i", "-x"],
                before_end,
                event["endNs"],
                as_json=False,
            )
            check_internal_cache(text, before["a"][0])
            require(
                operations
                == [reference["command"] for reference in attempts] + [internal["command"]],
                "Replication stage omits native cache command history.",
            )
            op_start, op_end = commands[operations[0]]["startNs"], commands[operations[-1]]["endNs"]
            entry["cacheSource"] = attempts[-1]["file"]
        else:
            expected = {
                "client-route": [
                    [
                        "ip",
                        "netns",
                        "exec",
                        "client",
                        "ip",
                        "route",
                        "replace",
                        "203.0.113.2/32",
                        "via",
                        "192.0.3.1",
                        "dev",
                        "cbl",
                        "src",
                        "192.0.2.2",
                    ]
                ],
                "server-route": [
                    [
                        "ip",
                        "netns",
                        "exec",
                        "server",
                        "ip",
                        "route",
                        "replace",
                        "203.0.113.1/32",
                        "via",
                        "198.51.101.1",
                        "dev",
                        "sbl",
                        "src",
                        "198.51.100.2",
                    ]
                ],
                "fence-primary": [
                    ["ip", "netns", "exec", "a", "ip", "link", "set", interface, "down"]
                    for interface in ("car", "sar")
                ],
                "commit": [
                    ["ip", "netns", "exec", "b", "conntrackd", "-C", f"{BASE}/b.conf", "-c"]
                ],
                "install-deny": [
                    ["ip", "netns", "exec", "b", "nft", "flush", "chain", "ip", "netlib", "forward"]
                ],
                "install-permit": [
                    [
                        "ip",
                        "netns",
                        "exec",
                        "b",
                        "nft",
                        "add",
                        "rule",
                        "ip",
                        "netlib",
                        "forward",
                        "ct",
                        "state",
                        "established",
                        "accept",
                    ]
                ],
            }[name]
            require(
                len(operations) == len(expected)
                and event["result"] == (operations if kind == "fence" else operations[0]),
                "Event operation or command count disagrees.",
            )
            for index, arguments in zip(operations, expected, strict=True):
                command_at(index, arguments, before_end, event["endNs"])
            op_start, op_end = commands[operations[0]]["startNs"], commands[operations[-1]]["endNs"]
            if kind == "handoff":
                require(
                    (event["source"], event["destination"]) == ("a", "b"),
                    "Unexpected route handoff direction.",
                )
                owners[event["leg"]] = "b"
            elif kind == "fence":
                require(event["gateway"] == "a", "Wrong gateway fenced.")
                fenced = True
            elif kind == "commit":
                require(
                    event["gateway"] == "b" and before["b"] == [],
                    "Unsupported destination collision at commit.",
                )
                statuses["b"] = 440
            else:
                require(
                    event["gateway"] == "b"
                    and event["policy"]
                    == ("deny" if name == "install-deny" else "permit-established"),
                    "Unexpected destination admission change.",
                )
                policy = "deny" if name == "install-deny" else "permit"
        after, after_refs, _, after_start, _ = observations(
            event["after"], f"{name}-after", op_end, event["endNs"]
        )
        require(
            before_end < op_start < op_end < after_start,
            "Event operation is outside adjacent actual state readbacks.",
        )
        entry.update(after=after)
        entry["snapshots"]["after"] = after_refs
        report_events.append(entry)
        operation_bounds[name] = op_start, op_end
        previous_event_end = event["endNs"]
    final, final_refs, _, _, final_end = observations(
        manifest["final"], "final", previous_event_end, manifest["endNs"]
    )
    for actor in GATEWAYS:
        text = exported(
            manifest["finalCaches"][actor],
            actor,
            ["conntrackd", "-C", f"{BASE}/{actor}.conf", "-e", "-x"],
            final_end,
            manifest["endNs"],
            as_json=False,
        )
        require(
            decode_cache_xml(text)
            == [
                {
                    "original": ORIGINAL,
                    "unreplied": actor == "b",
                    "assured": actor == "a",
                    **({"mark": 0} if actor == "a" else {}),
                }
            ],
            "Final external cache contradicts transferred selected flow.",
        )
        for kind in ("cache", "network", "runtime", "ct"):
            text = exported(
                manifest["statistics"][actor][kind],
                actor,
                ["conntrackd", "-C", f"{BASE}/{actor}.conf", "-s", kind],
                final_end,
                manifest["endNs"],
                as_json=False,
            )
            for line in text.splitlines():
                if re.search(
                    r"failed:|Malformed|Wrong protocol|Bad message|Truncated|Packets lost:|Packets before:|unknown type:|event failed:|netlink overrun:|flush kernel table:|resync with kernel table:|process segfault:|process termsig:|select failed:|wait failed:|read failed:|unknown request:|Error send",
                    line,
                ):
                    values = (
                        [int(line.rsplit(":", 1)[-1].rsplit("/", 1)[-1])]
                        if ":" in line
                        else [int(value) for value in re.findall(r"\b[0-9]+\b", line)]
                    )
                    require(
                        values and all(value == 0 for value in values),
                        "Daemon statistics report failed or lost observations.",
                    )
        log = (directory / f"{actor}.log").read_text()
        require(
            not re.search(
                r"\[error\]|can't be committed|commit-create:|commit-destroy:", log, re.I
            ),
            "Daemon log reports replication or commit errors.",
        )
        if actor == "b":
            require("Committed 1 new entries" in log, "Missing daemon commit summary.")
    fence_event = manifest["events"][4]
    fence_commands = {
        name: commands[index]
        for name, index in zip(("car", "sar"), fence_event["commands"], strict=True)
    }
    frames, sync, errors = [], [], []
    nflog, traces = {}, {}
    for actor in ACTORS:
        observer = observers[(actor, "packet")]
        previous_time = observer["ready"]["readyNs"]
        for number, row in enumerate(read_lines(directory / observer["file"]), 1):
            require(
                previous_time < row["timeNs"] <= observer["endNs"],
                "AF_PACKET observations are out of capture order.",
            )
            previous_time = row["timeNs"]
            decoded = decode_af(row, actor, number, indices, fence_commands)
            if decoded is None:
                continue
            if decoded.get("error"):
                errors.append((actor, decoded["interface"]))
            else:
                require(
                    not any(a == actor and name == decoded["interface"] for a, name in errors),
                    "AF_PACKET data appeared after its socket was closed.",
                )
                (sync if decoded["sync"] else frames).append(decoded)
    require(
        Counter(errors) == Counter({("a", "car"): 1, ("a", "sar"): 1}),
        "Missing or duplicate expected fence socket errors.",
    )
    for actor in GATEWAYS:
        observer = observers[(actor, "nflog")]
        rows = [
            decode_nflog(row, actor, number)
            for number, row in enumerate(read_lines(directory / observer["file"]), 1)
        ]
        previous_time = observer["ready"]["readyNs"]
        for index, row in enumerate(rows):
            require(
                previous_time < row["timeNs"] < observer["endNs"]
                and row["localSequence"] == index
                and row["globalSequence"] == index + 1,
                "NFLOG ordering or sequence completeness disagrees.",
            )
            previous_time = row["timeNs"]
        nflog[actor] = rows
        traces[actor] = parse_traces(directory / f"{actor}-trace.txt")
    require(
        len(frames) == 20
        and sum(map(len, nflog.values())) == 16
        and sum(map(len, traces.values())) == 6,
        "Missing or additional selected AF_PACKET, NFLOG, or trace observations.",
    )
    used_frames, used_logs, used_traces = set(), set(), set()
    for event, entry in zip(manifest["events"], report_events, strict=True):
        if event["type"] != "packet":
            continue
        name, actor, leg = event["id"], event["gateway"], event["leg"]
        require(
            (actor, leg)
            == (
                ("a", "original")
                if name == "establish"
                else ("b", "original")
                if name == "continued-original"
                else ("b", "reply")
            ),
            "Packet gateway or direction contradicts selected route ownership.",
        )
        sender, receiver = event["result"]["sender"], event["result"]["receiver"]
        source_actor, destination_actor = (
            ("client", "server") if leg == "original" else ("server", "client")
        )
        expected_input, expected_output = (
            (ORIGINAL, WIRE) if leg == "original" else (WIRE_REPLY, PEER_REPLY)
        )
        payload = f"replication:{name}".encode().hex()
        local = ["192.0.2.2", 41000] if source_actor == "client" else ["198.51.100.2", 9000]
        peer = [expected_input["destination"], expected_input["destinationPort"]]
        request = {"operation": "send", "peer": peer, "payloadHex": payload, "ttl": 64}
        require(
            sender["request"] == request
            and sender["response"]["result"]
            == {
                "bytesSent": len(bytes.fromhex(payload)),
                "payloadHex": payload,
                "local": local,
                "peer": peer,
                "ttl": 64,
            }
            and receiver["request"] == {"operation": "receive", "timeout": 0.3},
            "Native endpoint send request or result disagrees.",
        )
        selected = [
            (index, frame) for index, frame in enumerate(frames) if frame["payloadHex"] == payload
        ]
        success = name not in ("uncommitted", "denied")
        require(
            len(selected) == (4 if success else 2),
            "Unconsumed, missing, or duplicated selected packet frame.",
        )
        for index, frame in selected:
            require(
                index not in used_frames
                and sender["response"]["startNs"] <= frame["timeNs"] < receiver["endNs"],
                "Selected frame lies outside its actual socket operation.",
            )
            used_frames.add(index)
        inbound = [
            frame
            for _, frame in selected
            if frame["namespace"] == actor and frame["packetType"] == 0
        ]
        outbound = [
            frame
            for _, frame in selected
            if frame["namespace"] == actor and frame["packetType"] == 4
        ]
        require(
            len(inbound) == 1 and len(outbound) == int(success),
            "Missing gateway ingress or contradictory gateway egress.",
        )
        incoming, outgoing = inbound[0], outbound[0] if outbound else None
        require(
            incoming["header"] == expected_input and incoming["ttl"] == 64,
            "Gateway ingress tuple or TTL disagrees.",
        )
        sender_frames = [frame for _, frame in selected if frame["namespace"] == source_actor]
        receiver_frames = [
            frame for _, frame in selected if frame["namespace"] == destination_actor
        ]
        require(
            len(sender_frames) == 1
            and sender_frames[0]["packetType"] == 4
            and sender_frames[0]["hex"] == incoming["hex"]
            and len(receiver_frames) == int(success),
            "Endpoint and gateway frame bytes or directions disagree.",
        )
        if outgoing:
            require(
                outgoing["header"] == expected_output
                and outgoing["ttl"] == 63
                and outgoing["payloadHex"] == payload
                and outgoing["ipId"] == incoming["ipId"]
                and outgoing["ipLength"] == incoming["ipLength"]
                and outgoing["udpLength"] == incoming["udpLength"]
                and receiver_frames[0]["packetType"] == 0
                and receiver_frames[0]["hex"] == outgoing["hex"],
                "NAT egress, endpoint delivery, or preserved datagram identity disagrees.",
            )
            source_ip = bytes.fromhex(incoming["hex"])[14:34]
            output_ip = bytes.fromhex(outgoing["hex"])[14:34]
            require(
                source_ip[:8] == output_ip[:8] and source_ip[9] == output_ip[9],
                "Forwarding changed preserved IPv4 fields.",
            )
            received = {
                "payloadHex": payload,
                "peer": [expected_output["source"], expected_output["sourcePort"]],
                "local": [expected_output["destination"], expected_output["destinationPort"]],
            }
            require(
                receiver["response"]["result"] == received,
                "Socket delivery contradicts actual NAT output.",
            )
        else:
            require(
                receiver["response"]["result"] is None
                and receiver["response"]["endNs"] - receiver["response"]["startNs"] >= 300_000_000,
                "Native denied packet lacks its complete bounded receive observation.",
            )
        logs = [row for row in nflog[actor] if row["packet"]["payloadHex"] == payload]
        require(
            [row["prefix"] for row in logs]
            == (["INGRESS", "TRACKED", "EGRESS"] if success else ["INGRESS", "TRACKED"]),
            "NFLOG hook prefix is missing or duplicated.",
        )
        for row in logs:
            require(
                row["source"] not in used_logs
                and sender["response"]["startNs"] <= row["timeNs"] < receiver["endNs"],
                "NFLOG observation lies outside selected socket operation.",
            )
            used_logs.add(row["source"])
            packet = incoming if row["prefix"] != "EGRESS" else outgoing
            raw = bytes.fromhex(packet["hex"])
            expected_ip = raw[14 : 14 + packet["ipLength"]]
            logged = bytes.fromhex(row["packet"]["raw"])
            require(
                logged[14:] == expected_ip,
                "NFLOG packet bytes contradict unchanged AF_PACKET capture.",
            )
        candidates = [
            trace
            for trace in traces[actor]
            if trace["stages"][0]["ipId"] == incoming["ipId"]
            and trace["stages"][0]["packet"] == incoming["header"]
        ]
        require(len(candidates) == 1, "Missing or ambiguous selected native packet trace.")
        trace = candidates[0]
        require(
            (actor, trace["id"]) not in used_traces, "Trace reused for a later selected packet."
        )
        used_traces.add((actor, trace["id"]))
        table = nat.read_json(directory / event["before"]["tables"][actor]["file"])
        state, interface_in, interface_out = check_packet_trace(
            trace, incoming, outgoing, table, name, actor, indices
        )
        require(
            incoming["interface"] == interface_in
            and sender_frames[0]["interface"] == OPPOSITE[interface_in]
            and all(
                row["inputIndex"] == indices[actor][interface_in]
                and row["hardwareHex"] == incoming["hex"][:28]
                and row["outputIndex"]
                == (indices[actor][interface_out] if row["prefix"] == "EGRESS" else None)
                for row in logs
            ),
            "NFLOG or AF_PACKET interface binding disagrees with trace path.",
        )
        if outgoing:
            require(
                outgoing["interface"] == interface_out
                and receiver_frames[0]["interface"] == OPPOSITE[interface_out],
                "Egress route interface contradicts endpoint delivery.",
            )
        entry.update(
            inputHex=bytes.fromhex(incoming["hex"])[14 : 14 + incoming["ipLength"]].hex(),
            outputHex=bytes.fromhex(outgoing["hex"])[14 : 14 + outgoing["ipLength"]].hex()
            if outgoing
            else None,
            outputEthernetHex=outgoing["hex"] if outgoing else None,
            ingressSource=logs[0]["source"],
            postSource=logs[-1]["source"] if outgoing else None,
            frameSources=[frame["source"] for _, frame in selected],
            outputFrameSource=outgoing["source"] if outgoing else None,
            disposition="forwarded"
            if success
            else "routeDrop"
            if name == "uncommitted"
            else "forwardDrop",
            classification=state,
        )
    require(
        len(used_frames) == len(frames)
        and len(used_logs) == sum(map(len, nflog.values()))
        and len(used_traces) == 6,
        "Selected native packet evidence remains unconsumed.",
    )
    sent = Counter(frame["hex"] for frame in sync if frame["packetType"] == 4)
    received = Counter(frame["hex"] for frame in sync if frame["packetType"] == 0)
    require(sent == received, "Sync AF_PACKET sender and receiver bytes or counts disagree.")
    source_starts = {
        name: event["result"]["sender"]["response"]["startNs"]
        for event in manifest["events"]
        if event["type"] == "packet"
        for name in (event["id"],)
    }
    for frame in sync:
        actor = "a" if frame["header"]["source"] == "10.10.0.1" else "b"
        for message in frame["messages"]:
            attributes = message.get("attributes")
            if attributes:
                status = attributes["status"]
                source_name = (
                    "establish" if actor == "a" else "denied" if status == 442 else "permitted"
                )
                require(
                    frame["timeNs"] >= source_starts[source_name],
                    "FTFW data predates its actual source state transition.",
                )
    sync_data = []
    for actor in GATEWAYS:
        previous_sequence = None
        for frame in sorted(
            (frame for frame in sync if frame["namespace"] == actor and frame["packetType"] == 4),
            key=lambda row: row["timeNs"],
        ):
            for index, message in enumerate(frame["messages"]):
                sequence = message["sequence"]
                require(
                    previous_sequence is None or 0 < (sequence - previous_sequence) % 2**32 < 2**31,
                    "Outgoing FTFW sequence is repeated or reordered.",
                )
                previous_sequence = sequence
                if "attributes" in message:
                    attributes = message["attributes"]
                    require(
                        message["type"] in ("new", "update")
                        and attributes["original"] == ORIGINAL
                        and attributes["status"] in ((440,) if actor == "a" else (442, 446))
                        and attributes.get("zone", 0) == 0
                        and attributes.get("mark", 0) == 0
                        and "remainingTTL" not in attributes
                        and (
                            attributes.get("sourceNAT"),
                            attributes.get("sourceNATPort"),
                            attributes.get("destinationNAT"),
                            attributes.get("destinationNATPort"),
                        )
                        == (WIRE["source"], 40000, WIRE["destination"], 9000),
                        "Actual FTFW record contradicts selected source tuple, NAT attributes, status, zone, or timer profile.",
                    )
                    sync_data.append((frame, index, message))
    stage = report_events[1]
    source = stage["before"]["a"][0]
    stage_reference = manifest["events"][1]["result"]["external"]
    cache_start = commands[stage_reference["command"]]["startNs"]
    first_send = manifest["events"][0]["result"]["sender"]["response"]["startNs"]
    matches = []
    for frame in sync:
        if (
            frame["namespace"] != "b"
            or frame["packetType"] != 0
            or not first_send <= frame["timeNs"] < cache_start
        ):
            continue
        for index, message in enumerate(frame["messages"]):
            attributes = message.get("attributes")
            if (
                attributes
                and message["type"] in ("new", "update")
                and attributes["status"] == source["status"]
            ):
                matches.append(
                    {
                        "source": frame["source"],
                        "messageIndex": index,
                        "sequence": message["sequence"],
                        "attributes": attributes,
                    }
                )
    require(
        matches,
        "No actual incoming FTFW record binds the selected source to cached destination state.",
    )
    attributes = matches[-1]["attributes"]
    require(
        attributes["original"] == source["original"]
        and attributes["sourceNAT"] == source["reply"]["destination"]
        and attributes["sourceNATPort"] == source["reply"]["destinationPort"]
        and attributes["destinationNAT"] == source["reply"]["source"]
        and attributes["destinationNATPort"] == source["reply"]["sourcePort"],
        "Staged FTFW NAT attributes do not project the actual source table record.",
    )
    stage["sourceSync"] = matches
    stage["cache"] = [
        {
            "original": attributes["original"],
            "zone": attributes.get("zone", 0),
            "sourceNAT": {"address": attributes["sourceNAT"], "port": attributes["sourceNATPort"]},
            "destinationNAT": {
                "address": attributes["destinationNAT"],
                "port": attributes["destinationNATPort"],
            },
            "seenReply": bool(attributes["status"] & 2),
        }
    ]
    daemon_final = max(commands[index]["endNs"] for index in consumed)
    require(len(manifest["endpoints"]) == 2, "Missing or duplicate native endpoint lifetime.")
    for endpoint, actor, address, port in zip(
        manifest["endpoints"],
        ("client", "server"),
        ("192.0.2.2", "198.51.100.2"),
        (41000, 9000),
        strict=True,
    ):
        require(
            set(endpoint) == {"command", "startNs", "endNs", "binding", "returncode"}
            and endpoint["command"]
            == ["ip", "netns", "exec", actor, "python3", TASK, "endpoint", address, str(port)]
            and type(endpoint["returncode"]) is int
            and endpoint["returncode"] == 0
            and initial_end
            < endpoint["startNs"]
            < first_event
            < daemon_final
            < endpoint["endNs"]
            < manifest["endNs"],
            "Native endpoint identity, lifetime, or completion disagrees.",
        )
        binding = endpoint["binding"]
        interval(binding, endpoint["startNs"], first_event)
        interval(binding["response"], binding["startNs"], binding["endNs"])
        require(
            binding["request"] == {"operation": "bind"}
            and binding["response"]["result"] == {"local": [address, port], "mtuDiscover": 0},
            "Native endpoint socket binding disagrees.",
        )
    check_provenance(
        directory,
        commands,
        consumed,
        initial_start,
        daemon_final,
        min(observer["stopNs"] for observer in manifest["observers"]),
    )
    require(
        manifest["endNs"] - manifest["startNs"] < 30_000_000_000,
        "Capture exceeds the supported finite lifetime window.",
    )
    return {
        "schema": 1,
        "profile": manifest["profile"],
        "initial": initial,
        "initialSnapshots": initial_refs,
        "final": final,
        "finalSnapshots": final_refs,
        "events": report_events,
        "packetCount": 6,
        "snapshotCount": snapshot_count,
        "frameCount": len(frames),
        "nflogCount": len(used_logs),
        "syncFrameCount": len(sync),
        "syncDataCount": len(sync_data),
    }


if __name__ == "__main__":
    raise SystemExit(main())
