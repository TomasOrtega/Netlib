"""Decode unchanged fragment observations and replay their actual namespace domains."""

import copy
import ipaddress
import re
import struct

import check_reassembly_capture as reassembly
import check_wire_capture as wire
from attachment_capture_evidence import ifindex
from capture_evidence import EvidenceError, require
from reassembly_reference import ReassemblyOracle


def decode_ipv4(raw):
    try:
        return reassembly.decode_ipv4(raw)
    except reassembly.EvidenceError as error:
        raise EvidenceError(str(error)) from error


def namespace_ref(value):
    require(
        isinstance(value, dict)
        and set(value) == {"id", "birth"}
        and all(type(value[key]) is int and value[key] > 0 for key in value),
        "Fragment provenance lacks an actual namespace lifetime.",
    )
    return value["id"], value["birth"]


def interface_ref(value):
    require(
        isinstance(value, dict)
        and set(value) == {"ns", "ifindex", "birth"}
        and type(value["birth"]) is int
        and value["birth"] >= value["ns"]["birth"],
        "Fragment ingress lacks an actual interface lifetime.",
    )
    namespace_ref(value["ns"])
    ifindex(value["ifindex"])
    return value


def decode_ethernet(raw):
    require(
        isinstance(raw, str) and re.fullmatch(r"(?:[0-9a-f]{2})+", raw),
        "Fragment observation must retain unchanged hexadecimal Ethernet bytes.",
    )
    data = bytes.fromhex(raw)
    require(
        len(data) >= 34 and data[12:14] == bytes.fromhex("0800"),
        "Require an ordinary Ethernet IPv4 fragment observation.",
    )
    packet = decode_ipv4(data[14:].hex())
    return {
        **packet,
        "ethernetHex": raw,
        "sourceMAC": data[6:12].hex(":"),
        "destinationMAC": data[:6].hex(":"),
    }


def decode_udp(raw):
    packet = decode_ipv4(raw)
    require(
        packet["offsetBytes"] == 0 and not packet["moreFragments"],
        "Only an actual whole or reassembled datagram has a complete UDP tuple.",
    )
    data = bytes.fromhex(packet["payloadHex"])
    require(len(data) >= 8, "Truncated completed UDP header.")
    source, destination, length, checksum = struct.unpack("!HHHH", data[:8])
    require(length == len(data), "Completed UDP length contradicts its unchanged IPv4 payload.")
    pseudo = (
        ipaddress.IPv4Address(packet["source"]).packed
        + ipaddress.IPv4Address(packet["destination"]).packed
        + bytes((0, 17))
        + length.to_bytes(2, "big")
    )
    require(
        checksum == 0 or wire.folded_sum(pseudo + data) == 65535,
        "Completed UDP checksum is neither omitted nor valid.",
    )
    return {
        **packet,
        "header": {
            "source": packet["source"],
            "destination": packet["destination"],
            "protocol": 17,
            "sourcePort": source,
            "destinationPort": destination,
        },
        "dataHex": data[8:].hex(),
        "udpChecksum": {"value": checksum, "status": "omitted" if checksum == 0 else "valid"},
    }


def decode_fragment_af(row, actor, namespace, interfaces, source):
    namespace_ref(namespace)
    require(
        set(row) == {"namespace", "interface", "ifindex", "timeNs", "packetType", "hex"}
        and row["namespace"] == actor
        and row["interface"] in interfaces
        and type(row["timeNs"]) is int
        and row["timeNs"] >= 0
        and type(row["packetType"]) is int
        and row["packetType"] in (0, 4),
        "Raw fragment packet metadata contradicts its bound observer.",
    )
    interface = interface_ref(interfaces[row["interface"]])
    require(
        interface["ns"] == namespace
        and ifindex(row["ifindex"]) == interface["ifindex"]
        and row["timeNs"] >= interface["birth"],
        "Raw fragment arrived in a different namespace or interface instance.",
    )
    return {
        **decode_ethernet(row["hex"]),
        "source": source,
        "timeNs": row["timeNs"],
        "packetType": row["packetType"],
        "interfaceRef": copy.deepcopy(interface),
    }


def decode_fragment_nflog(row, namespace, source, prefixes):
    namespace_ref(namespace)
    require(
        set(row) == {"timeNs", "hex", "sender", "flags"}
        and isinstance(row["sender"], list)
        and len(row["sender"]) == 2
        and all(type(value) is int and value == 0 for value in row["sender"])
        and type(row["flags"]) is int
        and row["flags"] == 0
        and type(row["timeNs"]) is int
        and row["timeNs"] >= 0,
        "Fragment NFLOG message is truncated, mistimed, or not from the kernel.",
    )
    raw = bytes.fromhex(row["hex"])
    require(
        len(raw) >= 20
        and struct.unpack_from("=IHHII", raw) == (len(raw), 0x400, 0, 0, 0)
        and raw[16:20] == bytes((2, 0, 0, 42)),
        "Unexpected fragment NFLOG type, family, group, or native envelope.",
    )
    try:
        fields = reassembly.netlink_attributes(raw[20:])
    except reassembly.EvidenceError as error:
        raise EvidenceError(str(error)) from error
    require(
        set(fields)
        in ({1, 3, 4, 8, 9, 10, 12, 13, 15, 16, 17}, {1, 2, 3, 4, 8, 9, 10, 12, 13, 15, 16, 17})
        and fields[1] == bytes((8, 0, 0, 0))
        and fields[10].endswith(b"\0")
        and fields[10][:-1].decode("ascii") in prefixes,
        "Fragment NFLOG hook, selected prefix, or attribute inventory disagrees.",
    )
    require(
        all(len(fields[key]) == 4 for key in (4, 12, 13))
        and (2 not in fields or fields[2] == bytes(4))
        and len(fields[3]) == 16
        and fields[15] == bytes((0, 1))
        and fields[17] == bytes((0, 14))
        and len(fields[16]) == 14
        and fields[16][12:] == bytes.fromhex("0800")
        and len(fields[8]) == 12
        and fields[8][:4] == bytes.fromhex("00060000")
        and fields[8][4:10] == fields[16][6:12]
        and fields[8][10:] == bytes(2),
        "Fragment NFLOG hardware, timestamp, mark, or source MAC metadata disagrees.",
    )
    packet = decode_ipv4(fields[9].hex())
    return {
        "source": source,
        "namespace": copy.deepcopy(namespace),
        "timeNs": row["timeNs"],
        "prefix": fields[10][:-1].decode("ascii"),
        "inputIndex": ifindex(int.from_bytes(fields[4], "big")),
        "localSequence": int.from_bytes(fields[12], "big"),
        "globalSequence": int.from_bytes(fields[13], "big"),
        "hardwareHex": fields[16].hex(),
        "packet": packet,
    }


def join_fragment_ingress(frame, log, window):
    require(
        frame["packetType"] == 0
        and frame["interfaceRef"]["ns"] == log["namespace"]
        and frame["interfaceRef"]["ifindex"] == log["inputIndex"]
        and frame["raw"] == log["packet"]["raw"]
        and frame["ethernetHex"] == log["hardwareHex"] + log["packet"]["raw"],
        "Pre-defragmentation NFLOG bytes or actual iif contradict the bound physical arrival.",
    )
    require(
        len(window) == 2
        and all(type(value) is int for value in window)
        and window[0] < window[1]
        and all(window[0] <= value < window[1] for value in (frame["timeNs"], log["timeNs"])),
        "Fragment physical/log observations escape their actual operation window.",
    )
    return {
        "frameSource": frame["source"],
        "logSource": log["source"],
        "ingress": copy.deepcopy(frame["interfaceRef"]),
        "raw": frame["raw"],
        "observedDecision": log["prefix"],
    }


def reassembly_counters(text):
    require(isinstance(text, str), "Missing actual IPv4 SNMP readback.")
    lines = [line.split()[1:] for line in text.splitlines() if line.startswith("Ip:")]
    require(
        len(lines) == 2 and len(lines[0]) == len(lines[1]) and len(set(lines[0])) == len(lines[0]),
        "Malformed IPv4 SNMP counter observation.",
    )
    values = dict(zip(lines[0], map(int, lines[1]), strict=True))
    names = ("ReasmReqds", "ReasmOKs", "ReasmFails", "ReasmTimeout")
    require(
        all(name in values and values[name] >= 0 for name in names),
        "Missing or negative reassembly SNMP counter.",
    )
    return {name: values[name] for name in names}


def qualified_counter_delta(before, after, *, namespace_before, namespace_after):
    require(
        namespace_ref(namespace_before) == namespace_ref(namespace_after),
        "Reassembly counters belong to different namespace lifetimes.",
    )
    first, second = reassembly_counters(before), reassembly_counters(after)
    require(
        all(second[key] >= value for key, value in first.items()),
        "Reassembly counters moved backwards or crossed namespace/reset lifetimes.",
    )
    return {key: second[key] - value for key, value in first.items()}


def fragment_key(packet, namespace, user, vif):
    namespace_ref(namespace)
    require(
        type(user) is int and 0 <= user < 2**32 and type(vif) is int and 0 <= vif <= 2**31 - 1,
        "Invalid actual defragmentation user or L3 master domain.",
    )
    return {
        "namespace": copy.deepcopy(namespace),
        "user": user,
        "vif": vif,
        "source": packet["source"],
        "destination": packet["destination"],
        "protocol": packet["protocol"],
        "identification": packet["ipId"],
    }


class FragmentReplay:
    """Keep closed queues as historical state; only explicit fresh lifetimes reopen."""

    def __init__(self):
        self.domains = {}
        self.sources = {}
        self.piece_sources = {}
        self.seen_arrivals = set()

    def open(self, namespace):
        key = namespace_ref(namespace)
        require(key not in self.domains, "A closed namespace lifetime cannot be reopened.")
        require(
            not any(old[0] == key[0] and value["live"] for old, value in self.domains.items()),
            "Two live namespace lifetimes alias the same actual namespace inode.",
        )
        self.domains[key] = {
            "live": True,
            "oracle": ReassemblyOracle(user_base=0),
            "lastArrivalNs": namespace["birth"],
        }

    def close(self, namespace):
        key = namespace_ref(namespace)
        require(
            key in self.domains and self.domains[key]["live"], "No live namespace can be retired."
        )
        self.domains[key]["live"] = False

    def arrive(self, piece, *, user=2, vif=0, timeout=30_000_000_000):
        require(
            type(timeout) is int and timeout > 0,
            "Fragment queue timeout must be a positive integer.",
        )
        require(
            set(piece) == {"id", "raw", "timeNs", "ingress", "earlyAllowed", "authenticationPrefix"}
            and isinstance(piece["id"], str)
            and piece["id"] not in self.seen_arrivals
            and type(piece["timeNs"]) is int
            and piece["timeNs"] >= 0
            and type(piece["earlyAllowed"]) is bool
            and type(piece["authenticationPrefix"]) is int
            and piece["authenticationPrefix"] >= 0,
            "Malformed, reused, or untagged actual fragment arrival.",
        )
        ingress = interface_ref(piece["ingress"])
        key = namespace_ref(ingress["ns"])
        require(
            key in self.domains and self.domains[key]["live"],
            "A packet operation targets an archived namespace.",
        )
        require(
            piece["timeNs"] >= ingress["birth"]
            and piece["timeNs"] >= self.domains[key]["lastArrivalNs"],
            "Fragment arrival precedes its interface birth or reverses observed time.",
        )
        packet = decode_ipv4(piece["raw"])
        domain = fragment_key(packet, ingress["ns"], user, vif)
        self.seen_arrivals.add(piece["id"])
        self.sources[piece["id"]] = copy.deepcopy(piece)
        self.domains[key]["lastArrivalNs"] = piece["timeNs"]
        if not piece["earlyAllowed"]:
            return {
                "status": "earlyDrop",
                "domain": domain,
                "output": None,
                "contributors": [],
                "completingIngress": None,
            }
        oracle = self.domains[key]["oracle"]
        queue_key = (
            user,
            vif,
            int(ipaddress.IPv4Address(packet["source"])),
            int(ipaddress.IPv4Address(packet["destination"])),
            packet["protocol"],
            packet["ipId"],
        )
        previous = oracle.queues.get(queue_key)
        result = oracle.arrive(piece["raw"], piece["timeNs"], zone=user, vif=vif, timeout=timeout)
        queue = oracle.queues.get(queue_key) if result.output is None else previous
        if queue is not None:
            for fragment in queue.pieces:
                self.piece_sources.setdefault(id(fragment.ip), (fragment.ip, piece["id"]))
        contributors = []
        if result.output is not None:
            if result.status == "whole":
                contributors = [
                    {
                        "arrival": piece["id"],
                        "start": 0,
                        "end": len(bytes.fromhex(packet["payloadHex"])),
                    }
                ]
            else:
                require(
                    queue is not None, "A completed fragmented family has no actual earlier queue."
                )
                contributors = [
                    {
                        "arrival": self.piece_sources[id(fragment.ip)][1],
                        "start": fragment.start,
                        "end": fragment.end,
                    }
                    for fragment in queue.pieces
                ]
            require(
                all(self.sources[item["arrival"]]["earlyAllowed"] for item in contributors),
                "An early-rejected piece contributes to an emitted datagram.",
            )
        return {
            "status": result.status,
            "domain": domain,
            "output": result.packet.hex() if result.packet else None,
            "contributors": contributors,
            "completingIngress": copy.deepcopy(ingress) if result.output is not None else None,
        }

    def queues(self, namespace):
        key = namespace_ref(namespace)
        require(key in self.domains, "Unknown namespace reassembly history.")
        return copy.deepcopy(self.domains[key]["oracle"].queues)
