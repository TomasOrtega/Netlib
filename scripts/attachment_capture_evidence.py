"""Retain interface identity and pre-conntrack attachment decisions from raw evidence."""

import hashlib
import json
import re
import struct
from collections import Counter
from pathlib import Path

import capture_conntrack as conntrack
import check_eap_capture as eap
import check_replication_capture as replication
from campus_capture_evidence import CAMPUS_TASK, CampusEvidence, _authentication_setup_commands
from capture_evidence import (
    SAFE_BASE,
    SAFE_TC,
    _digests,
    _endpoint_nflog,
    _nflog_ready,
    _offload,
    _ReplicationAdapter,
    _safe_setup_commands,
    checked_window,
)

EvidenceError, require = replication.EvidenceError, replication.require
INT_MAX = 2**31 - 1
PROC_TICK_NS = 10_000_000


def attachment_setup_commands():
    setup, _ = _safe_setup_commands()
    setup = [row for row in setup if "conntrackd" not in row]
    actor = "attacker"
    prefix = ["ip", "netns", "exec", actor]
    setup.extend([["ip", "netns", "add", actor], prefix + ["ip", "link", "set", "lo", "up"]])
    for key, value in (
        ("net.ipv6.conf.all.disable_ipv6", 1),
        ("net.ipv6.conf.default.disable_ipv6", 1),
        ("net.ipv4.conf.all.rp_filter", 0),
        ("net.ipv4.conf.default.rp_filter", 0),
        ("net.ipv4.ip_forward", 0),
    ):
        setup.append(
            prefix + ["sh", "-c", f"echo {value} > /tmp/netlib-proc/sys/{key.replace('.', '/')}"]
        )
    for left, right in (("aal", "aar"), ("abl", "abr")):
        setup.append(["ip", "link", "add", left, "type", "veth", "peer", "name", right])
        for name in (left, right):
            actor = INTERFACES[name]
            address, mac = LINKS[actor][name]
            peer = OPPOSITE[name]
            peer_address, peer_mac = LINKS[INTERFACES[peer]][peer]
            prefix = ["ip", "netns", "exec", actor]
            setup.extend(
                [
                    ["ip", "link", "set", name, "netns", actor],
                    prefix + ["ip", "link", "set", name, "address", mac],
                    prefix + ["ip", "address", "add", address + "/30", "dev", name],
                    prefix + ["ip", "link", "set", name, "mtu", "1500", "up"],
                    prefix + ["python3", "/task/wire/exercise.py", "offload", name],
                    prefix
                    + [
                        "ip",
                        "neigh",
                        "replace",
                        peer_address,
                        "lladdr",
                        peer_mac,
                        "nud",
                        "permanent",
                        "dev",
                        name,
                    ],
                ]
            )
    setup.extend(
        [
            "ip",
            "netns",
            "exec",
            actor,
            "sh",
            "-c",
            "echo 1 > /tmp/netlib-proc/sys/net/netfilter/nf_conntrack_acct",
        ]
        for actor in GATEWAYS
    )
    setup.extend(_authentication_setup_commands())
    return setup, [["ip", "netns", "exec", "b", "conntrackd", "-C", f"{SAFE_BASE}/b.conf", "-k"]]


def ifindex(value):
    require(type(value) is int and 0 < value <= INT_MAX, "Invalid live input-interface index.")
    return value


def namespace_inode(value):
    require(
        isinstance(value, str) and re.fullmatch(r"net:\[[1-9][0-9]*\]", value),
        "Missing actual network namespace inode.",
    )
    return int(value[5:-1])


def resolve_iif(expression, links):
    require(set(expression) == {"match"}, "Expected a numeric input-interface predicate.")
    match = expression["match"]
    require(
        set(match) == {"op", "left", "right"}
        and match["op"] == "=="
        and match["left"] == {"meta": {"key": "iif"}},
        "Attachment guards require meta iif, not a name-based predicate.",
    )
    require(isinstance(links, list) and links, "Missing contemporaneous same-namespace links.")
    indices = [ifindex(row["ifindex"]) for row in links]
    names = [row["ifname"] for row in links]
    require(
        all(isinstance(name, str) and name for name in names)
        and len(indices) == len(set(indices))
        and len(names) == len(set(names)),
        "Ambiguous native input-interface inventory.",
    )
    value = match["right"]
    if type(value) is int:
        index = ifindex(value)
        require(index in indices, "Installed numeric input interface is no longer live.")
        return index
    require(
        isinstance(value, str) and value in names,
        "Exported input-interface name has no contemporaneous native index.",
    )
    return indices[names.index(value)]


def accounting(raw):
    data = bytes.fromhex(raw)
    require(len(data) >= 20, "Truncated accounted conntrack record.")
    try:
        attributes = conntrack.attributes(data[20:])
        result = {}
        for key, name in ((9, "original"), (10, "reply")):
            children = conntrack.nested(attributes, key, f"{name} accounting")
            require(
                all(
                    item.kind in (1, 2, 5)
                    and item.children is None
                    and item.flags == 0
                    and (item.kind != 5 or item.payload == b"")
                    for item in children
                ),
                "Unsupported conntrack accounting attributes.",
            )
            result[name] = {
                "packets": conntrack.scalar(children, 1, f"{name} packet count", 8, required=True),
                "bytes": conntrack.scalar(children, 2, f"{name} byte count", 8, required=True),
            }
        return result
    except conntrack.CaptureError as error:
        raise EvidenceError(str(error)) from error


def decode_snapshot(document):
    require(
        set(document) == {"schema", "family", "entries", "messages", "request"}
        and type(document["schema"]) is int
        and document["schema"] == 1
        and type(document["family"]) is int
        and document["family"] == 2,
        "Malformed accounted conntrack dump envelope.",
    )
    request = bytes.fromhex(document["request"])
    require(len(request) == 20, "Malformed accounted conntrack request.")
    size, kind, flags, sequence, port = struct.unpack_from("=IHHII", request)
    require(
        (size, kind, flags) == (20, 0x101, 0x301) and request[16:] == bytes((2, 0, 0, 0)),
        "Accounted dump has filtering or a different native request.",
    )
    try:
        decoder = conntrack.Dump(sequence, port)
        for text in document["messages"]:
            raw = bytes.fromhex(text)
            require(
                len(raw) >= 20 and int.from_bytes(raw[:4], "little") == len(raw),
                "Accounted dump has a truncated message envelope.",
            )
            message, message_flags = struct.unpack_from("=HH", raw, 4)
            require(
                (message == 0x100 and message_flags in (2, 0x22))
                or (message == 3 and message_flags == 2 and raw[16:] == bytes(4)),
                "Accounted dump has an interrupted or unsupported completion.",
            )
            decoder.feed(raw)
        require(decoder.finish() == document, "Accounted raw and structured dump records disagree.")
    except conntrack.CaptureError as error:
        raise EvidenceError(str(error)) from error
    for record in decoder.entries:
        accounting(record["raw"])
    return decoder.entries


def countdown_compatible(before, after, before_command, after_command):
    require(
        type(before) is int and type(after) is int and 0 < after <= before,
        "Rejected ingress changed or increased a selected native timeout.",
    )
    replication.interval(before_command)
    replication.interval(after_command, before_command["endNs"])
    second = 1_000_000_000
    earlier = (
        before_command["startNs"] + before * second,
        before_command["endNs"] + (before + 1) * second,
    )
    later = (
        after_command["startNs"] + after * second,
        after_command["endNs"] + (after + 1) * second,
    )
    require(
        max(earlier[0], later[0]) <= min(earlier[1], later[1]),
        "Rejected ingress contradicts countdown of the same selected expiry.",
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
        "Unexpected attachment NFLOG envelope.",
    )
    fields = replication.reassembly.netlink_attributes(raw[20:])
    require(10 in fields and fields[10].endswith(b"\0"), "Missing NFLOG prefix.")
    prefix = fields[10][:-1].decode("ascii")
    require(
        prefix in ("INGRESS", "ATTACH_ALLOW", "ATTACH_DROP", "TRACKED", "EGRESS"),
        "Unexpected attachment NFLOG prefix.",
    )
    expected = {1, 4, 8, 9, 10, 12, 13, 15, 16, 17} | ({5} if prefix == "EGRESS" else {3})
    require(set(fields) in (expected, expected | {2}), "Missing or extra attachment NFLOG fields.")
    require(
        fields[1] == bytes((8, 0, 4 if prefix == "EGRESS" else 0, 0))
        and fields[15] == b"\0\1"
        and fields[17] == b"\0\x0e"
        and len(fields[16]) == 14
        and fields[16][12:] == b"\x08\0",
        "Attachment hook or hardware metadata disagrees.",
    )
    require(
        len(fields[8]) == 12
        and fields[8][:4] == bytes.fromhex("00060000")
        and fields[8][4:10] == fields[16][6:12]
        and fields[8][10:] == bytes(2),
        "Attachment source MAC disagrees with its retained Ethernet header.",
    )
    for key in (4, 5, 12, 13, 2):
        require(key not in fields or len(fields[key]) == 4, "Malformed attachment NFLOG scalar.")
    require(2 not in fields or fields[2] == bytes(4), "Unexpected attachment packet mark.")
    if 3 in fields:
        require(len(fields[3]) == 16, "Malformed attachment NFLOG kernel timestamp.")
    packet = replication.wire.decode_frame((fields[16] + fields[9]).hex())
    require(
        packet["paddingHex"] == "" and packet["udpChecksum"]["status"] == "valid",
        "Require complete unchanged UDP bytes at the attachment hook.",
    )
    return {
        "source": f"{actor}-nflog.jsonl:{number}",
        "actor": actor,
        "timeNs": replication.integer(row["timeNs"]),
        "prefix": prefix,
        "inputIndex": ifindex(int.from_bytes(fields[4], "big")),
        "outputIndex": ifindex(int.from_bytes(fields[5], "big")) if 5 in fields else None,
        "localSequence": int.from_bytes(fields[12], "big"),
        "globalSequence": int.from_bytes(fields[13], "big"),
        "hardwareHex": fields[16].hex(),
        "sourceMAC": fields[8][4:10].hex(":"),
        "packet": packet,
    }


def decode_adversary_af(row, actor, number, indices, links, opposite, withdrawn_commands):
    require(
        row.get("namespace") == actor and row.get("interface") in links[actor],
        "Attachment AF observer actor or interface disagrees.",
    )
    name = row["interface"]
    if "socketError" in row:
        require(
            actor == "a"
            and name in withdrawn_commands
            and set(row) == {"namespace", "interface", "timeNs", "socketError"}
            and type(row["socketError"]) is int
            and row["socketError"] == 100
            and withdrawn_commands[name]["startNs"] <= row["timeNs"],
            "Attachment socket failed before its actual interface withdrawal.",
        )
        return {"error": True, "interface": name, "timeNs": replication.integer(row["timeNs"])}
    require(
        set(row) == {"namespace", "interface", "ifindex", "timeNs", "packetType", "hex"}
        and ifindex(row["ifindex"]) == indices[actor][name]
        and type(row["packetType"]) is int,
        "Attachment AF metadata contradicts the actual observer binding.",
    )
    require(actor == "attacker" or name in ("aar", "abr"), "Expected a selected adversary link.")
    require(
        row["packetType"] == (4 if actor == "attacker" else 0),
        "Adversary Ethernet direction disagrees.",
    )
    packet = replication.wire.decode_frame(row["hex"])
    require(
        packet["udpChecksum"]["status"] == "valid"
        and packet["paddingHex"] == ""
        and packet["header"] in (replication.ORIGINAL, replication.WIRE_REPLY)
        and packet["ttl"] == 64,
        "Adversary input is not a complete selected pre-NAT UDP datagram.",
    )
    gateway = ("a" if name == "aal" else "b") if actor == "attacker" else actor
    ingress = "aar" if gateway == "a" else "abr"
    original = packet["header"] == replication.ORIGINAL
    claimed_actor = "client" if original else "server"
    claimed_interface = (
        ("cal" if gateway == "a" else "cbl") if original else ("sal" if gateway == "a" else "sbl")
    )
    frame = bytes.fromhex(row["hex"])
    require(
        frame[6:12].hex(":") == replication.LINKS[claimed_actor][claimed_interface][1]
        and frame[:6].hex(":") == links[gateway][ingress][1]
        and opposite[name]
        == (ingress if actor == "attacker" else "aal" if gateway == "a" else "abl"),
        "Adversary did not actually copy the authorized tuple and source MAC on the distinct input port.",
    )
    return {
        **packet,
        **row,
        "source": f"{actor}-frames.jsonl:{number}",
        "sync": False,
        "adversary": True,
        "gateway": gateway,
        "leg": "original" if original else "reply",
    }


ATTACHMENT_TASK = "/task/attachments/exercise.py"
PROFILE = "campus-ingress-attachments"
ACTORS = (*replication.ACTORS, "attacker")
GATEWAYS = replication.GATEWAYS
LINKS = {actor: dict(links) for actor, links in replication.LINKS.items()}
LINKS["a"]["aar"] = ("172.20.0.1", "02:00:00:20:00:01")
LINKS["b"]["abr"] = ("172.20.1.1", "02:00:00:20:01:01")
LINKS["attacker"] = {
    "aal": ("172.20.0.2", "02:00:00:20:00:00"),
    "abl": ("172.20.1.2", "02:00:00:20:01:00"),
}
OPPOSITE = {**replication.OPPOSITE, "aal": "aar", "aar": "aal", "abl": "abr", "abr": "abl"}
INTERFACES = {name: actor for actor, links in LINKS.items() for name in links}
ARCHIVE = "withdraw-primary:before"
ROOT = Path(__file__).resolve().parents[1]


class AttachmentEvidence(CampusEvidence):
    def __init__(self, directory):
        self.directory = directory
        self.manifest = replication.nat.read_json(directory / "capture.json")
        self.commands = replication.nat.read_json(directory / "commands.json")
        self.polls = replication.nat.read_json(directory / "admission-polls.json")
        manifest = self.manifest
        require(
            type(manifest["schema"]) is int
            and manifest["schema"] == 1
            and manifest["profile"] == PROFILE
            and manifest["byteorder"] == "little"
            and manifest["admissionPolls"] == "admission-polls.json",
            "Unsupported campus producer profile.",
        )
        replication.interval(manifest)
        previous = manifest["startNs"]
        for command in self.commands:
            require(
                set(command) == {"arguments", "startNs", "endNs", "returncode", "stdout", "stderr"}
                and type(command["returncode"]) is int
                and command["returncode"] == 0
                and (
                    not command["stderr"]
                    or command["arguments"]
                    in (
                        ["ip", "netns", "exec", "a", "conntrack", "-F"],
                        ["ip", "netns", "exec", "b", "conntrack", "-F"],
                    )
                    and command["stderr"]
                    == "conntrack v1.4.9 (conntrack-tools): connection tracking table has been emptied.\n"
                )
                and isinstance(command["arguments"], list)
                and all(isinstance(value, str) for value in command["arguments"]),
                "Native command failed or has unsupported fields.",
            )
            _, previous = replication.interval(command, previous, manifest["endNs"])
        self.events = {event["id"]: event for event in manifest["events"]}
        require(
            len(self.events) == len(manifest["events"]) and self.events,
            "Duplicate or missing native event identity.",
        )
        previous = manifest["startNs"]
        self.operations = {}
        for event in manifest["events"]:
            _, previous = replication.interval(event, previous, manifest["endNs"])
            indices = event["commands"]
            require(
                isinstance(indices, list)
                and all(type(index) is int and 0 <= index < len(self.commands) for index in indices)
                and (not indices or indices == list(range(indices[0], indices[-1] + 1))),
                "Invalid event command inventory.",
            )
            if event["type"] in ("packet", "admit", "serve"):
                require(not indices, "Socket event contains unmodeled commands.")
                result = event["result"]
                start = (
                    result["sender"]["startNs"]
                    if "sender" in result
                    else result["receiver"]["startNs"]
                )
                end = (
                    result["receiver"]["endNs"]
                    if "receiver" in result
                    else self.polls[result["admission"]["poll"]]["endNs"]
                )
                for key in ("sender", "receiver"):
                    if key in result:
                        replication.interval(result[key], event["startNs"], event["endNs"])
                        replication.interval(
                            result[key]["response"], result[key]["startNs"], result[key]["endNs"]
                        )
                if event["type"] == "packet":
                    require(
                        result["sender"]["endNs"] < result["receiver"]["startNs"],
                        "Atomic packet receive precedes actual send completion.",
                    )
            elif event["type"] == "serve-pair":
                require(
                    not indices
                    and set(event["result"]) == {"receivers"}
                    and set(event["result"]["receivers"]) == {"original", "reply"},
                    "Joint service must retain both actual receive operations.",
                )
                receivers = event["result"]["receivers"].values()
                for receiver in receivers:
                    replication.interval(receiver, event["startNs"], event["endNs"])
                    replication.interval(
                        receiver["response"], receiver["startNs"], receiver["endNs"]
                    )
                start = min(value["startNs"] for value in receivers)
                end = max(value["endNs"] for value in receivers)
            else:
                require(indices, "Control event has no command evidence.")
                start, end = (
                    self.commands[indices[0]]["startNs"],
                    self.commands[indices[-1]]["endNs"],
                )
                if event["type"] == "attack":
                    receiver = event["result"]["receiver"]
                    replication.interval(receiver, event["startNs"], event["endNs"])
                    replication.interval(
                        receiver["response"], receiver["startNs"], receiver["endNs"]
                    )
                    end = max(end, receiver["endNs"])
                if event["type"] == "authentication":
                    result = event["result"]
                    replication.interval(result, event["startNs"], event["endNs"])
                    require(
                        result["startNs"] <= start < end <= result["endNs"],
                        "Authentication commands escape their actual operation receipt.",
                    )
                    start, end = result["startNs"], result["endNs"]
            checked_window(start, end, (event["startNs"], event["endNs"]))
            self.operations[event["id"]] = {
                "startNs": start,
                "endNs": end,
                "native": event,
                "commands": [self.commands[index] for index in indices],
            }
        self.boundaries = {"initial": manifest["initial"], "final": manifest["final"]}
        self.boundaries.update(
            {
                event["id"] + ":" + side: event[side]
                for event in manifest["events"]
                for side in ("before", "after")
            }
        )
        self.packets = {}
        for event in manifest["events"]:
            if event["type"] in ("packet", "admit"):
                key = event.get("ticket", "establish")
                require(key == "establish" or type(key) is int, "Invalid native ticket identity.")
                require(key not in self.packets, "Duplicate admission ticket identity.")
                self.packets[key] = {
                    "admit": event,
                    "serve": event if event["type"] == "packet" else None,
                }
        for event in manifest["events"]:
            if event["type"] == "serve":
                require(
                    type(event["ticket"]) is int
                    and event["ticket"] in self.packets
                    and self.packets[event["ticket"]]["serve"] is None,
                    "Serve event has no unique pending admission.",
                )
                self.packets[event["ticket"]]["serve"] = event
        for event in manifest["events"]:
            if event["type"] == "serve-pair":
                require(
                    event["tickets"] == [5, 6],
                    "Joint service changed the actual pending identities.",
                )
                for ticket, direction in ((5, "original"), (6, "reply")):
                    require(
                        ticket in self.packets and self.packets[ticket]["serve"] is None,
                        "Joint service has no unique earlier pending admission.",
                    )
                    self.packets[ticket]["serve"] = event
                    self.packets[ticket]["receiver"] = event["result"]["receivers"][direction]
        self.attacks = {
            event["id"]: event for event in manifest["events"] if event["type"] == "attack"
        }
        self.attack_reports = {}
        require(
            all(value["serve"] for value in self.packets.values()),
            "Admission has no observed service outcome.",
        )
        self.used_commands, self.used_sources, self.used_polls = set(), set(), set()
        self.used_artifacts = set()
        self.read_boundaries, self.packet_reports = {}, {}
        self._open_namespace_lifetimes()
        self._open_observers()
        self._open_packets()

    def _open_namespace_lifetimes(self):
        lifetimes = self.manifest["namespaceLifetimes"]
        require(
            set(lifetimes) == {*ACTORS, "auth"},
            "Missing namespace creation or interface lifetimes.",
        )
        self.namespace_refs, self.interface_refs, self.birth_identities = {}, {}, {}
        initial_start = min(
            self.commands[ref["command"]]["startNs"]
            for ref in _ReplicationAdapter._references(self.manifest["initial"])
        )
        for actor, lifetime in lifetimes.items():
            require(
                set(lifetime) == {"creationCommand", "identity", "interfaces"},
                "Unsupported namespace lifetime declaration.",
            )
            index = lifetime["creationCommand"]
            require(
                type(index) is int and 0 <= index < len(self.commands),
                "Invalid namespace creation reference.",
            )
            created = self.commands[index]
            require(
                created["arguments"] == ["ip", "netns", "add", actor]
                and created["endNs"] < initial_start,
                "Namespace birth is not its actual setup operation.",
            )
            reference = lifetime["identity"]
            identity = self._export(
                reference,
                actor,
                ["python3", ATTACHMENT_TASK, "identity"],
                (created["endNs"], initial_start),
                filename=f"birth-{actor}-identity.json",
            )
            self._identity(identity, self.commands[reference["command"]])
            namespace = {"id": namespace_inode(identity["namespace"]), "birth": created["endNs"]}
            self.namespace_refs[actor] = namespace
            self.birth_identities[actor] = identity
            ports = {
                row["name"]: row["ifindex"] for row in identity["interfaces"] if row["name"] != "lo"
            }
            require(
                set(lifetime["interfaces"]) == set(ports),
                "Interface lifetime inventory is incomplete.",
            )
            self.interface_refs[actor] = {}
            for name, source in lifetime["interfaces"].items():
                require(
                    set(source) == {"ifindex", "creationCommand", "moveCommand", "upCommand"}
                    and ifindex(source["ifindex"]) == ports[name],
                    "Interface birth changed its current numeric index.",
                )
                for key in ("creationCommand", "moveCommand", "upCommand"):
                    require(
                        type(source[key]) is int and 0 <= source[key] < reference["command"],
                        "Interface lifetime source is not an earlier actual command.",
                    )
                creation, movement, up = (
                    self.commands[source[key]]
                    for key in ("creationCommand", "moveCommand", "upCommand")
                )
                arguments = creation["arguments"]
                require(
                    arguments[:3] == ["ip", "link", "add"]
                    and (
                        arguments[3] == name
                        or any(
                            arguments[i : i + 2] == ["name", name]
                            for i in range(len(arguments) - 1)
                        )
                    )
                    and creation["endNs"] < movement["startNs"]
                    and movement["arguments"] == ["ip", "link", "set", name, "netns", actor]
                    and movement["endNs"] < up["startNs"]
                    and up["arguments"][:8]
                    == ["ip", "netns", "exec", actor, "ip", "link", "set", name]
                    and "up" in up["arguments"][8:]
                    and up["endNs"] < self.commands[reference["command"]]["startNs"],
                    "Interface creation, namespace move, or activation source disagrees.",
                )
                self.interface_refs[actor][name] = {
                    "ns": namespace,
                    "ifindex": ports[name],
                    "birth": movement["endNs"],
                }
        require(
            len({ref["id"] for ref in self.namespace_refs.values()}) == len(lifetimes),
            "Distinct live namespace lifetimes alias the same inode.",
        )

    @staticmethod
    def _identity(value, command):
        require(
            set(value) == {"namespace", "observedNs", "pid", "interfaces"}
            and type(value["pid"]) is int
            and value["pid"] > 0
            and command["startNs"] <= value["observedNs"] < command["endNs"],
            "Native namespace identity escapes its actual read receipt.",
        )
        namespace_inode(value["namespace"])
        rows = value["interfaces"]
        require(
            isinstance(rows, list)
            and rows
            and all(
                set(row) == {"ifindex", "name"} and isinstance(row["name"], str) and row["name"]
                for row in rows
            ),
            "Malformed native interface identity inventory.",
        )
        indices = [ifindex(row["ifindex"]) for row in rows]
        require(
            len(indices) == len(set(indices)) and len(rows) == len({row["name"] for row in rows}),
            "Native interface names or indices are ambiguous.",
        )

    def _open_observers(self):
        manifest = self.manifest
        observers = manifest["observers"]
        self.observers = {(row["actor"], row["kind"]): row for row in observers}
        required = {(actor, kind) for actor in ACTORS for kind in ("packet", "nflog")} | {
            (actor, "trace") for actor in GATEWAYS
        }
        require(
            len(observers) == len(self.observers) == len(required)
            and set(self.observers) == required,
            "Missing or duplicate raw observer.",
        )
        first, last = manifest["events"][0]["startNs"], manifest["events"][-1]["endNs"]
        self.indices = {}
        for (actor, kind), observer in self.observers.items():
            require(
                observer["runningBeforeStop"] is True
                and observer["stopSignal"] == 15
                and type(observer["returncode"]) is int
                and observer["returncode"] == (-15 if kind == "trace" else 0)
                and last < observer["stopNs"] < observer["endNs"] <= manifest["endNs"],
                "Raw observer exited early or failed.",
            )
            prefix = ["ip", "netns", "exec", actor]
            if kind == "packet":
                ready = observer["ready"]
                require(
                    observer["file"] == f"{actor}-frames.jsonl"
                    and ready["namespace"] == actor
                    and [row["interface"] for row in ready["interfaces"]] == list(LINKS[actor])
                    and all(row["receiveBuffer"] >= 131072 for row in ready["interfaces"]),
                    "Packet observer binding or buffer size disagrees.",
                )
                self.indices[actor] = {
                    row["interface"]: replication.integer(row["ifindex"], 2**32)
                    for row in ready["interfaces"]
                }
                expected = prefix + [
                    "python3",
                    ATTACHMENT_TASK,
                    "sniff",
                    f"{SAFE_BASE}/{observer['file']}",
                    actor,
                    *LINKS[actor],
                ]
            elif kind == "nflog":
                ready = observer["ready"]
                group = 42 if actor in GATEWAYS else 43
                _nflog_ready(ready, group)
                require(observer["file"] == f"{actor}-nflog.jsonl", "NFLOG file is misbound.")
                expected = prefix + [
                    "python3",
                    ATTACHMENT_TASK,
                    "nflog",
                    f"{SAFE_BASE}/{observer['file']}",
                    str(group),
                ]
            else:
                require(
                    observer["file"] == f"{actor}-trace.txt"
                    and observer["errors"] == f"{actor}-trace-errors.txt"
                    and not (self.directory / observer["errors"]).read_text(),
                    "Trace monitor reported errors.",
                )
                ready = {"readyNs": observer["startNs"]}
                expected = prefix + ["nft", "monitor", "trace"]
            if kind in ("packet", "nflog"):
                identity = observer["identity"]
                self._identity(
                    identity,
                    {
                        "startNs": self.commands[
                            self.manifest["namespaceLifetimes"][actor]["identity"]["command"]
                        ]["endNs"],
                        "endNs": ready["readyNs"],
                    },
                )
                require(
                    namespace_inode(identity["namespace"]) == self.namespace_refs[actor]["id"]
                    and identity["interfaces"] == self.birth_identities[actor]["interfaces"],
                    "Raw observer belongs to a different namespace or interface lifetime.",
                )
            require(
                observer["command"] == expected and manifest["startNs"] < ready["readyNs"] < first,
                "Observer command or startup time disagrees.",
            )
        require(
            manifest["interfaces"] == {actor: list(links) for actor, links in LINKS.items()},
            "Native topology interface inventory disagrees.",
        )

    def boundary(self, name, window=None):
        require(name in self.boundaries, "Unknown campus boundary reference.")
        native = self.boundaries[name]
        label = name.replace(":", "-")
        if name == "initial":
            lower, upper = self.manifest["startNs"], self.manifest["events"][0]["startNs"]
        elif name == "final":
            lower, upper = self.manifest["events"][-1]["endNs"], self.manifest["endNs"]
        else:
            event_name, side = name.split(":")
            event = self.events[event_name]
            operation = self.operations[event_name]
            lower, upper = (
                (event["startNs"], operation["startNs"])
                if side == "before"
                else (operation["endNs"], event["endNs"])
            )
        retired = name == "final" or (
            name != "initial" and lower >= self.operations["withdraw-primary"]["endNs"]
        )
        require(
            set(native)
            == {"conntrack", "tables", "networks", "qdiscs", "endpointTables", "identities"}
            | ({"archivedA"} if retired else set()),
            "Incomplete campus boundary inventory.",
        )
        gateways = {"b"} if retired else set(GATEWAYS)
        actors = set(ACTORS) - ({"a"} if retired else set())
        require(
            set(native["conntrack"]) == set(native["tables"]) == gateways
            and set(native["networks"]) == actors,
            "Live and archived gateway observations were mixed.",
        )
        if retired:
            require(native["archivedA"] == {"boundary": ARCHIVE}, "Wrong primary archive prefix.")
            require(ARCHIVE in self.read_boundaries, "Read the actual primary archive first.")
        result = {
            "id": name,
            "native": native,
            "conntrack": {},
            "tables": {},
            "networks": {},
            "qdiscs": {},
            "endpointTables": {},
            "identities": {},
            "accounting": {},
            "archivedA": {"boundary": ARCHIVE} if retired else None,
        }
        before_commands = set(self.used_commands)
        for actor in sorted(gateways):
            reference = native["conntrack"][actor]
            self._artifact(reference, f"{label}-{actor}-conntrack.json")
            command = self._command(
                reference["command"],
                [
                    "ip",
                    "netns",
                    "exec",
                    actor,
                    "python3",
                    "/task/capture_conntrack.py",
                    "--output",
                    f"{SAFE_BASE}/{reference['file']}",
                ],
                (lower, upper),
            )
            require(not command["stdout"], "Conntrack producer has unexpected stdout.")
            document = replication.nat.read_json(self.directory / reference["file"])
            require(
                type(document["schema"]) is int and type(document["family"]) is int,
                "Invalid conntrack numeric envelope.",
            )
            result["conntrack"][actor] = decode_snapshot(document)
            result["accounting"][actor] = [
                accounting(row["raw"]) for row in result["conntrack"][actor]
            ]
            result["tables"][actor] = self._export(
                native["tables"][actor],
                actor,
                ["nft", "-j", "-a", "list", "ruleset"],
                (lower, upper),
                filename=f"{label}-{actor}-nftables.json",
            )
        arguments = {
            "links": ["link", "show"],
            "addresses": ["address", "show"],
            "routes": ["-4", "route", "show", "table", "main"],
            "neighbors": ["neigh", "show"],
            "rules": ["-4", "rule", "show"],
        }
        require(set(native["identities"]) == actors, "Missing live namespace identity readbacks.")
        for actor, reference in native["identities"].items():
            identity = self._export(
                reference,
                actor,
                ["python3", ATTACHMENT_TASK, "identity"],
                (lower, upper),
                filename=f"{label}-{actor}-identity.json",
            )
            self._identity(identity, self.commands[reference["command"]])
            require(
                namespace_inode(identity["namespace"]) == self.namespace_refs[actor]["id"]
                and identity["interfaces"] == self.birth_identities[actor]["interfaces"],
                "A namespace or interface instance changed during the protected history.",
            )
            result["identities"][actor] = identity
        for actor, refs in native["networks"].items():
            require(set(refs) == set(arguments), "Missing namespace network readback.")
            result["networks"][actor] = {
                kind: self._export(
                    reference,
                    actor,
                    ["ip", "-j", *arguments[kind]],
                    (lower, upper),
                    filename=f"{label}-{actor}-{kind}.json",
                )
                for kind, reference in refs.items()
            }
            for kind in ("links", "addresses"):
                for row in result["networks"][actor][kind]:
                    interface = row["ifname"]
                    if actor == "client" and interface == "peer0":
                        continue
                    expected = 1 if interface == "lo" else self.indices[actor].get(interface)
                    require(
                        type(row["ifindex"]) is int and row["ifindex"] == expected,
                        "Native interface index contradicts its observer binding.",
                    )
                    if interface != "lo":
                        peer = OPPOSITE[interface]
                        require(
                            type(row["link_index"]) is int
                            and row["link_index"] == self.indices[INTERFACES[peer]][peer],
                            "Native interface peer index contradicts the observed topology.",
                        )
        require(
            set(native["qdiscs"]) == {"cal", "cbl", "sbl"}
            and set(native["endpointTables"]) == {"client", "server"},
            "Missing endpoint queue or policy readback.",
        )
        for interface, reference in native["qdiscs"].items():
            result["qdiscs"][interface] = self._export(
                reference,
                "server" if interface == "sbl" else "client",
                [SAFE_TC, "-j", "-s", "-d", "qdisc", "show", "dev", interface],
                (lower, upper),
                filename=f"{label}-{interface}-qdisc.json",
            )
        for actor, reference in native["endpointTables"].items():
            result["endpointTables"][actor] = self._export(
                reference,
                actor,
                ["nft", "-j", "-a", "list", "ruleset"],
                (lower, upper),
                filename=f"{label}-{actor}-nftables.json",
            )
        new_commands = self.used_commands - before_commands
        result.update(
            startNs=min(self.commands[i]["startNs"] for i in new_commands),
            endNs=max(self.commands[i]["endNs"] for i in new_commands),
        )
        checked_window(result["startNs"], result["endNs"], window)
        self.read_boundaries[name] = result
        if name.endswith(":before"):
            result["operation"] = self._operation(name.split(":")[0])
        return result

    def _open_packets(self):
        self.frames, self.sync, self.socket_errors, self.logs, self.raw_logs, self.traces = (
            [],
            [],
            [],
            {},
            {},
            {},
        )
        fence = self.events["fence-primary"]
        fence_commands = {
            name: self.commands[index]
            for name, index in zip(("car", "sar"), fence["commands"], strict=True)
        }
        withdraw = self.events["withdraw-primary"]
        withdrawn_commands = dict(fence_commands)
        for index in withdraw["commands"]:
            command = self.commands[index]
            if (
                command["arguments"][:7] == ["ip", "netns", "exec", "a", "ip", "link", "set"]
                and command["arguments"][-1] == "down"
            ):
                name = command["arguments"][7]
                require(
                    name in ("syncl", "aar") and name not in withdrawn_commands,
                    "Withdrawal repeats or changes an interface disable.",
                )
                withdrawn_commands[name] = command
        require(
            set(withdrawn_commands) == {"car", "sar", "syncl", "aar"},
            "Withdrawal leaves a selected primary interface active.",
        )
        for actor in ACTORS:
            observer = self.observers[(actor, "packet")]
            previous = observer["ready"]["readyNs"]
            for number, row in enumerate(
                replication.read_lines(self.directory / observer["file"]), 1
            ):
                require(
                    previous < row["timeNs"] <= observer["endNs"],
                    "Packet observer records are out of order.",
                )
                previous = row["timeNs"]
                if (
                    "socketError" in row
                    or actor == "attacker"
                    or row["interface"] in ("aar", "abr")
                ):
                    decoded = decode_adversary_af(
                        row, actor, number, self.indices, LINKS, OPPOSITE, withdrawn_commands
                    )
                else:
                    decoded = replication.decode_af(
                        row, actor, number, self.indices, fence_commands
                    )
                require(decoded is not None, "Unexpected ARP in the permanent-neighbor profile.")
                if decoded.get("error"):
                    self.socket_errors.append((actor, decoded["interface"]))
                else:
                    require(
                        (actor, decoded["interface"]) not in self.socket_errors,
                        "Packet data appears after socket shutdown.",
                    )
                    (self.sync if decoded["sync"] else self.frames).append(decoded)
            observer = self.observers[(actor, "nflog")]
            self.raw_logs[actor] = replication.read_lines(self.directory / observer["file"])
            decode = decode_nflog if actor in GATEWAYS else _endpoint_nflog
            self.logs[actor] = [
                decode(row, actor, i) for i, row in enumerate(self.raw_logs[actor], 1)
            ]
            previous = observer["ready"]["readyNs"]
            for index, row in enumerate(self.logs[actor]):
                require(
                    previous < row["timeNs"] < observer["endNs"]
                    and row["localSequence"] == index
                    and row["globalSequence"] == index + 1,
                    "NFLOG sequence or timestamp completeness disagrees.",
                )
                previous = row["timeNs"]
            if actor in GATEWAYS:
                self.traces[actor] = replication.parse_traces(self.directory / f"{actor}-trace.txt")
        require(
            Counter(self.socket_errors)
            == Counter({("a", name): 1 for name in ("car", "sar", "syncl", "aar")}),
            "Missing or duplicate fence/withdrawal socket errors.",
        )

    def packet(self, ticket, window):
        require(ticket in self.packets, "Unknown packet reference.")
        selected = self.packets[ticket]
        admit, serve = selected["admit"], selected["serve"]
        checked_window(admit["startNs"], serve["endNs"], window)
        sender = admit["result"]["sender"]
        receiver = selected.get("receiver", serve["result"].get("receiver"))
        request, response = sender["request"], sender["response"]["result"]
        marker = request["payloadHex"]
        original = request.get("peer") == ["203.0.113.2", 8080]
        source_actor, destination_actor = ("client", "server") if original else ("server", "client")
        local = ["192.0.2.2", 41000] if original else ["198.51.100.2", 9000]
        expected_input, expected_output = (
            (replication.ORIGINAL, replication.WIRE)
            if original
            else (replication.WIRE_REPLY, replication.PEER_REPLY)
        )
        require(
            request
            == {
                "operation": "send",
                "peer": [expected_input["destination"], expected_input["destinationPort"]],
                "payloadHex": marker,
                "ttl": 64,
            }
            and response
            == {
                "bytesSent": len(bytes.fromhex(marker)),
                "payloadHex": marker,
                "local": local,
                "peer": request["peer"],
                "ttl": 64,
            },
            "Endpoint send request or result disagrees with supported UDP input.",
        )
        admission, poll = self._poll(admit, source_actor, marker, sender)
        if admit is serve:
            require(
                poll["endNs"] < receiver["startNs"],
                "Atomic packet receive precedes the actual admission read.",
            )
        packet = admission["packet"]
        require(
            packet["header"] == expected_input and packet["ttl"] == 64,
            "Earlier route admission tuple or TTL disagrees.",
        )
        interfaces = [
            name
            for name, index in self.indices[source_actor].items()
            if index == admission["outputIndex"]
        ]
        require(len(interfaces) == 1, "Route admission output ifindex is unknown.")
        endpoint_interface = interfaces[0]
        gateway = "a" if endpoint_interface in ("cal", "sal") else "b"
        ingress_interface = OPPOSITE[endpoint_interface]
        output_interface = (
            ("sar" if original else "car") if gateway == "a" else ("sbr" if original else "cbr")
        )
        require(
            (admit["gateway"], admit["leg"])
            == (serve["gateway"], admit["leg"] if serve["type"] == "serve-pair" else serve["leg"])
            == (gateway, "original" if original else "reply"),
            "Selected ticket gateway or leg contradicts actual route admission.",
        )
        frames = [row for row in self.frames if row["payloadHex"] == marker]
        gateway_inputs = [
            row for row in frames if row["namespace"] == gateway and row["packetType"] == 0
        ]
        gateway_outputs = [
            row for row in frames if row["namespace"] == gateway and row["packetType"] == 4
        ]
        require(
            len(gateway_inputs) == 1 and len(gateway_outputs) <= 1,
            "Missing or ambiguous actual gateway packet path.",
        )
        incoming = gateway_inputs[0]
        outgoing = gateway_outputs[0] if gateway_outputs else None
        require(
            len(frames) == (4 if outgoing else 2)
            and all(
                sender["response"]["startNs"] <= row["timeNs"] < serve["endNs"] for row in frames
            ),
            "Missing, additional, or mistimed selected AF observations.",
        )
        require(
            admit is serve or all(receiver["startNs"] <= row["timeNs"] for row in frames),
            "Held AF observation precedes its actual queue service interval.",
        )
        require(
            incoming["header"] == expected_input
            and incoming["interface"] == ingress_interface
            and bytes.fromhex(incoming["hex"])[14 : 14 + incoming["ipLength"]].hex()
            == packet["raw"],
            "Earlier route-admission bytes disagree with actual later gateway ingress.",
        )
        source_frames = [row for row in frames if row["namespace"] == source_actor]
        destination_frames = [row for row in frames if row["namespace"] == destination_actor]
        require(
            len(source_frames) == 1
            and source_frames[0]["packetType"] == 4
            and source_frames[0]["interface"] == endpoint_interface
            and source_frames[0]["hex"] == incoming["hex"]
            and len(destination_frames) == int(outgoing is not None),
            "Endpoint AF bytes or physical interface disagree with the selected gateway.",
        )
        if outgoing:
            require(
                outgoing["header"] == expected_output
                and outgoing["interface"] == output_interface
                and outgoing["ttl"] == 63
                and outgoing["ipId"] == incoming["ipId"]
                and outgoing["ipLength"] == incoming["ipLength"]
                and outgoing["udpLength"] == incoming["udpLength"]
                and outgoing["payloadHex"] == marker
                and destination_frames[0]["packetType"] == 0
                and destination_frames[0]["interface"] == OPPOSITE[output_interface]
                and destination_frames[0]["hex"] == outgoing["hex"],
                "Gateway output, endpoint delivery, or preserved datagram fields disagree.",
            )
            source_ip, output_ip = (
                bytes.fromhex(incoming["hex"])[14:34],
                bytes.fromhex(outgoing["hex"])[14:34],
            )
            require(
                source_ip[:8] == output_ip[:8] and source_ip[9] == output_ip[9],
                "Forwarding changed preserved IPv4 fields.",
            )
            expected_receive = {
                "payloadHex": marker,
                "peer": [expected_output["source"], expected_output["sourcePort"]],
                "local": [expected_output["destination"], expected_output["destinationPort"]],
            }
            require(
                receiver["response"]["result"] == expected_receive,
                "Socket delivery contradicts actual NAT egress.",
            )
        else:
            require(
                receiver["response"]["result"] is None
                and receiver["response"]["endNs"] - receiver["response"]["startNs"]
                >= int(receiver["request"]["timeout"] * 1_000_000_000),
                "Denied packet lacks its bounded complete receive observation.",
            )
        require(
            receiver["request"]
            == {
                "operation": "receive",
                "timeout": 0.3 if admit is serve else 3 if serve["type"] == "serve-pair" else 4,
            },
            "Unexpected native receive operation.",
        )
        logs = [row for row in self.logs[gateway] if row["packet"]["payloadHex"] == marker]
        early_drop = any(row["prefix"] == "ATTACH_DROP" for row in logs)
        require(
            [row["prefix"] for row in logs]
            == (
                ["INGRESS", "ATTACH_DROP"]
                if early_drop
                else ["INGRESS", "ATTACH_ALLOW", "TRACKED", "EGRESS"]
                if outgoing
                else ["INGRESS", "ATTACH_ALLOW", "TRACKED"]
            ),
            "Missing or additional pre-conntrack guard and ordinary hook observations.",
        )
        for row in logs:
            comparison = incoming if row["prefix"] != "EGRESS" else outgoing
            frame = bytes.fromhex(comparison["hex"])
            require(
                admit is serve or receiver["startNs"] <= row["timeNs"],
                "Held gateway observation precedes its actual service interval.",
            )
            require(
                row["source"] not in self.used_sources
                and sender["response"]["startNs"] <= row["timeNs"] < serve["endNs"]
                and bytes.fromhex(row["packet"]["raw"])[14:]
                == frame[14 : 14 + comparison["ipLength"]]
                and row["hardwareHex"] == incoming["hex"][:28]
                and row["inputIndex"] == self.indices[gateway][ingress_interface]
                and row["outputIndex"]
                == (self.indices[gateway][output_interface] if row["prefix"] == "EGRESS" else None),
                "Gateway NFLOG bytes, interface, or timing contradicts actual AF evidence.",
            )
            self.used_sources.add(row["source"])
        candidates = [
            row
            for row in self.traces[gateway]
            if row["stages"][0]["ipId"] == incoming["ipId"]
            and row["stages"][0]["packet"] == incoming["header"]
        ]
        require(len(candidates) == 1, "Missing or ambiguous selected gateway trace.")
        trace = candidates[0]
        before_key = serve["id"] + ":before"
        require(
            before_key in self.read_boundaries,
            "Read the actual service boundary before binding its packet.",
        )
        before = self.read_boundaries[before_key]
        records = before["conntrack"][gateway]
        require(len(records) <= 1, "Unsupported selected gateway conntrack inventory.")
        fresh = not records
        state = "new" if fresh or (original and not records[0]["status"] & 2) else "established"
        verify_gateway_path(
            trace,
            incoming,
            outgoing,
            before["tables"][gateway],
            state,
            fresh,
            ingress_interface,
            output_interface,
            before["networks"][gateway]["links"],
            early_drop,
        )
        trace_source = f"{gateway}-trace.txt:{trace['stages'][0]['line']}"
        require(trace_source not in self.used_sources, "Native trace was reused.")
        self.used_sources.add(trace_source)
        for row in frames:
            require(
                row["source"] not in self.used_sources, "Selected AF packet observation was reused."
            )
            self.used_sources.add(row["source"])
        if admit is not serve:
            require(
                sender["endNs"] < poll["endNs"] < admit["endNs"] < serve["startNs"]
                and receiver["startNs"] <= incoming["timeNs"],
                "Held packet admission and later service intervals overlap or run backward.",
            )
        value = {
            "id": admit["id"],
            "ticket": ticket,
            "admitEvent": admit["id"],
            "serveEvent": serve["id"],
            "gateway": gateway,
            "leg": "original" if original else "reply",
            "classification": None if early_drop else state,
            "fresh": None if early_drop else fresh,
            "guardAdmitted": not early_drop,
            "ingress": self.interface_refs[gateway][ingress_interface],
            "guardSource": logs[1]["source"],
            "admission": {
                **packet,
                "point": "endpoint-postrouting",
                "source": admission["source"],
                "inputIndex": None,
                "outputIndex": admission["outputIndex"],
                "observedNs": admission["timeNs"],
                "readEndNs": poll["endNs"],
                "interface": endpoint_interface,
            },
            "inputHex": packet["raw"],
            "outputHex": bytes.fromhex(outgoing["hex"])[14 : 14 + outgoing["ipLength"]].hex()
            if outgoing
            else None,
            "outputEthernetHex": outgoing["hex"] if outgoing else None,
            "incoming": incoming,
            "outgoing": outgoing,
            "trace": trace,
            "ingressSource": logs[0]["source"],
            "postSource": logs[-1]["source"] if outgoing else None,
            "frameSources": [row["source"] for row in frames],
            "outputFrameSource": outgoing["source"] if outgoing else None,
            "sender": sender,
            "receiver": receiver,
            "operation": {
                "admit": self.operations[admit["id"]],
                "serve": self.operations[serve["id"]],
            },
            "disposition": "ingressDrop"
            if early_drop
            else "forwarded"
            if outgoing
            else "forwardDrop",
        }
        self.packet_reports[ticket] = value
        return value

    def bind_attack(self, name):
        require(
            name in self.attacks and name not in self.attack_reports,
            "Unknown or reused raw adversary input.",
        )
        event = self.attacks[name]
        sender, receiver = event["result"]["sender"], event["result"]["receiver"]
        require(
            set(event["result"]) == {"sender", "receiver"}
            and set(sender) == {"command", "input", "request", "response", "startNs", "endNs"}
            and event["commands"] == [sender["command"]]
            and sender["input"] == name + "-raw-input.json",
            "Adversary input is not its actual single raw-send operation.",
        )
        command = self.commands[sender["command"]]
        require(
            command["arguments"]
            == [
                "ip",
                "netns",
                "exec",
                "attacker",
                "python3",
                ATTACHMENT_TASK,
                "raw-send",
                f"{SAFE_BASE}/{sender['input']}",
            ]
            and (sender["startNs"], sender["endNs"]) == (command["startNs"], command["endNs"])
            and json.loads(command["stdout"]) == sender["response"],
            "Adversary transmit receipt contradicts its actual command and namespace.",
        )
        self._artifact({"file": sender["input"], "command": sender["command"]})
        request = replication.nat.read_json(self.directory / sender["input"])
        require(
            request == sender["request"] and set(request) == {"interface", "rawEthernet"},
            "Adversary transmit input differs from its unchanged source file.",
        )
        response = sender["response"]
        require(
            set(response)
            == {
                "startNs",
                "endNs",
                "bytesSent",
                "rawEthernet",
                "interface",
                "ifindex",
                "namespace",
            },
            "Unexpected adversary transmitter metadata.",
        )
        replication.interval(response, command["startNs"], command["endNs"])
        require(
            response["rawEthernet"] == request["rawEthernet"]
            and response["interface"] == request["interface"]
            and response["bytesSent"] == len(bytes.fromhex(request["rawEthernet"]))
            and namespace_inode(response["namespace"]) == self.namespace_refs["attacker"]["id"]
            and ifindex(response["ifindex"]) == self.indices["attacker"][request["interface"]],
            "Raw transmit bytes, interface instance, or complete send count disagrees.",
        )
        input_packet = replication.wire.decode_frame(request["rawEthernet"])
        marker = input_packet["payloadHex"]
        require(
            marker == ("attachments:" + name).encode().hex(),
            "Adversary payload identity is ambiguous.",
        )
        gateway, original = event["gateway"], event["leg"] == "original"
        ingress = "aar" if gateway == "a" else "abr"
        output_interface = (
            ("sar" if original else "car") if gateway == "a" else ("sbr" if original else "cbr")
        )
        destination_actor = "server" if original else "client"
        require(
            request["interface"] == ("aal" if gateway == "a" else "abl"),
            "Adversary used another gateway attachment instance.",
        )
        frames = [row for row in self.frames if row["payloadHex"] == marker]
        incoming = [row for row in frames if row["namespace"] == gateway and row["packetType"] == 0]
        outgoing = [row for row in frames if row["namespace"] == gateway and row["packetType"] == 4]
        source = [row for row in frames if row["namespace"] == "attacker"]
        target = [row for row in frames if row["namespace"] == destination_actor]
        require(
            len(incoming) == len(source) == 1
            and len(outgoing) <= 1
            and len(frames) == (4 if outgoing else 2),
            "Missing or additional raw adversary path observations.",
        )
        incoming, outgoing = incoming[0], outgoing[0] if outgoing else None
        require(
            source[0]["hex"] == incoming["hex"] == request["rawEthernet"]
            and incoming["gateway"] == gateway
            and incoming["leg"] == event["leg"]
            and source[0]["interface"] == request["interface"]
            and source[0]["packetType"] == 4
            and incoming["interface"] == ingress
            and len(target) == int(outgoing is not None)
            and all(response["startNs"] <= row["timeNs"] < receiver["endNs"] for row in frames),
            "Spoofed bytes, real input interface, or raw transmit chronology disagrees.",
        )
        replication.interval(receiver, event["startNs"], event["endNs"])
        replication.interval(receiver["response"], receiver["startNs"], receiver["endNs"])
        require(
            sender["endNs"] < receiver["startNs"]
            and receiver["request"] == {"operation": "receive", "timeout": 0.3},
            "Adversary outcome does not follow actual send completion.",
        )
        if outgoing:
            expected_output = replication.WIRE if original else replication.PEER_REPLY
            require(
                outgoing["header"] == expected_output
                and outgoing["interface"] == output_interface
                and outgoing["ttl"] == 63
                and outgoing["ipId"] == incoming["ipId"]
                and outgoing["ipLength"] == incoming["ipLength"]
                and outgoing["udpLength"] == incoming["udpLength"]
                and outgoing["payloadHex"] == marker
                and target[0]["packetType"] == 0
                and target[0]["interface"] == OPPOSITE[output_interface]
                and target[0]["hex"] == outgoing["hex"]
                and receiver["response"]["result"]
                == {
                    "payloadHex": marker,
                    "peer": [expected_output["source"], expected_output["sourcePort"]],
                    "local": [expected_output["destination"], expected_output["destinationPort"]],
                },
                "Header-only counterexample lacks actual translated gateway output and socket delivery.",
            )
        else:
            require(
                receiver["response"]["result"] is None
                and receiver["response"]["endNs"] - receiver["response"]["startNs"] >= 300_000_000,
                "Rejected adversary input lacks its complete bounded receive absence.",
            )
        logs = [row for row in self.logs[gateway] if row["packet"]["payloadHex"] == marker]
        early_drop = event["securityPhase"] != "unsafe"
        require(
            [row["prefix"] for row in logs]
            == (["INGRESS", "ATTACH_DROP"] if early_drop else ["INGRESS", "TRACKED", "EGRESS"])
            and (outgoing is None) == early_drop,
            "Adversary outcome reached tracking or bypassed the declared attachment guard.",
        )
        for row in logs:
            comparison = outgoing if row["prefix"] == "EGRESS" else incoming
            frame = bytes.fromhex(comparison["hex"])
            require(
                response["startNs"] <= row["timeNs"] < receiver["endNs"]
                and bytes.fromhex(row["packet"]["raw"])[14:]
                == frame[14 : 14 + comparison["ipLength"]]
                and row["hardwareHex"] == incoming["hex"][:28]
                and row["inputIndex"] == self.indices[gateway][ingress]
                and row["outputIndex"]
                == (self.indices[gateway][output_interface] if row["prefix"] == "EGRESS" else None),
                "Pre-conntrack NFLOG metadata or bytes contradict the actual adversary interface.",
            )
        traces = [
            row
            for row in self.traces[gateway]
            if row["stages"][0]["ipId"] == incoming["ipId"]
            and row["stages"][0]["packet"] == incoming["header"]
        ]
        require(len(traces) == 1, "Missing or ambiguous complete adversary trace.")
        before = self.read_boundaries[name + ":before"]
        records = before["conntrack"][gateway]
        fresh = not records
        state = "new" if fresh or (original and not records[0]["status"] & 2) else "established"
        verify_gateway_path(
            traces[0],
            incoming,
            outgoing,
            before["tables"][gateway],
            state,
            fresh,
            ingress,
            output_interface,
            before["networks"][gateway]["links"],
            early_drop,
            guarded=early_drop,
        )
        sources = [row["source"] for row in frames + logs]
        sources.append(f"{gateway}-trace.txt:{traces[0]['stages'][0]['line']}")
        require(
            len(sources) == len(set(sources)) and not (set(sources) & self.used_sources),
            "Adversary raw observations were reused.",
        )
        self.used_sources.update(sources)
        value = {
            "id": name,
            "gateway": gateway,
            "leg": event["leg"],
            "securityPhase": event["securityPhase"],
            "ingress": self.interface_refs[gateway][ingress],
            "sourceMAC": bytes.fromhex(incoming["hex"])[6:12].hex(":"),
            "inputHex": bytes.fromhex(incoming["hex"])[14 : 14 + incoming["ipLength"]].hex(),
            "outputEthernetHex": outgoing["hex"] if outgoing else None,
            "classification": None if early_drop else state,
            "fresh": None if early_drop else fresh,
            "guardAdmitted": not early_drop,
            "disposition": "ingressDrop" if early_drop else "forwarded",
            "incoming": incoming,
            "outgoing": outgoing,
            "sender": sender,
            "receiver": receiver,
            "trace": traces[0],
            "frameSources": [row["source"] for row in frames],
            "ingressSource": logs[0]["source"],
            "guardSource": logs[1]["source"] if early_drop else None,
        }
        self.attack_reports[name] = value
        return value

    def _operation(self, name):
        operation = self.operations[name]
        event, exports = operation["native"], {}
        result = event["result"]
        if event["type"] not in (
            "authentication",
            "credential",
            "policy",
            "withdraw",
            "guard",
            "reset",
            "replication-start",
            "protect",
            "barrier",
        ):
            return super()._operation(name)
        window = operation["startNs"], operation["endNs"]
        if event["type"] == "withdraw":
            require(
                result["archiveBoundary"] == ARCHIVE,
                "Withdrawal selected a different primary archive.",
            )
            for kind, ref in result["statistics"].items():
                require(kind in {"cache", "network", "runtime", "ct"}, "Unknown archive statistic.")
                exports[ref["file"]] = self._export(
                    ref,
                    "a",
                    ["conntrackd", "-C", f"{SAFE_BASE}/a.conf", "-s", kind],
                    window,
                    as_json=False,
                )
            ref = result["standbyLogBefore"]
            exports[ref["file"]] = self._export(
                ref, "b", ["cat", f"{SAFE_BASE}/b.log"], window, as_json=False
            )
            ref = result["cache"]
            exports[ref["file"]] = self._export(
                ref,
                "a",
                ["conntrackd", "-C", f"{SAFE_BASE}/a.conf", "-e", "-x"],
                window,
                as_json=False,
            )
            for kind, args in (
                ("links", ["ip", "-j", "link", "show"]),
                ("forwarding", ["sysctl", "net.ipv4.ip_forward"]),
                ("daemon", ["python3", ATTACHMENT_TASK, "daemon-stopped"]),
            ):
                ref = result["checks"][kind]
                exports[ref["file"]] = self._export(
                    ref, "a", args, window, as_json=kind != "forwarding"
                )
        elif event["type"] == "policy":
            self._policy_load(result, event["gateway"], name, event["policy"], window)
        elif event["type"] == "credential":
            ref = result["installed"]
            self._artifact(ref, "installed-demo-credential.json")
            command = self._command(
                ref["command"], ["cat", "/run/netlib-attachments/demo-credential.json"], window
            )
            require(
                command["stdout"] == (self.directory / ref["file"]).read_text(),
                "Installed credential bytes contradict the actual readback.",
            )
        elif event["type"] == "authentication":
            for field, actor, args in (
                (
                    "station",
                    "auth",
                    [
                        "hostapd_cli",
                        "-p",
                        "/run/netlib-eap/hostapd",
                        "-i",
                        "auth0",
                        "sta",
                        eap.PEER,
                    ],
                ),
                (
                    "status",
                    "client",
                    ["wpa_cli", "-p", "/run/netlib-eap/supplicant", "-i", "peer0", "status"],
                ),
            ):
                if field in result:
                    ref = result[field]
                    exports[ref["file"]] = self._export(ref, actor, args, window, as_json=False)
            if name == "logoff":
                arguments = {
                    "links": ["link", "show"],
                    "addresses": ["address", "show"],
                    "routes": ["-4", "route", "show", "table", "main"],
                    "rules": ["-4", "rule", "show"],
                }
                require(
                    set(result["network"]) == set(arguments),
                    "Missing post-Logoff authentication network.",
                )
                for kind, ref in result["network"].items():
                    exports[ref["file"]] = self._export(
                        ref, "auth", ["ip", "-j", *arguments[kind]], window
                    )
        elif event["type"] == "barrier":
            interface = {
                "primary-barrier": "cal",
                "original-barrier": "cbl",
                "reply-barrier": "sbl",
            }[name]
            ref = result["qdisc"]
            exports[ref["file"]] = self._export(
                ref,
                "server" if interface == "sbl" else "client",
                [SAFE_TC, "-j", "-s", "-d", "qdisc", "show", "dev", interface],
                window,
                filename=f"{name}-{interface}-qdisc.json",
            )
        elif event["type"] == "reset":
            require(
                set(result) == {"commands", "tables"}
                and set(result["commands"]) == set(result["tables"]) == set(GATEWAYS),
                "Reset omits a gateway flush or actual empty-table observation.",
            )
            for actor, ref in result["tables"].items():
                self._artifact(ref, f"reset-{actor}-conntrack.json")
                command = self._command(
                    ref["command"],
                    [
                        "ip",
                        "netns",
                        "exec",
                        actor,
                        "python3",
                        "/task/capture_conntrack.py",
                        "--output",
                        f"{SAFE_BASE}/{ref['file']}",
                    ],
                    window,
                )
                require(not command["stdout"], "Reset dump producer has unexpected stdout.")
                exports[ref["file"]] = decode_snapshot(
                    replication.nat.read_json(self.directory / ref["file"])
                )
        elif event["type"] in ("protect", "replication-start"):
            require(
                set(result["cacheReadiness"]) == set(GATEWAYS),
                "Missing actual ready-cache observations.",
            )
            for actor, refs in result["cacheReadiness"].items():
                require(
                    set(refs) == {"internal", "external"}, "Incomplete initial daemon cache views."
                )
                for kind, ref in refs.items():
                    exports[ref["file"]] = self._export(
                        ref,
                        actor,
                        [
                            "conntrackd",
                            "-C",
                            f"{SAFE_BASE}/{actor}.conf",
                            "-i" if kind == "internal" else "-e",
                            "-x",
                        ],
                        window,
                        as_json=False,
                    )
            if event["type"] == "replication-start":
                self.daemon_sockets = {}
                for actor, daemon in result["daemons"].items():
                    ref = daemon["runtime"]
                    exports[ref["file"]] = self._export(
                        ref,
                        actor,
                        ["conntrackd", "-C", f"{SAFE_BASE}/{actor}.conf", "-s", "runtime"],
                        window,
                        as_json=False,
                    )
                    attempts = result["socketAttempts"][actor]
                    require(
                        attempts and result["socketReadiness"][actor] == attempts[-1],
                        "Outgoing socket selection omits its actual final readiness poll.",
                    )
                    self.daemon_sockets[actor] = []
                    for ref in attempts:
                        value = self._export(
                            ref, actor, ["python3", ATTACHMENT_TASK, "daemon-sockets"], window
                        )
                        exports[ref["file"]] = value
                        self.daemon_sockets[actor].append((ref, value))
        elif event["type"] == "guard":
            actor = event["gateway"]
            require(
                set(result) == {"command", "file", "active", "binding"}
                and result["active"] is event["active"]
                and result["file"] == name + "-load.json"
                and set(result["binding"]) == {"file", "sources"}
                and set(result["binding"]["sources"]) == {"links", "identity"},
                "Attachment installation omits its actual controller input or native sources.",
            )
            for kind, arguments in (
                ("links", ["ip", "-j", "link", "show"]),
                ("identity", ["python3", ATTACHMENT_TASK, "identity"]),
            ):
                ref = result["binding"]["sources"][kind]
                exports[ref["file"]] = self._export(
                    ref, actor, arguments, window, filename=f"{name}-{kind}.json"
                )
            identity_ref = result["binding"]["sources"]["identity"]
            identity = exports[identity_ref["file"]]
            self._identity(identity, self.commands[identity_ref["command"]])
            require(
                namespace_inode(identity["namespace"]) == self.namespace_refs[actor]["id"],
                "Attachment installation moved to another namespace lifetime.",
            )
            filename = result["binding"]["file"]
            require(
                filename == name + "-bindings.json" and filename not in self.used_artifacts,
                "Attachment controller binding is reused or belongs to another operation.",
            )
            self.used_artifacts.add(filename)
            exports[filename] = replication.nat.read_json(self.directory / filename)
            require(
                exports[filename]["sources"] == result["binding"]["sources"],
                "Controller binding contradicts its actual link and namespace readbacks.",
            )
            self._artifact(
                {"file": result["file"], "command": result["command"]}, name + "-load.json"
            )
            command = self._command(
                result["command"],
                ["ip", "netns", "exec", actor, "nft", "-j", "-f", f"{SAFE_BASE}/{result['file']}"],
                window,
            )
            require(not command["stdout"], "Attachment installation has unexpected stdout.")
            exports[result["file"]] = replication.nat.read_json(self.directory / result["file"])
        for index in event["commands"]:
            if index not in self.used_commands:
                self._command(index, window=window)
        return {**operation, "exports": exports}

    def validate_daemon_sockets(self):
        start = self.events["start-replication"]["result"]
        require(
            set(start["socketAttempts"]) == set(start["socketReadiness"]) == set(GATEWAYS),
            "Missing current daemon socket ownership receipts.",
        )
        self.maintenance = {}
        process_namespaces, socket_namespaces = {}, {}
        for actor in GATEWAYS:
            birth = None
            selected = None
            for index, (reference, value) in enumerate(self.daemon_sockets[actor]):
                command = self.commands[reference["command"]]
                require(
                    set(value) == {"startNs", "endNs", "namespace", "processes", "sockets"}
                    and namespace_inode(value["namespace"]) == self.namespace_refs[actor]["id"],
                    "Daemon socket readiness refers to another network namespace.",
                )
                replication.interval(value, command["startNs"], command["endNs"])
                processes = value["processes"]
                require(
                    len(processes) == 1,
                    "No unique live conntrack daemon owns the maintenance sockets.",
                )
                process = processes[0]
                require(
                    set(process)
                    == {"pid", "comm", "cmdline", "namespace", "startTimeTicks", "fdSockets"}
                    and type(process["pid"]) is int
                    and process["pid"] > 0
                    and process["comm"] == "conntrackd"
                    and process["cmdline"]
                    == ["conntrackd", "-C", f"{SAFE_BASE}/{actor}.conf", "-d"]
                    and process["namespace"] == value["namespace"]
                    and type(process["startTimeTicks"]) is int
                    and process["startTimeTicks"] > 0,
                    "Maintenance sender is not the actual selected daemon process.",
                )
                current = process["pid"], process["startTimeTicks"]
                # The selected runtime assumes zero time-namespace clock offsets.
                require(
                    process["startTimeTicks"]
                    >= self.commands[start["daemons"][actor]["startCommand"]]["startNs"]
                    // PROC_TICK_NS,
                    "Daemon process birth predates its actual start command.",
                )
                require(
                    process_namespaces.get(process["pid"], actor) == actor,
                    "Simultaneously live namespace daemons alias the same process PID.",
                )
                process_namespaces[process["pid"]] = actor
                require(
                    birth is None or current == birth,
                    "Daemon process changed during socket readiness polling.",
                )
                birth = current
                descriptors = process["fdSockets"]
                require(
                    all(
                        set(row) == {"fd", "inode"}
                        and type(row["fd"]) is int
                        and 0 <= row["fd"] < 2**31
                        and type(row["inode"]) is int
                        and row["inode"] > 0
                        for row in descriptors
                    )
                    and len(descriptors) == len({row["fd"] for row in descriptors}),
                    "Malformed daemon descriptor-to-socket ownership mapping.",
                )
                descriptor_pairs = {(row["fd"], row["inode"]) for row in descriptors}
                outgoing = []
                require(
                    len(value["sockets"]) == len({row["inode"] for row in value["sockets"]}),
                    "Daemon UDP socket receipt repeats an inode.",
                )
                for socket in value["sockets"]:
                    require(
                        socket_namespaces.get(socket["inode"], actor) == actor,
                        "Live namespace socket ownership aliases an ambiguous native inode.",
                    )
                    socket_namespaces[socket["inode"]] = actor
                    require(
                        set(socket) == {"inode", "local", "remote", "state", "owners"}
                        and type(socket["inode"]) is int
                        and socket["inode"] > 0
                        and socket["owners"]
                        and all(
                            set(owner) == {"pid", "fd"}
                            and owner["pid"] == process["pid"]
                            and (owner["fd"], socket["inode"]) in descriptor_pairs
                            for owner in socket["owners"]
                        ),
                        "UDP socket is not owned by the actual daemon descriptor.",
                    )
                    for endpoint in (socket["local"], socket["remote"]):
                        require(
                            set(endpoint) == {"address", "port"}
                            and isinstance(endpoint["address"], str)
                            and type(endpoint["port"]) is int
                            and 0 <= endpoint["port"] < 65536,
                            "Malformed daemon UDP endpoint.",
                        )
                    local, remote = socket["local"], socket["remote"]
                    if local["port"] == 3780:
                        require(
                            local["address"] == ("10.10.0.1" if actor == "a" else "10.10.0.2")
                            and remote == {"address": "0.0.0.0", "port": 0}
                            and socket["state"] == "07",
                            "Daemon maintenance listener changed its exact binding.",
                        )
                    else:
                        require(
                            local["address"]
                            in ("0.0.0.0", "10.10.0.1" if actor == "a" else "10.10.0.2")
                            and local["port"] > 0
                            and (
                                (
                                    socket["state"] == "07"
                                    and remote == {"address": "0.0.0.0", "port": 0}
                                )
                                or (
                                    socket["state"] == "01"
                                    and remote
                                    == {
                                        "address": "10.10.0.2" if actor == "a" else "10.10.0.1",
                                        "port": 3780,
                                    }
                                )
                            ),
                            "Maintenance sender has an unmodeled local or remote UDP endpoint.",
                        )
                        outgoing.append(socket)
                require(
                    len(outgoing) <= 1 and len(value["sockets"]) == 1 + len(outgoing),
                    "Unaccounted daemon UDP sockets remain.",
                )
                final = index + 1 == len(self.daemon_sockets[actor])
                require(
                    bool(outgoing) == final,
                    "Socket readiness selection skips an earlier ready sender or selects an absent one.",
                )
                if final:
                    socket = outgoing[0]
                    selected = {
                        "source": reference,
                        "sourcePort": socket["local"]["port"],
                        "socketInode": socket["inode"],
                        "pid": process["pid"],
                        "startTimeTicks": process["startTimeTicks"],
                    }
            require(selected is not None, "No observed daemon sender binds the maintenance guard.")
            self.maintenance[actor] = selected
        for frame in self.sync:
            actor = "a" if frame["header"]["source"] == "10.10.0.1" else "b"
            require(
                frame["header"]["sourcePort"] == self.maintenance[actor]["sourcePort"]
                and frame["header"]["destinationPort"] == 3780
                and frame["timeNs"]
                >= self.commands[start["daemons"][actor]["startCommand"]]["startNs"],
                "Actual synchronization traffic differs from its current daemon socket lifetime.",
            )
        return self.maintenance

    def finish(self):
        require(
            len(self.packet_reports) == len(self.packets)
            and len(self.attack_reports) == len(self.attacks)
            and self.used_polls == set(range(len(self.polls))),
            "Unconsumed campus packet or admission poll remains.",
        )
        required = (
            {row["source"] for row in self.frames}
            | {row["source"] for rows in self.logs.values() for row in rows}
            | {
                f"{actor}-trace.txt:{row['stages'][0]['line']}"
                for actor, rows in self.traces.items()
                for row in rows
            }
        )
        require(self.used_sources == required, "Unconsumed selected packet, log, or trace remains.")
        self._sync_audit()
        initial, final = self.read_boundaries["initial"], self.read_boundaries["final"]
        first = self.manifest["events"][0]["startNs"]
        require(
            self.manifest["initialCaches"] == {},
            "No daemon cache existed before the explicit startup event.",
        )
        caches = {"startup": {}, "protected": {}, "final": {}}
        for phase, name in (("startup", "start-replication"), ("protected", "protect-marker")):
            operation = self.read_boundaries[name + ":before"]["operation"]
            for actor, refs in operation["native"]["result"]["cacheReadiness"].items():
                caches[phase][actor] = {}
                for kind, ref in refs.items():
                    rows = replication.decode_cache_xml(operation["exports"][ref["file"]])
                    require(rows == [], "A cached pre-reset flow leaks into the protected epoch.")
                    caches[phase][actor][kind] = rows
        self.validate_daemon_sockets()
        withdraw = self.read_boundaries[ARCHIVE]["operation"]
        archived = withdraw["native"]["result"]
        require(
            set(self.manifest["finalCaches"]) == set(GATEWAYS)
            and self.manifest["finalCaches"]["a"] == archived["cache"]
            and self.manifest["statistics"]["a"] == archived["statistics"],
            "Final primary daemon state is not the declared historical archive.",
        )
        caches["final"]["a"] = replication.decode_cache_xml(
            withdraw["exports"][archived["cache"]["file"]]
        )
        ref = self.manifest["finalCaches"]["b"]
        caches["final"]["b"] = replication.decode_cache_xml(
            self._export(
                ref,
                "b",
                ["conntrackd", "-C", f"{SAFE_BASE}/b.conf", "-e", "-x"],
                (final["endNs"], self.manifest["endNs"]),
                as_json=False,
                filename="final-b-cache.xml",
            )
        )
        statistics = {"a": {}, "b": {}}
        require(
            set(self.manifest["statistics"]) == set(GATEWAYS),
            "Missing daemon statistics inventory.",
        )
        for actor in GATEWAYS:
            require(
                set(self.manifest["statistics"][actor]) == {"cache", "network", "runtime", "ct"},
                "Incomplete daemon statistics.",
            )
            for kind, ref in self.manifest["statistics"][actor].items():
                text = (
                    withdraw["exports"][ref["file"]]
                    if actor == "a"
                    else self._export(
                        ref,
                        "b",
                        ["conntrackd", "-C", f"{SAFE_BASE}/b.conf", "-s", kind],
                        (final["endNs"], self.manifest["endNs"]),
                        as_json=False,
                        filename=f"b-{kind}-statistics.txt",
                    )
                )
                statistics[actor][kind] = text
                for line in text.splitlines():
                    if re.search(
                        r"failed:|Malformed|Wrong protocol|Bad message|Truncated|Packets lost:|Packets before:|unknown type:|netlink overrun:|flush kernel table:|resync with kernel table:|process segfault:|process termsig:|unknown request:|Error send",
                        line,
                    ):
                        values = (
                            [int(line.rsplit(":", 1)[-1].rsplit("/", 1)[-1])]
                            if ":" in line
                            else [int(value) for value in re.findall(r"\b[0-9]+\b", line)]
                        )
                        require(
                            values and all(value == 0 for value in values),
                            "Daemon reports failed or lost selected observations.",
                        )
            require(
                (self.directory / f"{actor}.conf").read_text()
                == replication.configuration(actor).replace(replication.BASE, SAFE_BASE),
                "Unexpected synchronization configuration.",
            )
        require(set(self.manifest["settings"]) == set(ACTORS), "Missing namespace settings.")
        for actor, ref in self.manifest["settings"].items():
            values = {
                "net.ipv4.ip_forward": int(actor in GATEWAYS),
                "net.ipv4.conf.all.rp_filter": 0,
                "net.ipv4.conf.default.rp_filter": 0,
                "net.ipv6.conf.all.disable_ipv6": 1,
                "net.ipv6.conf.default.disable_ipv6": 1,
                "net.netfilter.nf_conntrack_udp_timeout": 30,
                "net.netfilter.nf_conntrack_udp_timeout_stream": 120,
                "net.netfilter.nf_conntrack_acct": int(actor in GATEWAYS),
                **{f"net.ipv4.conf.{name}.rp_filter": 0 for name in LINKS[actor]},
            }
            text = self._export(
                ref,
                actor,
                ["sysctl", *values],
                (self.manifest["startNs"], initial["startNs"]),
                as_json=False,
                filename=f"{actor}-settings.txt",
            )
            require(
                text == "".join(f"{key} = {value}\n" for key, value in values.items()),
                "Namespace sysctl readback differs from the selected profile.",
            )
        for actor, result in zip(GATEWAYS, self.manifest["initialPolicyLoads"], strict=True):
            self._policy_load(
                result,
                actor,
                "initial-" + actor,
                "deny",
                (self.manifest["startNs"], initial["startNs"]),
            )
        self.authentication = self._authentication()
        simultaneous = (
            [
                observer["identity"]["pid"]
                for observer in self.observers.values()
                if observer["kind"] in ("packet", "nflog")
            ]
            + [life["pid"] for life in self.manifest["eap"]["producers"].values()]
            + [daemon["pid"] for daemon in self.maintenance.values()]
        )
        require(
            len(simultaneous) == len(set(simultaneous)),
            "Overlapping packet/authentication/daemon process lifetimes alias the same PID.",
        )
        for actor, source in (("auth", "auth"), ("client", "peer")):
            ref = self.manifest["authenticationNetwork"][source]["links"]
            rows = replication.nat.read_json(self.directory / ref["file"])
            require(
                {row["ifname"]: row["ifindex"] for row in rows}
                == {
                    row["name"]: row["ifindex"]
                    for row in self.birth_identities[actor]["interfaces"]
                },
                "Authentication attachment birth does not join the actual live EAP port inventory.",
            )
        self._daemon_logs()
        self._provenance(initial, first)
        return {
            "schema": 1,
            "profile": self.manifest["profile"],
            "captureID": self.manifest["captureID"],
            "packetCount": len(self.packets) + len(self.attacks),
            "snapshotCount": sum(
                len(row["native"]["conntrack"]) for row in self.read_boundaries.values()
            ),
            "frameCount": len(self.frames),
            "nflogCount": sum(len(rows) for rows in self.logs.values()),
            "syncFrameCount": len(self.sync),
            "initial": initial,
            "protectedInitial": self.read_boundaries["protect-marker:before"],
            "final": final,
            "cacheViews": caches,
            "statistics": statistics,
            "operations": self.operations,
            "syncData": self.sync_data,
            "eapEvidence": self.authentication,
            "credential": replication.nat.read_json(
                self.directory / "installed-demo-credential.json"
            ),
        }

    def _provenance(self, initial, first_event):
        root = Path(__file__).resolve().parents[1]
        versions = {
            "conntrack-version.txt": "conntrack v1.4.9 (conntrack-tools)\n",
            "conntrackd-version.txt": "Connection tracking userspace daemon v1.4.9. Licensed under GPLv2.\n(C) 2006-2009 Pablo Neira Ayuso <pablo@netfilter.org>\n",
            "nftables-version.txt": "nftables v1.1.3 (Commodore Bullmoose #4)\n",
            "iproute2-version.txt": "ip utility, iproute2-6.19.0\n",
            "tc-version.txt": "tc utility, iproute2-6.19.0\n",
        }
        require(
            re.fullmatch(
                r"Linux \S+ 6\.8\.0-117-generic .* aarch64 Linux\n",
                (self.directory / "kernel.txt").read_text(),
            ),
            "Unexpected native kernel release or architecture.",
        )
        for name, expected in versions.items():
            require(
                (self.directory / name).read_text() == expected,
                "Native producer version differs from selected profile.",
            )
        helpers = {
            "/task/attachments/exercise.py": root / "examples/attachments/exercise.py",
            "/task/campus/exercise.py": root / "examples/campus/exercise.py",
            "/task/safe-handoff/exercise.py": root / "examples/safe-handoff/exercise.py",
            "/task/eap_exercise.py": root / "examples/eap/exercise.py",
            "/task/replication/exercise.py": root / "examples/replication/exercise.py",
            "/task/replication/nflog.py": root / "examples/replication/nflog.py",
            "/task/wire/exercise.py": root / "examples/wire/exercise.py",
            "/task/capture_conntrack.py": root / "scripts/capture_conntrack.py",
        }
        actual = _digests(self.directory / "helper-sha256.txt")
        require(
            set(actual) == set(helpers)
            and all(
                actual[name] == hashlib.sha256(path.read_bytes()).hexdigest()
                for name, path in helpers.items()
            ),
            "Retained helper source digest disagrees.",
        )
        producers = _digests(self.directory / "producer-sha256.txt")
        require(
            set(producers)
            == {
                "/usr/local/bin/hostapd",
                "/usr/local/bin/wpa_supplicant",
                "/usr/local/bin/hostapd_cli",
                "/usr/local/bin/wpa_cli",
                "/usr/bin/openssl",
                "/opt/netlib/sbin/conntrackd",
                "/opt/netlib/sbin/conntrack",
                "/opt/netlib/sbin/nft",
                "/opt/netlib/sbin/ip",
                SAFE_TC,
                "/tmp/tools.tar.xz",
                "/tmp/library.tar.xz",
                "/tmp/iproute2.tar.gz",
                "/tmp/iproute2-6.19.0/tc/q_netem.c",
            }
            and producers["/tmp/tools.tar.xz"]
            == "c15afe488a8d408c9d6d61e97dbd19f3c591942f62c13df6453a961ca4231cae"
            and producers["/tmp/library.tar.xz"]
            == "769d3eaf57fa4fbdb05dd12873b6cb9a5be7844d8937e222b647381d44284820"
            and producers["/tmp/iproute2.tar.gz"]
            == "b39ac6a76f8299968408d3f2948ea59d9502b299d3e0c78c93658b65df3be5be"
            and producers["/tmp/iproute2-6.19.0/tc/q_netem.c"]
            == "999a1f78f6685c8567f68806b5430194de8d6d7416aec7fcf03b1255981fb57a",
            "Pinned producer source provenance disagrees.",
        )
        final_command = max(self.commands[index]["endNs"] for index in self.used_commands)
        require(len(self.manifest["endpoints"]) == 2, "Missing or duplicate endpoint lifetimes.")
        for endpoint, actor, address, port in zip(
            self.manifest["endpoints"],
            ("client", "server"),
            ("192.0.2.2", "198.51.100.2"),
            (41000, 9000),
            strict=True,
        ):
            require(
                set(endpoint) == {"command", "startNs", "endNs", "binding", "returncode"}
                and endpoint["command"]
                == [
                    "ip",
                    "netns",
                    "exec",
                    actor,
                    "python3",
                    CAMPUS_TASK,
                    "endpoint",
                    address,
                    str(port),
                ]
                and type(endpoint["returncode"]) is int
                and endpoint["returncode"] == 0
                and initial["endNs"]
                < endpoint["startNs"]
                < first_event
                < final_command
                < endpoint["endNs"]
                < self.manifest["endNs"],
                "Endpoint process identity, lifetime, or completion disagrees.",
            )
            binding = endpoint["binding"]
            replication.interval(binding, endpoint["startNs"], first_event)
            replication.interval(binding["response"], binding["startNs"], binding["endNs"])
            require(
                binding["request"] == {"operation": "bind"}
                and binding["response"]["result"] == {"local": [address, port], "mtuDiscover": 0},
                "Endpoint socket binding disagrees.",
            )
        remaining = [
            (index, row)
            for index, row in enumerate(self.commands)
            if index not in self.used_commands
        ]
        setup, shutdown = attachment_setup_commands()

        require(
            Counter(tuple(row["arguments"]) for _, row in remaining)
            == Counter(tuple(row) for row in setup + shutdown),
            "Command journal contains unaccounted mutations or missing bootstrap operations.",
        )
        for index, row in remaining:
            if row["arguments"] in shutdown:
                require(
                    final_command
                    < row["startNs"]
                    < row["endNs"]
                    < min(observer["stopNs"] for observer in self.observers.values()),
                    "Daemon shutdown precedes final observations or follows observer shutdown.",
                )
            else:
                require(
                    row["endNs"] < initial["startNs"],
                    "Bootstrap mutation occurs after initial state readbacks.",
                )
            if row["arguments"][-2:-1] == ["offload"]:
                _offload(row)
            self.used_commands.add(index)


def verify_gateway_path(
    trace,
    incoming,
    outgoing,
    document,
    classification,
    fresh,
    ingress_interface,
    output_interface,
    links,
    early_drop,
    guarded=True,
):
    expected = [("replication_observe", "ingress")]
    if guarded:
        expected.append(("netlib_attachment", "ingress"))
    if not early_drop:
        expected.extend([("sync_untracked", "prerouting"), ("replication_observe", "tracked")])
        if fresh:
            expected.append(("netlib_nat", "prerouting"))
        expected.append(("netlib", "forward"))
        if outgoing:
            if fresh:
                expected.append(("netlib_nat", "postrouting"))
            expected.extend([("netlib_late", "late"), ("replication_observe", "egress")])
    require(
        [(stage["table"], stage["chain"]) for stage in trace["stages"]] == expected,
        "Packet hook path contradicts its actual pre-conntrack attachment decision.",
    )
    translated = (
        replication.admission.REQUEST
        if incoming["header"] == replication.ORIGINAL
        else replication.admission.REPLY
    )
    for stage in trace["stages"]:
        late = stage["chain"] in ("late", "egress")
        forwarded = late or stage["chain"] in ("forward", "postrouting")
        header = outgoing["header"] if late else translated if forwarded else incoming["header"]
        checksum = replication.reassembly.expected_udp_checksum(
            header, bytes.fromhex(incoming["payloadHex"]), False
        )
        require(
            stage["packet"] == header
            and stage["iif"] == ingress_interface
            and stage["oif"] == (output_interface if forwarded else None)
            and stage["ipId"] == incoming["ipId"]
            and stage["ttl"] == (63 if forwarded else 64)
            and stage["ipLength"] == incoming["ipLength"]
            and stage["udpLength"] == incoming["udpLength"]
            and stage["udpChecksum"] == checksum,
            "Attachment trace changed packet bytes, interface, TTL, identity, or checksum.",
        )
        if stage["table"] == "netlib_attachment":
            check_guard_trace(
                stage, document, links, classification, incoming["header"], ingress_interface
            )
        else:
            replication.check_trace_rules(stage, document, classification)


def check_guard_trace(stage, document, links, classification, header, ingress_interface):
    import shlex

    chain, rules = replication.lifecycle.native_chain(document, "netlib_attachment", "ingress")
    ingress = next(row["ifindex"] for row in links if row["ifname"] == ingress_interface)
    matched = []
    for rule in rules:
        allowed = True
        for expression in rule["expr"]:
            if "match" not in expression:
                continue
            value = expression["match"]
            if value["left"] == {"meta": {"key": "iif"}}:
                allowed &= resolve_iif(expression, links) == ingress
            else:
                allowed &= replication.lifecycle.native_match(value, classification, header)
        if allowed:
            terminal = next(iter(rule["expr"][-1]))
            require(terminal in ("accept", "drop"), "Unsupported attachment trace terminal.")
            matched.append(("rule", terminal, rule))
            break
    if not matched:
        matched = [("policy", chain["policy"], None)]
    require(
        len(stage["verdicts"]) == len(matched), "Attachment trace omits or adds a guard decision."
    )
    for (kind, verdict, rule), actual in zip(matched, stage["verdicts"], strict=True):
        require(
            (actual["kind"], actual["verdict"]) == (kind, verdict),
            "Attachment trace contradicts the installed numeric guard.",
        )
        if rule is None:
            continue
        if actual["handle"] is not None:
            require(
                actual["handle"] == rule["handle"],
                "Attachment trace uses a different current rule handle.",
            )
            continue
        tokens = []
        for expression in rule["expr"]:
            if expression.get("match", {}).get("left") == {"meta": {"key": "iif"}}:
                index = resolve_iif(expression, links)
                name = next(row["ifname"] for row in links if row["ifindex"] == index)
                tokens.extend(["iif", name])
            else:
                tokens.extend(replication.trace_rule_tokens({"expr": [expression]}))
        if "comment" in rule:
            tokens.extend(["comment", rule["comment"]])
        require(
            shlex.split(actual["text"]) == tokens,
            "Attachment trace rule text contradicts its current export.",
        )
