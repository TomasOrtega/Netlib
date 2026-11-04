"""Check actual EAP-TLS, generated firewall loads, UDP outcomes, and cached flow state."""

import argparse
import ipaddress
import json
import sys
from pathlib import Path

import check_eap_capture as eap
import check_lifecycle_capture as lifecycle

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "examples/admission"
EvidenceError = eap.EvidenceError
require = eap.require
STAGES = ("unauthenticated", "authenticated-only", "credential-permitted", "logged-off-cached")
REQUEST = {
    "source": "192.0.2.2",
    "destination": "198.51.100.2",
    "protocol": 17,
    "sourcePort": 41000,
    "destinationPort": 9000,
}
REPLY = {
    "source": "198.51.100.2",
    "destination": "192.0.2.2",
    "protocol": 17,
    "sourcePort": 9000,
    "destinationPort": 41000,
}
SERVICE = "02:00:00:00:eb:01"
SERVER = "02:00:00:00:eb:02"


def read_json(path):
    return json.loads(path.read_text())


def interval(row, outer=None):
    require(
        eap.integer(row["startNs"]) and eap.integer(row["endNs"]) and row["startNs"] < row["endNs"],
        "Invalid native observation interval.",
    )
    if outer:
        require(
            outer["startNs"] <= row["startNs"] < row["endNs"] <= outer["endNs"],
            "Native observation lies outside its stage window.",
        )


def successful_command(row, expected):
    interval(row)
    require(
        row["command"] == expected
        and type(row["returncode"]) is int
        and row["returncode"] == 0
        and row["stderr"] == "",
        "Native command or successful completion disagreement.",
    )


def canonical_rule(rule):
    require(
        set(rule) <= {"family", "table", "chain", "handle", "comment", "expr"}
        and rule["family"] == "ip"
        and rule["table"] == "netlib"
        and rule["chain"] == "forward",
        "Unexpected native forward rule.",
    )
    result = {"id": rule["comment"]}
    expressions = rule["expr"]
    require(
        expressions and expressions[-1] == {"accept": None}, "Generated rule must end in accept."
    )
    explicit_protocol = False
    for expression in expressions[:-1]:
        require(set(expression) == {"match"}, "Unexpected forward expression or conntrack bypass.")
        match = expression["match"]
        require(
            set(match) == {"op", "left", "right"} and match["op"] == "==",
            "Unsupported generated match.",
        )
        left, right = match["left"], match["right"]
        if left == {"meta": {"key": "l4proto"}}:
            require(
                not explicit_protocol and type(right) is int and right == 17,
                "Unexpected generated protocol.",
            )
            explicit_protocol = True
            continue
        require(
            set(left) == {"payload"} and set(left["payload"]) == {"protocol", "field"},
            "Unexpected forward predicate or conntrack bypass.",
        )
        protocol, field = left["payload"]["protocol"], left["payload"]["field"]
        if protocol == "ip" and field in ("saddr", "daddr"):
            key = "source" if field == "saddr" else "destination"
            if isinstance(right, dict):
                require(
                    set(right) == {"prefix"} and right["prefix"]["len"] == 32,
                    "Generated admission prefix is not an exact host.",
                )
                right = right["prefix"]["addr"]
            value = str(ipaddress.IPv4Address(right))
        else:
            require(
                protocol == "udp"
                and field in ("sport", "dport")
                and type(right) is int
                and 0 <= right < 65536,
                "Unexpected generated UDP match.",
            )
            key, value = ("sourcePort" if field == "sport" else "destinationPort"), right
        require(key not in result, "Duplicate generated match predicate.")
        result[key] = value
    require(
        set(result) == {"id", "source", "destination", "sourcePort", "destinationPort"},
        "Missing generated header predicate.",
    )
    return {**result, "protocol": 17}


def canonical_table(document):
    objects = document["nftables"]
    require(
        isinstance(objects, list)
        and all(isinstance(item, dict) and len(item) == 1 for item in objects),
        "Invalid native nftables object sequence.",
    )
    meta = [item["metainfo"] for item in objects if "metainfo" in item]
    tables = [item["table"] for item in objects if "table" in item]
    chains = [item["chain"] for item in objects if "chain" in item]
    rules = [item["rule"] for item in objects if "rule" in item]
    require(
        len(objects) == len(meta) + len(tables) + len(chains) + len(rules)
        and len(meta) == len(tables) == len(chains) == 1,
        "Unexpected extra nftables objects.",
    )
    require(
        meta[0]["version"] == "1.1.3"
        and type(meta[0]["json_schema_version"]) is int
        and meta[0]["json_schema_version"] == 1,
        "Unexpected nftables producer version.",
    )
    require(
        {key: value for key, value in tables[0].items() if key != "handle"}
        == {"family": "ip", "name": "netlib"},
        "Unexpected generated table.",
    )
    require(
        {key: value for key, value in chains[0].items() if key != "handle"}
        == {
            "family": "ip",
            "table": "netlib",
            "name": "forward",
            "type": "filter",
            "hook": "forward",
            "prio": 0,
            "policy": "drop",
        },
        "Forward chain must be priority zero and deny by default.",
    )
    return [canonical_rule(rule) for rule in rules]


def check_ruleset(document, table, packets, byte_count):
    objects = document["nftables"]
    netlib = [
        item
        for item in objects
        if "metainfo" in item
        or ("table" in item and item["table"]["name"] == "netlib")
        or ("chain" in item and item["chain"]["table"] == "netlib")
        or ("rule" in item and item["rule"]["table"] == "netlib")
    ]
    require({"nftables": netlib} == table, "Table export contradicts the complete native ruleset.")
    remaining = [item for item in objects if item not in netlib]
    require(
        len(remaining) == 3
        and set(remaining[0]) == {"table"}
        and set(remaining[1]) == {"chain"}
        and set(remaining[2]) == {"rule"},
        "Unexpected extra native hooks or rules.",
    )
    tracking_table, chain, rule = remaining[0]["table"], remaining[1]["chain"], remaining[2]["rule"]
    require(
        {key: value for key, value in tracking_table.items() if key != "handle"}
        == {"family": "ip", "name": "netlib_tracking"},
        "Unexpected tracking table.",
    )
    require(
        {key: value for key, value in chain.items() if key != "handle"}
        == {
            "family": "ip",
            "table": "netlib_tracking",
            "name": "prerouting",
            "type": "filter",
            "hook": "prerouting",
            "prio": -199,
            "policy": "accept",
        },
        "Tracking instrumentation changed its hook.",
    )
    require(
        set(rule) == {"family", "table", "chain", "handle", "expr"}
        and rule["family"] == "ip"
        and rule["table"] == "netlib_tracking"
        and rule["chain"] == "prerouting"
        and len(rule["expr"]) == 2,
        "Unexpected tracking rule or terminal verdict.",
    )
    require(
        rule["expr"][0]
        == {"match": {"op": "==", "left": {"ct": {"key": "state"}}, "right": {"set": [2, 8]}}},
        "Tracking instrumentation must only count new and established packets.",
    )
    counter = rule["expr"][1]
    require(
        set(counter) == {"counter"}
        and set(counter["counter"]) == {"packets", "bytes"}
        and all(type(value) is int for value in counter["counter"].values())
        and counter["counter"] == {"packets": packets, "bytes": byte_count},
        "Tracking counters contradict the captured ingress packets.",
    )


def decode_packet(row):
    require(isinstance(row.get("hex"), str), "Missing raw Ethernet bytes.")
    frame = bytes.fromhex(row["hex"])
    require(
        len(frame) >= 42 and frame[12:14] == b"\x08\x00" and frame[14] == 0x45,
        "Malformed Ethernet IPv4 frame.",
    )
    header = frame[14:34]
    size = int.from_bytes(header[2:4], "big")
    require(
        28 <= size <= len(frame) - 14
        and header[9] == 17
        and int.from_bytes(header[6:8], "big") & 0x3FFF == 0,
        "Invalid IPv4 length, protocol, or fragmentation.",
    )
    checksum = sum(int.from_bytes(header[index : index + 2], "big") for index in range(0, 20, 2))
    while checksum >> 16:
        checksum = (checksum & 65535) + (checksum >> 16)
    require(checksum == 65535, "Invalid IPv4 header checksum.")
    udp = frame[34 : 14 + size]
    require(int.from_bytes(udp[4:6], "big") == len(udp), "UDP length contradicts the IPv4 payload.")
    packet = {
        "source": str(ipaddress.IPv4Address(header[12:16])),
        "destination": str(ipaddress.IPv4Address(header[16:20])),
        "protocol": 17,
        "sourcePort": int.from_bytes(udp[:2], "big"),
        "destinationPort": int.from_bytes(udp[2:4], "big"),
    }
    require(packet in (REQUEST, REPLY), "Captured packet has a different selected tuple.")
    source, destination = frame[6:12].hex(":"), frame[:6].hex(":")
    interface, kind = row["interface"], row["packetType"]
    require(type(kind) is int, "Invalid AF_PACKET direction.")
    if packet == REQUEST:
        valid = (interface, kind, source, destination) in (
            ("auth0", 0, eap.PEER, eap.AUTHENTICATOR),
            ("service0", 4, SERVICE, SERVER),
        )
    else:
        valid = (interface, kind, source, destination) in (
            ("service0", 0, SERVER, SERVICE),
            ("auth0", 4, eap.AUTHENTICATOR, eap.PEER),
        )
    require(valid, "Packet tuple, interface, MAC role, or direction disagreement.")
    require(header[8] == (64 if kind == 0 else 63), "Gateway forwarding TTL disagreement.")
    return {
        "raw": row["hex"],
        "timeNs": row["timeNs"],
        "interface": interface,
        "packetType": kind,
        "packet": packet,
        "payload": udp[8:].decode("ascii"),
        "ipId": int.from_bytes(header[4:6], "big"),
        "ipLength": size,
        "ttl": header[8],
        "paddingHex": frame[14 + size :].hex(),
    }


def check_network(directory):
    profiles = {
        "peer": {"peer0": (eap.PEER, "192.0.2.2")},
        "auth": {"auth0": (eap.AUTHENTICATOR, "192.0.2.1"), "service0": (SERVICE, "198.51.100.1")},
        "server": {"server0": (SERVER, "198.51.100.2")},
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
        },
    }
    neighbors = {
        "peer": {("192.0.2.1", "peer0", eap.AUTHENTICATOR)},
        "auth": {("192.0.2.2", "auth0", eap.PEER), ("198.51.100.2", "service0", SERVER)},
        "server": {("198.51.100.1", "server0", SERVICE)},
    }
    for namespace, interfaces in profiles.items():
        links = read_json(directory / f"{namespace}-links.json")
        require(
            {row["ifname"] for row in links} == {"lo", *interfaces}
            and len(links) == len(interfaces) + 1,
            "Unexpected native namespace link inventory.",
        )
        for row in links:
            if row["ifname"] != "lo":
                require(
                    row["address"] == interfaces[row["ifname"]][0] and "UP" in row["flags"],
                    "Native link MAC or state disagreement.",
                )
        addresses = read_json(directory / f"{namespace}-addresses.json")
        actual_addresses = {
            (row["ifname"], item["family"], item["local"], item["prefixlen"])
            for row in addresses
            if row["ifname"] != "lo"
            for item in row["addr_info"]
        }
        require(
            actual_addresses == {(name, "inet", pair[1], 24) for name, pair in interfaces.items()},
            "Native interface address disagreement.",
        )
        exported_routes = read_json(directory / f"{namespace}-routes.json")
        require(
            len(exported_routes) == len(routes[namespace])
            and all(
                set(row) <= {"dst", "dev", "gateway", "prefsrc", "protocol", "scope", "flags"}
                and row["flags"] == []
                for row in exported_routes
            )
            and {
                (row["dst"], row["dev"], row.get("gateway"), row.get("prefsrc"))
                for row in exported_routes
            }
            == routes[namespace],
            "Native route export contradicts the selected gateway path.",
        )
        exported_neighbors = read_json(directory / f"{namespace}-neighbors.json")
        require(
            len(exported_neighbors) == len(neighbors[namespace])
            and all(row["state"] == ["PERMANENT"] for row in exported_neighbors)
            and {(row["dst"], row["dev"], row["lladdr"]) for row in exported_neighbors}
            == neighbors[namespace],
            "Native neighbor identity disagreement.",
        )
        settings = dict(
            line.split(" = ", 1)
            for line in (directory / f"{namespace}-settings.txt").read_text().splitlines()
        )
        require(
            set(settings)
            == {
                "net.ipv4.ip_forward",
                "net.ipv6.conf.all.disable_ipv6",
                "net.ipv6.conf.default.disable_ipv6",
            }
            and settings["net.ipv4.ip_forward"] in ("0", "1")
            and settings["net.ipv6.conf.all.disable_ipv6"]
            == settings["net.ipv6.conf.default.disable_ipv6"]
            == "1"
            and (namespace != "auth" or settings["net.ipv4.ip_forward"] == "1"),
            "Native forwarding or IPv6 isolation setting disagreement.",
        )
    for namespace in ("auth", "peer"):
        require(
            (directory / "eap" / f"{namespace}-links.json").read_bytes()
            == (directory / f"{namespace}-links.json").read_bytes(),
            "EAP link export contradicts the gateway link inventory.",
        )


def check_eap(directory, metadata):
    require(
        metadata["name"] == "success"
        and type(metadata["phaseId"]) is int
        and metadata["phaseId"] == 1,
        "Unexpected EAP collector phase.",
    )
    interval(metadata)
    require(
        metadata["authenticatorCommand"]
        == [
            "ip",
            "netns",
            "exec",
            "auth",
            "hostapd",
            "-dd",
            "/tmp/netlib-admission/eap/hostapd.conf",
        ]
        and metadata["supplicantCommand"]
        == [
            "ip",
            "netns",
            "exec",
            "peer",
            "wpa_supplicant",
            "-dd",
            "-D",
            "wired",
            "-i",
            "peer0",
            "-c",
            "/tmp/netlib-admission/eap/success-supplicant.conf",
        ],
        "Unexpected native EAP producer command.",
    )
    eap.configuration(directory)
    fingerprints = {
        "ca": eap.certificate(directory, "ca", "Netlib private EAP test CA"),
        "server": eap.certificate(directory, "server", eap.SERVER, ("DNS", eap.SERVER)),
        "client": eap.certificate(directory, "client", eap.SUBJECT, ("email", eap.SUBJECT)),
    }
    phase = eap.check_phase(directory, metadata, fingerprints)
    status = (directory / "supplicant-status.txt").read_text()
    require(
        all(
            line in status.splitlines()
            for line in (
                "suppPortStatus=Authorized",
                "EAP state=SUCCESS",
                "selectedMethod=13 (EAP-TLS)",
                "eap_tls_version=TLSv1.3",
                "tls_session_reused=0",
                f"address={eap.PEER}",
            )
        ),
        "Native TLS or logical authorization status disagreement.",
    )
    before, after = [
        (directory / name).read_text()
        for name in ("authorized-station.txt", "logged-off-station.txt")
    ]
    require(
        before.startswith(eap.PEER + "\nflags=[AUTHORIZED]\n")
        and "dot1xAuthAuthControlledPortStatus=1\n" in before
        and after.startswith(eap.PEER + "\nflags=\n")
        and "dot1xAuthAuthControlledPortStatus=2\n" in after
        and "dot1xAuthEapolLogoffFramesRx=1\n" in after,
        "Native EAP Logoff authorization state disagreement.",
    )
    return {
        "schema": 1,
        "scope": "checked-native-eap-evidence",
        "link": {"authenticator": eap.AUTHENTICATOR, "peer": eap.PEER},
        "subject": eap.SUBJECT,
        "outerIdentity": eap.OUTER,
        "method": 13,
        "phases": [phase],
        "frameCount": len(phase["frames"]),
        "certificateSHA256": fingerprints,
    }


def socket_observation(row, stage, expected):
    interval(row, stage)
    require(
        row["result"] == expected,
        "Native UDP socket result contradicts the selected tuple or payload.",
    )


def check_commands(directory, observations):
    commands = read_json(directory / "commands.json")
    previous_end = 0
    for record in commands:
        interval(record)
        require(
            record["startNs"] > previous_end
            and type(record["returncode"]) is int
            and record["returncode"] == 0
            and record["stderr"] == "",
            "Native command history has unordered or failed producer records.",
        )
        previous_end = record["endNs"]

    def records(command):
        return [row for row in commands if row["command"] == command]

    def copied(row):
        original = {
            key: row[key]
            for key in ("command", "startNs", "endNs", "returncode", "stdout", "stderr")
        }
        require(
            sum(record == original for record in commands) == 1,
            "Native observation contradicts its command-history record.",
        )

    for name in ("credentialInstall", "logoff"):
        copied(observations[name])
    for stage in observations["stages"]:
        copied(stage["snapshot"])
        if stage["load"] is not None:
            copied(stage["load"])
        for filename, arguments in (
            (stage["firewall"], ["list", "table", "ip", "netlib"]),
            (stage["ruleset"], ["list", "ruleset"]),
        ):
            found = [
                row
                for row in records(["ip", "netns", "exec", "auth", "nft", "-j", "-nn", *arguments])
                if stage["client"]["endNs"]
                < row["startNs"]
                < row["endNs"]
                < stage["snapshot"]["startNs"]
            ]
            require(
                len(found) == 1 and found[0]["stdout"] == (directory / filename).read_text(),
                "Native firewall export command stdout or observation interval contradicts the saved snapshot.",
            )
    nft_commands = [
        row for row in commands if row["command"][:5] == ["ip", "netns", "exec", "auth", "nft"]
    ]
    require(len(nft_commands) == 12, "Unexpected extra native firewall mutation or export command.")
    for namespace in ("peer", "auth", "server"):
        for kind, arguments in (
            ("links", ["link", "show"]),
            ("addresses", ["address", "show"]),
            ("routes", ["-4", "route", "show"]),
            ("neighbors", ["neigh", "show"]),
        ):
            found = records(["ip", "-n", namespace, "-j", *arguments])
            require(
                len(found) == 1
                and found[0]["stdout"] == (directory / f"{namespace}-{kind}.json").read_text(),
                "Native network export command stdout contradicts the saved configuration.",
            )
        found = records(
            [
                "ip",
                "netns",
                "exec",
                namespace,
                "sysctl",
                "net.ipv4.ip_forward",
                "net.ipv6.conf.all.disable_ipv6",
                "net.ipv6.conf.default.disable_ipv6",
            ]
        )
        require(
            len(found) == 1
            and found[0]["stdout"] == (directory / f"{namespace}-settings.txt").read_text(),
            "Native settings export command stdout disagreement.",
        )
    stations = records(
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
            eap.PEER,
        ]
    )
    status = records(
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
        ]
    )
    require(
        len(stations) == 2 and len(status) == 1,
        "Missing or duplicate native authorization status export.",
    )
    for row, filename in (
        (stations[0], "authorized-station.txt"),
        (stations[1], "logged-off-station.txt"),
        (status[0], "supplicant-status.txt"),
    ):
        require(
            row["stdout"] == (directory / "eap" / filename).read_text(),
            "Native authorization export command stdout contradicts its saved status.",
        )
    require(
        stations[0]["endNs"] < observations["stages"][1]["startNs"]
        and status[0]["endNs"] < observations["stages"][1]["startNs"]
        and observations["logoff"]["endNs"]
        < stations[1]["startNs"]
        < stations[1]["endNs"]
        < observations["stages"][3]["load"]["startNs"],
        "Native authorization status export lies outside its checkpoint.",
    )


def check_capture(directory, *, input_directory=INPUT):
    directory, input_directory = Path(directory), Path(input_directory)
    observations = read_json(directory / "observations.json")
    require(
        type(observations["schema"]) is int
        and observations["schema"] == 1
        and observations["scope"] == "wired-gateway-session-admission",
        "Invalid admission capture schema.",
    )
    check_network(directory)
    for name in ("requirements", "deny", "permit", "demo-credential"):
        require(
            (directory / "input" / f"{name}.json").read_bytes()
            == (input_directory / f"{name}.json").read_bytes(),
            "Immutable generated policy or credential input disagreement.",
        )
    expected_rules = [{"id": "REQUEST", **REQUEST}, {"id": "REPLY", **REPLY}]
    policies = {
        name: canonical_table(read_json(directory / "input" / f"{name}.json"))
        for name in ("deny", "permit")
    }
    require(
        policies == {"deny": [], "permit": expected_rules},
        "Generated policy does not cover exactly the selected request and reply classes.",
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
        },
        "Declared demo credential changed its scope or principal.",
    )
    require(
        (directory / "installed-demo-credential.json").read_bytes()
        == (directory / "input/demo-credential.json").read_bytes(),
        "Installed local demo credential differs from the controller input.",
    )
    credential_install = observations["credentialInstall"]
    successful_command(
        credential_install,
        [
            "install",
            "-m",
            "0644",
            "/task/admission/input/demo-credential.json",
            "/run/netlib-admission/demo-credential.json",
        ],
    )
    logoff = observations["logoff"]
    successful_command(
        logoff,
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
    )
    require(logoff["stdout"] == "OK\n", "Native EAP Logoff command was not acknowledged.")
    authentication = check_eap(directory / "eap", observations["eap"])
    eap_frames = authentication["phases"][0]["frames"]
    raw = eap.read_lines(directory / "data-frames.jsonl", observations["eap"])
    packets = [
        dict(decode_packet(row), source=f"data-frames.jsonl:{index}")
        for index, row in enumerate(raw, 1)
    ]
    stages = observations["stages"]
    require(
        len(stages) == 4 and [stage["stage"] for stage in stages] == list(STAGES),
        "Missing, duplicate, or reordered admission stage.",
    )
    require(
        all(
            eap_frames[0]["timeNs"] <= source["timeNs"] < stages[1]["startNs"]
            for source in authentication["phases"][0]["methodEvidence"]["source"]
        ),
        "Native method evidence is outside its authenticated checkpoint.",
    )
    reports, seen_packets, seen_bytes, previous_end, old_row = [], 0, 0, 0, None
    for index, stage in enumerate(stages):
        name, permitted = stage["stage"], index == 2
        interval(stage, observations["eap"])
        require(previous_end < stage["startNs"], "Admission stage windows overlap.")
        previous_end = stage["endNs"]
        require(
            stage["policy"] == ("permit" if permitted else "deny"),
            "Admission stage policy disagreement.",
        )
        request = {key: value for key, value in REQUEST.items() if key != "protocol"}
        reply = {key: value for key, value in REPLY.items() if key != "protocol"}
        request["payload"], reply["payload"] = (
            f"admission:{name}:request",
            f"admission:{name}:reply",
        )
        socket_observation(stage["sent"], stage, request)
        socket_observation(stage["server"], stage, request if permitted else None)
        socket_observation(stage["client"], stage, reply if permitted else None)
        require(
            stage["sent"]["endNs"] <= stage["server"]["startNs"],
            "UDP receive begins before the socket send completed.",
        )
        if permitted:
            socket_observation(stage["reply"], stage, reply)
            require(
                stage["server"]["endNs"]
                <= stage["reply"]["startNs"]
                < stage["reply"]["endNs"]
                <= stage["client"]["startNs"],
                "Native request/reply socket order disagrees.",
            )
        else:
            require(
                stage["reply"] is None
                and stage["server"]["endNs"] <= stage["client"]["startNs"]
                and all(
                    stage[key]["endNs"] - stage[key]["startNs"] >= 200_000_000
                    for key in ("server", "client")
                ),
                "Denied traffic lacks the measured server and client timeout windows.",
            )
        frame_group = [
            packet for packet in packets if stage["startNs"] < packet["timeNs"] < stage["endNs"]
        ]
        expected = [("auth0", 0, REQUEST, request["payload"])]
        if permitted:
            expected += [
                ("service0", 4, REQUEST, request["payload"]),
                ("service0", 0, REPLY, reply["payload"]),
                ("auth0", 4, REPLY, reply["payload"]),
            ]
        actual = [
            (packet["interface"], packet["packetType"], packet["packet"], packet["payload"])
            for packet in frame_group
        ]
        require(
            len(actual) == len(expected) and all(actual.count(item) == 1 for item in expected),
            "Raw packet count, interface visits, tuple, or payload contradicts the native socket result.",
        )
        require(
            all(packet["timeNs"] >= stage["sent"]["startNs"] for packet in frame_group),
            "Captured packet precedes its socket send.",
        )
        for direction in (REQUEST, REPLY) if permitted else (REQUEST,):
            group = [packet for packet in frame_group if packet["packet"] == direction]
            require(
                len({packet["ipId"] for packet in group}) == 1,
                "Ingress and egress IPv4 packet identities disagree.",
            )
        ingress = [packet for packet in frame_group if packet["packetType"] == 0]
        seen_packets += len(ingress)
        seen_bytes += sum(packet["ipLength"] for packet in ingress)
        require(
            stage["firewall"] == f"{name}-firewall.json"
            and stage["ruleset"] == f"{name}-ruleset.json"
            and stage["conntrack"] == f"{name}-conntrack.json",
            "Native stage artifact binding disagreement.",
        )
        firewall = read_json(directory / stage["firewall"])
        require(
            canonical_table(firewall) == policies[stage["policy"]],
            "Active native forward policy contradicts the generated policy.",
        )
        check_ruleset(read_json(directory / stage["ruleset"]), firewall, seen_packets, seen_bytes)
        load = stage["load"]
        if index == 1:
            require(
                load is None, "Unexpected policy load before the local credential installation."
            )
        else:
            successful_command(
                load,
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
                load["endNs"] < stage["startNs"]
                and load["input"] == f"input/{stage['policy']}.json"
                and load["batch"] == f"{name}-load.json",
                "Native policy load is late or misbound.",
            )
            source_objects = read_json(directory / load["input"])["nftables"]
            expected_objects = (
                source_objects
                if index == 0
                else [
                    source_objects[0],
                    {"delete": {"table": {"family": "ip", "name": "netlib"}}},
                    *source_objects[1:],
                ]
            )
            require(
                read_json(directory / load["batch"]) == {"nftables": expected_objects},
                "Applied transaction changed the immutable generated policy.",
            )
        snapshot = stage["snapshot"]
        successful_command(
            snapshot,
            [
                "ip",
                "netns",
                "exec",
                "auth",
                "python3",
                "/task/capture_conntrack.py",
                "--output",
                f"/tmp/netlib-admission/{name}-conntrack.json",
            ],
        )
        interval(snapshot, stage)
        require(
            stage["client"]["endNs"] < snapshot["startNs"],
            "Conntrack snapshot precedes the measured UDP outcome.",
        )
        document = read_json(directory / stage["conntrack"])
        require(
            type(document["schema"]) is int and type(document["family"]) is int,
            "Invalid conntrack snapshot schema.",
        )
        try:
            entries = lifecycle.decode_snapshot(document)
        except ValueError as error:
            raise EvidenceError(f"Conntrack raw evidence: {error}") from error
        if index < 2:
            require(
                not entries, "Denied unconfirmed traffic unexpectedly has a cached visible flow."
            )
            row = None
        else:
            require(len(entries) == 1, "Missing or extra retained cached UDP flow.")
            row = entries[0]
            require(
                row["original"] == REQUEST
                and row["reply"] == REPLY
                and row["originalZone"] == row["replyZone"] == 0
                and row["status"] == 10
                and type(row["id"]) is int
                and row["remainingTTL"] > 0,
                "Cached flow tuple, direction, confirmation, or reply evidence disagreement.",
            )
            if old_row:
                require(
                    row["id"] == old_row["id"] and row["remainingTTL"] <= old_row["remainingTTL"],
                    "Logoff did not retain the same cached flow identity.",
                )
            old_row = row
        before = sum(frame["timeNs"] < stage["sent"]["startNs"] for frame in eap_frames)
        require(
            before == (0, 16, 16, 18)[index], "EAP checkpoint does not match the native UDP stage."
        )
        reports.append(
            {
                "name": name,
                "eapFramesBeforeSend": before,
                "firewallFile": stage["firewall"],
                "rulesetFile": stage["ruleset"],
                "conntrackFile": stage["conntrack"],
                "credentialInstalled": index >= 2,
                "delivered": permitted,
                "window": {"startNs": stage["startNs"], "endNs": stage["endNs"]},
                "observations": stage,
                "dataFrames": frame_group,
                "cachedRow": row,
            }
        )
    require(
        sum(len(stage["dataFrames"]) for stage in reports) == len(packets) == 7,
        "Extra raw data packet outside the four measured stages.",
    )
    require(
        stages[1]["endNs"]
        < credential_install["startNs"]
        < credential_install["endNs"]
        < stages[2]["load"]["startNs"]
        and stages[2]["endNs"] < logoff["startNs"] < logoff["endNs"] < stages[3]["load"]["startNs"],
        "Credential installation, permit load, or Logoff cutover order disagrees.",
    )
    logoff_frame = eap_frames[authentication["phases"][0]["logoffFrame"] - 1]
    require(
        logoff["startNs"] <= logoff_frame["timeNs"] < stages[3]["load"]["startNs"],
        "Deny policy was not installed after the captured EAPOL Logoff.",
    )
    check_commands(directory, observations)
    return {
        "schema": 1,
        "scope": "checked-native-session-firewall-evidence",
        "eapEvidence": authentication,
        "credential": credential,
        "credentialInstall": credential_install,
        "logoff": logoff,
        "stages": reports,
        "frameCount": len(packets),
        "eapFrameCount": len(eap_frames),
        "limits": [
            "finite-private-wired-gateway-capture",
            "declared-local-demo-credential-not-a-network-signature",
            "trusted-native-TLS-and-certificate-policy",
            "current-round-link-and-header-attribution-assumptions",
            "no-offline-TLS-cryptographic-verification",
            "no-global-instantaneous-update-or-anti-spoofing-proof",
            "no-capture-authenticity-or-kernel-refinement-proof",
        ],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture-dir", type=Path, default=INPUT / "native")
    parser.add_argument("--input-dir", type=Path, default=INPUT)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = check_capture(args.capture_dir, input_directory=args.input_dir)
        if args.output:
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(
            f"Verified {report['frameCount']} IPv4 frames, {report['eapFrameCount']} EAPOL frames, and four admission stages."
        )
    except (ValueError, OSError, KeyError, TypeError, IndexError, OverflowError) as error:
        print(f"admission evidence: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
