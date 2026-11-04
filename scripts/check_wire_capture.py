"""Validate fresh IPv4/UDP bytes, offload readbacks, and native failure probes."""

import argparse
import ipaddress
import json
import re
import sys
from pathlib import Path

import check_admission_capture as admission
import check_eap_capture as eap

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/wire"
EvidenceError = admission.EvidenceError
require = admission.require
FEATURES = {
    "txChecksum": (0x16, 0x17),
    "tso": (0x1E, 0x1F),
    "gso": (0x23, 0x24),
    "gro": (0x2B, 0x2C),
}
PROBES = (
    "raw-valid",
    "udp-zero-omitted",
    "udp-bad-checksum",
    "udp-short-length",
    "ipv4-bad-checksum",
)


def folded_sum(data):
    total = 0
    for index in range(0, len(data), 2):
        total += data[index] << 8
        if index + 1 < len(data):
            total += data[index + 1]
    while total > 65535:
        total = (total & 65535) + (total >> 16)
    return total


def inspect_frame(raw):
    require(
        isinstance(raw, str) and re.fullmatch(r"(?:[0-9a-fA-F]{2})+", raw),
        "Require hexadecimal byte pairs without separators or whitespace.",
    )
    frame = bytes.fromhex(raw)
    require(len(frame) >= 42 and frame[12:14] == b"\x08\x00", "Unsupported Ethernet IPv4 frame.")
    ip = frame[14:34]
    require(
        ip[0] == 0x45 and ip[9] == 17 and int.from_bytes(ip[6:8], "big") in (0, 0x4000),
        "Unsupported wire profile: require IHL five and unfragmented UDP.",
    )
    size = int.from_bytes(ip[2:4], "big")
    require(28 <= size <= len(frame) - 14, "Invalid IPv4 wire length.")
    udp = frame[34 : 14 + size]
    length, value = int.from_bytes(udp[4:6], "big"), int.from_bytes(udp[6:8], "big")
    ip_valid = folded_sum(ip) == 65535
    length_valid = 8 <= length == len(udp)
    pseudo = ip[12:20] + bytes((0, 17)) + length.to_bytes(2, "big")
    status = (
        "invalid-length"
        if not length_valid
        else "omitted"
        if value == 0
        else "valid"
        if folded_sum(pseudo + udp) == 65535
        else "invalid"
    )
    reason = (
        "ipv4-checksum"
        if not ip_valid
        else "udp-length"
        if not length_valid
        else "udp-checksum"
        if status == "invalid"
        else None
    )
    return {
        "raw": raw,
        "valid": reason is None,
        "reason": reason,
        "header": {
            "source": str(ipaddress.IPv4Address(ip[12:16])),
            "destination": str(ipaddress.IPv4Address(ip[16:20])),
            "protocol": 17,
            "sourcePort": int.from_bytes(udp[:2], "big"),
            "destinationPort": int.from_bytes(udp[2:4], "big"),
        },
        "ipLength": size,
        "udpLength": length,
        "ipId": int.from_bytes(ip[4:6], "big"),
        "ttl": ip[8],
        "ipChecksum": {"value": int.from_bytes(ip[10:12], "big"), "valid": ip_valid},
        "udpChecksum": {"value": value, "status": status},
        "payloadHex": udp[8:].hex(),
        "paddingHex": frame[14 + size :].hex(),
    }


def decode_frame(raw):
    result = inspect_frame(raw)
    require(result["valid"], f"Invalid wire datagram: {result['reason']}.")
    return result


def check_offloads(directory, admission_evidence):
    settings = admission.read_json(directory / "offloads.json")
    commands = admission.read_json(directory / "commands.json")
    expected = (("peer", "peer0"), ("auth", "auth0"), ("auth", "service0"), ("server", "server0"))
    require(
        [(row["namespace"], row["interface"]) for row in settings] == list(expected),
        "Missing or misbound interface offload readback.",
    )
    first_send = admission_evidence["stages"][0]["observations"]["sent"]["startNs"]
    for row in settings:
        command = row["command"]
        admission.successful_command(
            command,
            [
                "ip",
                "netns",
                "exec",
                row["namespace"],
                "python3",
                "/task/wire/exercise.py",
                "offload",
                row["interface"],
            ],
        )
        require(
            sum(record == command for record in commands) == 1 and command["endNs"] < first_send,
            "Offload command is missing, duplicated, or later than the first socket send.",
        )
        response = json.loads(command["stdout"])
        require(
            response == {key: row[key] for key in ("interface", "before", "after", "operations")},
            "Offload readback contradicts its native producer stdout.",
        )
        require(
            set(row["before"]) == set(FEATURES)
            and set(row["after"]) == set(FEATURES)
            and all(type(value) is int and value in (0, 1) for value in row["before"].values())
            and all(type(value) is int and value == 0 for value in row["after"].values()),
            "TX checksum or segmentation offload remains enabled.",
        )
        operations = row["operations"]
        require(len(operations) == 12, "Incomplete ethtool ioctl operation sequence.")
        previous_end = command["startNs"]
        for index, (name, (get, set_)) in enumerate(FEATURES.items()):
            triple = operations[3 * index : 3 * index + 3]
            require(
                [item["command"] for item in triple] == [get, set_, get]
                and [item["result"] for item in triple] == [row["before"][name], 0, 0]
                and all(
                    type(item["requested"]) is int and item["requested"] == 0 for item in triple
                ),
                "Offload getter, setter, or readback values disagree.",
            )
            for item in triple:
                admission.interval(item, command)
                require(
                    item["startNs"] > previous_end and type(item["result"]) is int,
                    "Offload ioctl observations are out of order.",
                )
                previous_end = item["endNs"]
    return settings


def command_copy(record, commands):
    original = {
        key: record[key]
        for key in ("command", "startNs", "endNs", "returncode", "stdout", "stderr")
    }
    require(
        sum(row == original for row in commands) == 1,
        "Wire probe observation contradicts its native command history.",
    )


def expected_forward(raw):
    frame = bytearray.fromhex(raw)
    frame[:12] = bytes.fromhex("02000000eb0202000000eb01")
    frame[22] = 63
    frame[24:26] = bytes(2)
    frame[24:26] = (65535 - folded_sum(frame[14:34])).to_bytes(2, "big")
    return frame.hex()


def check_probes(directory, admission_evidence):
    observations = admission.read_json(directory / "probe-observations.json")
    require(
        type(observations["schema"]) is int and observations["schema"] == 1,
        "Invalid wire probe schema.",
    )
    commands = admission.read_json(directory / "probe-commands.json")
    previous_end = 0
    for command in commands:
        admission.interval(command)
        require(
            command["startNs"] > previous_end
            and type(command["returncode"]) is int
            and command["returncode"] == 0
            and command["stderr"] == "",
            "Invalid or failed native wire probe command.",
        )
        previous_end = command["endNs"]
    require(len(commands) == 8, "Unexpected extra wire probe command.")
    probes = observations["probes"]
    require(
        [probe["name"] for probe in probes] == list(PROBES),
        "Missing, duplicate, or reordered native wire probe.",
    )
    load = observations["load"]
    admission.successful_command(
        load,
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "nft",
            "-j",
            "-f",
            "/tmp/netlib-admission/wire-probes-load.json",
        ],
    )
    command_copy(load, commands)
    require(
        admission_evidence["eapEvidence"]["phases"][0]["window"]["endNs"] < load["startNs"]
        and load["input"] == "input/permit.json"
        and load["batch"] == "wire-probes-load.json",
        "The separate raw-probe permit load is misbound to the admission episode.",
    )
    source = admission.read_json(directory / "input/permit.json")["nftables"]
    require(
        admission.read_json(directory / load["batch"])
        == {
            "nftables": [
                source[0],
                {"delete": {"table": {"family": "ip", "name": "netlib"}}},
                *source[1:],
            ]
        },
        "Wire probe load changed the immutable generated permit policy.",
    )
    exports = observations["exports"]
    require(set(exports) == {"firewall", "ruleset"}, "Missing active wire-probe policy export.")
    for kind, arguments in (
        ("firewall", ["list", "table", "ip", "netlib"]),
        ("ruleset", ["list", "ruleset"]),
    ):
        export = exports[kind]
        require(export["file"] == f"wire-probes-{kind}.json", "Misbound active wire-probe export.")
        command = export["command"]
        admission.successful_command(
            command, ["ip", "netns", "exec", "auth", "nft", "-j", "-nn", *arguments]
        )
        command_copy(command, commands)
        require(
            load["endNs"] < command["startNs"] < command["endNs"] < probes[0]["startNs"]
            and command["stdout"] == (directory / export["file"]).read_text(),
            "Wire probe export stdout or activation interval disagrees.",
        )
    firewall = admission.read_json(directory / exports["firewall"]["file"])
    require(
        admission.canonical_table(firewall)
        == admission.canonical_table(admission.read_json(directory / "input/permit.json")),
        "Active wire-probe firewall contradicts the generated permit policy.",
    )
    ingress = [
        frame
        for stage in admission_evidence["stages"]
        for frame in stage["dataFrames"]
        if frame["packetType"] == 0
    ]
    admission.check_ruleset(
        admission.read_json(directory / exports["ruleset"]["file"]),
        firewall,
        len(ingress),
        sum(frame["ipLength"] for frame in ingress),
    )
    raw_rows = eap.read_lines(
        directory / "probe-frames.jsonl", {"startNs": load["endNs"], "endNs": probes[-1]["endNs"]}
    )
    decoded = [
        dict(
            inspect_frame(row["hex"]),
            timeNs=row["timeNs"],
            interface=row["interface"],
            packetType=row["packetType"],
            source=f"probe-frames.jsonl:{index}",
        )
        for index, row in enumerate(raw_rows, 1)
    ]
    require(
        all(
            type(frame["packetType"]) is int and frame["interface"] in ("auth0", "service0")
            for frame in decoded
        ),
        "Invalid native probe interface or packet direction.",
    )
    reports, previous_end = [], load["endNs"]
    reasons = (None, None, "udp-checksum", "udp-length", "ipv4-checksum")
    for index, probe in enumerate(probes):
        name = probe["name"]
        admission.interval(probe)
        require(previous_end < probe["startNs"], "Native wire probe windows overlap.")
        previous_end = probe["endNs"]
        require(probe["input"] == f"probe-{name}-input.json", "Misbound raw probe source file.")
        source = admission.read_json(directory / probe["input"])
        require(
            set(source) == {"name", "raw"} and source["name"] == name,
            "Raw probe source label disagrees.",
        )
        sender = probe["sender"]
        admission.successful_command(
            sender,
            [
                "ip",
                "netns",
                "exec",
                "peer",
                "python3",
                "/task/wire/exercise.py",
                "raw-send",
                f"/tmp/netlib-admission/{probe['input']}",
            ],
        )
        command_copy(sender, commands)
        admission.interval(sender, probe)
        sent = json.loads(sender["stdout"])
        admission.interval(sent, sender)
        require(
            sent["raw"] == source["raw"]
            and type(sent["bytesSent"]) is int
            and sent["bytesSent"] == len(bytes.fromhex(source["raw"])),
            "Raw sender bytes or send completion contradicts the generated probe.",
        )
        inspected = inspect_frame(source["raw"])
        require(
            bytes.fromhex(source["raw"])[:12] == bytes.fromhex("02000000ea0102000000ea02"),
            "Raw probe Ethernet peer or authenticator MAC disagrees.",
        )
        expected_status = (
            "omitted"
            if index == 1
            else "invalid"
            if index == 2
            else "invalid-length"
            if index == 3
            else "valid"
        )
        require(
            inspected["reason"] == reasons[index]
            and inspected["udpChecksum"]["status"] == expected_status
            and inspected["header"] == admission.REQUEST
            and inspected["ipId"] == 0xF000 + index
            and inspected["ttl"] == 64
            and inspected["payloadHex"] == f"wire-probe:{name}".encode().hex(),
            "The injected bytes do not represent the declared wire probe.",
        )
        group = [frame for frame in decoded if probe["startNs"] < frame["timeNs"] < probe["endNs"]]
        incoming = [
            frame for frame in group if frame["interface"] == "auth0" and frame["packetType"] == 0
        ]
        outgoing = [
            frame
            for frame in group
            if frame["interface"] == "service0" and frame["packetType"] == 4
        ]
        forwarded = index != 4
        require(
            len(group) == (2 if forwarded else 1)
            and len(incoming) == 1
            and len(outgoing) == int(forwarded),
            "Native ingress or egress count contradicts the wire probe.",
        )
        require(
            incoming[0]["raw"] == source["raw"]
            and all(frame["timeNs"] >= sent["startNs"] for frame in group),
            "Captured ingress bytes or times contradict the actual raw send.",
        )
        if forwarded:
            require(
                outgoing[0]["raw"] == expected_forward(source["raw"]),
                "Forwarded Ethernet, TTL, checksum, or payload bytes disagree.",
            )
        receiver = probe["receiver"]
        admission.interval(receiver, probe)
        require(
            sender["endNs"] < receiver["startNs"],
            "UDP receiver observation precedes the raw send completion.",
        )
        received = index < 2
        expected_result = {
            key: value for key, value in admission.REQUEST.items() if key != "protocol"
        }
        expected_result["payload"] = f"wire-probe:{name}"
        require(
            receiver["result"] == (expected_result if received else None),
            "Native UDP socket outcome contradicts the wire checksum or length probe.",
        )
        require(
            received or receiver["endNs"] - receiver["startNs"] >= 200_000_000,
            "Malformed UDP probe lacks a measured socket timeout.",
        )
        reports.append(
            {
                "name": name,
                "valid": inspected["valid"],
                "reason": inspected["reason"],
                "forwarded": forwarded,
                "received": received,
                "ingress": incoming[0],
                "egress": outgoing[0] if forwarded else None,
                "observations": probe,
            }
        )
    require(
        sum(1 + int(row["forwarded"]) for row in reports) == len(decoded) == 9,
        "Unexpected raw frame outside the five native wire probes.",
    )
    return reports, len(decoded)


def check_capture(directory, *, input_directory=DIRECTORY):
    directory = Path(directory)
    admission_evidence = admission.check_capture(directory, input_directory=input_directory)
    settings = check_offloads(directory, admission_evidence)
    frames = []
    for stage in admission_evidence["stages"]:
        for raw in stage["dataFrames"]:
            decoded = decode_frame(raw["raw"])
            require(
                decoded["udpChecksum"]["status"] == "valid"
                and decoded["udpChecksum"]["value"] != 0
                and decoded["header"] == raw["packet"]
                and decoded["payloadHex"] == raw["payload"].encode().hex(),
                "Normal socket datagram lacks a complete nonzero wire UDP checksum or matching header.",
            )
            frames.append(
                {
                    **decoded,
                    **{key: raw[key] for key in ("source", "timeNs", "interface", "packetType")},
                }
            )
    probes, count = check_probes(directory, admission_evidence)
    return {
        "schema": 1,
        "scope": "checked-native-ipv4-udp-wire-evidence",
        "admissionEvidence": admission_evidence,
        "frames": frames,
        "offloads": settings,
        "probes": probes,
        "frameCount": len(frames),
        "eapFrameCount": admission_evidence["eapFrameCount"],
        "probeFrameCount": count,
        "limits": [
            "finite-private-wired-capture",
            "IHL-five-unfragmented-UDP-exact-payload-length-profile",
            "normal-positive-socket-datagrams-with-offload-readback",
            "separate-raw-injected-wire-probes-after-admission-episode",
            "UDP-zero-is-omission-not-checksum-verification",
            "forwarded-invalid-UDP-can-fail-at-the-final-socket",
            "no-TLS-cryptographic-kernel-refinement-or-capture-authenticity-proof",
        ],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture-dir", type=Path, default=DIRECTORY / "native")
    parser.add_argument("--input-dir", type=Path, default=DIRECTORY)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = check_capture(args.capture_dir, input_directory=args.input_dir)
        if args.output:
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(
            f"Verified {report['frameCount']} complete UDP wire frames, {report['eapFrameCount']} EAPOL frames, and five native wire probes."
        )
    except (ValueError, OSError, KeyError, TypeError, IndexError, OverflowError) as error:
        print(f"wire evidence: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
