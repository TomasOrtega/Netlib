"""Capture valid socket UDP bytes and intentionally malformed raw probes."""

import ctypes
import fcntl
import importlib.util
import ipaddress
import json
import signal
import socket
import struct
import subprocess
import sys
import time
from pathlib import Path

OUTPUT = Path("/tmp/netlib-admission")
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


def admission_helper():
    spec = importlib.util.spec_from_file_location(
        "admission_capture_helper", "/task/admission/exercise.py"
    )
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    return helper


def offload(interface):
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    operations = []

    def control(command, value=0):
        data = ctypes.create_string_buffer(struct.pack("II", command, value))
        request = struct.pack("16sP", interface.encode("ascii"), ctypes.addressof(data)) + bytes(16)
        start = time.monotonic_ns()
        fcntl.ioctl(sock.fileno(), 0x8946, request)
        result = struct.unpack("II", data.raw[:8])[1]
        operations.append(
            {
                "command": command,
                "requested": value,
                "result": result,
                "startNs": start,
                "endNs": time.monotonic_ns(),
            }
        )
        return result

    before, after = {}, {}
    for name, (get, set_) in FEATURES.items():
        before[name] = control(get)
        control(set_, 0)
        after[name] = control(get)
        if after[name] != 0:
            raise RuntimeError(f"Offload remains enabled: {interface}/{name}")
    sock.close()
    print(
        json.dumps(
            {"interface": interface, "before": before, "after": after, "operations": operations}
        )
    )


def checksum(data):
    if len(data) % 2:
        data += b"\0"
    value = sum(struct.unpack(f"!{len(data) // 2}H", data))
    while value >> 16:
        value = (value & 65535) + (value >> 16)
    return (~value) & 65535


def probe_frame(name, index):
    payload = f"wire-probe:{name}".encode("ascii")
    source, destination = (
        ipaddress.IPv4Address("192.0.2.2").packed,
        ipaddress.IPv4Address("198.51.100.2").packed,
    )
    udp_size = 8 + len(payload)
    declared_size = 7 if name == "udp-short-length" else udp_size
    udp = struct.pack("!HHHH", 41000, 9000, declared_size, 0) + payload
    pseudo = source + destination + struct.pack("!BBH", 0, 17, udp_size)
    udp_checksum = checksum(pseudo + udp) or 65535
    if name == "udp-zero-omitted":
        udp_checksum = 0
    elif name == "udp-bad-checksum":
        udp_checksum ^= 1
    udp = udp[:6] + struct.pack("!H", udp_checksum) + udp[8:]
    header = struct.pack(
        "!BBHHHBBH4s4s",
        0x45,
        0,
        20 + udp_size,
        0xF000 + index,
        0x4000,
        64,
        17,
        0,
        source,
        destination,
    )
    ip_checksum = checksum(header)
    if name == "ipv4-bad-checksum":
        ip_checksum ^= 1
    header = header[:10] + struct.pack("!H", ip_checksum) + header[12:]
    ethernet = bytes.fromhex("02000000ea0102000000ea020800")
    return ethernet + header + udp


def raw_send(path):
    document = json.loads(Path(path).read_text())
    frame = bytes.fromhex(document["raw"])
    sock = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(3))
    sock.bind(("peer0", 0))
    start = time.monotonic_ns()
    sent = sock.send(frame)
    result = {"startNs": start, "endNs": time.monotonic_ns(), "raw": frame.hex(), "bytesSent": sent}
    sock.close()
    print(json.dumps(result))


def capture():
    helper = admission_helper()
    original_setup = helper.setup
    settings = []

    def setup():
        original_setup()
        for namespace, interface in (
            ("peer", "peer0"),
            ("auth", "auth0"),
            ("auth", "service0"),
            ("server", "server0"),
        ):
            record = helper.run(
                "ip",
                "netns",
                "exec",
                namespace,
                "python3",
                "/task/wire/exercise.py",
                "offload",
                interface,
            )
            settings.append(
                {"namespace": namespace, "command": record, **json.loads(record["stdout"])}
            )
        helper.save("offloads.json", settings)

    helper.setup = setup
    helper.capture()
    admission_commands = json.loads((OUTPUT / "commands.json").read_text())
    helper.COMMANDS = []
    load = helper.load_policy("wire-probes", "permit", True)
    exports = {}
    for kind, arguments in (
        ("firewall", ("list", "table", "ip", "netlib")),
        ("ruleset", ("list", "ruleset")),
    ):
        record = helper.native("nft", "-j", "-nn", *arguments)
        filename = f"wire-probes-{kind}.json"
        (OUTPUT / filename).write_text(record["stdout"])
        exports[kind] = {"file": filename, "command": record}
    sniffer = subprocess.Popen(
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "python3",
            "/task/wire/exercise.py",
            "sniff-probes",
            str(OUTPUT / "probe-frames.jsonl"),
        ]
    )
    receiver = helper.Endpoint("server", "198.51.100.2")
    probes = []
    try:
        time.sleep(0.2)
        for index, name in enumerate(PROBES):
            start = time.monotonic_ns()
            frame = probe_frame(name, index)
            source = OUTPUT / f"probe-{name}-input.json"
            source.write_text(json.dumps({"name": name, "raw": frame.hex()}, indent=2) + "\n")
            sender = helper.run(
                "ip",
                "netns",
                "exec",
                "peer",
                "python3",
                "/task/wire/exercise.py",
                "raw-send",
                str(source),
            )
            received = receiver.call("receive", timeout=0.25)
            expected = name in ("raw-valid", "udp-zero-omitted")
            if (received["result"] is not None) != expected:
                raise RuntimeError(f"Unexpected native UDP receive result: {name}")
            time.sleep(0.03)
            probes.append(
                {
                    "name": name,
                    "startNs": start,
                    "endNs": time.monotonic_ns(),
                    "input": source.name,
                    "sender": sender,
                    "receiver": received,
                }
            )
    finally:
        receiver.close()
        sniffer.send_signal(signal.SIGTERM)
        sniffer.wait(timeout=5)
    helper.save(
        "probe-observations.json", {"schema": 1, "load": load, "exports": exports, "probes": probes}
    )
    helper.save("probe-commands.json", helper.COMMANDS)
    helper.save("commands.json", admission_commands)


if __name__ == "__main__":
    if sys.argv[1] == "offload":
        offload(sys.argv[2])
    elif sys.argv[1] == "raw-send":
        raw_send(sys.argv[2])
    elif sys.argv[1] == "sniff-probes":
        admission_helper().sniff_data(sys.argv[2])
    else:
        capture()
