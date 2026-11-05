"""Capture ordered IPv4 fragment arrivals and native pre-conntrack reassembly."""

import importlib.util
import ipaddress
import json
import os
import shutil
import socket
import struct
import subprocess
import sys
import time
from pathlib import Path

OUTPUT = Path("/tmp/netlib-admission")
TASK = "/task/reassembly/exercise.py"


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def checksum(data):
    if len(data) % 2:
        data += bytes(1)
    total = sum(
        int.from_bytes(data[offset : offset + 2], "big") for offset in range(0, len(data), 2)
    )
    while total >> 16:
        total = (total & 65535) + (total >> 16)
    return (~total) & 65535


def udp(payload):
    source = ipaddress.IPv4Address("192.0.2.2").packed
    destination = ipaddress.IPv4Address("203.0.113.2").packed
    segment = struct.pack("!HHHH", 41000, 8080, 8 + len(payload), 0) + payload
    pseudo = source + destination + bytes((0, 17)) + len(segment).to_bytes(2, "big")
    return segment[:6] + (checksum(pseudo + segment) or 65535).to_bytes(2, "big") + segment[8:]


def fragment(payload, identifier, offset, more, ttl=64, tos=0, df=False):
    header = struct.pack(
        "!BBHHHBBH4s4s",
        0x45,
        tos,
        20 + len(payload),
        identifier,
        (offset // 8) | (8192 if more else 0) | (16384 if df else 0),
        ttl,
        17,
        0,
        ipaddress.IPv4Address("192.0.2.2").packed,
        ipaddress.IPv4Address("203.0.113.2").packed,
    )
    header = header[:10] + checksum(header).to_bytes(2, "big") + header[12:]
    return (bytes.fromhex("02000000ea0102000000ea020800") + header + payload).hex()


def setup(helper):
    helper.setup()
    for namespace, interface, mtu in (
        ("peer", "peer0", 600),
        ("auth", "auth0", 600),
        ("auth", "service0", 1500),
        ("server", "server0", 1500),
    ):
        helper.run("ip", "-n", namespace, "link", "set", "dev", interface, "mtu", str(mtu))
    for address in ("203.0.113.1/32", "203.0.113.2/32"):
        helper.run("ip", "-n", "auth", "addr", "add", address, "dev", "service0")
    helper.run("ip", "-n", "server", "route", "add", "203.0.113.0/24", "via", "198.51.100.1")
    helper.native(
        "sh",
        "-c",
        "echo 0 > /tmp/netlib-proc/sys/net/ipv4/ipfrag_max_dist; echo 30 > /tmp/netlib-proc/sys/net/ipv4/ipfrag_time; echo 0 > /tmp/netlib-proc/sys/net/ipv4/icmp_errors_use_inbound_ifaddr; echo 0 > /tmp/netlib-proc/sys/net/ipv4/icmp_ratelimit; echo 0 > /tmp/netlib-proc/sys/net/ipv4/icmp_ratemask",
    )
    settings = helper.native(
        "sysctl",
        "net.ipv4.ipfrag_max_dist",
        "net.ipv4.ipfrag_time",
        "net.ipv4.ipfrag_high_thresh",
        "net.ipv4.ip_forward",
        "net.ipv4.icmp_errors_use_inbound_ifaddr",
        "net.ipv4.icmp_ratelimit",
        "net.ipv4.icmp_ratemask",
        "net.ipv4.ip_default_ttl",
    )
    (OUTPUT / "fragment-settings.txt").write_text(settings["stdout"])
    for namespace, interface in (
        ("peer", "peer0"),
        ("auth", "auth0"),
        ("auth", "service0"),
        ("server", "server0"),
    ):
        helper.run(
            "ip",
            "netns",
            "exec",
            namespace,
            "python3",
            "/task/wire/exercise.py",
            "offload",
            interface,
        )
    path = OUTPUT / "instrumentation.nft"
    path.write_text(
        "table ip reassembly_observe {\n"
        " chain trace { type filter hook prerouting priority -452; policy accept; meta l4proto udp meta nftrace set 1; }\n"
        " chain zone { type filter hook prerouting priority -451; policy accept; ct zone set 0; meta mark set 0; }\n"
        ' chain before { type filter hook prerouting priority -450; policy accept; meta l4proto udp meta nftrace set 1; meta l4proto udp counter log prefix "PRE_DEFRAG" group 42 snaplen 65531 queue-threshold 1; }\n'
        ' chain after { type filter hook prerouting priority -300; policy accept; meta l4proto udp counter log prefix "POST_DEFRAG" group 42 snaplen 65531 queue-threshold 1; }\n'
        " chain afterDestination { type filter hook prerouting priority -90; policy accept; }\n"
        " chain beforeSource { type filter hook postrouting priority 90; policy accept; }\n"
        " chain afterSource { type filter hook postrouting priority 110; policy accept; }\n"
        ' chain late { type filter hook postrouting priority 210; policy accept; meta l4proto icmp log prefix "TIMEOUT_EGRESS" group 42 snaplen 65531 queue-threshold 1; }\n'
        " chain input { type filter hook input priority 0; policy drop; }\n"
        "}\n"
        "table ip netlib_nat {\n"
        " chain destination { type nat hook prerouting priority -100; policy accept; ip daddr 203.0.113.2 udp dport 8080 dnat to 198.51.100.2:9000; }\n"
        " chain source { type nat hook postrouting priority 100; policy accept; ip saddr 192.0.2.0/24 ip daddr 198.51.100.2 udp dport 9000 snat to 203.0.113.1:40000; }\n"
        "}\n"
        "table ip netlib_late {\n chain late { type filter hook postrouting priority 200; policy accept; }\n}\n"
    )
    helper.native("nft", "-f", str(path))
    timeout = OUTPUT / "timeout-output.nft"
    timeout.write_text(
        "table ip reassembly_timeout {\n"
        ' chain before { type filter hook output priority -301; policy accept; meta l4proto icmp meta nftrace set 1; meta l4proto icmp ct zone 0 counter comment "TIMEOUT_TEMPLATE_ZONE0"; meta l4proto icmp ct zone 10 counter comment "TIMEOUT_TEMPLATE_ZONE10"; meta l4proto icmp ct zone 20 counter comment "TIMEOUT_TEMPLATE_ZONE20"; meta l4proto icmp log prefix "TIMEOUT_OUTPUT" group 42 snaplen 65531 queue-threshold 1; }\n'
        ' chain tracked { type filter hook output priority -199; policy accept; meta l4proto icmp ct state related counter comment "TIMEOUT_RELATED"; meta l4proto icmp ct state invalid counter comment "TIMEOUT_INVALID"; meta l4proto icmp ct state new counter comment "TIMEOUT_NEW"; meta l4proto icmp ct state established counter comment "TIMEOUT_ESTABLISHED"; meta l4proto icmp ct state untracked counter comment "TIMEOUT_UNTRACKED"; meta l4proto icmp ct zone 0 counter comment "TIMEOUT_AFTER_ZONE0"; meta l4proto icmp ct zone 10 counter comment "TIMEOUT_AFTER_ZONE10"; meta l4proto icmp ct zone 20 counter comment "TIMEOUT_AFTER_ZONE20"; meta l4proto icmp log prefix "TIMEOUT_TRACKED" group 42 snaplen 65531 queue-threshold 1; }\n'
        ' chain output { type filter hook output priority 0; policy drop; meta l4proto icmp icmp type time-exceeded icmp code 1 counter accept comment "ALLOW_REASSEMBLY_TIMEOUT"; }\n'
        "}\n"
    )
    helper.native("nft", "-f", str(timeout))
    return settings


def raw_send(path, interface):
    request = json.loads(Path(path).read_text())
    sock = socket.socket(socket.AF_PACKET, socket.SOCK_RAW)
    sock.bind((interface, 0))
    start = time.monotonic_ns()
    count = sock.send(bytes.fromhex(request["raw"]))
    print(
        json.dumps(
            {
                "startNs": start,
                "endNs": time.monotonic_ns(),
                "raw": request["raw"],
                "bytesSent": count,
            }
        ),
        flush=True,
    )
    sock.close()


def capture():
    helper = module("admission_helper", "/task/admission/exercise.py")
    received = module("received_helper", "/task/received-icmp/exercise.py")
    eap = helper.eap_helper()
    eap.OUTPUT.mkdir(exist_ok=True)
    eap.certificates()
    eap.configurations()
    os.chdir(OUTPUT)
    shutil.copytree(helper.INPUT, OUTPUT / "input", dirs_exist_ok=True)
    settings = setup(helper)
    networks = {}
    for namespace in ("peer", "auth", "server"):
        for kind, arguments in (
            ("links", ("link", "show")),
            ("addresses", ("address", "show")),
            ("routes", ("-4", "route", "show", "table", "main")),
            ("neighbors", ("neigh", "show")),
        ):
            command = helper.run("ip", "-n", namespace, "-j", *arguments)
            filename = f"network-{namespace}-{kind}.json"
            (OUTPUT / filename).write_text(command["stdout"])
            networks[f"{namespace}-{kind}"] = {"file": filename, "command": command}
    trace_stream = (OUTPUT / "trace.txt").open("w")
    trace_errors = (OUTPUT / "trace-errors.txt").open("w")
    trace_command = ["ip", "netns", "exec", "auth", "nft", "monitor", "trace"]
    trace = subprocess.Popen(trace_command, stdout=trace_stream, stderr=trace_errors)
    nflog_command = [
        "ip",
        "netns",
        "exec",
        "auth",
        "python3",
        "/task/reassembly/nflog.py",
        str(OUTPUT / "nflog.jsonl"),
        "42",
    ]
    nflog = subprocess.Popen(nflog_command, stdout=subprocess.PIPE, text=True)
    ready = json.loads(nflog.stdout.readline())
    helper.save("nflog-ready.json", ready)
    eap_start = time.monotonic_ns()
    eap_sniffer = subprocess.Popen(
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "python3",
            "/task/eap_exercise.py",
            "sniff",
            str(eap.OUTPUT / "success-frames.jsonl"),
        ]
    )
    sniffers = [
        subprocess.Popen(
            [
                "ip",
                "netns",
                "exec",
                namespace,
                "python3",
                "/task/received-icmp/exercise.py",
                "sniff",
                str(OUTPUT / f"frames-{namespace}.jsonl"),
                namespace,
                *interfaces,
            ]
        )
        for namespace, interfaces in (
            ("peer", ["peer0"]),
            ("auth", ["auth0", "service0"]),
            ("server", ["server0"]),
        )
    ]
    peer, server = (
        received.Endpoint("peer", "192.0.2.2", 41000),
        received.Endpoint("server", "198.51.100.2", 9000),
    )
    auth = supplicant = None
    steps, stages, controls = [], [], []
    current_zone = 0
    current_policy = "unauthenticated"
    queue_policy = "normal"

    def snapshot(name):
        filename = f"{name}-conntrack.json"
        command = helper.native(
            "python3", "/task/capture_conntrack.py", "--output", str(OUTPUT / filename)
        )
        return {"file": filename, "command": command}

    def copied_json(name, namespace, *arguments):
        command = helper.run("ip", "-n", namespace, "-j", *arguments)
        filename = f"{name}-{namespace}-links.json"
        (OUTPUT / filename).write_text(command["stdout"])
        return {"file": filename, "command": command}

    def exports(name):
        result = {}
        for kind, arguments in (
            ("firewall", ("list", "table", "ip", "netlib")),
            ("nat", ("list", "table", "ip", "netlib_nat")),
            ("late", ("list", "table", "ip", "netlib_late")),
            ("instrumentation", ("list", "table", "ip", "reassembly_observe")),
            ("timeout", ("list", "table", "ip", "reassembly_timeout")),
            ("tracking", ("list", "table", "ip", "netlib_tracking")),
            ("ruleset", ("list", "ruleset")),
        ):
            command = helper.native("nft", "-j", "-nn", *arguments)
            filename = f"{name}-{kind}.json"
            (OUTPUT / filename).write_text(command["stdout"])
            result[kind] = {"file": filename, "command": command}
        return result

    def statistics():
        return {
            kind: helper.native("cat", f"/tmp/netlib-proc/net/{kind}")
            for kind in ("snmp", "sockstat")
        }

    def zone(value):
        nonlocal current_zone
        if value == current_zone:
            return None
        filename = f"zone-{len(steps)}-{value}.nft"
        (OUTPUT / filename).write_text(
            f"flush chain ip reassembly_observe zone\nadd rule ip reassembly_observe zone ct zone set {value} meta mark set {value}\n"
        )
        command = helper.native("nft", "-f", str(OUTPUT / filename))
        current_zone = value
        return {"file": filename, "command": command}

    def record(name, kind, operation, *, value=0, reply=False, metadata=None):
        changed = zone(value)
        start = time.monotonic_ns()
        before = snapshot(f"{name}-before")
        stats_before = statistics()
        config_before = exports(f"{name}-before")
        links = {
            namespace: copied_json(name, namespace, "link", "show")
            for namespace in ("peer", "auth", "server")
        }
        sent = operation()
        delivered = server.call("receive", timeout=0.08) if kind not in ("wait", "erase") else None
        response = client = None
        if reply:
            response = server.call(
                "send", peer=["203.0.113.1", 40000], payload=f"reassembly:{name}:reply"
            )
            client = peer.call("receive", timeout=0.1)
        elif kind == "socket":
            client = peer.call("receive", timeout=0.08)
        time.sleep(0.04)
        config_after = exports(f"{name}-after")
        stats_after = statistics()
        after = snapshot(f"{name}-after")
        result = {
            "name": name,
            "kind": kind,
            "zone": value,
            "vif": 0,
            "config": current_policy,
            "queuePolicy": queue_policy,
            "startNs": start,
            "endNs": time.monotonic_ns(),
            "before": before,
            "after": after,
            "statsBefore": stats_before,
            "statsAfter": stats_after,
            "links": links,
            "exportsBefore": config_before,
            "exportsAfter": config_after,
            "zoneLoad": changed,
            "sent": sent,
            "server": delivered,
            "reply": response,
            "client": client,
            **(metadata or {}),
        }
        steps.append(result)
        return result

    def payload(name):
        prefix = f"reassembly:{name}|".encode("ascii")
        return udp(prefix + b"x" * (1200 - len(prefix)))

    def raw(
        name,
        datagram,
        identifier,
        offset,
        size,
        more,
        *,
        value=0,
        ttl=64,
        tos=0,
        df=False,
        replacement=None,
    ):
        piece = datagram[offset : offset + size] if replacement is None else replacement
        encoded = fragment(piece, identifier, offset, more, ttl, tos, df)
        filename = f"{name}-input.json"
        helper.save(filename, {"origin": "raw-synthetic-sender", "raw": encoded})
        return record(
            name,
            "raw",
            lambda: helper.run(
                "ip",
                "netns",
                "exec",
                "peer",
                "python3",
                TASK,
                "raw-send",
                str(OUTPUT / filename),
                "peer0",
            ),
            value=value,
            metadata={"input": filename, "origin": "raw-synthetic-sender"},
        )

    def data_stage(name, policy, load=None, reply=False):
        nonlocal current_policy
        current_policy = name
        value = record(
            name,
            "socket",
            lambda: peer.call(
                "send", peer=["203.0.113.2", 8080], payload=payload(name)[8:].decode("ascii")
            ),
            reply=reply,
        )
        value.update(stage=name, policy=policy, load=load)
        stages.append(value)
        return value

    def mtu_for_eap(value):
        writes = [
            helper.run("ip", "-n", namespace, "link", "set", "dev", interface, "mtu", str(value))
            for namespace, interface in (("peer", "peer0"), ("auth", "auth0"))
        ]
        reads = {
            namespace: copied_json(f"eap-mtu-{value}", namespace, "link", "show")
            for namespace in ("peer", "auth")
        }
        if value == 1500:
            for namespace, record in reads.items():
                shutil.copyfile(OUTPUT / record["file"], eap.OUTPUT / f"{namespace}-links.json")
        controls.append(
            {"kind": "eap-link-mtu", "mtu": value, "writes": writes, "readbacks": reads}
        )

    try:
        time.sleep(0.2)
        initial = snapshot("initial")
        load = helper.load_policy("unauthenticated", "deny", False)
        data_stage("unauthenticated", "deny", load)
        mtu_for_eap(1500)
        auth = eap.Producer(
            "success",
            "authenticator",
            "ip",
            "netns",
            "exec",
            "auth",
            "hostapd",
            "-dd",
            str(eap.OUTPUT / "hostapd.conf"),
        )
        auth.wait_for("AP-ENABLED")
        supplicant = eap.Producer(
            "success",
            "supplicant",
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
            str(eap.OUTPUT / "success-supplicant.conf"),
        )
        supplicant.wait_for("CTRL-EVENT-EAP-SUCCESS")
        auth.wait_for("AP-STA-CONNECTED")
        for filename, command in (
            (
                "authorized-station.txt",
                (
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
                    helper.PEER,
                ),
            ),
            (
                "supplicant-status.txt",
                (
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
                ),
            ),
        ):
            (eap.OUTPUT / filename).write_text(helper.run(*command)["stdout"])
        mtu_for_eap(600)
        data_stage("authenticated-only", "deny")
        credential = helper.run(
            "install",
            "-m",
            "0644",
            str(helper.INPUT / "demo-credential.json"),
            str(helper.RUNTIME / "demo-credential.json"),
        )
        shutil.copyfile(
            helper.RUNTIME / "demo-credential.json", OUTPUT / "installed-demo-credential.json"
        )
        load = helper.load_policy("credential-permitted", "permit", True)
        data_stage("credential-permitted", "permit", load, True)
        denied_completion = payload("logoff-split")
        raw("logoff-split-head", denied_completion, 0xA001, 0, 576, True, ttl=43, tos=0x10)
        logoff = helper.run(
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
        )
        auth.wait_for("AP-STA-DISCONNECTED")
        (eap.OUTPUT / "logged-off-station.txt").write_text(
            helper.run(
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
                helper.PEER,
            )["stdout"]
        )
        load = helper.load_policy("logged-off-cached", "deny", True)
        current_policy = "logged-off-cached"
        raw("logoff-split-middle", denied_completion, 0xA001, 576, 576, True)
        raw("logoff-split-tail", denied_completion, 0xA001, 1152, 56, False)
        data_stage("logged-off-cached", "deny", load)
        allowed_completion = payload("permit-split")
        raw("permit-split-head", allowed_completion, 0xA002, 0, 576, True)
        suffix_load = helper.load_policy("reassembly-probes", "permit", True)
        current_policy = "reassembly-probes"
        raw("permit-split-middle", allowed_completion, 0xA002, 576, 576, True)
        raw("permit-split-tail", allowed_completion, 0xA002, 1152, 56, False)
        record(
            "erase-before-raw-families",
            "erase",
            lambda: helper.native(
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
            ),
            metadata={"keySource": "permit-split-tail"},
        )
        value = payload("reversed")
        for index, (offset, size, more) in enumerate(
            ((1152, 56, False), (576, 576, True), (0, 576, True))
        ):
            raw(
                f"reversed-{index}",
                value,
                0xA100,
                offset,
                size,
                more,
                ttl=1 if index == 0 else 61 + index,
                tos=8 * index,
            )
        first, second = payload("interleave-a"), payload("interleave-b")
        for label, value, identifier, offset, size, more in (
            ("a-head", first, 0xA101, 0, 576, True),
            ("b-tail", second, 0xA102, 1152, 56, False),
            ("a-tail", first, 0xA101, 1152, 56, False),
            ("b-head", second, 0xA102, 0, 576, True),
            ("a-middle", first, 0xA101, 576, 576, True),
            ("b-middle", second, 0xA102, 576, 576, True),
        ):
            raw(f"interleaved-{label}", value, identifier, offset, size, more)
        value = payload("duplicates")
        raw("duplicate-head", value, 0xA103, 0, 576, True)
        raw(
            "duplicate-exact-different-bytes",
            value,
            0xA103,
            0,
            576,
            True,
            ttl=19,
            tos=0xFF,
            df=True,
            replacement=bytes([0x55]) * 576,
        )
        raw(
            "duplicate-contained-different-bytes",
            value,
            0xA103,
            8,
            8,
            True,
            replacement=bytes([0xAA]) * 8,
        )
        raw("duplicate-middle", value, 0xA103, 576, 576, True)
        raw("duplicate-tail", value, 0xA103, 1152, 56, False)
        value = payload("duplicate-final")
        raw("duplicate-final-head", value, 0xA10E, 0, 256, True)
        raw("duplicate-final-stored-tail", value, 0xA10E, 832, 376, True)
        raw(
            "duplicate-final-different-bytes",
            value,
            0xA10E,
            832,
            376,
            False,
            replacement=bytes([0x77]) * 376,
        )
        raw("duplicate-final-middle", value, 0xA10E, 256, 576, True)
        value = payload("overlap-restart")
        raw(
            "overlap-old-head",
            value,
            0xA104,
            0,
            576,
            True,
            replacement=value[:32] + b"wrong" + value[37:576],
        )
        raw("overlap-kill", value, 0xA104, 568, 16, True)
        raw("overlap-new-tail", value, 0xA104, 1152, 56, False)
        raw("overlap-new-middle", value, 0xA104, 576, 576, True)
        raw("overlap-new-head", value, 0xA104, 0, 576, True)
        value = payload("final-conflict")
        raw("final-old-head", value, 0xA105, 0, 576, True)
        raw("final-old-tail", value, 0xA105, 1152, 56, False)
        raw("final-conflict-kill", value, 0xA105, 576, 8, False)
        raw("final-new-middle", value, 0xA105, 576, 576, True)
        raw("final-new-tail", value, 0xA105, 1152, 56, False)
        raw("final-new-head", value, 0xA105, 0, 576, True)
        value = payload("odd-trim")
        raw("odd-trim-head", value, 0xA106, 0, 579, True, replacement=value[:576] + b"odd")
        raw("odd-trim-middle", value, 0xA106, 576, 576, True)
        raw("odd-trim-tail", value, 0xA106, 1152, 56, False)
        value = payload("zero-trim")
        raw("zero-trim-old-head", value, 0xA107, 0, 576, True)
        raw("zero-trim-kill", value, 0xA107, 576, 3, True, replacement=b"bad")
        raw("zero-trim-new-tail", value, 0xA107, 1152, 56, False)
        raw("zero-trim-new-middle", value, 0xA107, 576, 576, True)
        raw("zero-trim-new-head", value, 0xA107, 0, 576, True)
        for name, identifier, choices in (
            ("ecn-invalid", 0xA108, (0, 2, 3)),
            ("ecn-merged", 0xA109, (0x22, 3, 0x11)),
        ):
            value = payload(name)
            for part, offset, size, more, tos in zip(
                ("head", "middle", "tail"),
                (0, 576, 1152),
                (576, 576, 56),
                (True, True, False),
                choices,
                strict=True,
            ):
                raw(
                    f"{name}-{part}",
                    value,
                    identifier,
                    offset,
                    size,
                    more,
                    ttl=37 if part == "head" else 55,
                    tos=tos,
                )
        for name, identifier, lengths in (
            ("df-largest", 0xA10A, (576, 576, 56)),
            ("df-smaller", 0xA10B, (256, 576, 376)),
        ):
            value = payload(name)
            offset = 0
            for index, size in enumerate(lengths):
                raw(f"{name}-{index}", value, identifier, offset, size, index != 2, df=index == 0)
                offset += size
        a, b = payload("zone-a"), payload("zone-b")
        for label, value, zone_value, offset, size, more in (
            ("ten-head", a, 10, 0, 576, True),
            ("twenty-middle", b, 20, 576, 576, True),
            ("ten-tail", a, 10, 1152, 56, False),
            ("twenty-tail", b, 20, 1152, 56, False),
            ("ten-middle", a, 10, 576, 576, True),
            ("twenty-head", b, 20, 0, 576, True),
        ):
            raw(f"zone-{label}", value, 0xA10C, offset, size, more, value=zone_value)
        timeout_routes = {
            "input": helper.native(
                "ip",
                "-j",
                "route",
                "get",
                "203.0.113.2",
                "from",
                "192.0.2.2",
                "iif",
                "auth0",
                "mark",
                "0",
            ),
            "return": helper.native(
                "ip", "-j", "route", "get", "192.0.2.2", "from", "203.0.113.2", "mark", "0"
            ),
        }
        controls.append({"kind": "timeout-routes", **timeout_routes})
        timeout_write = helper.native(
            "sh", "-c", "echo 1 > /tmp/netlib-proc/sys/net/ipv4/ipfrag_time"
        )
        timeout_read = helper.native("sysctl", "net.ipv4.ipfrag_time", "net.ipv4.ipfrag_max_dist")
        controls.append(
            {
                "kind": "queue-policy",
                "id": "short",
                "write": timeout_write,
                "readback": timeout_read,
            }
        )
        queue_policy = "short"
        old, fresh = payload("timeout-old"), payload("timeout-new")
        raw("timeout-old-head", old, 0xA10D, 0, 576, True)

        def wait():
            start = time.monotonic_ns()
            time.sleep(1.5)
            return {"startNs": start, "endNs": time.monotonic_ns(), "seconds": 1.5}

        record("timeout-wait", "wait", wait)
        raw("timeout-new-tail", fresh, 0xA10D, 1152, 56, False)
        raw("timeout-new-middle", fresh, 0xA10D, 576, 576, True)
        raw("timeout-new-head", fresh, 0xA10D, 0, 576, True)
        zone_timeout = payload("timeout-zone-ten")
        raw("timeout-zone-ten-head", zone_timeout, 0xA10F, 0, 576, True, value=10)
        record("timeout-zone-ten-wait", "wait", wait)
        final_exports = exports("final")
        time.sleep(0.1)
    finally:
        peer.close()
        server.close()
        for producer in (supplicant, auth):
            if producer is not None:
                producer.stop()
        for process in (*sniffers, eap_sniffer, nflog, trace):
            process.terminate()
            process.wait(timeout=5)
        trace_stream.close()
        trace_errors.close()
        helper.save("commands.json", helper.COMMANDS)
        helper.save("eap/commands.json", eap.COMMANDS)
        shutil.rmtree(eap.RUNTIME)
        shutil.rmtree(helper.RUNTIME)
    helper.save(
        "observations.json",
        {
            "schema": 1,
            "scope": "ordered-ipv4-input-reassembly",
            "initial": initial,
            "networkExports": networks,
            "fragmentSettings": settings,
            "traceCommand": trace_command,
            "nflogCommand": nflog_command,
            "nflogReady": "nflog-ready.json",
            "stages": stages,
            "steps": steps,
            "controls": controls,
            "credentialInstall": credential,
            "logoff": logoff,
            "probeLoad": suffix_load,
            "finalExports": final_exports,
            "eap": {
                "name": "success",
                "phaseId": 1,
                "startNs": eap_start,
                "endNs": time.monotonic_ns(),
                "authenticatorCommand": auth.command,
                "supplicantCommand": supplicant.command,
            },
        },
    )


if __name__ == "__main__":
    if sys.argv[1] == "raw-send":
        raw_send(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == "capture":
        capture()
    else:
        raise SystemExit("Expected capture or raw-send.")
