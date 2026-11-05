"""Capture received ICMP NAT correction and native host PMTU feedback."""

import importlib.util
import ipaddress
import json
import os
import select
import shutil
import signal
import socket
import struct
import subprocess
import sys
import time
from pathlib import Path

OUTPUT = Path("/tmp/netlib-admission")
TASK = "/task/received-icmp/exercise.py"


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def endpoint(address, port):
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind((address, port))
    sock.setsockopt(socket.IPPROTO_IP, 10, 0)
    for line in sys.stdin:
        request = json.loads(line)
        start = time.monotonic_ns()
        result = None
        try:
            if request["operation"] == "connect":
                sock.setsockopt(socket.IPPROTO_IP, 10, 2)
                sock.setsockopt(socket.IPPROTO_IP, 11, 1)
                sock.connect(tuple(request["peer"]))
                result = {
                    "peer": request["peer"],
                    "mtuDiscover": 2,
                    "receiveErrors": 1,
                    "initialMTU": sock.getsockopt(socket.IPPROTO_IP, 14),
                }
            elif request["operation"] == "send":
                sock.setsockopt(socket.IPPROTO_IP, socket.IP_TTL, request.get("ttl", 64))
                payload = request["payload"].encode("ascii")
                count = (
                    sock.send(payload)
                    if request.get("connected")
                    else sock.sendto(payload, tuple(request["peer"]))
                )
                result = {"payload": request["payload"], "bytesSent": count}
            elif request["operation"] == "receive":
                sock.settimeout(request["timeout"])
                data, peer = sock.recvfrom(4096)
                result = {"source": peer[0], "sourcePort": peer[1], "payload": data.decode("ascii")}
            elif request["operation"] == "error":
                sock.settimeout(request["timeout"])
                data, ancillary, flags, peer = sock.recvmsg(4096, 4096, socket.MSG_ERRQUEUE)
                result = {
                    "payloadHex": data.hex(),
                    "flags": flags,
                    "peer": list(peer),
                    "ancillary": [],
                }
                for level, kind, raw in ancillary:
                    row = {"level": level, "type": kind, "hex": raw.hex()}
                    if level == 0 and kind == 11:
                        values = struct.unpack("=IBBBBII", raw[:16])
                        row.update(
                            zip(
                                ("errno", "origin", "icmpType", "icmpCode", "pad", "info", "data"),
                                values,
                            )
                        )
                    result["ancillary"].append(row)
            elif request["operation"] == "mtu":
                result = {"mtu": sock.getsockopt(socket.IPPROTO_IP, 14)}
            elif request["operation"] != "bind":
                raise ValueError("Unknown socket operation.")
        except (TimeoutError, BlockingIOError):
            pass
        except OSError as error:
            result = {"errno": error.errno, "error": str(error)}
        print(
            json.dumps({"startNs": start, "endNs": time.monotonic_ns(), "result": result}),
            flush=True,
        )
    sock.close()


class Endpoint:
    def __init__(self, namespace, address, port):
        self.process = subprocess.Popen(
            ["ip", "netns", "exec", namespace, "python3", TASK, "endpoint", address, str(port)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
        )
        self.call("bind")

    def call(self, operation, **fields):
        self.process.stdin.write(json.dumps({"operation": operation, **fields}) + "\n")
        self.process.stdin.flush()
        result = self.process.stdout.readline()
        if not result:
            raise RuntimeError("UDP endpoint exited.")
        return json.loads(result)

    def close(self):
        self.process.stdin.close()
        self.process.wait(timeout=5)


def sniff(path, namespace, interfaces):
    active = True

    def stop(*_):
        nonlocal active
        active = False

    signal.signal(signal.SIGTERM, stop)
    sockets = {}
    for interface in interfaces:
        sock = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(3))
        sock.bind((interface, 0))
        sockets[sock] = interface
    with Path(path).open("w") as stream:
        while active:
            ready, _, _ = select.select(list(sockets), [], [], 0.1)
            for sock in ready:
                frame, address = sock.recvfrom(65535)
                if len(frame) < 34 or frame[12:14] != b"\x08\x00":
                    continue
                stream.write(
                    json.dumps(
                        {
                            "timeNs": time.monotonic_ns(),
                            "namespace": namespace,
                            "interface": sockets[sock],
                            "packetType": address[2],
                            "hex": frame.hex(),
                        }
                    )
                    + "\n"
                )
                stream.flush()


def sized_payload(name, size):
    prefix = f"mtu:{name}|"
    return prefix + "x" * (size - len(prefix))


def raw_error(wire, quote, source, destination, ttl, mtu, index):
    icmp = bytes((3, 4, 0, 0, 0, 0)) + mtu.to_bytes(2, "big") + quote
    icmp = icmp[:2] + wire.checksum(icmp).to_bytes(2, "big") + icmp[4:]
    ip = struct.pack(
        "!BBHHHBBH4s4s",
        0x45,
        0,
        20 + len(icmp),
        0xED00 + index,
        0,
        ttl,
        1,
        0,
        ipaddress.IPv4Address(source).packed,
        ipaddress.IPv4Address(destination).packed,
    )
    ip = ip[:10] + wire.checksum(ip).to_bytes(2, "big") + ip[12:]
    return (bytes.fromhex("02000000eb0102000000eb020800") + ip + icmp).hex()


def setup_network(helper, eap):
    for namespace in ("peer", "auth", "router", "server"):
        helper.run("ip", "netns", "add", namespace)
        helper.run(
            "ip",
            "netns",
            "exec",
            namespace,
            "sh",
            "-c",
            "echo 1 > /tmp/netlib-proc/sys/net/ipv6/conf/all/disable_ipv6; echo 1 > /tmp/netlib-proc/sys/net/ipv6/conf/default/disable_ipv6",
        )
        helper.run("ip", "-n", namespace, "link", "set", "lo", "up")
    for left, lmac, right, rmac in (
        ("auth0", helper.AUTH, "peer0", helper.PEER),
        ("service0", helper.SERVICE, "router0", helper.SERVER),
        ("srvlink", "02:00:00:00:ec:01", "server0", "02:00:00:00:ec:02"),
    ):
        helper.run(
            "ip",
            "link",
            "add",
            left,
            "address",
            lmac,
            "type",
            "veth",
            "peer",
            "name",
            right,
            "address",
            rmac,
        )
    for namespace, interface, address, mtu in (
        ("peer", "peer0", "192.0.2.2/24", 4096),
        ("auth", "auth0", "192.0.2.1/24", 4096),
        ("auth", "service0", "198.51.101.1/24", 1500),
        ("router", "router0", "198.51.101.254/24", 1500),
        ("router", "srvlink", "198.51.100.254/24", 600),
        ("server", "server0", "198.51.100.2/24", 600),
    ):
        helper.run("ip", "link", "set", interface, "netns", namespace)
        helper.run("ip", "-n", namespace, "address", "add", address, "dev", interface)
        helper.run("ip", "-n", namespace, "link", "set", interface, "mtu", str(mtu), "up")
    for address in ("203.0.113.1/32", "203.0.113.2/32"):
        helper.run("ip", "-n", "auth", "addr", "add", address, "dev", "service0")
    for namespace, network, gateway in (
        ("peer", "default", "192.0.2.1"),
        ("auth", "198.51.100.0/24", "198.51.101.254"),
        ("router", "203.0.113.0/24", "198.51.101.1"),
        ("router", "192.0.2.0/24", "198.51.101.1"),
        ("server", "default", "198.51.100.254"),
    ):
        helper.run("ip", "-n", namespace, "route", "add", network, "via", gateway)
    for namespace, interface, address, mac in (
        ("peer", "peer0", "192.0.2.1", helper.AUTH),
        ("auth", "auth0", "192.0.2.2", helper.PEER),
        ("auth", "service0", "198.51.101.254", helper.SERVER),
        ("router", "router0", "198.51.101.1", helper.SERVICE),
        ("router", "srvlink", "198.51.100.2", "02:00:00:00:ec:02"),
        ("server", "server0", "198.51.100.254", "02:00:00:00:ec:01"),
    ):
        helper.run(
            "ip",
            "-n",
            namespace,
            "neigh",
            "add",
            address,
            "lladdr",
            mac,
            "nud",
            "permanent",
            "dev",
            interface,
        )
    for namespace in ("auth", "router"):
        helper.run(
            "ip",
            "netns",
            "exec",
            namespace,
            "sh",
            "-c",
            "echo 1 > /tmp/netlib-proc/sys/net/ipv4/ip_forward",
        )
    for namespace in ("peer", "auth", "router", "server"):
        record = helper.run(
            "ip",
            "netns",
            "exec",
            namespace,
            "sysctl",
            "net.ipv4.ip_forward",
            "net.ipv6.conf.all.disable_ipv6",
            "net.ipv6.conf.default.disable_ipv6",
            "net.ipv4.conf.all.rp_filter",
            "net.ipv4.conf.default.rp_filter",
            "net.ipv4.conf.all.accept_redirects",
            "net.ipv4.conf.all.send_redirects",
            "net.ipv4.route.min_pmtu",
            "net.ipv4.route.mtu_expires",
            "net.ipv4.ip_no_pmtu_disc",
            *[
                f"net.ipv4.conf.{interface}.{key}"
                for interface in {
                    "peer": ["peer0"],
                    "auth": ["auth0", "service0"],
                    "router": ["router0", "srvlink"],
                    "server": ["server0"],
                }[namespace]
                for key in ("rp_filter", "accept_redirects", "send_redirects", "forwarding")
            ],
        )
        (OUTPUT / f"{namespace}-settings.txt").write_text(record["stdout"])
    tracking = OUTPUT / "tracking.nft"
    tracking.write_text(
        "table ip netlib_tracking { chain prerouting { type filter hook prerouting priority -199; policy accept; ct state { new, established } counter; }\n}\n"
    )
    helper.native("nft", "-f", str(tracking))


def capture():
    helper = module("admission_helper", "/task/admission/exercise.py")
    wire = module("wire_helper", "/task/wire/exercise.py")
    eap = helper.eap_helper()
    eap.OUTPUT.mkdir(exist_ok=True)
    eap.certificates()
    eap.configurations()
    os.chdir(OUTPUT)
    shutil.copytree(helper.INPUT, OUTPUT / "input", dirs_exist_ok=True)
    setup_network(helper, eap)
    icmp_settings = helper.run(
        "ip",
        "netns",
        "exec",
        "router",
        "sh",
        "-c",
        "echo 0 > /tmp/netlib-proc/sys/net/ipv4/icmp_errors_use_inbound_ifaddr; "
        "echo 0 > /tmp/netlib-proc/sys/net/ipv4/icmp_ratelimit; "
        "echo 0 > /tmp/netlib-proc/sys/net/ipv4/icmp_ratemask",
    )
    icmp_readback = helper.run(
        "ip",
        "netns",
        "exec",
        "router",
        "sysctl",
        "net.ipv4.icmp_errors_use_inbound_ifaddr",
        "net.ipv4.icmp_ratelimit",
        "net.ipv4.icmp_ratemask",
        "net.ipv4.ip_default_ttl",
    )
    (OUTPUT / "icmp-settings.txt").write_text(icmp_readback["stdout"])
    network_exports = {}
    for namespace in ("peer", "auth", "router", "server"):
        for kind, arguments in (
            ("links", ("link", "show")),
            ("addresses", ("address", "show")),
            ("routes", ("-4", "route", "show", "table", "main")),
            ("neighbors", ("neigh", "show")),
        ):
            record = helper.run("ip", "-n", namespace, "-j", *arguments)
            filename = f"network-{namespace}-{kind}.json"
            (OUTPUT / filename).write_text(record["stdout"])
            network_exports[f"{namespace}-{kind}"] = {"file": filename, "command": record}
            if kind == "links" and namespace in ("peer", "auth"):
                (eap.OUTPUT / f"{namespace}-links.json").write_text(record["stdout"])
    settings = []
    for namespace, interface in (
        ("peer", "peer0"),
        ("auth", "auth0"),
        ("auth", "service0"),
        ("router", "router0"),
        ("router", "srvlink"),
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
        settings.append({"namespace": namespace, "command": record, **json.loads(record["stdout"])})
    helper.save("offloads.json", settings)
    setup = OUTPUT / "nat-and-trace.nft"
    setup.write_text(
        "table ip netlib_nat {\n"
        " chain destination { type nat hook prerouting priority -100; policy accept;\n"
        '  ip daddr 203.0.113.2 udp dport 8080 dnat to 198.51.100.2:9000 comment "DNAT_SERVICE"\n }\n'
        " chain source { type nat hook postrouting priority 100; policy accept;\n"
        '  ip saddr 192.0.2.0/24 ip daddr 198.51.100.2 udp dport 9000 snat to 203.0.113.1:40000 comment "SNAT_PEER"\n }\n}\n'
        "table ip netlib_late {\n chain late { type filter hook postrouting priority 200; policy accept; }\n}\n"
        "table ip netlib_trace {\n"
        " chain before { type filter hook prerouting priority -301; policy accept; meta l4proto { udp, icmp } meta nftrace set 1; }\n"
        " chain afterDestination { type filter hook prerouting priority -90; policy accept; }\n"
        " chain beforeSource { type filter hook postrouting priority 90; policy accept; }\n"
        " chain afterSource { type filter hook postrouting priority 110; policy accept; }\n}\n"
    )
    with setup.open("a") as stream:
        stream.write(
            "table ip netlib_received {\n"
            " chain tracked { type filter hook prerouting priority -199; policy accept; "
            'meta l4proto icmp ct state related counter comment "RECEIVED_RELATED"; '
            'meta l4proto icmp ct state invalid counter comment "RECEIVED_INVALID"; }\n'
            " chain input { type filter hook input priority 0; policy drop; }\n"
            "}\n"
        )
    helper.native("nft", "-f", str(setup))
    trace_stdout = (OUTPUT / "trace.txt").open("w")
    trace_stderr = (OUTPUT / "trace-errors.txt").open("w")
    trace_command = ["ip", "netns", "exec", "auth", "nft", "monitor", "trace"]
    trace = subprocess.Popen(trace_command, stdout=trace_stdout, stderr=trace_stderr)
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
    data_sniffers = []
    for namespace, interfaces in (
        ("auth", ["auth0", "service0"]),
        ("router", ["router0", "srvlink"]),
        ("peer", ["peer0"]),
        ("server", ["server0"]),
    ):
        data_sniffers.append(
            subprocess.Popen(
                [
                    "ip",
                    "netns",
                    "exec",
                    namespace,
                    "python3",
                    TASK,
                    "sniff",
                    str(OUTPUT / f"frames-{namespace}.jsonl"),
                    namespace,
                    *interfaces,
                ]
            )
        )
    peer, server = Endpoint("peer", "192.0.2.2", 41000), Endpoint("server", "198.51.100.2", 9000)
    auth = supplicant = None

    def snapshot(name):
        filename = f"{name}-conntrack.json"
        record = helper.native(
            "python3", "/task/capture_conntrack.py", "--output", str(OUTPUT / filename)
        )
        return {"file": filename, "command": record}

    def exports(name):
        result = {}
        for kind, arguments in (
            ("firewall", ("list", "table", "ip", "netlib")),
            ("nat", ("list", "table", "ip", "netlib_nat")),
            ("late", ("list", "table", "ip", "netlib_late")),
            ("received", ("list", "table", "ip", "netlib_received")),
            ("ruleset", ("list", "ruleset")),
        ):
            record = helper.native("nft", "-j", "-nn", *arguments)
            filename = f"{name}-{kind}.json"
            (OUTPUT / filename).write_text(record["stdout"])
            result[kind] = {"file": filename, "command": record}
        return result

    def link_exports(name):
        result = {}
        for namespace in ("peer", "auth", "router", "server"):
            record = helper.run("ip", "-n", namespace, "-j", "link", "show")
            filename = f"{name}-{namespace}-links.json"
            (OUTPUT / filename).write_text(record["stdout"])
            result[namespace] = {"file": filename, "command": record}
        return result

    def probe(name, policy, load=None):
        start = time.monotonic_ns()
        request_links = link_exports(f"{name}-request")
        sent = peer.call(
            "send", peer=["203.0.113.2", 8080], payload=sized_payload(f"{name}-request", 1200)
        )
        received = server.call("receive", timeout=0.25)
        reply = None
        reply_links = None
        if policy == "permit":
            if received["result"] is None:
                raise RuntimeError("NAT request did not reach the server.")
            reply_links = link_exports(f"{name}-reply")
            reply = server.call("send", peer=["203.0.113.1", 40000], payload=f"mtu:{name}:reply")
        client = peer.call("receive", timeout=0.25)
        permitted = policy == "permit"
        if (received["result"] is not None) != permitted or (
            client["result"] is not None
        ) != permitted:
            raise RuntimeError(f"Unexpected NAT socket outcome: {name}")
        config = exports(name)
        state = snapshot(name)
        return {
            "stage": name,
            "policy": policy,
            "startNs": start,
            "endNs": time.monotonic_ns(),
            "sent": sent,
            "requestLinks": request_links,
            "replyLinks": reply_links,
            "server": received,
            "reply": reply,
            "client": client,
            "load": load,
            "exports": config,
            "state": state,
        }

    try:
        time.sleep(0.2)
        initial = snapshot("initial")
        load = helper.load_policy("unauthenticated", "deny", False)
        stages = [probe("unauthenticated", "deny", load)]
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
        for filename, arguments in (
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
            (eap.OUTPUT / filename).write_text(helper.run(*arguments)["stdout"])
        stages.append(probe("authenticated-only", "deny"))
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
        stages.append(probe("credential-permitted", "permit", load))
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
        stages.append(probe("logged-off-cached", "deny", load))
        suffix_load = helper.load_policy("received-probes", "permit", True)
        related_rule = helper.native(
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
        )
        suffix_exports = exports("received-probes")
        erase = helper.native(
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
        )
        erased = snapshot("erased")
        feedback = []
        connected = peer.call("connect", peer=["203.0.113.2", 8080])

        def feedback_probe(name, size, reply=False):
            start = time.monotonic_ns()
            before = snapshot(f"{name}-before")
            route_before = helper.run("ip", "-n", "peer", "-j", "route", "get", "203.0.113.2")
            links = link_exports(name)
            mtu_before = peer.call("mtu")
            sent = peer.call("send", connected=True, payload=sized_payload(name, size))
            time.sleep(0.08)
            error = peer.call("error", timeout=0.15)
            mtu = peer.call("mtu")
            route_after = helper.run("ip", "-n", "peer", "-j", "route", "get", "203.0.113.2")
            received = server.call("receive", timeout=0.15)
            response = client = None
            if reply:
                response = server.call(
                    "send", peer=["203.0.113.1", 40000], payload=f"mtu:{name}:reply"
                )
                client = peer.call("receive", timeout=0.15)
            time.sleep(0.05)
            after = snapshot(f"{name}-after")
            feedback.append(
                {
                    "name": name,
                    "origin": "native-host",
                    "startNs": start,
                    "endNs": time.monotonic_ns(),
                    "before": before,
                    "after": after,
                    "routeBefore": route_before,
                    "routeAfter": route_after,
                    "links": links,
                    "sent": sent,
                    "mtuBefore": mtu_before,
                    "error": error,
                    "mtu": mtu,
                    "server": received,
                    "reply": response,
                    "client": client,
                }
            )

        feedback_probe("native-df-oversize", 1200)
        feedback_probe("cached-pmtu-emsgsize", 1200)
        feedback_probe("pmtu-small-roundtrip", 500, True)
        rows = [
            json.loads(line) for line in (OUTPUT / "frames-auth.jsonl").read_text().splitlines()
        ]
        native_error = next(
            bytes.fromhex(row["hex"])
            for row in rows
            if row["interface"] == "service0" and bytes.fromhex(row["hex"])[23] == 1
        )
        quote = native_error[42 : 14 + int.from_bytes(native_error[16:18], "big")]
        full_quote_frame = next(
            bytes.fromhex(row["hex"])
            for row in rows
            if row["interface"] == "service0"
            and row["packetType"] == 4
            and bytes.fromhex(row["hex"])[23] == 17
            and b"mtu:pmtu-small-roundtrip|" in bytes.fromhex(row["hex"])
        )
        full_quote = full_quote_frame[14 : 14 + int.from_bytes(full_quote_frame[16:18], "big")]
        raw_probes = []
        for index, (name, outer_source, outer_destination, ttl, port, mtu) in enumerate(
            (
                ("unmatched-quote", "198.51.101.254", "203.0.113.1", 64, 40001, 600),
                ("wrong-outer-destination", "198.51.101.254", "203.0.113.2", 64, 40000, 600),
                ("ttl-one-control", "198.51.101.254", "203.0.113.1", 1, 40000, 600),
                ("full-bad-udp-checksum", "198.51.101.254", "203.0.113.1", 64, 40000, 600),
                ("bad-inner-ip-checksum", "198.51.101.254", "203.0.113.1", 64, 40000, 600),
                ("forged-outer-source", "198.51.100.99", "203.0.113.1", 64, 40000, 576),
            )
        ):
            start = time.monotonic_ns()
            before = snapshot(f"{name}-before")
            route_before = helper.run("ip", "-n", "peer", "-j", "route", "get", "203.0.113.2")
            links = link_exports(name)
            changed = bytearray(full_quote if name == "full-bad-udp-checksum" else quote)
            if name == "full-bad-udp-checksum":
                changed[26] ^= 1
            if name == "bad-inner-ip-checksum":
                changed[10] ^= 1
            if port != 40000:
                old = int.from_bytes(changed[26:28], "big")
                total = (~old & 65535) + (~40000 & 65535) + port
                total = (total & 65535) + (total >> 16)
                total = (total & 65535) + (total >> 16)
                changed[26:28] = ((~total & 65535) or 65535).to_bytes(2, "big")
                changed[20:22] = port.to_bytes(2, "big")
            raw = raw_error(wire, bytes(changed), outer_source, outer_destination, ttl, mtu, index)
            filename = f"{name}-input.json"
            helper.save(filename, {"name": name, "origin": "raw-synthetic-sender", "raw": raw})
            sent = helper.run(
                "ip",
                "netns",
                "exec",
                "router",
                "python3",
                TASK,
                "raw-send",
                str(OUTPUT / filename),
                "router0",
            )
            time.sleep(0.06)
            error = peer.call("error", timeout=0.15)
            mtu_read = peer.call("mtu")
            route_after = helper.run("ip", "-n", "peer", "-j", "route", "get", "203.0.113.2")
            time.sleep(0.04)
            after = snapshot(f"{name}-after")
            raw_probes.append(
                {
                    "name": name,
                    "origin": "raw-synthetic-sender",
                    "startNs": start,
                    "endNs": time.monotonic_ns(),
                    "before": before,
                    "after": after,
                    "routeBefore": route_before,
                    "routeAfter": route_after,
                    "links": links,
                    "input": filename,
                    "sent": sent,
                    "error": error,
                    "mtu": mtu_read,
                }
            )
        final_exports = exports("icmp-final")
        time.sleep(0.1)
    finally:
        peer.close()
        server.close()
        for producer in (supplicant, auth):
            if producer is not None:
                producer.stop()
        for sniffer in (eap_sniffer, *data_sniffers):
            sniffer.terminate()
            sniffer.wait(timeout=5)
        trace.terminate()
        trace.wait(timeout=5)
        trace_stdout.close()
        trace_stderr.close()
        helper.save("commands.json", helper.COMMANDS)
        helper.save("eap/commands.json", eap.COMMANDS)
        shutil.rmtree(eap.RUNTIME)
        shutil.rmtree(helper.RUNTIME)
    helper.save(
        "observations.json",
        {
            "schema": 1,
            "scope": "received-icmp-pmtu",
            "icmpSettingsWrite": icmp_settings,
            "icmpSettingsReadback": icmp_readback,
            "finalExports": final_exports,
            "initial": initial,
            "networkExports": network_exports,
            "traceCommand": trace_command,
            "stages": stages,
            "credentialInstall": credential,
            "logoff": logoff,
            "erase": {"command": erase, "state": erased},
            "probeLoad": suffix_load,
            "probeExports": suffix_exports,
            "relatedRule": related_rule,
            "connectedSocket": connected,
            "hostFeedback": feedback,
            "receivedProbes": raw_probes,
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
    if sys.argv[1] == "endpoint":
        endpoint(sys.argv[2], int(sys.argv[3]))
    elif sys.argv[1] == "raw-send":
        request = json.loads(Path(sys.argv[2]).read_text())
        sock = socket.socket(socket.AF_PACKET, socket.SOCK_RAW)
        sock.bind((sys.argv[3], 0))
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
    elif sys.argv[1] == "sniff":
        sniff(sys.argv[2], sys.argv[3], sys.argv[4:])
    else:
        capture()
