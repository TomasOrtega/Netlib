"""Capture two-sided NAT, wire checksums, authentication, and TTL ordering."""

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
TASK = "/task/wire-nat/exercise.py"


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def endpoint(address, port):
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind((address, port))
    for line in sys.stdin:
        request = json.loads(line)
        start = time.monotonic_ns()
        result = None
        if request["operation"] == "send":
            sock.setsockopt(socket.IPPROTO_IP, socket.IP_TTL, request.get("ttl", 64))
            peer = tuple(request["peer"])
            sock.sendto(request["payload"].encode("ascii"), peer)
            result = {
                "source": address,
                "sourcePort": port,
                "destination": peer[0],
                "destinationPort": peer[1],
                "payload": request["payload"],
                "ttl": sock.getsockopt(socket.IPPROTO_IP, socket.IP_TTL),
            }
        elif request["operation"] == "receive":
            sock.settimeout(request["timeout"])
            try:
                data, peer = sock.recvfrom(4096)
                result = {
                    "source": peer[0],
                    "sourcePort": peer[1],
                    "destination": address,
                    "destinationPort": port,
                    "payload": data.decode("ascii"),
                }
            except TimeoutError:
                pass
        elif request["operation"] != "bind":
            raise ValueError("Unknown socket operation.")
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


def sniff(path):
    active = True

    def stop(*_):
        nonlocal active
        active = False

    signal.signal(signal.SIGTERM, stop)
    sockets = {}
    for interface in ("auth0", "service0"):
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
                            "interface": sockets[sock],
                            "packetType": address[2],
                            "hex": frame.hex(),
                        }
                    )
                    + "\n"
                )
                stream.flush()


def raw_probe(wire, ttl, index, omitted=False):
    payload = f"wire-nat:ttl-{ttl}".encode() if not omitted else b"wire-nat:udp-zero"
    source, destination = (
        ipaddress.IPv4Address("192.0.2.2").packed,
        ipaddress.IPv4Address("203.0.113.2").packed,
    )
    udp = struct.pack("!HHHH", 41000, 8080, 8 + len(payload), 0) + payload
    checksum = (
        0
        if omitted
        else wire.checksum(
            source + destination + bytes((0, 17)) + len(udp).to_bytes(2, "big") + udp
        )
        or 65535
    )
    udp = udp[:6] + checksum.to_bytes(2, "big") + udp[8:]
    ip = struct.pack(
        "!BBHHHBBH4s4s",
        0x45,
        0,
        20 + len(udp),
        0xFC00 + index,
        0x4000,
        ttl,
        17,
        0,
        source,
        destination,
    )
    ip = ip[:10] + wire.checksum(ip).to_bytes(2, "big") + ip[12:]
    return (bytes.fromhex("02000000ea0102000000ea020800") + ip + udp).hex()


def capture():
    helper = module("admission_helper", "/task/admission/exercise.py")
    wire = module("wire_helper", "/task/wire/exercise.py")
    eap = helper.eap_helper()
    eap.OUTPUT.mkdir(exist_ok=True)
    eap.certificates()
    eap.configurations()
    os.chdir(OUTPUT)
    shutil.copytree(helper.INPUT, OUTPUT / "input", dirs_exist_ok=True)
    helper.setup()
    helper.run("ip", "-n", "auth", "addr", "add", "203.0.113.1/32", "dev", "service0")
    helper.run("ip", "-n", "auth", "addr", "add", "203.0.113.2/32", "dev", "service0")
    helper.run("ip", "-n", "server", "route", "add", "203.0.113.0/24", "via", "198.51.100.1")
    network_exports = {}
    for namespace in ("peer", "auth", "server"):
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
    settings = []
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
        " chain before { type filter hook prerouting priority -301; policy accept; meta l4proto udp meta nftrace set 1; }\n"
        " chain afterDestination { type filter hook prerouting priority -90; policy accept; }\n"
        " chain beforeSource { type filter hook postrouting priority 90; policy accept; }\n"
        " chain afterSource { type filter hook postrouting priority 110; policy accept; }\n}\n"
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
    data_sniffer = subprocess.Popen(
        ["ip", "netns", "exec", "auth", "python3", TASK, "sniff", str(OUTPUT / "frames.jsonl")]
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
            ("ruleset", ("list", "ruleset")),
        ):
            record = helper.native("nft", "-j", "-nn", *arguments)
            filename = f"{name}-{kind}.json"
            (OUTPUT / filename).write_text(record["stdout"])
            result[kind] = {"file": filename, "command": record}
        return result

    def probe(name, policy, load=None):
        start = time.monotonic_ns()
        sent = peer.call("send", peer=["203.0.113.2", 8080], payload=f"wire-nat:{name}:request")
        received = server.call("receive", timeout=0.25)
        low = None
        reply = None
        if policy == "permit":
            if received["result"] is None:
                raise RuntimeError("NAT request did not reach the server.")
            before = snapshot("before-ttl-one-reply")
            low_sent = server.call(
                "send", peer=["203.0.113.1", 40000], payload=f"wire-nat:{name}:ttl-one-reply", ttl=1
            )
            low_received = peer.call("receive", timeout=0.25)
            if low_received["result"] is not None:
                raise RuntimeError("TTL-one reply reached the client.")
            after = snapshot("after-ttl-one-reply")
            low = {"sent": low_sent, "client": low_received, "before": before, "after": after}
            reply = server.call(
                "send", peer=["203.0.113.1", 40000], payload=f"wire-nat:{name}:reply"
            )
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
            "server": received,
            "lowTTLReply": low,
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
        suffix_load = helper.load_policy("ttl-probes", "permit", True)
        suffix_exports = exports("ttl-probes")
        ttl_probes = []
        for index, (name, ttl, omitted) in enumerate(
            (
                ("ttl-zero", 0, False),
                ("ttl-one", 1, False),
                ("ttl-two", 2, False),
                ("udp-zero", 64, True),
            )
        ):
            start = time.monotonic_ns()
            before = snapshot(f"{name}-before")
            filename = f"{name}-input.json"
            helper.save(filename, {"name": name, "raw": raw_probe(wire, ttl, index, omitted)})
            sent = helper.run(
                "ip",
                "netns",
                "exec",
                "peer",
                "python3",
                "/task/wire/exercise.py",
                "raw-send",
                str(OUTPUT / filename),
            )
            received = server.call("receive", timeout=0.25)
            if (received["result"] is not None) != (ttl > 1):
                raise RuntimeError(f"Unexpected TTL socket outcome: {name}")
            after = snapshot(f"{name}-after")
            time.sleep(0.03)
            ttl_probes.append(
                {
                    "name": name,
                    "ttl": ttl,
                    "startNs": start,
                    "endNs": time.monotonic_ns(),
                    "input": filename,
                    "sent": sent,
                    "server": received,
                    "before": before,
                    "after": after,
                }
            )
        time.sleep(0.1)
    finally:
        peer.close()
        server.close()
        for producer in (supplicant, auth):
            if producer is not None:
                producer.stop()
        for sniffer in (eap_sniffer, data_sniffer):
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
            "scope": "wire-nat-forwarding",
            "initial": initial,
            "networkExports": network_exports,
            "traceCommand": trace_command,
            "stages": stages,
            "credentialInstall": credential,
            "logoff": logoff,
            "erase": {"command": erase, "state": erased},
            "ttlLoad": suffix_load,
            "ttlExports": suffix_exports,
            "ttlProbes": ttl_probes,
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
    elif sys.argv[1] == "sniff":
        sniff(sys.argv[2])
    else:
        capture()
