"""Capture TLS authentication, generated policy loads, and real UDP admission."""

import importlib.util
import json
import os
import select
import shutil
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path

OUTPUT = Path("/tmp/netlib-admission")
INPUT = Path("/task/admission/input")
RUNTIME = Path("/run/netlib-admission")
COMMANDS = []
AUTH = "02:00:00:00:ea:01"
PEER = "02:00:00:00:ea:02"
SERVICE = "02:00:00:00:eb:01"
SERVER = "02:00:00:00:eb:02"


def save(name, document):
    (OUTPUT / name).write_text(json.dumps(document, indent=2) + "\n")


def run(*arguments):
    start = time.monotonic_ns()
    result = subprocess.run(arguments, capture_output=True, text=True, check=False)
    record = {
        "command": list(arguments),
        "startNs": start,
        "endNs": time.monotonic_ns(),
        "returncode": result.returncode,
        "stdout": result.stdout,
        "stderr": result.stderr,
    }
    COMMANDS.append(record)
    if result.returncode:
        raise RuntimeError(f"Failed {arguments}: {result.stderr}")
    return record


def native(*arguments):
    return run("ip", "netns", "exec", "auth", *arguments)


def eap_helper():
    spec = importlib.util.spec_from_file_location("eap_capture_helper", "/task/eap_exercise.py")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    helper.OUTPUT = OUTPUT / "eap"
    return helper


def setup():
    for namespace in ("peer", "auth", "server"):
        run("ip", "netns", "add", namespace)
        run(
            "ip",
            "netns",
            "exec",
            namespace,
            "sh",
            "-c",
            "echo 1 > /tmp/netlib-proc/sys/net/ipv6/conf/all/disable_ipv6; echo 1 > /tmp/netlib-proc/sys/net/ipv6/conf/default/disable_ipv6",
        )
        run("ip", "-n", namespace, "link", "set", "lo", "up")
    run(
        "ip",
        "link",
        "add",
        "auth0",
        "address",
        AUTH,
        "type",
        "veth",
        "peer",
        "name",
        "peer0",
        "address",
        PEER,
    )
    run(
        "ip",
        "link",
        "add",
        "service0",
        "address",
        SERVICE,
        "type",
        "veth",
        "peer",
        "name",
        "server0",
        "address",
        SERVER,
    )
    for namespace, interface, address in (
        ("peer", "peer0", "192.0.2.2/24"),
        ("auth", "auth0", "192.0.2.1/24"),
        ("auth", "service0", "198.51.100.1/24"),
        ("server", "server0", "198.51.100.2/24"),
    ):
        run("ip", "link", "set", interface, "netns", namespace)
        run("ip", "-n", namespace, "address", "add", address, "dev", interface)
        run("ip", "-n", namespace, "link", "set", interface, "up")
    run("ip", "-n", "peer", "route", "add", "default", "via", "192.0.2.1")
    run("ip", "-n", "server", "route", "add", "192.0.2.0/24", "via", "198.51.100.1")
    for namespace, interface, address, mac in (
        ("peer", "peer0", "192.0.2.1", AUTH),
        ("auth", "auth0", "192.0.2.2", PEER),
        ("auth", "service0", "198.51.100.2", SERVER),
        ("server", "server0", "198.51.100.1", SERVICE),
    ):
        run(
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
    native("sh", "-c", "echo 1 > /tmp/netlib-proc/sys/net/ipv4/ip_forward")
    for namespace in ("peer", "auth", "server"):
        for kind, command in (
            ("links", ("link", "show")),
            ("addresses", ("address", "show")),
            ("routes", ("-4", "route", "show")),
            ("neighbors", ("neigh", "show")),
        ):
            record = run("ip", "-n", namespace, "-j", *command)
            (OUTPUT / f"{namespace}-{kind}.json").write_text(record["stdout"])
        record = run(
            "ip",
            "netns",
            "exec",
            namespace,
            "sysctl",
            "net.ipv4.ip_forward",
            "net.ipv6.conf.all.disable_ipv6",
            "net.ipv6.conf.default.disable_ipv6",
        )
        (OUTPUT / f"{namespace}-settings.txt").write_text(record["stdout"])
    for namespace in ("auth", "peer"):
        shutil.copyfile(
            OUTPUT / f"{namespace}-links.json", OUTPUT / "eap" / f"{namespace}-links.json"
        )
    tracking = OUTPUT / "tracking.nft"
    tracking.write_text(
        "table ip netlib_tracking {\n"
        " chain prerouting { type filter hook prerouting priority -199; policy accept;\n"
        "  ct state { new, established } counter\n"
        " }\n}\n"
    )
    native("nft", "-f", str(tracking))


def load_policy(stage, policy, replace):
    document = json.loads((INPUT / f"{policy}.json").read_text())
    objects = document["nftables"]
    if replace:
        objects = [
            objects[0],
            {"delete": {"table": {"family": "ip", "name": "netlib"}}},
            *objects[1:],
        ]
    path = OUTPUT / f"{stage}-load.json"
    path.write_text(json.dumps({"nftables": objects}, indent=2) + "\n")
    record = native("nft", "-j", "-f", str(path))
    return {**record, "input": f"input/{policy}.json", "batch": path.name}


def endpoint(address):
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind((address, 41000 if address == "192.0.2.2" else 9000))
    for line in sys.stdin:
        request = json.loads(line)
        start = time.monotonic_ns()
        result = None
        if request["operation"] == "send":
            peer = tuple(request["peer"])
            sock.sendto(request["payload"].encode("ascii"), peer)
            result = {
                "source": address,
                "sourcePort": sock.getsockname()[1],
                "destination": peer[0],
                "destinationPort": peer[1],
                "payload": request["payload"],
            }
        elif request["operation"] == "receive":
            sock.settimeout(request["timeout"])
            try:
                data, peer = sock.recvfrom(4096)
                result = {
                    "source": peer[0],
                    "sourcePort": peer[1],
                    "destination": address,
                    "destinationPort": sock.getsockname()[1],
                    "payload": data.decode("ascii"),
                }
            except TimeoutError:
                pass
        elif request["operation"] != "bind":
            raise ValueError("Unknown endpoint operation.")
        print(
            json.dumps({"startNs": start, "endNs": time.monotonic_ns(), "result": result}),
            flush=True,
        )
    sock.close()


class Endpoint:
    def __init__(self, namespace, address):
        self.process = subprocess.Popen(
            ["ip", "netns", "exec", namespace, "python3", __file__, "endpoint", address],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
        )
        self.call("bind")

    def call(self, operation, **fields):
        self.process.stdin.write(json.dumps({"operation": operation, **fields}) + "\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError("Native UDP endpoint exited.")
        return json.loads(line)

    def close(self):
        self.process.stdin.close()
        self.process.wait(timeout=5)


def sniff_data(path):
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
                if len(frame) < 42 or frame[12:14] != b"\x08\x00" or frame[23] != 17:
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


def probe(stage, policy, peer, server, load=None):
    start = time.monotonic_ns()
    sent = peer.call("send", peer=["198.51.100.2", 9000], payload=f"admission:{stage}:request")
    received = server.call("receive", timeout=0.25)
    reply = None
    if received["result"] is not None:
        reply = server.call("send", peer=["192.0.2.2", 41000], payload=f"admission:{stage}:reply")
    client = peer.call("receive", timeout=0.25)
    expected = policy == "permit"
    if (received["result"] is not None) != expected or (client["result"] is not None) != expected:
        raise RuntimeError(f"Unexpected native UDP outcome during {stage}.")
    firewall = f"{stage}-firewall.json"
    ruleset = f"{stage}-ruleset.json"
    state = f"{stage}-conntrack.json"
    for filename, arguments in (
        (firewall, ("list", "table", "ip", "netlib")),
        (ruleset, ("list", "ruleset")),
    ):
        record = native("nft", "-j", "-nn", *arguments)
        (OUTPUT / filename).write_text(record["stdout"])
    snapshot = native("python3", "/task/capture_conntrack.py", "--output", str(OUTPUT / state))
    return {
        "stage": stage,
        "policy": policy,
        "startNs": start,
        "endNs": time.monotonic_ns(),
        "sent": sent,
        "server": received,
        "reply": reply,
        "client": client,
        "load": load,
        "firewall": firewall,
        "ruleset": ruleset,
        "conntrack": state,
        "snapshot": snapshot,
    }


def capture():
    helper = eap_helper()
    helper.OUTPUT.mkdir(exist_ok=True)
    helper.certificates()
    helper.configurations()
    os.chdir(OUTPUT)
    shutil.copytree(INPUT, OUTPUT / "input", dirs_exist_ok=True)
    setup()
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
            str(helper.OUTPUT / "success-frames.jsonl"),
        ]
    )
    data_sniffer = subprocess.Popen(
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "python3",
            __file__,
            "sniff-data",
            str(OUTPUT / "data-frames.jsonl"),
        ]
    )
    peer, server = Endpoint("peer", "192.0.2.2"), Endpoint("server", "198.51.100.2")
    auth = supplicant = None
    try:
        time.sleep(0.2)
        load = load_policy("unauthenticated", "deny", False)
        stages = [probe("unauthenticated", "deny", peer, server, load)]
        auth = helper.Producer(
            "success",
            "authenticator",
            "ip",
            "netns",
            "exec",
            "auth",
            "hostapd",
            "-dd",
            str(helper.OUTPUT / "hostapd.conf"),
        )
        auth.wait_for("AP-ENABLED")
        supplicant = helper.Producer(
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
            str(helper.OUTPUT / "success-supplicant.conf"),
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
                    PEER,
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
            (helper.OUTPUT / filename).write_text(run(*arguments)["stdout"])
        stages.append(probe("authenticated-only", "deny", peer, server))
        credential = run(
            "install",
            "-m",
            "0644",
            str(INPUT / "demo-credential.json"),
            str(RUNTIME / "demo-credential.json"),
        )
        shutil.copyfile(RUNTIME / "demo-credential.json", OUTPUT / "installed-demo-credential.json")
        load = load_policy("credential-permitted", "permit", True)
        stages.append(probe("credential-permitted", "permit", peer, server, load))
        logoff = run(
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
        (helper.OUTPUT / "logged-off-station.txt").write_text(
            run(
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
                PEER,
            )["stdout"]
        )
        load = load_policy("logged-off-cached", "deny", True)
        stages.append(probe("logged-off-cached", "deny", peer, server, load))
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
        save("commands.json", COMMANDS)
        save("eap/commands.json", helper.COMMANDS)
        shutil.rmtree(helper.RUNTIME)
        shutil.rmtree(RUNTIME)
    save(
        "observations.json",
        {
            "schema": 1,
            "scope": "wired-gateway-session-admission",
            "stages": stages,
            "credentialInstall": credential,
            "logoff": logoff,
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
        endpoint(sys.argv[2])
    elif sys.argv[1] == "sniff-data":
        sniff_data(sys.argv[2])
    else:
        capture()
