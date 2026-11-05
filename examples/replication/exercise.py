"""Capture ordered FTFW replication, kernel commit, and a fenced UDP handoff."""

import errno
import json
import select
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path

OUTPUT = Path("/tmp/netlib-replication")
TASK = "/task/replication/exercise.py"
ACTORS = ("client", "a", "b", "server")
GATEWAYS = ("a", "b")
LINKS = (
    ("ca", "client", "a", "192.0.2.2/24", "192.0.2.1/24"),
    ("cb", "client", "b", "192.0.3.2/24", "192.0.3.1/24"),
    ("sa", "server", "a", "198.51.100.2/24", "198.51.100.1/24"),
    ("sb", "server", "b", "198.51.101.2/24", "198.51.101.1/24"),
    ("sync", "a", "b", "10.10.0.1/24", "10.10.0.2/24"),
)
COMMANDS = []


def save(name, value):
    (OUTPUT / name).write_text(json.dumps(value, indent=2) + "\n")
    return name


def run(*arguments):
    start = time.monotonic_ns()
    result = subprocess.run(arguments, text=True, capture_output=True)
    index = len(COMMANDS)
    COMMANDS.append(
        {
            "arguments": list(arguments),
            "startNs": start,
            "endNs": time.monotonic_ns(),
            "returncode": result.returncode,
            "stdout": result.stdout,
            "stderr": result.stderr,
        }
    )
    if result.returncode:
        raise RuntimeError(COMMANDS[-1])
    return index, result.stdout


def native(actor, *arguments):
    return run("ip", "netns", "exec", actor, *arguments)


def export(actor, name, *arguments):
    index, text = native(actor, *arguments)
    (OUTPUT / name).write_text(text)
    return {"file": name, "command": index}


def endpoints():
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind((sys.argv[2], int(sys.argv[3])))
    sock.setsockopt(socket.IPPROTO_IP, 10, 0)
    for line in sys.stdin:
        request = json.loads(line)
        start = time.monotonic_ns()
        result = None
        try:
            if request["operation"] == "bind":
                result = {
                    "local": list(sock.getsockname()),
                    "mtuDiscover": sock.getsockopt(socket.IPPROTO_IP, 10),
                }
            elif request["operation"] == "send":
                sock.setsockopt(socket.IPPROTO_IP, socket.IP_TTL, request["ttl"])
                payload = bytes.fromhex(request["payloadHex"])
                count = sock.sendto(payload, tuple(request["peer"]))
                result = {
                    "bytesSent": count,
                    "payloadHex": payload.hex(),
                    "local": list(sock.getsockname()),
                    "peer": request["peer"],
                    "ttl": sock.getsockopt(socket.IPPROTO_IP, socket.IP_TTL),
                }
            elif request["operation"] == "receive":
                sock.settimeout(request["timeout"])
                data, peer = sock.recvfrom(4096)
                result = {
                    "payloadHex": data.hex(),
                    "peer": list(peer),
                    "local": list(sock.getsockname()),
                }
            else:
                raise ValueError("Unknown endpoint operation.")
        except TimeoutError:
            pass
        except OSError as error:
            result = {"errno": error.errno, "error": str(error)}
        print(
            json.dumps({"startNs": start, "endNs": time.monotonic_ns(), "result": result}),
            flush=True,
        )
    sock.close()


class Endpoint:
    def __init__(self, actor, address, port):
        self.actor = actor
        self.command = [
            "ip",
            "netns",
            "exec",
            actor,
            "python3",
            TASK,
            "endpoint",
            address,
            str(port),
        ]
        self.start = time.monotonic_ns()
        self.process = subprocess.Popen(
            self.command, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE
        )
        self.binding = self.call("bind")

    def call(self, operation, **fields):
        request = {"operation": operation, **fields}
        start = time.monotonic_ns()
        self.process.stdin.write(json.dumps(request) + "\n")
        self.process.stdin.flush()
        raw = self.process.stdout.readline()
        if not raw:
            raise RuntimeError("UDP endpoint exited.")
        return {
            "request": request,
            "response": json.loads(raw),
            "startNs": start,
            "endNs": time.monotonic_ns(),
        }

    def close(self):
        self.process.stdin.close()
        self.process.wait(timeout=5)
        return {
            "command": self.command,
            "startNs": self.start,
            "binding": self.binding,
            "returncode": self.process.returncode,
            "endNs": time.monotonic_ns(),
        }


def sniff():
    active = True

    def stop(*_):
        nonlocal active
        active = False

    signal.signal(signal.SIGTERM, stop)
    sockmap = {}
    ready = []
    for interface in sys.argv[4:]:
        sock = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(3))
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1 << 20)
        sock.bind((interface, 0))
        sockmap[sock] = interface
        ready.append(
            {
                "interface": interface,
                "ifindex": socket.if_nametoindex(interface),
                "receiveBuffer": sock.getsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF),
            }
        )
    print(
        json.dumps({"readyNs": time.monotonic_ns(), "namespace": sys.argv[3], "interfaces": ready}),
        flush=True,
    )
    with Path(sys.argv[2]).open("w") as stream:
        while active:
            available, _, _ = select.select(list(sockmap), [], [], 0.1)
            for sock in available:
                try:
                    frame, address = sock.recvfrom(65535)
                except OSError as error:
                    if error.errno != errno.ENETDOWN:
                        raise
                    stream.write(
                        json.dumps(
                            {
                                "timeNs": time.monotonic_ns(),
                                "namespace": sys.argv[3],
                                "interface": sockmap.pop(sock),
                                "socketError": error.errno,
                            }
                        )
                        + "\n"
                    )
                    stream.flush()
                    sock.close()
                    continue
                stream.write(
                    json.dumps(
                        {
                            "timeNs": time.monotonic_ns(),
                            "namespace": sys.argv[3],
                            "interface": sockmap[sock],
                            "ifindex": socket.if_nametoindex(sockmap[sock]),
                            "packetType": address[2],
                            "hex": frame.hex(),
                        }
                    )
                    + "\n"
                )
                stream.flush()
    for sock in sockmap:
        sock.close()


def configuration(actor):
    local, remote = ("10.10.0.1", "10.10.0.2") if actor == "a" else ("10.10.0.2", "10.10.0.1")
    interface = "syncl" if actor == "a" else "syncr"
    return f"""Sync {{
 Mode FTFW {{ CommitTimeout 180 DisableExternalCache Off ACKWindowSize 300 }}
 UDP {{ IPv4_address {local} IPv4_Destination_Address {remote} Port 3780 Interface {interface} Checksum on }}
}}
General {{
 HashSize 1024 HashLimit 4096
 LogFile {OUTPUT}/{actor}.log
 LockFile {OUTPUT}/{actor}.lock
 UNIX {{ Path {OUTPUT}/{actor}.ctl }}
 Filter From Userspace {{ Protocol Accept {{ UDP }} Address Ignore {{ IPv4_address 10.10.0.0/24 }} }}
}}
"""


def setup():
    for actor in ACTORS:
        run("ip", "netns", "add", actor)
        native(actor, "ip", "link", "set", "lo", "up")
        for key, value in (
            ("net.ipv6.conf.all.disable_ipv6", 1),
            ("net.ipv6.conf.default.disable_ipv6", 1),
            ("net.ipv4.conf.all.rp_filter", 0),
            ("net.ipv4.conf.default.rp_filter", 0),
            ("net.ipv4.ip_forward", int(actor in GATEWAYS)),
        ):
            native(
                actor, "sh", "-c", f"echo {value} > /tmp/netlib-proc/sys/{key.replace('.', '/')}"
            )
    interfaces = {actor: [] for actor in ACTORS}
    for index, (label, left, right, first, second) in enumerate(LINKS):
        run("ip", "link", "add", label + "l", "type", "veth", "peer", "name", label + "r")
        for side, (actor, interface, address) in enumerate(
            ((left, label + "l", first), (right, label + "r", second))
        ):
            run("ip", "link", "set", interface, "netns", actor)
            native(
                actor,
                "ip",
                "link",
                "set",
                interface,
                "address",
                f"02:00:00:10:{index:02x}:{side:02x}",
            )
            native(actor, "ip", "address", "add", address, "dev", interface)
            native(actor, "ip", "link", "set", interface, "mtu", "1500", "up")
            native(actor, "python3", "/task/wire/exercise.py", "offload", interface)
            interfaces[actor].append(interface)
    native(
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
    )
    native(
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
    )
    native("b", "ip", "route", "add", "192.0.2.2/32", "via", "192.0.3.2", "dev", "cbr")
    native("b", "ip", "route", "add", "198.51.100.2/32", "via", "198.51.101.2", "dev", "sbr")
    for actor in GATEWAYS:
        native(actor, "ip", "route", "add", "blackhole", "203.0.113.1/32")
        rules = """table ip netlib_nat {
 chain prerouting { type nat hook prerouting priority -100; policy accept; ip daddr 203.0.113.2 udp dport 8080 dnat to 198.51.100.2:9000; }
 chain postrouting { type nat hook postrouting priority 100; policy accept; ip saddr 192.0.2.2 ip daddr 198.51.100.2 udp sport 41000 udp dport 9000 snat to 203.0.113.1:40000; }
}
table ip netlib {
 chain forward { type filter hook forward priority 0; policy drop; ip saddr 192.0.2.2 ip daddr 198.51.100.2 udp sport 41000 udp dport 9000 ct state new,established accept; ct state established accept; }
}
table ip sync_untracked {
 chain prerouting { type filter hook prerouting priority -300; policy accept; ip saddr 10.10.0.0/24 udp dport 3780 notrack; }
 chain output { type filter hook output priority -300; policy accept; ip saddr 10.10.0.0/24 udp dport 3780 notrack; }
}
table ip netlib_late {
 chain late { type filter hook postrouting priority 200; policy accept; }
}
table ip replication_observe {
 chain ingress { type filter hook prerouting priority -450; policy accept; meta l4proto udp udp dport != 3780 meta nftrace set 1; meta l4proto udp udp dport != 3780 counter log prefix "INGRESS" group 42 snaplen 65531 queue-threshold 1; }
 chain tracked { type filter hook prerouting priority -199; policy accept; meta l4proto udp udp dport != 3780 ct state new counter comment "NEW"; meta l4proto udp udp dport != 3780 ct state established counter comment "ESTABLISHED"; meta l4proto udp udp dport != 3780 counter log prefix "TRACKED" group 42 snaplen 65531 queue-threshold 1; }
 chain egress { type filter hook postrouting priority 210; policy accept; meta l4proto udp udp dport != 3780 counter log prefix "EGRESS" group 42 snaplen 65531 queue-threshold 1; }
}
"""
        path = OUTPUT / f"{actor}-initial.nft"
        path.write_text(rules)
        native(actor, "nft", "-f", str(path))
        (OUTPUT / f"{actor}.conf").write_text(configuration(actor))
    return interfaces


def observations(label):
    result = {"conntrack": {}, "tables": {}, "networks": {}}
    for actor in GATEWAYS:
        name = f"{label}-{actor}-conntrack.json"
        index, _ = native(
            actor, "python3", "/task/capture_conntrack.py", "--output", str(OUTPUT / name)
        )
        result["conntrack"][actor] = {"file": name, "command": index}
        result["tables"][actor] = export(
            actor, f"{label}-{actor}-nftables.json", "nft", "-j", "-a", "list", "ruleset"
        )
    for actor in ACTORS:
        result["networks"][actor] = {}
        for kind, arguments in (
            ("links", ("link", "show")),
            ("addresses", ("address", "show")),
            ("routes", ("-4", "route", "show", "table", "main")),
            ("rules", ("-4", "rule", "show")),
            ("neighbors", ("neigh", "show")),
        ):
            result["networks"][actor][kind] = export(
                actor, f"{label}-{actor}-{kind}.json", "ip", "-j", *arguments
            )
    return result


def capture():
    OUTPUT.mkdir(parents=True, exist_ok=True)
    start = time.monotonic_ns()
    interfaces = setup()
    processes, observers = [], []
    endpoints_ = []
    events = []
    manifest = {
        "schema": 1,
        "profile": "conntrackd-ftfw-udp-handoff",
        "startNs": start,
        "byteorder": sys.byteorder,
        "interfaces": interfaces,
        "events": events,
    }
    manifest["settings"] = {
        actor: export(
            actor,
            f"{actor}-settings.txt",
            "sysctl",
            "net.ipv4.ip_forward",
            "net.ipv4.conf.all.rp_filter",
            "net.ipv4.conf.default.rp_filter",
            "net.ipv6.conf.all.disable_ipv6",
            "net.ipv6.conf.default.disable_ipv6",
            "net.netfilter.nf_conntrack_udp_timeout",
            "net.netfilter.nf_conntrack_udp_timeout_stream",
            *(f"net.ipv4.conf.{interface}.rp_filter" for interface in interfaces[actor]),
        )
        for actor in ACTORS
    }
    try:
        for actor in ACTORS:
            command = [
                "ip",
                "netns",
                "exec",
                actor,
                "python3",
                TASK,
                "sniff",
                str(OUTPUT / f"{actor}-frames.jsonl"),
                actor,
                *interfaces[actor],
            ]
            process = subprocess.Popen(command, text=True, stdout=subprocess.PIPE)
            ready = json.loads(process.stdout.readline())
            processes.append(process)
            observers.append(
                {
                    "kind": "packet",
                    "actor": actor,
                    "command": command,
                    "ready": ready,
                    "file": f"{actor}-frames.jsonl",
                }
            )
        for actor in GATEWAYS:
            command = [
                "ip",
                "netns",
                "exec",
                actor,
                "python3",
                "/task/replication/nflog.py",
                str(OUTPUT / f"{actor}-nflog.jsonl"),
                "42",
            ]
            process = subprocess.Popen(command, text=True, stdout=subprocess.PIPE)
            ready = json.loads(process.stdout.readline())
            processes.append(process)
            observers.append(
                {
                    "kind": "nflog",
                    "actor": actor,
                    "command": command,
                    "ready": ready,
                    "file": f"{actor}-nflog.jsonl",
                }
            )
            command = ["ip", "netns", "exec", actor, "nft", "monitor", "trace"]
            with (
                (OUTPUT / f"{actor}-trace.txt").open("w") as output,
                (OUTPUT / f"{actor}-trace-errors.txt").open("w") as errors,
            ):
                process = subprocess.Popen(command, text=True, stdout=output, stderr=errors)
            processes.append(process)
            observers.append(
                {
                    "kind": "trace",
                    "actor": actor,
                    "command": command,
                    "startNs": time.monotonic_ns(),
                    "file": f"{actor}-trace.txt",
                    "errors": f"{actor}-trace-errors.txt",
                }
            )
        time.sleep(0.1)
        for actor in GATEWAYS:
            native(actor, "conntrackd", "-C", str(OUTPUT / f"{actor}.conf"), "-d")
            native(actor, "conntrackd", "-C", str(OUTPUT / f"{actor}.conf"), "-s", "runtime")
        manifest["initial"] = observations("initial")
        manifest["initialCaches"] = {
            actor: export(
                actor,
                f"initial-{actor}-cache.xml",
                "conntrackd",
                "-C",
                str(OUTPUT / f"{actor}.conf"),
                "-e",
                "-x",
            )
            for actor in GATEWAYS
        }
        client = Endpoint("client", "192.0.2.2", 41000)
        server = Endpoint("server", "198.51.100.2", 9000)
        endpoints_ = [client, server]

        def event(name, kind, operation, **fields):
            row = {"id": name, "type": kind, "startNs": time.monotonic_ns(), **fields}
            row["before"] = observations(name + "-before")
            mark = len(COMMANDS)
            row["result"] = operation()
            row["commands"] = list(range(mark, len(COMMANDS)))
            row["after"] = observations(name + "-after")
            row["endNs"] = time.monotonic_ns()
            events.append(row)
            return row

        def packet(sender, receiver, peer, payload):
            return {
                "sender": sender.call(
                    "send", peer=peer, payloadHex=payload.encode("ascii").hex(), ttl=64
                ),
                "receiver": receiver.call("receive", timeout=0.3),
            }

        event(
            "establish",
            "packet",
            lambda: packet(client, server, ["203.0.113.2", 8080], "replication:establish"),
            gateway="a",
            leg="original",
        )

        def stage():
            attempts = []
            for index in range(40):
                found = export(
                    "b",
                    f"stage-b-cache-{index}.xml",
                    "conntrackd",
                    "-C",
                    str(OUTPUT / "b.conf"),
                    "-e",
                    "-x",
                )
                attempts.append(found)
                if "<sport>41000</sport>" in (OUTPUT / found["file"]).read_text():
                    return {
                        "external": found,
                        "attempts": attempts,
                        "internal": export(
                            "a",
                            "stage-a-internal.xml",
                            "conntrackd",
                            "-C",
                            str(OUTPUT / "a.conf"),
                            "-i",
                            "-x",
                        ),
                    }
                time.sleep(0.05)
            raise RuntimeError("Replica did not reach the external cache.")

        event("replicate", "stage", stage, source="a", destination="b")
        event(
            "client-route",
            "handoff",
            lambda: native(
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
            )[0],
            leg="original",
            source="a",
            destination="b",
        )
        event(
            "server-route",
            "handoff",
            lambda: native(
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
            )[0],
            leg="reply",
            source="a",
            destination="b",
        )
        event(
            "fence-primary",
            "fence",
            lambda: [
                native("a", "ip", "link", "set", interface, "down")[0]
                for interface in ("car", "sar")
            ],
            gateway="a",
        )
        event(
            "uncommitted",
            "packet",
            lambda: packet(server, client, ["203.0.113.1", 40000], "replication:uncommitted"),
            gateway="b",
            leg="reply",
        )
        event(
            "commit",
            "commit",
            lambda: native("b", "conntrackd", "-C", str(OUTPUT / "b.conf"), "-c")[0],
            gateway="b",
        )
        event(
            "install-deny",
            "policy",
            lambda: native("b", "nft", "flush", "chain", "ip", "netlib", "forward")[0],
            gateway="b",
            policy="deny",
        )
        event(
            "denied",
            "packet",
            lambda: packet(server, client, ["203.0.113.1", 40000], "replication:denied"),
            gateway="b",
            leg="reply",
        )
        event(
            "install-permit",
            "policy",
            lambda: native(
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
            )[0],
            gateway="b",
            policy="permit-established",
        )
        event(
            "permitted",
            "packet",
            lambda: packet(server, client, ["203.0.113.1", 40000], "replication:permitted"),
            gateway="b",
            leg="reply",
        )
        event(
            "continued-original",
            "packet",
            lambda: packet(client, server, ["203.0.113.2", 8080], "replication:continued-original"),
            gateway="b",
            leg="original",
        )
        event(
            "continued-reply",
            "packet",
            lambda: packet(server, client, ["203.0.113.1", 40000], "replication:continued-reply"),
            gateway="b",
            leg="reply",
        )
        manifest["final"] = observations("final")
        manifest["finalCaches"] = {
            actor: export(
                actor,
                f"final-{actor}-cache.xml",
                "conntrackd",
                "-C",
                str(OUTPUT / f"{actor}.conf"),
                "-e",
                "-x",
            )
            for actor in GATEWAYS
        }
        manifest["statistics"] = {
            actor: {
                kind: export(
                    actor,
                    f"{actor}-{kind}-statistics.txt",
                    "conntrackd",
                    "-C",
                    str(OUTPUT / f"{actor}.conf"),
                    "-s",
                    kind,
                )
                for kind in ("cache", "network", "runtime", "ct")
            }
            for actor in GATEWAYS
        }
    finally:
        manifest["endpoints"] = [endpoint.close() for endpoint in endpoints_]
        for actor in GATEWAYS:
            if (OUTPUT / f"{actor}.ctl").exists():
                native(actor, "conntrackd", "-C", str(OUTPUT / f"{actor}.conf"), "-k")
        time.sleep(0.15)
        for process, observer in zip(processes, observers, strict=True):
            observer["runningBeforeStop"] = process.poll() is None
            observer["stopNs"] = time.monotonic_ns()
            observer["stopSignal"] = signal.SIGTERM
            process.send_signal(signal.SIGTERM)
            observer["returncode"] = process.wait(timeout=5)
            observer["endNs"] = time.monotonic_ns()
        manifest["observers"] = observers
        manifest["endNs"] = time.monotonic_ns()
        save("commands.json", COMMANDS)
        save("capture.json", manifest)
        if any(
            not observer["runningBeforeStop"]
            or observer["returncode"] != (-signal.SIGTERM if observer["kind"] == "trace" else 0)
            for observer in observers
        ):
            raise RuntimeError("An observation process failed.")


if __name__ == "__main__":
    if sys.argv[1] == "endpoint":
        endpoints()
    elif sys.argv[1] == "sniff":
        sniff()
    else:
        capture()
