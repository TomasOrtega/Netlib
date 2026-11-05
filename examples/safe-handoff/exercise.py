"""Capture queued route admissions, current-policy service, and a guarded handoff."""

import importlib.util
import ipaddress
import json
import signal
import struct
import subprocess
import sys
import time
from pathlib import Path

SPEC = importlib.util.spec_from_file_location("replication_base", "/task/replication/exercise.py")
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
BASE.OUTPUT = Path("/tmp/netlib-safe-handoff")
BASE.TASK = "/task/safe-handoff/exercise.py"
TC = "/opt/netlib/sbin/tc"
POLLS = []


def queue(label, interface):
    return BASE.export(
        "client",
        f"{label}-{interface}-qdisc.json",
        TC,
        "-j",
        "-s",
        "-d",
        "qdisc",
        "show",
        "dev",
        interface,
    )


def observations(label):
    result = BASE.observations(label)
    result["qdiscs"] = {interface: queue(label, interface) for interface in ("cal", "cbl")}
    result["endpointTables"] = {
        actor: BASE.export(
            actor, f"{label}-{actor}-nftables.json", "nft", "-j", "-a", "list", "ruleset"
        )
        for actor in ("client", "server")
    }
    return result


def setup():
    interfaces = BASE.setup()
    for index, (label, left, right, first, second) in enumerate(BASE.LINKS):
        for side, (actor, address) in enumerate(((left, second), (right, first))):
            interface = label + ("l" if side == 0 else "r")
            BASE.native(
                actor,
                "ip",
                "neigh",
                "replace",
                str(ipaddress.ip_interface(address).ip),
                "lladdr",
                f"02:00:00:10:{index:02x}:{1 - side:02x}",
                "nud",
                "permanent",
                "dev",
                interface,
            )
    for actor in ("client", "server"):
        path = BASE.OUTPUT / f"{actor}-admission.nft"
        path.write_text(
            "table ip handoff_admission {\n"
            " chain admission { type filter hook postrouting priority 210; policy accept; "
            'meta l4proto udp counter log prefix "ROUTE_ADMIT" group 43 snaplen 65531 queue-threshold 1; }\n'
            "}\n"
        )
        BASE.native(actor, "nft", "-f", str(path))
    return interfaces


def payload(raw):
    message = bytes.fromhex(raw)
    offset = 20
    while offset < len(message):
        length, kind = struct.unpack_from("=HH", message, offset)
        if length < 4 or offset + length > len(message):
            raise RuntimeError("Malformed admission log attribute.")
        if kind == 9:
            packet = message[offset + 4 : offset + length]
            ihl = (packet[0] & 15) * 4
            return packet[ihl + 8 : int.from_bytes(packet[2:4], "big")].hex()
        offset += (length + 3) & ~3
    return None


def admission(actor, marker):
    start = time.monotonic_ns()
    path = BASE.OUTPUT / f"{actor}-nflog.jsonl"
    attempts = []
    while time.monotonic_ns() - start < 5_000_000_000:
        beginning = time.monotonic_ns()
        lines = path.read_text().splitlines()
        selected = None
        for number, line in enumerate(lines, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            if payload(row["hex"]) == marker:
                if selected is not None:
                    raise RuntimeError("The admission marker is not unique.")
                selected = (number, row)
        attempts.append(
            {
                "startNs": beginning,
                "endNs": time.monotonic_ns(),
                "lineCount": len(lines),
                "selectedLine": selected[0] if selected else None,
            }
        )
        if selected:
            result = {
                "actor": actor,
                "payloadHex": marker,
                "startNs": start,
                "endNs": time.monotonic_ns(),
                "attempts": attempts,
                "source": f"{path.name}:{selected[0]}",
                "record": selected[1],
            }
            index = len(POLLS)
            POLLS.append(result)
            return {"poll": index, "source": result["source"]}
        time.sleep(0.002)
    raise RuntimeError("The endpoint admission was not observed.")


def capture():
    BASE.OUTPUT.mkdir(parents=True, exist_ok=True)
    started = time.monotonic_ns()
    interfaces = setup()
    processes, observers, endpoints, events = [], [], [], []
    manifest = {
        "schema": 1,
        "profile": "queued-ftfw-safe-handoff",
        "startNs": started,
        "byteorder": sys.byteorder,
        "interfaces": interfaces,
        "events": events,
        "admissionPolls": "admission-polls.json",
    }
    manifest["settings"] = {
        actor: BASE.export(
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
        for actor in BASE.ACTORS
    }
    try:
        for actor in BASE.ACTORS:
            command = [
                "ip",
                "netns",
                "exec",
                actor,
                "python3",
                BASE.TASK,
                "sniff",
                str(BASE.OUTPUT / f"{actor}-frames.jsonl"),
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
        for actor in BASE.ACTORS:
            group = 42 if actor in BASE.GATEWAYS else 43
            command = [
                "ip",
                "netns",
                "exec",
                actor,
                "python3",
                "/task/replication/nflog.py",
                str(BASE.OUTPUT / f"{actor}-nflog.jsonl"),
                str(group),
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
        for actor in BASE.GATEWAYS:
            command = ["ip", "netns", "exec", actor, "nft", "monitor", "trace"]
            with (
                (BASE.OUTPUT / f"{actor}-trace.txt").open("w") as out,
                (BASE.OUTPUT / f"{actor}-trace-errors.txt").open("w") as err,
            ):
                process = subprocess.Popen(command, stdout=out, stderr=err)
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
        for actor in BASE.GATEWAYS:
            BASE.native(actor, "conntrackd", "-C", str(BASE.OUTPUT / f"{actor}.conf"), "-d")
            BASE.native(
                actor, "conntrackd", "-C", str(BASE.OUTPUT / f"{actor}.conf"), "-s", "runtime"
            )
        manifest["initial"] = observations("initial")
        manifest["initialCaches"] = {
            actor: BASE.export(
                actor,
                f"initial-{actor}-cache.xml",
                "conntrackd",
                "-C",
                str(BASE.OUTPUT / f"{actor}.conf"),
                "-e",
                "-x",
            )
            for actor in BASE.GATEWAYS
        }
        client = BASE.Endpoint("client", "192.0.2.2", 41000)
        server = BASE.Endpoint("server", "198.51.100.2", 9000)
        endpoints = [client, server]

        def event(name, kind, operation, **fields):
            row = {"id": name, "type": kind, "startNs": time.monotonic_ns(), **fields}
            row["before"] = observations(name + "-before")
            mark, poll_mark = len(BASE.COMMANDS), len(POLLS)
            row["result"] = operation()
            row["commands"] = list(range(mark, len(BASE.COMMANDS)))
            row["polls"] = list(range(poll_mark, len(POLLS)))
            row["after"] = observations(name + "-after")
            row["endNs"] = time.monotonic_ns()
            events.append(row)
            return row

        def send(endpoint, actor, name, peer):
            marker = ("safe-handoff:" + name).encode("ascii").hex()
            sender = endpoint.call("send", peer=peer, payloadHex=marker, ttl=64)
            return {"sender": sender, "admission": admission(actor, marker)}

        def packet(sender, receiver, actor, name, peer):
            result = send(sender, actor, name, peer)
            result["receiver"] = receiver.call("receive", timeout=0.3)
            return result

        event(
            "establish",
            "packet",
            lambda: packet(client, server, "client", "establish", ["203.0.113.2", 8080]),
            gateway="a",
            leg="original",
        )

        def stage():
            attempts = []
            for index in range(40):
                reference = BASE.export(
                    "b",
                    f"stage-b-cache-{index}.xml",
                    "conntrackd",
                    "-C",
                    str(BASE.OUTPUT / "b.conf"),
                    "-e",
                    "-x",
                )
                attempts.append(reference)
                if "<sport>41000</sport>" in (BASE.OUTPUT / reference["file"]).read_text():
                    return {
                        "external": reference,
                        "attempts": attempts,
                        "internal": BASE.export(
                            "a",
                            "stage-a-internal.xml",
                            "conntrackd",
                            "-C",
                            str(BASE.OUTPUT / "a.conf"),
                            "-i",
                            "-x",
                        ),
                    }
                time.sleep(0.05)
            raise RuntimeError("The source binding was not replicated.")

        event("replicate", "stage", stage, source="a", destination="b")
        event(
            "commit",
            "commit",
            lambda: BASE.native("b", "conntrackd", "-C", str(BASE.OUTPUT / "b.conf"), "-c")[0],
            gateway="b",
        )
        event(
            "install-primary-delay",
            "qdisc",
            lambda: BASE.native(
                "client",
                TC,
                "qdisc",
                "add",
                "dev",
                "cal",
                "root",
                "handle",
                "10:",
                "netem",
                "limit",
                "16",
                "delay",
                "2500ms",
            )[0],
            interface="cal",
            delayMilliseconds=2500,
        )
        event(
            "admit-primary",
            "admit",
            lambda: send(client, "client", "held-primary", ["203.0.113.2", 8080]),
            gateway="a",
            leg="original",
            ticket=0,
        )
        event(
            "client-route",
            "handoff",
            lambda: BASE.native(
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
            lambda: BASE.native(
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
            "overtake-request",
            "packet",
            lambda: packet(client, server, "client", "overtake-request", ["203.0.113.2", 8080]),
            gateway="b",
            leg="original",
            ticket=1,
        )
        event(
            "overtake-reply",
            "packet",
            lambda: packet(server, client, "server", "overtake-reply", ["203.0.113.1", 40000]),
            gateway="b",
            leg="reply",
            ticket=2,
        )
        event(
            "serve-primary",
            "serve",
            lambda: {"receiver": server.call("receive", timeout=4)},
            gateway="a",
            leg="original",
            ticket=0,
        )

        def barrier(name, interface, ticket, completion):
            reference = queue(name, interface)
            index, _ = BASE.native("client", TC, "qdisc", "del", "dev", interface, "root")
            return {
                "qdisc": reference,
                "ticket": ticket,
                "completion": completion,
                "deleteCommand": index,
            }

        event(
            "primary-barrier",
            "barrier",
            lambda: barrier("primary-barrier", "cal", 0, "serve-primary"),
            gateway="a",
        )
        event(
            "fence-primary",
            "fence",
            lambda: [
                BASE.native("a", "ip", "link", "set", interface, "down")[0]
                for interface in ("car", "sar")
            ],
            gateway="a",
        )
        event(
            "install-standby-delay",
            "qdisc",
            lambda: BASE.native(
                "client",
                TC,
                "qdisc",
                "add",
                "dev",
                "cbl",
                "root",
                "handle",
                "20:",
                "netem",
                "limit",
                "16",
                "delay",
                "1500ms",
            )[0],
            interface="cbl",
            delayMilliseconds=1500,
        )
        event(
            "admit-standby",
            "admit",
            lambda: send(client, "client", "held-standby", ["203.0.113.2", 8080]),
            gateway="b",
            leg="original",
            ticket=3,
        )
        event(
            "install-deny",
            "policy",
            lambda: BASE.native("b", "nft", "flush", "chain", "ip", "netlib", "forward")[0],
            gateway="b",
            policy="deny",
        )
        event(
            "serve-standby",
            "serve",
            lambda: {"receiver": server.call("receive", timeout=2)},
            gateway="b",
            leg="original",
            ticket=3,
        )
        event(
            "standby-barrier",
            "barrier",
            lambda: barrier("standby-barrier", "cbl", 3, "serve-standby"),
            gateway="b",
        )
        event(
            "install-permit",
            "policy",
            lambda: BASE.native(
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
            "continued-request",
            "packet",
            lambda: packet(client, server, "client", "continued-request", ["203.0.113.2", 8080]),
            gateway="b",
            leg="original",
            ticket=4,
        )
        event(
            "continued-reply",
            "packet",
            lambda: packet(server, client, "server", "continued-reply", ["203.0.113.1", 40000]),
            gateway="b",
            leg="reply",
            ticket=5,
        )
        manifest["final"] = observations("final")
        manifest["finalCaches"] = {
            actor: BASE.export(
                actor,
                f"final-{actor}-cache.xml",
                "conntrackd",
                "-C",
                str(BASE.OUTPUT / f"{actor}.conf"),
                "-e",
                "-x",
            )
            for actor in BASE.GATEWAYS
        }
        manifest["statistics"] = {
            actor: {
                kind: BASE.export(
                    actor,
                    f"{actor}-{kind}-statistics.txt",
                    "conntrackd",
                    "-C",
                    str(BASE.OUTPUT / f"{actor}.conf"),
                    "-s",
                    kind,
                )
                for kind in ("cache", "network", "runtime", "ct")
            }
            for actor in BASE.GATEWAYS
        }
    finally:
        manifest["endpoints"] = [endpoint.close() for endpoint in endpoints]
        for actor in BASE.GATEWAYS:
            if (BASE.OUTPUT / f"{actor}.ctl").exists():
                BASE.native(actor, "conntrackd", "-C", str(BASE.OUTPUT / f"{actor}.conf"), "-k")
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
        BASE.save("commands.json", BASE.COMMANDS)
        BASE.save("admission-polls.json", POLLS)
        BASE.save("capture.json", manifest)
        if any(
            not observer["runningBeforeStop"]
            or observer["returncode"] != (-signal.SIGTERM if observer["kind"] == "trace" else 0)
            for observer in observers
        ):
            raise RuntimeError("An observer failed during capture.")


if __name__ == "__main__":
    if sys.argv[1] == "endpoint":
        BASE.endpoints()
    elif sys.argv[1] == "sniff":
        BASE.sniff()
    else:
        capture()
