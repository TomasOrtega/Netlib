"""Capture interface-bound ingress guards before ordinary tracked forwarding."""

import importlib.util
import ipaddress
import json
import os
import shutil
import signal
import socket
import struct
import subprocess
import sys
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

SPEC = importlib.util.spec_from_file_location("queued_base", "/task/safe-handoff/exercise.py")
SAFE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SAFE)
BASE = SAFE.BASE
ATTACHMENT_TASK = "/task/attachments/exercise.py"
CAMPUS_TASK = "/task/campus/exercise.py"
BASE.TASK = ATTACHMENT_TASK
BASE.ACTORS = (*BASE.ACTORS, "attacker")
INPUT = Path("/task/attachments/input")
RUNTIME = Path("/run/netlib-attachments")
AUTH = "02:00:00:00:ea:01"
PEER = "02:00:00:00:ea:02"
ARCHIVED = False
ATTACK_LINKS = (
    ("aa", "a", "172.20.0.2/30", "172.20.0.1/30", 0),
    ("ab", "b", "172.20.1.2/30", "172.20.1.1/30", 1),
)


def identity():
    return {
        "namespace": os.readlink("/proc/self/ns/net"),
        "observedNs": time.monotonic_ns(),
        "pid": os.getpid(),
        "interfaces": [{"ifindex": index, "name": name} for index, name in socket.if_nameindex()],
    }


def queue(label, interface):
    actor = "server" if interface == "sbl" else "client"
    return BASE.export(
        actor,
        f"{label}-{interface}-qdisc.json",
        SAFE.TC,
        "-j",
        "-s",
        "-d",
        "qdisc",
        "show",
        "dev",
        interface,
    )


def attachment_setup(interfaces):
    for label, actor, first, second, number in ATTACK_LINKS:
        left, right = label + "l", label + "r"
        BASE.run("ip", "link", "add", left, "type", "veth", "peer", "name", right)
        for side, (namespace, interface, address) in enumerate(
            (("attacker", left, first), (actor, right, second))
        ):
            BASE.run("ip", "link", "set", interface, "netns", namespace)
            BASE.native(
                namespace,
                "ip",
                "link",
                "set",
                interface,
                "address",
                f"02:00:00:20:{number:02x}:{side:02x}",
            )
            BASE.native(namespace, "ip", "address", "add", address, "dev", interface)
            BASE.native(namespace, "ip", "link", "set", interface, "mtu", "1500", "up")
            BASE.native(namespace, "python3", "/task/wire/exercise.py", "offload", interface)
            interfaces[namespace].append(interface)
        for side, (namespace, interface, peer) in enumerate(
            (("attacker", left, second), (actor, right, first))
        ):
            BASE.native(
                namespace,
                "ip",
                "neigh",
                "replace",
                str(ipaddress.ip_interface(peer).ip),
                "lladdr",
                f"02:00:00:20:{number:02x}:{1 - side:02x}",
                "nud",
                "permanent",
                "dev",
                interface,
            )
    for actor in BASE.GATEWAYS:
        BASE.native(
            actor, "sh", "-c", "echo 1 > /tmp/netlib-proc/sys/net/netfilter/nf_conntrack_acct"
        )


def tuple_match(source, sport, destination, dport):
    return [
        {
            "match": {
                "op": "==",
                "left": {"payload": {"protocol": "ip", "field": "saddr"}},
                "right": source,
            }
        },
        {
            "match": {
                "op": "==",
                "left": {"payload": {"protocol": "ip", "field": "daddr"}},
                "right": destination,
            }
        },
        {"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 17}},
        {
            "match": {
                "op": "==",
                "left": {"payload": {"protocol": "udp", "field": "sport"}},
                "right": sport,
            }
        },
        {
            "match": {
                "op": "==",
                "left": {"payload": {"protocol": "udp", "field": "dport"}},
                "right": dport,
            }
        },
    ]


def guard_document(actor, ports, peer_port, active, replace):
    objects = [{"metainfo": {"json_schema_version": 1}}]
    if replace:
        objects.append({"delete": {"table": {"family": "ip", "name": "netlib_attachment"}}})
    objects.extend(
        [
            {"table": {"family": "ip", "name": "netlib_attachment"}},
            {
                "chain": {
                    "family": "ip",
                    "table": "netlib_attachment",
                    "name": "ingress",
                    "type": "filter",
                    "hook": "prerouting",
                    "prio": -300,
                    "policy": "drop",
                }
            },
        ]
    )

    def rule(role, expressions):
        objects.append(
            {
                "rule": {
                    "family": "ip",
                    "table": "netlib_attachment",
                    "chain": "ingress",
                    "comment": role,
                    "expr": expressions,
                }
            }
        )

    def interface(role):
        return {"match": {"op": "==", "left": {"meta": {"key": "iif"}}, "right": ports[role]}}

    def log(prefix):
        return {"log": {"prefix": prefix, "group": 42, "snaplen": 65531, "queue-threshold": 1}}

    local, peer = ("10.10.0.1", "10.10.0.2") if actor == "a" else ("10.10.0.2", "10.10.0.1")
    rule(
        "SYNC",
        [interface("maintenance"), *tuple_match(peer, peer_port, local, 3780), {"accept": None}],
    )
    if active:
        rule(
            "ORIGINAL",
            [
                interface("original"),
                *tuple_match("192.0.2.2", 41000, "203.0.113.2", 8080),
                log("ATTACH_ALLOW"),
                {"accept": None},
            ],
        )
        rule(
            "REPLY",
            [
                interface("reply"),
                *tuple_match("198.51.100.2", 9000, "203.0.113.1", 40000),
                log("ATTACH_ALLOW"),
                {"accept": None},
            ],
        )
    rule("FALLBACK", [log("ATTACH_DROP"), {"drop": None}])
    return {"nftables": objects}


def load_guard(name, actor, active, authentication_port, socket_sources, replace=False):
    links = BASE.export(actor, name + "-links.json", "ip", "-j", "link", "show")
    context = BASE.export(actor, name + "-identity.json", "python3", ATTACHMENT_TASK, "identity")
    rows = json.loads((BASE.OUTPUT / links["file"]).read_text())
    names = {
        "original": "car" if actor == "a" else "cbr",
        "reply": "sar" if actor == "a" else "sbr",
        "maintenance": "syncl" if actor == "a" else "syncr",
    }
    ports = {
        role: next(row["ifindex"] for row in rows if row["ifname"] == interface)
        for role, interface in names.items()
    }
    peer = "b" if actor == "a" else "a"
    socket_source = socket_sources[peer]
    sockets = json.loads((BASE.OUTPUT / socket_source["file"]).read_text())["sockets"]
    outgoing = [item for item in sockets if item["local"]["port"] != 3780]
    if len(outgoing) != 1:
        raise RuntimeError("The peer daemon has no unique outgoing UDP socket.")
    peer_port = outgoing[0]["local"]["port"]
    binding = {
        "gateway": actor,
        "namespace": json.loads((BASE.OUTPUT / context["file"]).read_text())["namespace"],
        "scope": {"resource": "campus-application", "operation": "use"},
        "principal": "alice@campus.example.test",
        "authenticationEvent": "authenticate",
        "credentialEvent": "credential",
        "authenticationPort": authentication_port,
        "currentAuthenticationEvent": "credential" if active else "logoff",
        "active": active,
        "maintenanceSource": {
            "gateway": peer,
            "sourcePort": peer_port,
            "socketInode": outgoing[0]["inode"],
            "source": socket_source,
        },
        "roles": [
            {"role": role, "interface": names[role], "ifindex": index}
            for role, index in ports.items()
        ],
        "sources": {"links": links, "identity": context},
    }
    binding_name, load_name = name + "-bindings.json", name + "-load.json"
    BASE.save(binding_name, binding)
    BASE.save(load_name, guard_document(actor, ports, peer_port, active, replace))
    command, _ = BASE.native(actor, "nft", "-j", "-f", str(BASE.OUTPUT / load_name))
    return {
        "command": command,
        "file": load_name,
        "active": active,
        "binding": {"file": binding_name, "sources": binding["sources"]},
    }


def raw_frame(gateway, direction, marker, number):
    original = direction == "original"
    source, sport, destination, dport = (
        ("192.0.2.2", 41000, "203.0.113.2", 8080)
        if original
        else ("198.51.100.2", 9000, "203.0.113.1", 40000)
    )
    payload = ("attachments:" + marker).encode("ascii")
    src, dst = ipaddress.IPv4Address(source).packed, ipaddress.IPv4Address(destination).packed

    def checksum(data):
        if len(data) % 2:
            data += bytes(1)
        value = sum(struct.unpack(f"!{len(data) // 2}H", data))
        while value >> 16:
            value = (value & 65535) + (value >> 16)
        return (~value) & 65535

    udp = struct.pack("!HHHH", sport, dport, 8 + len(payload), 0) + payload
    udp_sum = checksum(src + dst + struct.pack("!BBH", 0, 17, len(udp)) + udp) or 65535
    udp = udp[:6] + struct.pack("!H", udp_sum) + udp[8:]
    ip = struct.pack(
        "!BBHHHBBH4s4s", 0x45, 0, 20 + len(udp), 0xD000 + number, 0x4000, 64, 17, 0, src, dst
    )
    ip = ip[:10] + struct.pack("!H", checksum(ip)) + ip[12:]
    peer = 0 if gateway == "a" else 1
    spoof = (0 if gateway == "a" else 1) if original else (2 if gateway == "a" else 3)
    return bytes.fromhex(f"02000020{peer:02x}0102000010{spoof:02x}000800") + ip + udp


def raw_send(path):
    document = json.loads(Path(path).read_text())
    sock = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(3))
    sock.bind((document["interface"], 0))
    raw = bytes.fromhex(document["rawEthernet"])
    start = time.monotonic_ns()
    count = sock.send(raw)
    end = time.monotonic_ns()
    print(
        json.dumps(
            {
                "startNs": start,
                "endNs": end,
                "bytesSent": count,
                "rawEthernet": raw.hex(),
                "interface": document["interface"],
                "ifindex": socket.if_nametoindex(document["interface"]),
                "namespace": os.readlink("/proc/self/ns/net"),
            }
        )
    )
    sock.close()


def load_policy(name, actor, policy):
    document = json.loads((INPUT / f"{policy}.json").read_text())
    objects = document["nftables"]
    batch = {
        "nftables": [
            objects[0],
            {"delete": {"table": {"family": "ip", "name": "netlib"}}},
            *objects[1:],
        ]
    }
    filename = name + "-load.json"
    BASE.save(filename, batch)
    command, _ = BASE.native(actor, "nft", "-j", "-f", str(BASE.OUTPUT / filename))
    return {"command": command, "file": filename, "inputPolicy": f"input/{policy}.json"}


def daemon_sockets():
    start = time.monotonic_ns()
    namespace = os.readlink("/proc/self/ns/net")
    processes, owners = [], {}
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            comm = (process / "comm").read_text().strip()
            if comm != "conntrackd" or os.readlink(process / "ns/net") != namespace:
                continue
            command = [
                os.fsdecode(value)
                for value in (process / "cmdline").read_bytes().split(bytes(1))
                if value
            ]
            fields = (process / "stat").read_text().rsplit(")", 1)[1].split()
            record = {
                "pid": int(process.name),
                "comm": comm,
                "cmdline": command,
                "namespace": namespace,
                "startTimeTicks": int(fields[19]),
                "fdSockets": [],
            }
            for fd in (process / "fd").iterdir():
                target = os.readlink(fd)
                if target.startswith("socket:[") and target.endswith("]"):
                    inode = int(target[8:-1])
                    item = {"pid": int(process.name), "fd": int(fd.name)}
                    record["fdSockets"].append({"fd": int(fd.name), "inode": inode})
                    owners.setdefault(inode, []).append(item)
            processes.append(record)
        except (FileNotFoundError, ProcessLookupError):
            continue

    def address(text):
        host, port = text.split(":")
        return {
            "address": str(ipaddress.IPv4Address(struct.pack("=I", int(host, 16)))),
            "port": int(port, 16),
        }

    sockets = []
    for line in Path("/proc/self/net/udp").read_text().splitlines()[1:]:
        fields = line.split()
        inode = int(fields[9])
        if inode in owners:
            sockets.append(
                {
                    "inode": inode,
                    "local": address(fields[1]),
                    "remote": address(fields[2]),
                    "state": fields[3],
                    "owners": owners[inode],
                }
            )
    print(
        json.dumps(
            {
                "startNs": start,
                "endNs": time.monotonic_ns(),
                "namespace": namespace,
                "processes": processes,
                "sockets": sockets,
            }
        )
    )


def observations(label):
    gateways = ("b",) if ARCHIVED else BASE.GATEWAYS
    actors = tuple(actor for actor in BASE.ACTORS if actor != "a" or not ARCHIVED)
    result = {"conntrack": {}, "tables": {}, "networks": {}, "identities": {}}
    for actor in gateways:
        name = f"{label}-{actor}-conntrack.json"
        command, _ = BASE.native(
            actor, "python3", "/task/capture_conntrack.py", "--output", str(BASE.OUTPUT / name)
        )
        result["conntrack"][actor] = {"file": name, "command": command}
        result["tables"][actor] = BASE.export(
            actor, f"{label}-{actor}-nftables.json", "nft", "-j", "-a", "list", "ruleset"
        )
    for actor in actors:
        result["identities"][actor] = BASE.export(
            actor, f"{label}-{actor}-identity.json", "python3", ATTACHMENT_TASK, "identity"
        )
        result["networks"][actor] = {}
        for kind, arguments in (
            ("links", ("link", "show")),
            ("addresses", ("address", "show")),
            ("routes", ("-4", "route", "show", "table", "main")),
            ("rules", ("-4", "rule", "show")),
            ("neighbors", ("neigh", "show")),
        ):
            result["networks"][actor][kind] = BASE.export(
                actor, f"{label}-{actor}-{kind}.json", "ip", "-j", *arguments
            )
    result["qdiscs"] = {interface: queue(label, interface) for interface in ("cal", "cbl", "sbl")}
    result["endpointTables"] = {
        actor: BASE.export(
            actor, f"{label}-{actor}-nftables.json", "nft", "-j", "-a", "list", "ruleset"
        )
        for actor in ("client", "server")
    }
    if ARCHIVED:
        result["archivedA"] = {"boundary": "withdraw-primary:before"}
    return result


def namespace_lifetimes():
    result = {}
    for actor in (*BASE.ACTORS, "auth"):
        birth = next(
            index
            for index, command in enumerate(BASE.COMMANDS)
            if command["arguments"] == ["ip", "netns", "add", actor]
        )
        reference = BASE.export(
            actor, f"birth-{actor}-identity.json", "python3", ATTACHMENT_TASK, "identity"
        )
        current = json.loads((BASE.OUTPUT / reference["file"]).read_text())
        ports = {}
        for item in current["interfaces"]:
            interface = item["name"]
            if interface == "lo":
                continue
            created = next(
                index
                for index, command in enumerate(BASE.COMMANDS)
                if command["arguments"][:3] == ["ip", "link", "add"]
                and (
                    command["arguments"][3] == interface
                    or ["name", interface]
                    in [
                        command["arguments"][i : i + 2]
                        for i in range(len(command["arguments"]) - 1)
                    ]
                )
            )
            moved = next(
                index
                for index, command in enumerate(BASE.COMMANDS)
                if command["arguments"] == ["ip", "link", "set", interface, "netns", actor]
            )
            up = next(
                index
                for index, command in enumerate(BASE.COMMANDS)
                if command["arguments"][:8]
                == ["ip", "netns", "exec", actor, "ip", "link", "set", interface]
                and "up" in command["arguments"][8:]
            )
            ports[interface] = {
                "ifindex": item["ifindex"],
                "creationCommand": created,
                "moveCommand": moved,
                "upCommand": up,
            }
        result[actor] = {"creationCommand": birth, "identity": reference, "interfaces": ports}
    return result


def auth_network():
    BASE.run("ip", "netns", "add", "auth")
    BASE.native("auth", "ip", "link", "set", "lo", "up")
    for key in ("net.ipv6.conf.all.disable_ipv6", "net.ipv6.conf.default.disable_ipv6"):
        BASE.native("auth", "sh", "-c", f"echo 1 > /tmp/netlib-proc/sys/{key.replace('.', '/')}")
    BASE.run(
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
    for actor, interface in (("auth", "auth0"), ("client", "peer0")):
        BASE.run("ip", "link", "set", interface, "netns", actor)
        BASE.native(actor, "ip", "link", "set", interface, "up")
    return {
        name: {
            kind: BASE.export(actor, f"eap/{name}-{kind}.json", "ip", "-j", *arguments)
            for kind, arguments in (
                ("links", ("link", "show")),
                ("addresses", ("address", "show")),
                ("routes", ("-4", "route", "show", "table", "main")),
                ("rules", ("-4", "rule", "show")),
            )
        }
        for actor, name in (("auth", "auth"), ("client", "peer"))
    }


def eap_sniff():
    active = True

    def stop(*_):
        nonlocal active
        active = False

    signal.signal(signal.SIGTERM, stop)
    sock = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(3))
    sock.bind(("auth0", 0))
    sock.settimeout(0.1)
    print(
        json.dumps(
            {
                "readyNs": time.monotonic_ns(),
                "interface": "auth0",
                "ifindex": socket.if_nametoindex("auth0"),
            }
        ),
        flush=True,
    )
    with Path(sys.argv[2]).open("w") as stream:
        while active:
            try:
                frame, address = sock.recvfrom(65535)
            except TimeoutError:
                continue
            if frame[12:14] == bytes.fromhex("888e"):
                stream.write(
                    json.dumps(
                        {
                            "timeNs": time.monotonic_ns(),
                            "packetType": address[2],
                            "hex": frame.hex(),
                        }
                    )
                    + "\n"
                )
                stream.flush()
    sock.close()


def daemon_stopped():
    started = time.monotonic_ns()
    namespace = os.readlink("/proc/self/ns/net")
    matches = []
    while time.monotonic_ns() - started < 2_000_000_000:
        matches = []
        for process in Path("/proc").iterdir():
            if not process.name.isdigit():
                continue
            try:
                name = (process / "comm").read_text().strip()
                network = os.readlink(process / "ns/net")
            except (FileNotFoundError, ProcessLookupError):
                continue
            if name == "conntrackd" and network == namespace:
                matches.append(int(process.name))
        if not matches:
            break
        time.sleep(0.005)
    print(
        json.dumps(
            {
                "startNs": started,
                "endNs": time.monotonic_ns(),
                "namespace": namespace,
                "matchingProcesses": matches,
            }
        )
    )
    if matches:
        raise RuntimeError("The retired gateway daemon remains running.")


def capture():
    global ARCHIVED
    BASE.OUTPUT.mkdir(parents=True, exist_ok=True)
    (BASE.OUTPUT / "eap").mkdir(exist_ok=True)
    started = time.monotonic_ns()
    spec = importlib.util.spec_from_file_location("eap_base", "/task/eap_exercise.py")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    helper.OUTPUT = BASE.OUTPUT / "eap"
    helper.certificates()
    helper.configurations()
    os.chdir(BASE.OUTPUT)
    shutil.copytree(INPUT, BASE.OUTPUT / "input", dirs_exist_ok=True)
    interfaces = SAFE.setup()
    attachment_setup(interfaces)
    authentication_network = auth_network()
    processes, observers, endpoints, events = [], [], [], []
    manifest = {
        "schema": 1,
        "profile": "campus-ingress-attachments",
        "captureID": str(uuid.uuid4()),
        "startNs": started,
        "byteorder": sys.byteorder,
        "interfaces": interfaces,
        "events": events,
        "admissionPolls": "admission-polls.json",
        "authenticationNetwork": authentication_network,
        "namespaceLifetimes": namespace_lifetimes(),
        "initialPolicyLoads": [
            load_policy("initial-" + actor, actor, "deny") for actor in BASE.GATEWAYS
        ],
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
            "net.netfilter.nf_conntrack_acct",
            *(f"net.ipv4.conf.{interface}.rp_filter" for interface in interfaces[actor]),
        )
        for actor in BASE.ACTORS
    }
    auth = supplicant = None
    producer_lifetimes = {}
    eap_observer = None
    archive_cache, archive_statistics = None, None
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
            namespace = json.loads(process.stdout.readline())
            ready = json.loads(process.stdout.readline())
            processes.append(process)
            observers.append(
                {
                    "kind": "packet",
                    "actor": actor,
                    "command": command,
                    "identity": namespace,
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
                ATTACHMENT_TASK,
                "nflog",
                str(BASE.OUTPUT / f"{actor}-nflog.jsonl"),
                str(group),
            ]
            process = subprocess.Popen(command, text=True, stdout=subprocess.PIPE)
            namespace = json.loads(process.stdout.readline())
            ready = json.loads(process.stdout.readline())
            processes.append(process)
            observers.append(
                {
                    "kind": "nflog",
                    "actor": actor,
                    "command": command,
                    "identity": namespace,
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
        command = [
            "ip",
            "netns",
            "exec",
            "auth",
            "python3",
            CAMPUS_TASK,
            "sniff-eap",
            str(helper.OUTPUT / "success-frames.jsonl"),
        ]
        process = subprocess.Popen(command, text=True, stdout=subprocess.PIPE)
        eap_observer = {
            "command": command,
            "ready": json.loads(process.stdout.readline()),
            "file": "eap/success-frames.jsonl",
        }
        eap_process = process
        time.sleep(0.1)
        manifest["initial"] = observations("initial")
        manifest["initialCaches"] = {}
        BASE.TASK = CAMPUS_TASK
        client = BASE.Endpoint("client", "192.0.2.2", 41000)
        server = BASE.Endpoint("server", "198.51.100.2", 9000)
        BASE.TASK = ATTACHMENT_TASK
        endpoints = [client, server]

        def event(name, kind, operation, **fields):
            row = {"id": name, "type": kind, "startNs": time.monotonic_ns(), **fields}
            row["before"] = observations(name + "-before")
            mark, poll_mark = len(BASE.COMMANDS), len(SAFE.POLLS)
            row["result"] = operation()
            row["commands"] = list(range(mark, len(BASE.COMMANDS)))
            row["polls"] = list(range(poll_mark, len(SAFE.POLLS)))
            row["after"] = observations(name + "-after")
            row["endNs"] = time.monotonic_ns()
            events.append(row)
            return row

        def authenticate():
            nonlocal auth, supplicant
            beginning = time.monotonic_ns()
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
            producer_lifetimes["authenticator"] = {
                "startNs": beginning,
                "pid": auth.process.pid,
                "command": auth.command,
            }
            auth.wait_for("AP-ENABLED")
            peer_start = time.monotonic_ns()
            supplicant = helper.Producer(
                "success",
                "supplicant",
                "ip",
                "netns",
                "exec",
                "client",
                "wpa_supplicant",
                "-dd",
                "-D",
                "wired",
                "-i",
                "peer0",
                "-c",
                str(helper.OUTPUT / "success-supplicant.conf"),
            )
            producer_lifetimes["supplicant"] = {
                "startNs": peer_start,
                "pid": supplicant.process.pid,
                "command": supplicant.command,
            }
            supplicant.wait_for("CTRL-EVENT-EAP-SUCCESS")
            auth.wait_for("AP-STA-CONNECTED")
            station = BASE.export(
                "auth",
                "eap/authorized-station.txt",
                "hostapd_cli",
                "-p",
                "/run/netlib-eap/hostapd",
                "-i",
                "auth0",
                "sta",
                PEER,
            )
            status = BASE.export(
                "client",
                "eap/supplicant-status.txt",
                "wpa_cli",
                "-p",
                "/run/netlib-eap/supplicant",
                "-i",
                "peer0",
                "status",
            )
            return {
                "startNs": beginning,
                "endNs": time.monotonic_ns(),
                "station": station,
                "status": status,
                "authenticatorCommand": auth.command,
                "supplicantCommand": supplicant.command,
                "producers": producer_lifetimes,
            }

        authentication = event("authenticate", "authentication", authenticate)

        def credential():
            index, _ = BASE.run(
                "install",
                "-m",
                "0644",
                str(INPUT / "demo-credential.json"),
                str(RUNTIME / "demo-credential.json"),
            )
            read, content = BASE.run("cat", str(RUNTIME / "demo-credential.json"))
            (BASE.OUTPUT / "installed-demo-credential.json").write_text(content)
            return {
                "command": index,
                "input": "input/demo-credential.json",
                "installed": {"file": "installed-demo-credential.json", "command": read},
            }

        event("credential", "credential", credential)
        for actor, name in (("a", "primary"), ("b", "standby")):
            event(
                "install-" + name + "-permit",
                "policy",
                lambda actor=actor, name=name: load_policy(
                    "install-" + name + "-permit", actor, "permit"
                ),
                gateway=actor,
                policy="permit",
            )

        def send(endpoint, actor, name, peer):
            marker = ("attachments:" + name).encode("ascii").hex()
            sender = endpoint.call("send", peer=peer, payloadHex=marker, ttl=64)
            return {"sender": sender, "admission": SAFE.admission(actor, marker)}

        def packet(sender, receiver, actor, name, peer, timeout=0.3):
            result = send(sender, actor, name, peer)
            result["receiver"] = receiver.call("receive", timeout=timeout)
            return result

        attack_number = 0

        def attack(name, gateway, direction):
            nonlocal attack_number
            frame = raw_frame(gateway, direction, name, attack_number)
            attack_number += 1
            interface = "aal" if gateway == "a" else "abl"
            filename = name + "-raw-input.json"
            request = {"interface": interface, "rawEthernet": frame.hex()}
            BASE.save(filename, request)
            command, output = BASE.native(
                "attacker", "python3", ATTACHMENT_TASK, "raw-send", str(BASE.OUTPUT / filename)
            )
            receipt = json.loads(output)
            native = BASE.COMMANDS[command]
            sender = {
                "command": command,
                "input": filename,
                "request": request,
                "response": receipt,
                "startNs": native["startNs"],
                "endNs": native["endNs"],
            }
            receiver = server if direction == "original" else client
            return {"sender": sender, "receiver": receiver.call("receive", timeout=0.3)}

        def caches(label):
            return {
                actor: {
                    kind: BASE.export(
                        actor,
                        f"{label}-{actor}-{kind}.xml",
                        "conntrackd",
                        "-C",
                        str(BASE.OUTPUT / f"{actor}.conf"),
                        option,
                        "-x",
                    )
                    for kind, option in (("internal", "-i"), ("external", "-e"))
                }
                for actor in BASE.GATEWAYS
            }

        event(
            "unsafe-original",
            "attack",
            lambda: attack("unsafe-original", "a", "original"),
            gateway="a",
            leg="original",
            securityPhase="unsafe",
        )

        def reset():
            commands = {actor: BASE.native(actor, "conntrack", "-F")[0] for actor in BASE.GATEWAYS}
            tables = {}
            for actor in BASE.GATEWAYS:
                filename = f"reset-{actor}-conntrack.json"
                command, _ = BASE.native(
                    actor,
                    "python3",
                    "/task/capture_conntrack.py",
                    "--output",
                    str(BASE.OUTPUT / filename),
                )
                tables[actor] = {"file": filename, "command": command}
            return {"commands": commands, "tables": tables}

        event("reset-tracking", "reset", reset)

        def start_replication():
            daemons = {}
            for actor in BASE.GATEWAYS:
                start = BASE.native(
                    actor, "conntrackd", "-C", str(BASE.OUTPUT / f"{actor}.conf"), "-d"
                )[0]
                runtime = BASE.export(
                    actor,
                    f"start-{actor}-runtime.txt",
                    "conntrackd",
                    "-C",
                    str(BASE.OUTPUT / f"{actor}.conf"),
                    "-s",
                    "runtime",
                )
                daemons[actor] = {"startCommand": start, "runtime": runtime}
            resynchronization = {
                actor: BASE.native(
                    actor, "conntrackd", "-C", str(BASE.OUTPUT / f"{actor}.conf"), "-n"
                )[0]
                for actor in BASE.GATEWAYS
            }
            attempts = {actor: [] for actor in BASE.GATEWAYS}
            for index in range(40):
                sockets = {
                    actor: BASE.export(
                        actor,
                        f"start-{actor}-sockets-{index}.json",
                        "python3",
                        ATTACHMENT_TASK,
                        "daemon-sockets",
                    )
                    for actor in BASE.GATEWAYS
                }
                for actor, reference in sockets.items():
                    attempts[actor].append(reference)
                if all(
                    len(
                        [
                            item
                            for item in json.loads((BASE.OUTPUT / reference["file"]).read_text())[
                                "sockets"
                            ]
                            if item["local"]["port"] != 3780
                        ]
                    )
                    == 1
                    for reference in sockets.values()
                ):
                    break
                time.sleep(0.01)
            else:
                raise RuntimeError("The daemon sending sockets were not observed.")
            return {
                "daemons": daemons,
                "cacheReadiness": caches("start"),
                "resynchronization": resynchronization,
                "socketReadiness": sockets,
                "socketAttempts": attempts,
            }

        replication = event("start-replication", "replication-start", start_replication)
        socket_sources = replication["result"]["socketReadiness"]
        authentication_port = {
            "namespace": "auth",
            "interface": "auth0",
            "source": manifest["namespaceLifetimes"]["auth"]["identity"],
        }
        guard_installs = {}
        for actor, name in (("a", "primary"), ("b", "standby")):
            guard_installs[actor] = event(
                "install-" + name + "-attachment",
                "guard",
                lambda actor=actor, name=name: load_guard(
                    "install-" + name + "-attachment",
                    actor,
                    True,
                    authentication_port,
                    socket_sources,
                ),
                gateway=actor,
                active=True,
            )

        event(
            "protect-marker",
            "protect",
            lambda: {
                "initialBoundary": "protect-marker:before",
                "guardInstallations": {actor: row["id"] for actor, row in guard_installs.items()},
                "bindings": {
                    actor: row["result"]["binding"]["file"] for actor, row in guard_installs.items()
                },
                "cacheReadiness": caches("protect"),
            },
        )
        event(
            "fresh-original-a",
            "attack",
            lambda: attack("fresh-original-a", "a", "original"),
            gateway="a",
            leg="original",
            securityPhase="guarded",
        )
        event(
            "fresh-original-b",
            "attack",
            lambda: attack("fresh-original-b", "b", "original"),
            gateway="b",
            leg="original",
            securityPhase="guarded",
        )

        event(
            "establish",
            "packet",
            lambda: packet(client, server, "client", "establish", ["203.0.113.2", 8080]),
            gateway="a",
            leg="original",
        )
        event(
            "cached-original-a",
            "attack",
            lambda: attack("cached-original-a", "a", "original"),
            gateway="a",
            leg="original",
            securityPhase="guarded",
        )
        event(
            "forged-reply-a",
            "attack",
            lambda: attack("forged-reply-a", "a", "reply"),
            gateway="a",
            leg="reply",
            securityPhase="guarded",
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
            "cached-original-b",
            "attack",
            lambda: attack("cached-original-b", "b", "original"),
            gateway="b",
            leg="original",
            securityPhase="guarded",
        )
        event(
            "forged-reply-b",
            "attack",
            lambda: attack("forged-reply-b", "b", "reply"),
            gateway="b",
            leg="reply",
            securityPhase="guarded",
        )
        event(
            "install-primary-delay",
            "qdisc",
            lambda: BASE.native(
                "client",
                SAFE.TC,
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
            command, _ = BASE.native(
                "server" if interface == "sbl" else "client",
                SAFE.TC,
                "qdisc",
                "del",
                "dev",
                interface,
                "root",
            )
            return {
                "qdisc": reference,
                "ticket": ticket,
                "completion": completion,
                "deleteCommand": command,
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

        def withdraw():
            global ARCHIVED
            nonlocal archive_cache, archive_statistics
            standby_log = BASE.export(
                "b", "withdraw-b-log-before.txt", "cat", str(BASE.OUTPUT / "b.log")
            )
            archive_cache = BASE.export(
                "a",
                "withdraw-a-cache.xml",
                "conntrackd",
                "-C",
                str(BASE.OUTPUT / "a.conf"),
                "-e",
                "-x",
            )
            archive_statistics = {
                kind: BASE.export(
                    "a",
                    f"a-{kind}-statistics.txt",
                    "conntrackd",
                    "-C",
                    str(BASE.OUTPUT / "a.conf"),
                    "-s",
                    kind,
                )
                for kind in ("cache", "network", "runtime", "ct")
            }
            commands = [
                BASE.native("a", "conntrackd", "-C", str(BASE.OUTPUT / "a.conf"), "-k")[0],
                BASE.native("a", "ip", "link", "set", "syncl", "down")[0],
                BASE.native("a", "ip", "link", "set", "aar", "down")[0],
                BASE.native("a", "sh", "-c", "echo 0 > /tmp/netlib-proc/sys/net/ipv4/ip_forward")[
                    0
                ],
            ]
            links = BASE.export("a", "withdraw-a-disabled-links.json", "ip", "-j", "link", "show")
            settings = BASE.export(
                "a", "withdraw-a-disabled-settings.txt", "sysctl", "net.ipv4.ip_forward"
            )
            daemon = BASE.export(
                "a",
                "withdraw-a-daemon.json",
                "python3",
                BASE.TASK,
                "daemon-stopped",
            )
            retired = BASE.COMMANDS[-1]["endNs"]
            ARCHIVED = True
            return {
                "archiveBoundary": "withdraw-primary:before",
                "retiredAtNs": retired,
                "standbyLogBefore": standby_log,
                "cache": archive_cache,
                "statistics": archive_statistics,
                "commands": commands,
                "checks": {"links": links, "forwarding": settings, "daemon": daemon},
            }

        event("withdraw-primary", "withdraw", withdraw, gateway="a")
        event(
            "continued-request",
            "packet",
            lambda: packet(client, server, "client", "continued-request", ["203.0.113.2", 8080]),
            gateway="b",
            leg="original",
            ticket=3,
        )
        event(
            "continued-reply",
            "packet",
            lambda: packet(server, client, "server", "continued-reply", ["203.0.113.1", 40000]),
            gateway="b",
            leg="reply",
            ticket=4,
        )
        for actor, interface, name, handle in (
            ("client", "cbl", "original", "20:"),
            ("server", "sbl", "reply", "30:"),
        ):
            event(
                "install-" + name + "-delay",
                "qdisc",
                lambda actor=actor, interface=interface, handle=handle: BASE.native(
                    actor,
                    SAFE.TC,
                    "qdisc",
                    "add",
                    "dev",
                    interface,
                    "root",
                    "handle",
                    handle,
                    "netem",
                    "limit",
                    "16",
                    "delay",
                    "2500ms",
                )[0],
                actor=actor,
                interface=interface,
                delayMilliseconds=2500,
            )
        event(
            "admit-stale-original",
            "admit",
            lambda: send(client, "client", "stale-original", ["203.0.113.2", 8080]),
            gateway="b",
            leg="original",
            ticket=5,
        )
        event(
            "admit-stale-reply",
            "admit",
            lambda: send(server, "server", "stale-reply", ["203.0.113.1", 40000]),
            gateway="b",
            leg="reply",
            ticket=6,
        )

        def logoff():
            beginning = time.monotonic_ns()
            command, _ = BASE.native(
                "client", "wpa_cli", "-p", "/run/netlib-eap/supplicant", "-i", "peer0", "logoff"
            )
            auth.wait_for("AP-STA-DISCONNECTED")
            station = BASE.export(
                "auth",
                "eap/logged-off-station.txt",
                "hostapd_cli",
                "-p",
                "/run/netlib-eap/hostapd",
                "-i",
                "auth0",
                "sta",
                PEER,
            )
            network = {
                kind: BASE.export(
                    "auth", f"eap/logged-off-auth-{kind}.json", "ip", "-j", *arguments
                )
                for kind, arguments in (
                    ("links", ("link", "show")),
                    ("addresses", ("address", "show")),
                    ("routes", ("-4", "route", "show", "table", "main")),
                    ("rules", ("-4", "rule", "show")),
                )
            }
            return {
                "startNs": beginning,
                "endNs": time.monotonic_ns(),
                "command": command,
                "station": station,
                "network": network,
            }

        event("logoff", "authentication", logoff)
        event(
            "install-standby-attachment-deny",
            "guard",
            lambda: load_guard(
                "install-standby-attachment-deny",
                "b",
                False,
                authentication_port,
                socket_sources,
                replace=True,
            ),
            gateway="b",
            active=False,
        )

        def serve_pair():
            with ThreadPoolExecutor(max_workers=2) as pool:
                original = pool.submit(server.call, "receive", timeout=3)
                reply = pool.submit(client.call, "receive", timeout=3)
                return {"receivers": {"original": original.result(), "reply": reply.result()}}

        event("serve-stale-pair", "serve-pair", serve_pair, gateway="b", tickets=[5, 6])
        event(
            "original-barrier",
            "barrier",
            lambda: barrier("original-barrier", "cbl", 5, "serve-stale-pair"),
            gateway="b",
        )
        event(
            "reply-barrier",
            "barrier",
            lambda: barrier("reply-barrier", "sbl", 6, "serve-stale-pair"),
            gateway="b",
        )
        event(
            "install-standby-deny",
            "policy",
            lambda: load_policy("install-standby-deny", "b", "deny"),
            gateway="b",
            policy="deny",
        )
        manifest["final"] = observations("final")
        manifest["finalCaches"] = {
            "a": archive_cache,
            "b": BASE.export(
                "b",
                "final-b-cache.xml",
                "conntrackd",
                "-C",
                str(BASE.OUTPUT / "b.conf"),
                "-e",
                "-x",
            ),
        }
        manifest["statistics"] = {
            "a": archive_statistics,
            "b": {
                kind: BASE.export(
                    "b",
                    f"b-{kind}-statistics.txt",
                    "conntrackd",
                    "-C",
                    str(BASE.OUTPUT / "b.conf"),
                    "-s",
                    kind,
                )
                for kind in ("cache", "network", "runtime", "ct")
            },
        }
        manifest["eap"] = {
            "name": "success",
            "phaseId": 1,
            "startNs": authentication["result"]["startNs"],
            "endNs": time.monotonic_ns(),
            "authenticatorCommand": auth.command,
            "supplicantCommand": supplicant.command,
            "observer": eap_observer,
            "producers": producer_lifetimes,
        }
    finally:
        manifest["endpoints"] = [endpoint.close() for endpoint in endpoints]
        if not ARCHIVED and (BASE.OUTPUT / "a.ctl").exists():
            BASE.native("a", "conntrackd", "-C", str(BASE.OUTPUT / "a.conf"), "-k")
        if (BASE.OUTPUT / "b.ctl").exists():
            BASE.native("b", "conntrackd", "-C", str(BASE.OUTPUT / "b.conf"), "-k")
        for role, producer in (("supplicant", supplicant), ("authenticator", auth)):
            if producer is not None:
                producer_lifetimes[role]["runningBeforeStop"] = producer.process.poll() is None
                producer_lifetimes[role]["stopNs"] = time.monotonic_ns()
                producer.stop()
                producer_lifetimes[role]["returncode"] = producer.process.returncode
                producer_lifetimes[role]["endNs"] = time.monotonic_ns()
        if eap_observer is not None:
            eap_observer["runningBeforeStop"] = eap_process.poll() is None
            eap_observer["stopNs"] = time.monotonic_ns()
            eap_process.send_signal(signal.SIGTERM)
            eap_observer["returncode"] = eap_process.wait(timeout=5)
            eap_observer["endNs"] = time.monotonic_ns()
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
        if "eap" in manifest:
            manifest["eap"]["endNs"] = manifest["endNs"]
        BASE.save("commands.json", BASE.COMMANDS)
        BASE.save("admission-polls.json", SAFE.POLLS)
        BASE.save("eap/commands.json", helper.COMMANDS)
        BASE.save("capture.json", manifest)
        shutil.rmtree(helper.RUNTIME)
        shutil.rmtree(RUNTIME)
        if any(
            not observer["runningBeforeStop"]
            or observer["returncode"] != (-signal.SIGTERM if observer["kind"] == "trace" else 0)
            for observer in observers
        ):
            raise RuntimeError("A data observer failed during capture.")
        if eap_observer is not None and (
            not eap_observer["runningBeforeStop"] or eap_observer["returncode"] != 0
        ):
            raise RuntimeError("The EAP observer failed during capture.")


if __name__ == "__main__":
    if sys.argv[1] == "endpoint":
        BASE.endpoints()
    elif sys.argv[1] == "sniff":
        print(json.dumps(identity()), flush=True)
        BASE.sniff()
    elif sys.argv[1] == "nflog":
        print(json.dumps(identity()), flush=True)
        spec = importlib.util.spec_from_file_location("nflog_base", "/task/replication/nflog.py")
        helper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(helper)
        helper.capture(sys.argv[2], int(sys.argv[3]))
    elif sys.argv[1] == "identity":
        print(json.dumps(identity()))
    elif sys.argv[1] == "daemon-sockets":
        daemon_sockets()
    elif sys.argv[1] == "raw-send":
        raw_send(sys.argv[2])
    elif sys.argv[1] == "sniff-eap":
        eap_sniff()
    elif sys.argv[1] == "daemon-stopped":
        daemon_stopped()
    else:
        capture()
