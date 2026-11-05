"""Capture one EAP session, installed policies, tracked handoff, and withdrawal."""

import importlib.util
import json
import os
import shutil
import signal
import socket
import subprocess
import sys
import time
import uuid
from pathlib import Path

SPEC = importlib.util.spec_from_file_location("queued_base", "/task/safe-handoff/exercise.py")
SAFE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SAFE)
BASE = SAFE.BASE
BASE.TASK = "/task/campus/exercise.py"
INPUT = Path("/task/campus/input")
RUNTIME = Path("/run/netlib-campus")
AUTH = "02:00:00:00:ea:01"
PEER = "02:00:00:00:ea:02"
ARCHIVED = False


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


def observations(label):
    gateways = ("b",) if ARCHIVED else BASE.GATEWAYS
    actors = tuple(actor for actor in BASE.ACTORS if actor != "a" or not ARCHIVED)
    result = {"conntrack": {}, "tables": {}, "networks": {}}
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
    result["qdiscs"] = {interface: SAFE.queue(label, interface) for interface in ("cal", "cbl")}
    result["endpointTables"] = {
        actor: BASE.export(
            actor, f"{label}-{actor}-nftables.json", "nft", "-j", "-a", "list", "ruleset"
        )
        for actor in ("client", "server")
    }
    if ARCHIVED:
        result["archivedA"] = {"boundary": "withdraw-primary:before"}
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
    authentication_network = auth_network()
    processes, observers, endpoints, events = [], [], [], []
    manifest = {
        "schema": 1,
        "profile": "campus-wired-eap-safe-withdrawal",
        "captureID": str(uuid.uuid4()),
        "startNs": started,
        "byteorder": sys.byteorder,
        "interfaces": interfaces,
        "events": events,
        "admissionPolls": "admission-polls.json",
        "authenticationNetwork": authentication_network,
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
        command = [
            "ip",
            "netns",
            "exec",
            "auth",
            "python3",
            BASE.TASK,
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
            marker = ("campus:" + name).encode("ascii").hex()
            sender = endpoint.call("send", peer=peer, payloadHex=marker, ttl=64)
            return {"sender": sender, "admission": SAFE.admission(actor, marker)}

        def packet(sender, receiver, actor, name, peer, timeout=0.3):
            result = send(sender, actor, name, peer)
            result["receiver"] = receiver.call("receive", timeout=timeout)
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
            reference = SAFE.queue(name, interface)
            command, _ = BASE.native("client", SAFE.TC, "qdisc", "del", "dev", interface, "root")
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
        event(
            "install-standby-delay",
            "qdisc",
            lambda: BASE.native(
                "client",
                SAFE.TC,
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
            ticket=5,
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
            "install-standby-deny",
            "policy",
            lambda: load_policy("install-standby-deny", "b", "deny"),
            gateway="b",
            policy="deny",
        )
        event(
            "serve-standby",
            "serve",
            lambda: {"receiver": server.call("receive", timeout=2)},
            gateway="b",
            leg="original",
            ticket=5,
        )
        event(
            "standby-barrier",
            "barrier",
            lambda: barrier("standby-barrier", "cbl", 5, "serve-standby"),
            gateway="b",
        )
        event(
            "denied-reply",
            "packet",
            lambda: packet(
                server, client, "server", "denied-reply", ["203.0.113.1", 40000], timeout=0.3
            ),
            gateway="b",
            leg="reply",
            ticket=6,
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
        BASE.sniff()
    elif sys.argv[1] == "sniff-eap":
        eap_sniff()
    elif sys.argv[1] == "daemon-stopped":
        daemon_stopped()
    else:
        capture()
