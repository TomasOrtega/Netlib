"""Bind one campus execution to strict data, authentication, and withdrawal evidence."""

import hashlib
import re
from collections import Counter
from pathlib import Path

import check_eap_capture as eap
import check_replication_capture as replication
from capture_evidence import (
    SAFE_BASE,
    SAFE_TC,
    _digests,
    _endpoint_nflog,
    _nflog_ready,
    _offload,
    _safe_setup_commands,
    _SafeHandoffAdapter,
    checked_window,
    require,
)

CAMPUS_TASK = "/task/campus/exercise.py"
PROFILE = "campus-wired-eap-safe-withdrawal"
ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = "withdraw-primary:before"


class CampusEvidence(_SafeHandoffAdapter):
    def __init__(self, directory):
        self.directory = directory
        self.manifest = replication.nat.read_json(directory / "capture.json")
        self.commands = replication.nat.read_json(directory / "commands.json")
        self.polls = replication.nat.read_json(directory / "admission-polls.json")
        manifest = self.manifest
        require(
            type(manifest["schema"]) is int
            and manifest["schema"] == 1
            and manifest["profile"] == PROFILE
            and manifest["byteorder"] == "little"
            and manifest["admissionPolls"] == "admission-polls.json",
            "Unsupported campus producer profile.",
        )
        replication.interval(manifest)
        previous = manifest["startNs"]
        for command in self.commands:
            require(
                set(command) == {"arguments", "startNs", "endNs", "returncode", "stdout", "stderr"}
                and type(command["returncode"]) is int
                and command["returncode"] == 0
                and not command["stderr"]
                and isinstance(command["arguments"], list)
                and all(isinstance(value, str) for value in command["arguments"]),
                "Native command failed or has unsupported fields.",
            )
            _, previous = replication.interval(command, previous, manifest["endNs"])
        self.events = {event["id"]: event for event in manifest["events"]}
        require(
            len(self.events) == len(manifest["events"]) and self.events,
            "Duplicate or missing native event identity.",
        )
        previous = manifest["startNs"]
        self.operations = {}
        for event in manifest["events"]:
            _, previous = replication.interval(event, previous, manifest["endNs"])
            indices = event["commands"]
            require(
                isinstance(indices, list)
                and all(type(index) is int and 0 <= index < len(self.commands) for index in indices)
                and (not indices or indices == list(range(indices[0], indices[-1] + 1))),
                "Invalid event command inventory.",
            )
            if event["type"] in ("packet", "admit", "serve"):
                require(not indices, "Socket event contains unmodeled commands.")
                result = event["result"]
                start = (
                    result["sender"]["startNs"]
                    if "sender" in result
                    else result["receiver"]["startNs"]
                )
                end = (
                    result["receiver"]["endNs"]
                    if "receiver" in result
                    else self.polls[result["admission"]["poll"]]["endNs"]
                )
                for key in ("sender", "receiver"):
                    if key in result:
                        replication.interval(result[key], event["startNs"], event["endNs"])
                        replication.interval(
                            result[key]["response"], result[key]["startNs"], result[key]["endNs"]
                        )
                if event["type"] == "packet":
                    require(
                        result["sender"]["endNs"] < result["receiver"]["startNs"],
                        "Atomic packet receive precedes actual send completion.",
                    )
            else:
                require(indices, "Control event has no command evidence.")
                start, end = (
                    self.commands[indices[0]]["startNs"],
                    self.commands[indices[-1]]["endNs"],
                )
                if event["type"] == "authentication":
                    result = event["result"]
                    replication.interval(result, event["startNs"], event["endNs"])
                    require(
                        result["startNs"] <= start < end <= result["endNs"],
                        "Authentication commands escape their actual operation receipt.",
                    )
                    start, end = result["startNs"], result["endNs"]
            checked_window(start, end, (event["startNs"], event["endNs"]))
            self.operations[event["id"]] = {
                "startNs": start,
                "endNs": end,
                "native": event,
                "commands": [self.commands[index] for index in indices],
            }
        self.boundaries = {"initial": manifest["initial"], "final": manifest["final"]}
        self.boundaries.update(
            {
                event["id"] + ":" + side: event[side]
                for event in manifest["events"]
                for side in ("before", "after")
            }
        )
        self.packets = {}
        for event in manifest["events"]:
            if event["type"] in ("packet", "admit"):
                key = event.get("ticket", "establish")
                require(key == "establish" or type(key) is int, "Invalid native ticket identity.")
                require(key not in self.packets, "Duplicate admission ticket identity.")
                self.packets[key] = {
                    "admit": event,
                    "serve": event if event["type"] == "packet" else None,
                }
        for event in manifest["events"]:
            if event["type"] == "serve":
                require(
                    type(event["ticket"]) is int
                    and event["ticket"] in self.packets
                    and self.packets[event["ticket"]]["serve"] is None,
                    "Serve event has no unique pending admission.",
                )
                self.packets[event["ticket"]]["serve"] = event
        require(
            all(value["serve"] for value in self.packets.values()),
            "Admission has no observed service outcome.",
        )
        self.used_commands, self.used_sources, self.used_polls = set(), set(), set()
        self.used_artifacts = set()
        self.read_boundaries, self.packet_reports = {}, {}
        self._open_observers()
        self._open_packets()

    def _open_observers(self):
        manifest = self.manifest
        observers = manifest["observers"]
        self.observers = {(row["actor"], row["kind"]): row for row in observers}
        required = {
            (actor, kind) for actor in replication.ACTORS for kind in ("packet", "nflog")
        } | {(actor, "trace") for actor in replication.GATEWAYS}
        require(
            len(observers) == len(self.observers) == len(required)
            and set(self.observers) == required,
            "Missing or duplicate raw observer.",
        )
        first, last = manifest["events"][0]["startNs"], manifest["events"][-1]["endNs"]
        self.indices = {}
        for (actor, kind), observer in self.observers.items():
            require(
                observer["runningBeforeStop"] is True
                and observer["stopSignal"] == 15
                and type(observer["returncode"]) is int
                and observer["returncode"] == (-15 if kind == "trace" else 0)
                and last < observer["stopNs"] < observer["endNs"] <= manifest["endNs"],
                "Raw observer exited early or failed.",
            )
            prefix = ["ip", "netns", "exec", actor]
            if kind == "packet":
                ready = observer["ready"]
                require(
                    observer["file"] == f"{actor}-frames.jsonl"
                    and ready["namespace"] == actor
                    and [row["interface"] for row in ready["interfaces"]]
                    == list(replication.LINKS[actor])
                    and all(row["receiveBuffer"] >= 131072 for row in ready["interfaces"]),
                    "Packet observer binding or buffer size disagrees.",
                )
                self.indices[actor] = {
                    row["interface"]: replication.integer(row["ifindex"], 2**32)
                    for row in ready["interfaces"]
                }
                expected = prefix + [
                    "python3",
                    CAMPUS_TASK,
                    "sniff",
                    f"{SAFE_BASE}/{observer['file']}",
                    actor,
                    *replication.LINKS[actor],
                ]
            elif kind == "nflog":
                ready = observer["ready"]
                group = 42 if actor in replication.GATEWAYS else 43
                _nflog_ready(ready, group)
                require(observer["file"] == f"{actor}-nflog.jsonl", "NFLOG file is misbound.")
                expected = prefix + [
                    "python3",
                    "/task/replication/nflog.py",
                    f"{SAFE_BASE}/{observer['file']}",
                    str(group),
                ]
            else:
                require(
                    observer["file"] == f"{actor}-trace.txt"
                    and observer["errors"] == f"{actor}-trace-errors.txt"
                    and not (self.directory / observer["errors"]).read_text(),
                    "Trace monitor reported errors.",
                )
                ready = {"readyNs": observer["startNs"]}
                expected = prefix + ["nft", "monitor", "trace"]
            require(
                observer["command"] == expected and manifest["startNs"] < ready["readyNs"] < first,
                "Observer command or startup time disagrees.",
            )
        require(
            manifest["interfaces"]
            == {actor: list(links) for actor, links in replication.LINKS.items()},
            "Native topology interface inventory disagrees.",
        )

    def boundary(self, name, window=None):
        require(name in self.boundaries, "Unknown campus boundary reference.")
        native = self.boundaries[name]
        label = name.replace(":", "-")
        if name == "initial":
            lower, upper = self.manifest["startNs"], self.manifest["events"][0]["startNs"]
        elif name == "final":
            lower, upper = self.manifest["events"][-1]["endNs"], self.manifest["endNs"]
        else:
            event_name, side = name.split(":")
            event = self.events[event_name]
            operation = self.operations[event_name]
            lower, upper = (
                (event["startNs"], operation["startNs"])
                if side == "before"
                else (operation["endNs"], event["endNs"])
            )
        retired = name == "final" or (
            name != "initial" and lower >= self.operations["withdraw-primary"]["endNs"]
        )
        require(
            set(native)
            == {"conntrack", "tables", "networks", "qdiscs", "endpointTables"}
            | ({"archivedA"} if retired else set()),
            "Incomplete campus boundary inventory.",
        )
        gateways = {"b"} if retired else set(replication.GATEWAYS)
        actors = set(replication.ACTORS) - ({"a"} if retired else set())
        require(
            set(native["conntrack"]) == set(native["tables"]) == gateways
            and set(native["networks"]) == actors,
            "Live and archived gateway observations were mixed.",
        )
        if retired:
            require(native["archivedA"] == {"boundary": ARCHIVE}, "Wrong primary archive prefix.")
            require(ARCHIVE in self.read_boundaries, "Read the actual primary archive first.")
        result = {
            "id": name,
            "native": native,
            "conntrack": {},
            "tables": {},
            "networks": {},
            "qdiscs": {},
            "endpointTables": {},
            "archivedA": {"boundary": ARCHIVE} if retired else None,
        }
        before_commands = set(self.used_commands)
        for actor in sorted(gateways):
            reference = native["conntrack"][actor]
            self._artifact(reference, f"{label}-{actor}-conntrack.json")
            command = self._command(
                reference["command"],
                [
                    "ip",
                    "netns",
                    "exec",
                    actor,
                    "python3",
                    "/task/capture_conntrack.py",
                    "--output",
                    f"{SAFE_BASE}/{reference['file']}",
                ],
                (lower, upper),
            )
            require(not command["stdout"], "Conntrack producer has unexpected stdout.")
            document = replication.nat.read_json(self.directory / reference["file"])
            require(
                type(document["schema"]) is int and type(document["family"]) is int,
                "Invalid conntrack numeric envelope.",
            )
            result["conntrack"][actor] = replication.lifecycle.decode_snapshot(document)
            result["tables"][actor] = self._export(
                native["tables"][actor],
                actor,
                ["nft", "-j", "-a", "list", "ruleset"],
                (lower, upper),
                filename=f"{label}-{actor}-nftables.json",
            )
        arguments = {
            "links": ["link", "show"],
            "addresses": ["address", "show"],
            "routes": ["-4", "route", "show", "table", "main"],
            "neighbors": ["neigh", "show"],
            "rules": ["-4", "rule", "show"],
        }
        for actor, refs in native["networks"].items():
            require(set(refs) == set(arguments), "Missing namespace network readback.")
            result["networks"][actor] = {
                kind: self._export(
                    reference,
                    actor,
                    ["ip", "-j", *arguments[kind]],
                    (lower, upper),
                    filename=f"{label}-{actor}-{kind}.json",
                )
                for kind, reference in refs.items()
            }
            for kind in ("links", "addresses"):
                for row in result["networks"][actor][kind]:
                    interface = row["ifname"]
                    if actor == "client" and interface == "peer0":
                        continue
                    expected = 1 if interface == "lo" else self.indices[actor].get(interface)
                    require(
                        type(row["ifindex"]) is int and row["ifindex"] == expected,
                        "Native interface index contradicts its observer binding.",
                    )
                    if interface != "lo":
                        peer = replication.OPPOSITE[interface]
                        require(
                            type(row["link_index"]) is int
                            and row["link_index"]
                            == self.indices[replication.INTERFACES[peer]][peer],
                            "Native interface peer index contradicts the observed topology.",
                        )
        require(
            set(native["qdiscs"]) == {"cal", "cbl"}
            and set(native["endpointTables"]) == {"client", "server"},
            "Missing endpoint queue or policy readback.",
        )
        for interface, reference in native["qdiscs"].items():
            result["qdiscs"][interface] = self._export(
                reference,
                "client",
                [SAFE_TC, "-j", "-s", "-d", "qdisc", "show", "dev", interface],
                (lower, upper),
                filename=f"{label}-{interface}-qdisc.json",
            )
        for actor, reference in native["endpointTables"].items():
            result["endpointTables"][actor] = self._export(
                reference,
                actor,
                ["nft", "-j", "-a", "list", "ruleset"],
                (lower, upper),
                filename=f"{label}-{actor}-nftables.json",
            )
        new_commands = self.used_commands - before_commands
        result.update(
            startNs=min(self.commands[i]["startNs"] for i in new_commands),
            endNs=max(self.commands[i]["endNs"] for i in new_commands),
        )
        checked_window(result["startNs"], result["endNs"], window)
        self.read_boundaries[name] = result
        if name.endswith(":before"):
            result["operation"] = self._operation(name.split(":")[0])
        return result

    def _artifact(self, reference, filename=None):
        require(
            set(reference) == {"file", "command"}
            and isinstance(reference["file"], str)
            and re.fullmatch(r"(?:eap/)?[a-z0-9.-]+", reference["file"])
            and reference["file"] not in self.used_artifacts
            and (filename is None or reference["file"] == filename),
            "Raw campus artifact reference is reused or misbound.",
        )
        self.used_artifacts.add(reference["file"])

    def _operation(self, name):
        operation = self.operations[name]
        event, exports = operation["native"], {}
        result = event["result"]
        if event["type"] not in ("authentication", "credential", "policy", "withdraw"):
            return super()._operation(name)
        window = operation["startNs"], operation["endNs"]
        if event["type"] == "withdraw":
            require(
                result["archiveBoundary"] == ARCHIVE,
                "Withdrawal selected a different primary archive.",
            )
            for kind, ref in result["statistics"].items():
                require(kind in {"cache", "network", "runtime", "ct"}, "Unknown archive statistic.")
                exports[ref["file"]] = self._export(
                    ref,
                    "a",
                    ["conntrackd", "-C", f"{SAFE_BASE}/a.conf", "-s", kind],
                    window,
                    as_json=False,
                )
            ref = result["standbyLogBefore"]
            exports[ref["file"]] = self._export(
                ref, "b", ["cat", f"{SAFE_BASE}/b.log"], window, as_json=False
            )
            ref = result["cache"]
            exports[ref["file"]] = self._export(
                ref,
                "a",
                ["conntrackd", "-C", f"{SAFE_BASE}/a.conf", "-e", "-x"],
                window,
                as_json=False,
            )
            for kind, args in (
                ("links", ["ip", "-j", "link", "show"]),
                ("forwarding", ["sysctl", "net.ipv4.ip_forward"]),
                ("daemon", ["python3", CAMPUS_TASK, "daemon-stopped"]),
            ):
                ref = result["checks"][kind]
                exports[ref["file"]] = self._export(
                    ref, "a", args, window, as_json=kind != "forwarding"
                )
        elif event["type"] == "policy":
            self._policy_load(result, event["gateway"], name, event["policy"], window)
        elif event["type"] == "credential":
            ref = result["installed"]
            self._artifact(ref, "installed-demo-credential.json")
            command = self._command(
                ref["command"], ["cat", "/run/netlib-campus/demo-credential.json"], window
            )
            require(
                command["stdout"] == (self.directory / ref["file"]).read_text(),
                "Installed credential bytes contradict the actual readback.",
            )
        elif event["type"] == "authentication":
            for field, actor, args in (
                (
                    "station",
                    "auth",
                    [
                        "hostapd_cli",
                        "-p",
                        "/run/netlib-eap/hostapd",
                        "-i",
                        "auth0",
                        "sta",
                        eap.PEER,
                    ],
                ),
                (
                    "status",
                    "client",
                    ["wpa_cli", "-p", "/run/netlib-eap/supplicant", "-i", "peer0", "status"],
                ),
            ):
                if field in result:
                    ref = result[field]
                    exports[ref["file"]] = self._export(ref, actor, args, window, as_json=False)
            if name == "logoff":
                arguments = {
                    "links": ["link", "show"],
                    "addresses": ["address", "show"],
                    "routes": ["-4", "route", "show", "table", "main"],
                    "rules": ["-4", "rule", "show"],
                }
                require(
                    set(result["network"]) == set(arguments),
                    "Missing post-Logoff authentication network.",
                )
                for kind, ref in result["network"].items():
                    exports[ref["file"]] = self._export(
                        ref, "auth", ["ip", "-j", *arguments[kind]], window
                    )
        for index in event["commands"]:
            if index not in self.used_commands:
                self._command(index, window=window)
        return {**operation, "exports": exports}

    def _open_packets(self):
        self.frames, self.sync, self.socket_errors, self.logs, self.raw_logs, self.traces = (
            [],
            [],
            [],
            {},
            {},
            {},
        )
        fence = self.events["fence-primary"]
        fence_commands = {
            name: self.commands[index]
            for name, index in zip(("car", "sar"), fence["commands"], strict=True)
        }
        withdraw = self.events["withdraw-primary"]
        sync_down = [
            self.commands[i]
            for i in withdraw["commands"]
            if self.commands[i]["arguments"]
            == ["ip", "netns", "exec", "a", "ip", "link", "set", "syncl", "down"]
        ]
        require(len(sync_down) == 1, "Withdrawal lacks its actual synchronization-link disable.")
        for actor in replication.ACTORS:
            observer = self.observers[(actor, "packet")]
            previous = observer["ready"]["readyNs"]
            for number, row in enumerate(
                replication.read_lines(self.directory / observer["file"]), 1
            ):
                require(
                    previous < row["timeNs"] <= observer["endNs"],
                    "Packet observer records are out of order.",
                )
                previous = row["timeNs"]
                if "socketError" in row and actor == "a" and row["interface"] == "syncl":
                    require(
                        set(row) == {"namespace", "interface", "timeNs", "socketError"}
                        and row["namespace"] == "a"
                        and type(row["socketError"]) is int
                        and row["socketError"] == 100
                        and sync_down[0]["startNs"] <= row["timeNs"],
                        "Synchronization socket error precedes its actual withdrawal.",
                    )
                    decoded = {"error": True, "interface": "syncl", "timeNs": row["timeNs"]}
                else:
                    decoded = replication.decode_af(
                        row, actor, number, self.indices, fence_commands
                    )
                require(decoded is not None, "Unexpected ARP in the permanent-neighbor profile.")
                if decoded.get("error"):
                    self.socket_errors.append((actor, decoded["interface"]))
                else:
                    require(
                        (actor, decoded["interface"]) not in self.socket_errors,
                        "Packet data appears after socket shutdown.",
                    )
                    (self.sync if decoded["sync"] else self.frames).append(decoded)
            observer = self.observers[(actor, "nflog")]
            self.raw_logs[actor] = replication.read_lines(self.directory / observer["file"])
            decode = replication.decode_nflog if actor in replication.GATEWAYS else _endpoint_nflog
            self.logs[actor] = [
                decode(row, actor, i) for i, row in enumerate(self.raw_logs[actor], 1)
            ]
            previous = observer["ready"]["readyNs"]
            for index, row in enumerate(self.logs[actor]):
                require(
                    previous < row["timeNs"] < observer["endNs"]
                    and row["localSequence"] == index
                    and row["globalSequence"] == index + 1,
                    "NFLOG sequence or timestamp completeness disagrees.",
                )
                previous = row["timeNs"]
            if actor in replication.GATEWAYS:
                self.traces[actor] = replication.parse_traces(self.directory / f"{actor}-trace.txt")
        require(
            Counter(self.socket_errors)
            == Counter({("a", "car"): 1, ("a", "sar"): 1, ("a", "syncl"): 1}),
            "Missing or duplicate fence/withdrawal socket errors.",
        )

    def _provenance(self, initial, first_event):
        root = Path(__file__).resolve().parents[1]
        versions = {
            "conntrack-version.txt": "conntrack v1.4.9 (conntrack-tools)\n",
            "conntrackd-version.txt": "Connection tracking userspace daemon v1.4.9. Licensed under GPLv2.\n(C) 2006-2009 Pablo Neira Ayuso <pablo@netfilter.org>\n",
            "nftables-version.txt": "nftables v1.1.3 (Commodore Bullmoose #4)\n",
            "iproute2-version.txt": "ip utility, iproute2-6.19.0\n",
            "tc-version.txt": "tc utility, iproute2-6.19.0\n",
        }
        require(
            re.fullmatch(
                r"Linux \S+ 6\.8\.0-117-generic .* aarch64 Linux\n",
                (self.directory / "kernel.txt").read_text(),
            ),
            "Unexpected native kernel release or architecture.",
        )
        for name, expected in versions.items():
            require(
                (self.directory / name).read_text() == expected,
                "Native producer version differs from selected profile.",
            )
        helpers = {
            "/task/campus/exercise.py": root / "examples/campus/exercise.py",
            "/task/safe-handoff/exercise.py": root / "examples/safe-handoff/exercise.py",
            "/task/eap_exercise.py": root / "examples/eap/exercise.py",
            "/task/replication/exercise.py": root / "examples/replication/exercise.py",
            "/task/replication/nflog.py": root / "examples/replication/nflog.py",
            "/task/wire/exercise.py": root / "examples/wire/exercise.py",
            "/task/capture_conntrack.py": root / "scripts/capture_conntrack.py",
        }
        actual = _digests(self.directory / "helper-sha256.txt")
        require(
            set(actual) == set(helpers)
            and all(
                actual[name] == hashlib.sha256(path.read_bytes()).hexdigest()
                for name, path in helpers.items()
            ),
            "Retained helper source digest disagrees.",
        )
        producers = _digests(self.directory / "producer-sha256.txt")
        require(
            set(producers)
            == {
                "/usr/local/bin/hostapd",
                "/usr/local/bin/wpa_supplicant",
                "/usr/local/bin/hostapd_cli",
                "/usr/local/bin/wpa_cli",
                "/usr/bin/openssl",
                "/opt/netlib/sbin/conntrackd",
                "/opt/netlib/sbin/conntrack",
                "/opt/netlib/sbin/nft",
                "/opt/netlib/sbin/ip",
                SAFE_TC,
                "/tmp/tools.tar.xz",
                "/tmp/library.tar.xz",
                "/tmp/iproute2.tar.gz",
                "/tmp/iproute2-6.19.0/tc/q_netem.c",
            }
            and producers["/tmp/tools.tar.xz"]
            == "c15afe488a8d408c9d6d61e97dbd19f3c591942f62c13df6453a961ca4231cae"
            and producers["/tmp/library.tar.xz"]
            == "769d3eaf57fa4fbdb05dd12873b6cb9a5be7844d8937e222b647381d44284820"
            and producers["/tmp/iproute2.tar.gz"]
            == "b39ac6a76f8299968408d3f2948ea59d9502b299d3e0c78c93658b65df3be5be"
            and producers["/tmp/iproute2-6.19.0/tc/q_netem.c"]
            == "999a1f78f6685c8567f68806b5430194de8d6d7416aec7fcf03b1255981fb57a",
            "Pinned producer source provenance disagrees.",
        )
        final_command = max(self.commands[index]["endNs"] for index in self.used_commands)
        require(len(self.manifest["endpoints"]) == 2, "Missing or duplicate endpoint lifetimes.")
        for endpoint, actor, address, port in zip(
            self.manifest["endpoints"],
            ("client", "server"),
            ("192.0.2.2", "198.51.100.2"),
            (41000, 9000),
            strict=True,
        ):
            require(
                set(endpoint) == {"command", "startNs", "endNs", "binding", "returncode"}
                and endpoint["command"]
                == [
                    "ip",
                    "netns",
                    "exec",
                    actor,
                    "python3",
                    CAMPUS_TASK,
                    "endpoint",
                    address,
                    str(port),
                ]
                and type(endpoint["returncode"]) is int
                and endpoint["returncode"] == 0
                and initial["endNs"]
                < endpoint["startNs"]
                < first_event
                < final_command
                < endpoint["endNs"]
                < self.manifest["endNs"],
                "Endpoint process identity, lifetime, or completion disagrees.",
            )
            binding = endpoint["binding"]
            replication.interval(binding, endpoint["startNs"], first_event)
            replication.interval(binding["response"], binding["startNs"], binding["endNs"])
            require(
                binding["request"] == {"operation": "bind"}
                and binding["response"]["result"] == {"local": [address, port], "mtuDiscover": 0},
                "Endpoint socket binding disagrees.",
            )
        remaining = [
            (index, row)
            for index, row in enumerate(self.commands)
            if index not in self.used_commands
        ]
        setup, shutdown = _safe_setup_commands()
        shutdown = [row for row in shutdown if row[3] == "b"]
        setup.extend(_authentication_setup_commands())
        require(
            Counter(tuple(row["arguments"]) for _, row in remaining)
            == Counter(tuple(row) for row in setup + shutdown),
            "Command journal contains unaccounted mutations or missing bootstrap operations.",
        )
        for index, row in remaining:
            if row["arguments"] in shutdown:
                require(
                    final_command
                    < row["startNs"]
                    < row["endNs"]
                    < min(observer["stopNs"] for observer in self.observers.values()),
                    "Daemon shutdown precedes final observations or follows observer shutdown.",
                )
            else:
                require(
                    row["endNs"] < initial["startNs"],
                    "Bootstrap mutation occurs after initial state readbacks.",
                )
            if row["arguments"][-2:-1] == ["offload"]:
                _offload(row)
            self.used_commands.add(index)

    def _policy_load(self, result, actor, name, policy, window):
        require(
            set(result) == {"file", "command", "inputPolicy"}
            and result["file"] == name + "-load.json"
            and result["inputPolicy"] == f"input/{policy}.json",
            "Policy installation refers to a different supplied input.",
        )
        reference = {"file": result["file"], "command": result["command"]}
        self._artifact(reference)
        command = self._command(
            result["command"],
            ["ip", "netns", "exec", actor, "nft", "-j", "-f", f"{SAFE_BASE}/{result['file']}"],
            window,
        )
        require(not command["stdout"], "Policy transaction has unexpected stdout.")
        original = replication.nat.read_json(self.directory / result["inputPolicy"])["nftables"]
        expected = {
            "nftables": [
                original[0],
                {"delete": {"table": {"family": "ip", "name": "netlib"}}},
                *original[1:],
            ]
        }
        require(
            replication.nat.read_json(self.directory / result["file"]) == expected,
            "Actual transaction differs from the complete retained generated policy.",
        )

    def finish(self):
        require(
            len(self.packet_reports) == len(self.packets)
            and self.used_polls == set(range(len(self.polls))),
            "Unconsumed campus packet or admission poll remains.",
        )
        required = (
            {row["source"] for row in self.frames}
            | {row["source"] for rows in self.logs.values() for row in rows}
            | {
                f"{actor}-trace.txt:{row['stages'][0]['line']}"
                for actor, rows in self.traces.items()
                for row in rows
            }
        )
        require(self.used_sources == required, "Unconsumed selected packet, log, or trace remains.")
        self._sync_audit()
        initial, final = self.read_boundaries["initial"], self.read_boundaries["final"]
        first = self.manifest["events"][0]["startNs"]
        caches = {"initial": {}, "final": {}}
        require(
            set(self.manifest["initialCaches"]) == set(replication.GATEWAYS),
            "Missing initial cache observations.",
        )
        for actor, ref in self.manifest["initialCaches"].items():
            text = self._export(
                ref,
                actor,
                ["conntrackd", "-C", f"{SAFE_BASE}/{actor}.conf", "-e", "-x"],
                (initial["endNs"], first),
                as_json=False,
                filename=f"initial-{actor}-cache.xml",
            )
            caches["initial"][actor] = replication.decode_cache_xml(text)
        withdraw = self.read_boundaries[ARCHIVE]["operation"]
        archived = withdraw["native"]["result"]
        require(
            set(self.manifest["finalCaches"]) == set(replication.GATEWAYS)
            and self.manifest["finalCaches"]["a"] == archived["cache"]
            and self.manifest["statistics"]["a"] == archived["statistics"],
            "Final primary daemon state is not the declared historical archive.",
        )
        caches["final"]["a"] = replication.decode_cache_xml(
            withdraw["exports"][archived["cache"]["file"]]
        )
        ref = self.manifest["finalCaches"]["b"]
        caches["final"]["b"] = replication.decode_cache_xml(
            self._export(
                ref,
                "b",
                ["conntrackd", "-C", f"{SAFE_BASE}/b.conf", "-e", "-x"],
                (final["endNs"], self.manifest["endNs"]),
                as_json=False,
                filename="final-b-cache.xml",
            )
        )
        statistics = {"a": {}, "b": {}}
        require(
            set(self.manifest["statistics"]) == set(replication.GATEWAYS),
            "Missing daemon statistics inventory.",
        )
        for actor in replication.GATEWAYS:
            require(
                set(self.manifest["statistics"][actor]) == {"cache", "network", "runtime", "ct"},
                "Incomplete daemon statistics.",
            )
            for kind, ref in self.manifest["statistics"][actor].items():
                text = (
                    withdraw["exports"][ref["file"]]
                    if actor == "a"
                    else self._export(
                        ref,
                        "b",
                        ["conntrackd", "-C", f"{SAFE_BASE}/b.conf", "-s", kind],
                        (final["endNs"], self.manifest["endNs"]),
                        as_json=False,
                        filename=f"b-{kind}-statistics.txt",
                    )
                )
                statistics[actor][kind] = text
                for line in text.splitlines():
                    if re.search(
                        r"failed:|Malformed|Wrong protocol|Bad message|Truncated|Packets lost:|Packets before:|unknown type:|netlink overrun:|flush kernel table:|resync with kernel table:|process segfault:|process termsig:|unknown request:|Error send",
                        line,
                    ):
                        values = (
                            [int(line.rsplit(":", 1)[-1].rsplit("/", 1)[-1])]
                            if ":" in line
                            else [int(value) for value in re.findall(r"\b[0-9]+\b", line)]
                        )
                        require(
                            values and all(value == 0 for value in values),
                            "Daemon reports failed or lost selected observations.",
                        )
            require(
                (self.directory / f"{actor}.conf").read_text()
                == replication.configuration(actor).replace(replication.BASE, SAFE_BASE),
                "Unexpected synchronization configuration.",
            )
        require(
            set(self.manifest["settings"]) == set(replication.ACTORS), "Missing namespace settings."
        )
        for actor, ref in self.manifest["settings"].items():
            values = {
                "net.ipv4.ip_forward": int(actor in replication.GATEWAYS),
                "net.ipv4.conf.all.rp_filter": 0,
                "net.ipv4.conf.default.rp_filter": 0,
                "net.ipv6.conf.all.disable_ipv6": 1,
                "net.ipv6.conf.default.disable_ipv6": 1,
                "net.netfilter.nf_conntrack_udp_timeout": 30,
                "net.netfilter.nf_conntrack_udp_timeout_stream": 120,
                **{f"net.ipv4.conf.{name}.rp_filter": 0 for name in replication.LINKS[actor]},
            }
            text = self._export(
                ref,
                actor,
                ["sysctl", *values],
                (self.manifest["startNs"], initial["startNs"]),
                as_json=False,
                filename=f"{actor}-settings.txt",
            )
            require(
                text == "".join(f"{key} = {value}\n" for key, value in values.items()),
                "Namespace sysctl readback differs from the selected profile.",
            )
        for actor, result in zip(
            replication.GATEWAYS, self.manifest["initialPolicyLoads"], strict=True
        ):
            self._policy_load(
                result,
                actor,
                "initial-" + actor,
                "deny",
                (self.manifest["startNs"], initial["startNs"]),
            )
        self.authentication = self._authentication()
        self._daemon_logs()
        self._provenance(initial, first)
        return {
            "schema": 1,
            "profile": self.manifest["profile"],
            "captureID": self.manifest["captureID"],
            "packetCount": len(self.packets),
            "snapshotCount": sum(
                len(row["native"]["conntrack"]) for row in self.read_boundaries.values()
            ),
            "frameCount": len(self.frames),
            "nflogCount": sum(len(rows) for rows in self.logs.values()),
            "syncFrameCount": len(self.sync),
            "initial": initial,
            "final": final,
            "cacheViews": caches,
            "statistics": statistics,
            "operations": self.operations,
            "syncData": self.sync_data,
            "eapEvidence": self.authentication,
            "credential": replication.nat.read_json(
                self.directory / "installed-demo-credential.json"
            ),
        }

    def _sync_audit(self):
        sent = Counter(row["hex"] for row in self.sync if row["packetType"] == 4)
        received = Counter(row["hex"] for row in self.sync if row["packetType"] == 0)
        require(not (received - sent), "Synchronization receive has no actual sender.")
        missing = sent - received
        retired = self.events["withdraw-primary"]["result"]["retiredAtNs"]
        sync_down = next(
            self.commands[i]
            for i in self.events["withdraw-primary"]["commands"]
            if self.commands[i]["arguments"]
            == ["ip", "netns", "exec", "a", "ip", "link", "set", "syncl", "down"]
        )
        for raw, count in missing.items():
            rows = [row for row in self.sync if row["hex"] == raw and row["packetType"] == 4]
            require(
                count == len(rows)
                and all(
                    row["namespace"] == "b" and sync_down["startNs"] <= row["timeNs"]
                    for row in rows
                ),
                "Unpaired synchronization traffic predates the declared channel withdrawal.",
            )
        require(
            all(row["timeNs"] < retired for row in self.sync if row["namespace"] == "a"),
            "Withdrawn primary produced a later synchronization observation.",
        )
        possible, earliest = {}, {}
        for boundary in self.read_boundaries.values():
            for actor, records in boundary["conntrack"].items():
                possible.setdefault(actor, []).extend(records)
        for packet in self.packet_reports.values():
            boundary = self.read_boundaries[packet["serveEvent"] + ":after"]
            actor = packet["gateway"]
            lower = (
                packet["sender"]["response"]["startNs"]
                if packet["admitEvent"] == packet["serveEvent"]
                else packet["receiver"]["startNs"]
            )
            for record in boundary["conntrack"][actor]:
                key = actor, record["status"]
                earliest[key] = min(earliest.get(key, lower), lower)
        self.sync_data = []
        previous = {}
        for frame in sorted(self.sync, key=lambda row: row["timeNs"]):
            actor = "a" if frame["header"]["source"] == "10.10.0.1" else "b"
            for index, message in enumerate(frame["messages"]):
                if frame["packetType"] == 4:
                    sequence = message["sequence"]
                    require(
                        actor not in previous or 0 < (sequence - previous[actor]) % 2**32 < 2**31,
                        "Outgoing FTFW sequence repeats or moves backward.",
                    )
                    previous[actor] = sequence
                attrs = message.get("attributes")
                if attrs:
                    require(
                        message["type"] in ("new", "update")
                        and "remainingTTL" not in attrs
                        and attrs.get("zone", 0) == attrs.get("mark", 0) == 0,
                        "Unsupported replicated record attributes or timer mode.",
                    )
                    matches = [
                        record
                        for record in possible.get(actor, [])
                        if record["original"] == attrs["original"]
                        and record["status"] == attrs["status"]
                        and record["originalZone"] == record["replyZone"] == 0
                        and record["reply"]["destination"] == attrs.get("sourceNAT")
                        and record["reply"]["destinationPort"] == attrs.get("sourceNATPort")
                        and record["reply"]["source"] == attrs.get("destinationNAT")
                        and record["reply"]["sourcePort"] == attrs.get("destinationNATPort")
                    ]
                    require(
                        matches
                        and (actor, attrs["status"]) in earliest
                        and frame["timeNs"] >= earliest[(actor, attrs["status"])],
                        "FTFW data contradicts actual source kernel state or its chronology.",
                    )
                    self.sync_data.append(
                        {
                            "actor": actor,
                            "packetType": frame["packetType"],
                            "timeNs": frame["timeNs"],
                            "source": frame["source"],
                            "messageIndex": index,
                            "sequence": message["sequence"],
                            "attributes": attrs,
                        }
                    )

    def _authentication(self):
        phase = self.manifest["eap"]
        require(
            set(phase)
            == {
                "name",
                "phaseId",
                "startNs",
                "endNs",
                "authenticatorCommand",
                "supplicantCommand",
                "observer",
                "producers",
            }
            and phase["name"] == "success"
            and type(phase["phaseId"]) is int
            and phase["phaseId"] == 1
            and phase["startNs"] == self.operations["authenticate"]["startNs"]
            and phase["endNs"] == self.manifest["endNs"],
            "Authentication phase belongs to another execution.",
        )
        directory = self.directory / "eap"
        journal = replication.nat.read_json(directory / "commands.json")
        commands = _certificate_commands()
        require(len(journal) == len(commands), "Missing certificate creation or export command.")
        previous = self.manifest["startNs"]
        for row, expected_command in zip(journal, commands, strict=True):
            require(
                set(row) == {"command", "startNs", "endNs", "returncode", "stdout", "stderr"}
                and row["command"] == expected_command
                and type(row["returncode"]) is int
                and row["returncode"] == 0
                and isinstance(row["stdout"], str)
                and isinstance(row["stderr"], str),
                "Certificate journal has a failed or unmodeled operation.",
            )
            _, previous = replication.interval(
                row, previous, self.read_boundaries["initial"]["startNs"]
            )
        for row, role in zip(journal[-3:], ("ca", "server", "client"), strict=True):
            require(
                row["stdout"] == (directory / f"{role}-certificate.txt").read_text()
                and not row["stderr"],
                "Certificate export contradicts its actual creation journal.",
            )
        eap.configuration(directory)
        require(
            (directory / "source-sha256.txt").read_text().splitlines()
            == [f"{digest}  /tmp/{name}" for name, digest in eap.SOURCES.items()],
            "EAP source release hashes differ from the selected profile.",
        )
        require(
            (directory / "hostapd-version.txt").read_text().startswith("hostapd v2.12\n")
            and (directory / "supplicant-version.txt")
            .read_text()
            .startswith("wpa_supplicant v2.12\n")
            and (directory / "openssl-version.txt").read_text().startswith("OpenSSL 3.5.9 "),
            "Unexpected authentication producer versions.",
        )
        fingerprints = {
            "ca": eap.certificate(directory, "ca", "Netlib private EAP test CA"),
            "server": eap.certificate(directory, "server", eap.SERVER, ("DNS", eap.SERVER)),
            "client": eap.certificate(directory, "client", eap.SUBJECT, ("email", eap.SUBJECT)),
        }
        checked = eap.check_phase(directory, phase, fingerprints)
        observer = phase["observer"]
        require(
            set(observer)
            == {"command", "ready", "file", "runningBeforeStop", "stopNs", "returncode", "endNs"}
            and observer["command"]
            == [
                "ip",
                "netns",
                "exec",
                "auth",
                "python3",
                CAMPUS_TASK,
                "sniff-eap",
                f"{SAFE_BASE}/eap/success-frames.jsonl",
            ]
            and observer["file"] == "eap/success-frames.jsonl"
            and observer["runningBeforeStop"] is True
            and type(observer["returncode"]) is int
            and observer["returncode"] == 0
            and self.manifest["startNs"] < observer["ready"]["readyNs"] < phase["startNs"]
            and self.manifest["events"][-1]["endNs"]
            < observer["stopNs"]
            < observer["endNs"]
            < phase["endNs"],
            "EAP observer command or complete lifetime disagrees.",
        )
        require(
            set(phase["producers"]) == {"authenticator", "supplicant"},
            "Missing authentication producer lifetimes.",
        )
        expected = {
            "authenticator": [
                "ip",
                "netns",
                "exec",
                "auth",
                "hostapd",
                "-dd",
                f"{SAFE_BASE}/eap/hostapd.conf",
            ],
            "supplicant": [
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
                f"{SAFE_BASE}/eap/success-supplicant.conf",
            ],
        }
        authentication = self.read_boundaries["authenticate:before"]["operation"]
        require(
            authentication["native"]["result"]["producers"] == phase["producers"],
            "Authentication operation and episode identify different processes.",
        )
        for role, command in expected.items():
            life = phase["producers"][role]
            require(
                set(life)
                == {
                    "startNs",
                    "pid",
                    "command",
                    "runningBeforeStop",
                    "stopNs",
                    "returncode",
                    "endNs",
                }
                and life["command"] == command
                and phase[role + "Command"] == command
                and authentication["native"]["result"][role + "Command"] == command
                and life["runningBeforeStop"] is True
                and type(life["pid"]) is int
                and life["pid"] > 0
                and type(life["returncode"]) is int
                and life["returncode"] == 0
                and authentication["startNs"] <= life["startNs"] < authentication["endNs"]
                and self.manifest["events"][-1]["endNs"]
                < life["stopNs"]
                < life["endNs"]
                < observer["stopNs"],
                "Authentication producer was replaced, failed, or exited before the data history.",
            )
        require(
            phase["producers"]["authenticator"]["startNs"] == authentication["startNs"],
            "Authenticator launch does not anchor the actual authentication operation.",
        )
        for role, life in phase["producers"].items():
            rows = eap.read_lines(directory / f"success-{role}.jsonl", phase)
            require(
                all(life["startNs"] <= row["timeNs"] < life["endNs"] for row in rows),
                "Native authentication log escapes its actual producer lifetime.",
            )
        for frame in checked["frames"]:
            life = phase["producers"][
                "authenticator" if frame["role"] == "authenticator" else "supplicant"
            ]
            require(
                life["startNs"] <= frame["timeNs"] < life["endNs"],
                "EAP frame escapes its actual role's producer lifetime.",
            )
        require(
            phase["producers"]["authenticator"]["pid"] != phase["producers"]["supplicant"]["pid"],
            "Authentication roles alias a process.",
        )
        logoff = self.read_boundaries["logoff:before"]["operation"]
        for index, frame in enumerate(checked["frames"]):
            window = authentication if index < checked["logoffFrame"] - 1 else logoff
            require(
                window["startNs"] <= frame["timeNs"] <= window["endNs"],
                "EAP frames escape their actual authentication or Logoff operation.",
            )
        require(
            all(
                source["timeNs"] <= authentication["endNs"]
                for source in checked["methodEvidence"]["source"]
            ),
            "Method evidence was only observed after policy installation.",
        )
        require(
            checked["logicalAuthorization"] == {"beforeLogoff": True, "afterLogoff": False},
            "Unexpected native authentication state transition.",
        )
        status = (directory / "supplicant-status.txt").read_text().splitlines()
        require(
            all(
                line in status
                for line in (
                    "suppPortStatus=Authorized",
                    "EAP state=SUCCESS",
                    "selectedMethod=13 (EAP-TLS)",
                    "eap_tls_version=TLSv1.3",
                    "tls_session_reused=0",
                    f"address={eap.PEER}",
                )
            ),
            "Native authentication status contradicts the selected method.",
        )
        before, after = (
            (directory / name).read_text()
            for name in ("authorized-station.txt", "logged-off-station.txt")
        )
        require(
            before.startswith(eap.PEER + "\nflags=[AUTHORIZED]\n")
            and "dot1xAuthAuthControlledPortStatus=1\n" in before
            and "dot1xAuthEapolLogoffFramesRx=0\n" in before
            and after.startswith(eap.PEER + "\nflags=\n")
            and "dot1xAuthAuthControlledPortStatus=2\n" in after
            and "dot1xAuthEapolLogoffFramesRx=1\n" in after,
            "Native station readbacks disagree with actual Logoff.",
        )
        args = {
            "links": ["link", "show"],
            "addresses": ["address", "show"],
            "routes": ["-4", "route", "show", "table", "main"],
            "rules": ["-4", "rule", "show"],
        }
        require(
            set(self.manifest["authenticationNetwork"]) == {"auth", "peer"},
            "Missing authentication topology.",
        )
        networks = {}
        for name, actor in (("auth", "auth"), ("peer", "client")):
            refs = self.manifest["authenticationNetwork"][name]
            require(set(refs) == set(args), "Incomplete authentication namespace exports.")
            networks[name] = {
                kind: self._export(
                    ref,
                    actor,
                    ["ip", "-j", *args[kind]],
                    (self.manifest["startNs"], self.read_boundaries["initial"]["startNs"]),
                    filename=f"eap/{name}-{kind}.json",
                )
                for kind, ref in refs.items()
            }
        client_link = next(row for row in networks["peer"]["links"] if row["ifname"] == "peer0")
        auth_link = next(row for row in networks["auth"]["links"] if row["ifname"] == "auth0")
        require(
            set(observer["ready"]) == {"readyNs", "interface", "ifindex"}
            and observer["ready"]["interface"] == "auth0"
            and observer["ready"]["ifindex"] == auth_link["ifindex"]
            and auth_link["link_index"] == client_link["ifindex"]
            and client_link["link_index"] == auth_link["ifindex"]
            and client_link["address"] == eap.PEER
            and auth_link["address"] == eap.AUTHENTICATOR,
            "EAP observer and actual UDP client are not adjacent on the same isolated link.",
        )
        require(
            all(
                networks["peer"][kind]
                == self.read_boundaries["initial"]["networks"]["client"][kind]
                for kind in args
            ),
            "Authentication and data refer to different client network exports.",
        )
        _authentication_namespace(networks["auth"])
        require(
            {row["ifname"] for row in networks["auth"]["links"]} == {"lo", "auth0"}
            and len(networks["auth"]["links"]) == 2
            and networks["auth"]["routes"] == []
            and all(
                row["addr_info"] == []
                for row in networks["auth"]["addresses"]
                if row["ifname"] == "auth0"
            ),
            "Authentication namespace has an unmodeled data path or IP address.",
        )
        for kind, ref in logoff["native"]["result"]["network"].items():
            require(
                logoff["exports"][ref["file"]] == networks["auth"][kind],
                "Authentication network changed during the shared data history.",
            )
        self.auth_link = client_link
        return {
            "schema": 1,
            "scope": "checked-native-eap-evidence",
            "link": {"authenticator": eap.AUTHENTICATOR, "peer": eap.PEER},
            "subject": eap.SUBJECT,
            "outerIdentity": eap.OUTER,
            "method": 13,
            "phases": [checked],
            "frameCount": len(checked["frames"]),
            "certificateSHA256": fingerprints,
        }

    def _daemon_logs(self):
        withdrawal = self.read_boundaries[ARCHIVE]["operation"]
        result = withdrawal["native"]["result"]
        ref = result["standbyLogBefore"]
        prefix = withdrawal["exports"][ref["file"]]
        before_disable = self.commands[result["commands"][0]]["startNs"]
        require(
            self.commands[ref["command"]]["endNs"] < before_disable,
            "Standby daemon prefix was read after withdrawal began.",
        )
        primary, standby = (
            (self.directory / f"{actor}.log").read_text() for actor in replication.GATEWAYS
        )
        require(
            not re.search(
                r"\[error\]|can't be committed|commit-create:|commit-destroy:", primary, re.I
            )
            and not re.search(
                r"\[error\]|can't be committed|commit-create:|commit-destroy:", prefix, re.I
            )
            and standby.startswith(prefix)
            and "Committed 1 new entries" in prefix,
            "Daemon failed before the actual commitment and withdrawal prefix.",
        )
        errors = re.findall(r"\[error\].*", standby[len(prefix) :], re.I)
        require(
            errors == ["[ERROR] no dedicated links available!"],
            "Post-withdrawal daemon errors exceed the declared channel loss.",
        )


def _authentication_setup_commands():
    result = [
        ["ip", "netns", "add", "auth"],
        ["ip", "netns", "exec", "auth", "ip", "link", "set", "lo", "up"],
    ]
    for key in ("net.ipv6.conf.all.disable_ipv6", "net.ipv6.conf.default.disable_ipv6"):
        result.append(
            [
                "ip",
                "netns",
                "exec",
                "auth",
                "sh",
                "-c",
                f"echo 1 > /tmp/netlib-proc/sys/{key.replace('.', '/')}",
            ]
        )
    result.append(
        [
            "ip",
            "link",
            "add",
            "auth0",
            "address",
            eap.AUTHENTICATOR,
            "type",
            "veth",
            "peer",
            "name",
            "peer0",
            "address",
            eap.PEER,
        ]
    )
    for actor, interface in (("auth", "auth0"), ("client", "peer0")):
        result.extend(
            [
                ["ip", "link", "set", interface, "netns", actor],
                ["ip", "netns", "exec", actor, "ip", "link", "set", interface, "up"],
            ]
        )
    return result


def _certificate_commands():
    result = [
        [
            "openssl",
            "req",
            "-new",
            "-x509",
            "-newkey",
            "ec",
            "-pkeyopt",
            "ec_paramgen_curve:P-256",
            "-noenc",
            "-keyout",
            "ca.key",
            "-out",
            "ca.pem",
            "-days",
            "7",
            "-subj",
            "/CN=Netlib private EAP test CA",
            "-addext",
            "basicConstraints=critical,CA:TRUE,pathlen:0",
            "-addext",
            "keyUsage=critical,keyCertSign,cRLSign",
        ]
    ]
    for role, principal in (("server", eap.SERVER), ("client", eap.SUBJECT)):
        result.extend(
            [
                [
                    "openssl",
                    "req",
                    "-new",
                    "-newkey",
                    "ec",
                    "-pkeyopt",
                    "ec_paramgen_curve:P-256",
                    "-noenc",
                    "-keyout",
                    f"{role}.key",
                    "-out",
                    f"{role}.csr",
                    "-subj",
                    f"/CN={principal}",
                ],
                [
                    "openssl",
                    "ca",
                    "-batch",
                    "-config",
                    "ca.conf",
                    "-extfile",
                    f"{role}.ext",
                    "-in",
                    f"{role}.csr",
                    "-out",
                    f"{role}.pem",
                    "-notext",
                ],
            ]
        )
    result.extend(
        [
            ["openssl", "ca", "-config", "ca.conf", "-gencrl", "-out", "ca.crl.pem"],
            [
                "openssl",
                "ocsp",
                "-index",
                "index.txt",
                "-rsigner",
                "ca.pem",
                "-rkey",
                "ca.key",
                "-CA",
                "ca.pem",
                "-issuer",
                "ca.pem",
                "-cert",
                "server.pem",
                "-respout",
                "server.ocsp.der",
                "-ndays",
                "1",
            ],
        ]
    )
    result.extend(
        [
            [
                "openssl",
                "x509",
                "-in",
                f"{role}.pem",
                "-noout",
                "-subject",
                "-issuer",
                "-serial",
                "-fingerprint",
                "-sha256",
                "-dates",
            ]
            for role in ("ca", "server", "client")
        ]
    )
    return result


def _authentication_namespace(network):
    require(
        set(network) == {"links", "addresses", "routes", "rules"},
        "Incomplete authentication namespace envelope.",
    )
    links = network["links"]
    require(
        len(links) == 2 and {row["ifname"] for row in links} == {"lo", "auth0"},
        "Unexpected authentication link inventory.",
    )
    for row in links:
        loopback = row["ifname"] == "lo"
        expected = {
            "ifindex": 1 if loopback else row["ifindex"],
            "ifname": "lo" if loopback else "auth0",
            "flags": ["LOOPBACK", "UP", "LOWER_UP"]
            if loopback
            else ["BROADCAST", "MULTICAST", "UP", "LOWER_UP"],
            "mtu": 65536 if loopback else 1500,
            "qdisc": "noqueue",
            "operstate": "UNKNOWN" if loopback else "UP",
            "linkmode": "DEFAULT",
            "group": "default",
            "txqlen": 1000,
            "link_type": "loopback" if loopback else "ether",
            "address": "00:00:00:00:00:00" if loopback else eap.AUTHENTICATOR,
            "broadcast": "00:00:00:00:00:00" if loopback else "ff:ff:ff:ff:ff:ff",
        }
        if not loopback:
            expected.update(link_index=row["link_index"], link_netnsid=row["link_netnsid"])
            require(
                type(row["ifindex"]) is int
                and 1 < row["ifindex"] < 2**32
                and type(row["link_index"]) is int
                and 1 < row["link_index"] < 2**32
                and type(row["link_netnsid"]) is int
                and 0 <= row["link_netnsid"] < 2**31,
                "Authentication link indices lack a native namespace binding.",
            )
        require(
            row == expected,
            "Unsupported authentication link attributes, MTU, or bridge membership.",
        )
    addresses = network["addresses"]
    require(
        len(addresses) == 2 and {row["ifname"] for row in addresses} == {"lo", "auth0"},
        "Unexpected authentication address interface inventory.",
    )
    for row in addresses:
        link = next(value for value in links if value["ifname"] == row["ifname"])
        expected = {key: value for key, value in link.items() if key != "linkmode"}
        expected["addr_info"] = (
            []
            if row["ifname"] == "auth0"
            else [
                {
                    "family": "inet",
                    "local": "127.0.0.1",
                    "prefixlen": 8,
                    "scope": "host",
                    "label": "lo",
                    "valid_life_time": 2**32 - 1,
                    "preferred_life_time": 2**32 - 1,
                }
            ]
        )
        require(
            row == expected, "Authentication addresses contradict the exact isolated link envelope."
        )
    require(
        network["routes"] == []
        and network["rules"]
        == [
            {"priority": 0, "src": "all", "table": "local"},
            {"priority": 32766, "src": "all", "table": "main"},
            {"priority": 32767, "src": "all", "table": "default"},
        ],
        "Authentication namespace has an unmodeled route or routing policy.",
    )
