"""Audit named native captures through unchanged observations and explicit consumption."""

import copy
import hashlib
import json
import re
import struct
from collections import Counter
from pathlib import Path

import check_replication_capture as replication

EvidenceError, require = replication.EvidenceError, replication.require


def complete_admission(raw):
    try:
        packet = replication.reassembly.decode_ipv4(raw)
        udp = replication.reassembly.udp_value(packet)
    except ValueError as error:
        raise EvidenceError(str(error)) from error
    require(
        udp["udpChecksum"]["status"] == "valid",
        "Admission requires a complete, present UDP checksum.",
    )
    return {**packet, **udp, "mode": "complete", "raw": raw}


def checked_window(start, end, window):
    if window is not None:
        require(isinstance(window, tuple) and len(window) == 2, "Invalid observation window.")
        lower, upper = window
        replication.integer(lower)
        replication.integer(upper)
        require(
            lower <= start < end <= upper, "Native observation lies outside its selected window."
        )


class _ReplicationAdapter:
    def __init__(self, directory):
        self.directory = directory
        self.report = replication.check_capture(directory)
        self.manifest = replication.nat.read_json(directory / "capture.json")
        self.commands = replication.nat.read_json(directory / "commands.json")
        self.boundaries = {
            "initial": (self.manifest["initial"], self.report["initial"]),
            "final": (self.manifest["final"], self.report["final"]),
        }
        self.packets = {}
        for event, checked in zip(self.manifest["events"], self.report["events"], strict=True):
            for side in ("before", "after"):
                self.boundaries[event["id"] + ":" + side] = event[side], checked[side]
            if event["type"] == "packet":
                self.packets[event["id"]] = event, checked

    def boundary(self, name, window):
        require(name in self.boundaries, "Unknown boundary reference.")
        native, conntrack = self.boundaries[name]
        commands = [self.commands[reference["command"]] for reference in self._references(native)]
        start = min(command["startNs"] for command in commands)
        end = max(command["endNs"] for command in commands)
        checked_window(start, end, window)
        return {
            "id": name,
            "startNs": start,
            "endNs": end,
            "conntrack": conntrack,
            "native": native,
        }

    def packet(self, name, window):
        require(name in self.packets, "Unknown packet reference.")
        native, checked = self.packets[name]
        checked_window(native["startNs"], native["endNs"], window)
        admission = complete_admission(checked["inputHex"])
        filename, number = checked["ingressSource"].split(":")
        rows = replication.read_lines(self.directory / filename)
        logged = replication.decode_nflog(rows[int(number) - 1], native["gateway"], int(number))
        require(
            logged["prefix"] == "INGRESS", "Compatibility packet has no actual ingress admission."
        )
        admission.update(
            point="gateway-ingress",
            source=checked["ingressSource"],
            inputIndex=logged["inputIndex"],
            outputIndex=None,
            observedNs=logged["timeNs"],
        )
        return {**checked, "admission": admission}

    @staticmethod
    def _references(value):
        if isinstance(value, dict):
            if set(value) == {"file", "command"}:
                yield value
            else:
                for child in value.values():
                    yield from _ReplicationAdapter._references(child)
        elif isinstance(value, list):
            for child in value:
                yield from _ReplicationAdapter._references(child)

    def finish(self):
        return {key: value for key, value in self.report.items() if key != "events"}


SAFE_BASE = "/tmp/netlib-safe-handoff"
SAFE_TASK = "/task/safe-handoff/exercise.py"
SAFE_TC = "/opt/netlib/sbin/tc"


def _nflog_ready(ready, group):
    require(
        ready["group"] == group
        and ready["receiveBuffer"] >= 131072
        and len(ready["configuration"]) == 2,
        "Incomplete NFLOG configuration.",
    )
    expected = [
        {1: bytes((3,))},
        {
            1: bytes((1,)),
            2: struct.pack("!IBB", 65531, 2, 0),
            4: struct.pack("!I", 1),
            5: struct.pack("!I", 1),
            6: struct.pack("!H", 3),
        },
    ]
    previous = 0
    for index, row in enumerate(ready["configuration"]):
        start, end = replication.interval(row, previous, ready["readyNs"])
        request, answer = bytes.fromhex(row["request"]), bytes.fromhex(row["acknowledgment"])
        require(
            len(request) >= 20
            and struct.unpack_from("=IHHII", request)
            == (len(request), 0x401, 5, index + 1, ready["port"])
            and request[16:20] == bytes((2, 0, 0, 0 if index == 0 else group))
            and replication.reassembly.netlink_attributes(request[20:]) == expected[index],
            "NFLOG configuration bytes disagree.",
        )
        require(
            row["sender"] == [0, 0]
            and row["flags"] == 0
            and len(answer) == 36
            and struct.unpack_from("=IHHII", answer) == (36, 2, 256, index + 1, ready["port"])
            and answer[16:20] == bytes(4)
            and answer[20:] == request[:16]
            and start < end,
            "NFLOG kernel acknowledgment disagrees.",
        )
        previous = end


def _endpoint_nflog(row, actor, number):
    require(
        set(row) == {"timeNs", "hex", "sender", "flags"}
        and row["sender"] == [0, 0]
        and row["flags"] == 0,
        "Endpoint NFLOG sender or truncation flags disagree.",
    )
    raw = bytes.fromhex(row["hex"])
    require(
        len(raw) >= 20
        and struct.unpack_from("=IHHII", raw) == (len(raw), 0x400, 0, 0, 0)
        and raw[16:20] == bytes((2, 0, 0, 43)),
        "Endpoint NFLOG envelope disagrees.",
    )
    fields = replication.reassembly.netlink_attributes(raw[20:])
    require(
        set(fields) == {1, 5, 9, 10, 11, 12, 13, 14}
        and fields[1] == bytes((8, 0, 4, 0))
        and fields[10] == b"ROUTE_ADMIT\0"
        and fields[11] == fields[14] == bytes(4)
        and all(len(fields[key]) == 4 for key in (5, 12, 13)),
        "Endpoint NFLOG hook, UID/GID, or attribute inventory disagrees.",
    )
    return {
        "source": f"{actor}-nflog.jsonl:{number}",
        "actor": actor,
        "timeNs": replication.integer(row["timeNs"]),
        "prefix": "ROUTE_ADMIT",
        "inputIndex": None,
        "outputIndex": int.from_bytes(fields[5], "big"),
        "localSequence": int.from_bytes(fields[12], "big"),
        "globalSequence": int.from_bytes(fields[13], "big"),
        "packet": complete_admission(fields[9].hex()),
    }


class _SafeHandoffAdapter:
    def __init__(self, directory):
        self.directory = directory
        self.manifest = replication.nat.read_json(directory / "capture.json")
        self.commands = replication.nat.read_json(directory / "commands.json")
        self.polls = replication.nat.read_json(directory / "admission-polls.json")
        manifest = self.manifest
        require(
            type(manifest["schema"]) is int
            and manifest["schema"] == 1
            and manifest["profile"] == "queued-ftfw-safe-handoff"
            and manifest["byteorder"] == "little"
            and manifest["admissionPolls"] == "admission-polls.json",
            "Unsupported safe handoff producer profile.",
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

    def _command(self, index, expected=None, window=None):
        require(
            type(index) is int
            and 0 <= index < len(self.commands)
            and index not in self.used_commands,
            "Command reference is invalid or reused.",
        )
        command = self.commands[index]
        if expected is not None:
            require(
                command["arguments"] == expected,
                "Native command arguments contradict their reference.",
            )
        checked_window(command["startNs"], command["endNs"], window)
        self.used_commands.add(index)
        return command

    def _artifact(self, reference, filename=None):
        require(
            set(reference) == {"file", "command"}
            and isinstance(reference["file"], str)
            and re.fullmatch(r"[a-z0-9.-]+", reference["file"])
            and reference["file"] not in self.used_artifacts
            and (filename is None or reference["file"] == filename),
            "Raw artifact reference is reused or contradicts its selected boundary.",
        )
        self.used_artifacts.add(reference["file"])

    def _export(self, reference, actor, args, window, *, as_json=True, filename=None):
        self._artifact(reference, filename)
        command = self._command(reference["command"], ["ip", "netns", "exec", actor, *args], window)
        text = (self.directory / reference["file"]).read_text()
        require(text == command["stdout"], "Native export differs from exact command stdout.")
        return replication.nat.read_json(self.directory / reference["file"]) if as_json else text

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
                    SAFE_TASK,
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
                decoded = replication.decode_af(row, actor, number, self.indices, fence_commands)
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
                decode(row, actor, number) for number, row in enumerate(self.raw_logs[actor], 1)
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
            Counter(self.socket_errors) == Counter({("a", "car"): 1, ("a", "sar"): 1}),
            "Missing or duplicate selected fence socket errors.",
        )

    def boundary(self, name, window):
        require(name in self.boundaries, "Unknown boundary reference.")
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
        require(
            set(native) == {"conntrack", "tables", "networks", "qdiscs", "endpointTables"},
            "Incomplete native boundary inventory.",
        )
        result = {
            "id": name,
            "native": native,
            "conntrack": {},
            "tables": {},
            "networks": {},
            "qdiscs": {},
            "endpointTables": {},
        }
        before_commands = set(self.used_commands)
        for actor in replication.GATEWAYS:
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
        require(
            set(native["conntrack"]) == set(native["tables"]) == set(replication.GATEWAYS)
            and set(native["networks"]) == set(replication.ACTORS),
            "Boundary actor inventory disagrees.",
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
                    refs[kind],
                    actor,
                    ["ip", "-j", *args],
                    (lower, upper),
                    filename=f"{label}-{actor}-{kind}.json",
                )
                for kind, args in arguments.items()
            }
            for kind in ("links", "addresses"):
                for row in result["networks"][actor][kind]:
                    expected_index = (
                        1 if row["ifname"] == "lo" else self.indices[actor].get(row["ifname"])
                    )
                    require(
                        type(row["ifindex"]) is int and row["ifindex"] == expected_index,
                        "Native interface index contradicts the observer binding.",
                    )
                    if row["ifname"] != "lo":
                        peer = replication.OPPOSITE[row["ifname"]]
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
            startNs=min(self.commands[index]["startNs"] for index in new_commands),
            endNs=max(self.commands[index]["endNs"] for index in new_commands),
        )
        checked_window(result["startNs"], result["endNs"], window)
        self.read_boundaries[name] = result
        if name.endswith(":before"):
            result["operation"] = self._operation(name.split(":")[0])
        return result

    def _operation(self, name):
        operation = self.operations[name]
        event = operation["native"]
        result = event["result"]
        exports = {}
        if event["type"] == "stage":
            require(
                result["attempts"] and result["external"] == result["attempts"][-1],
                "Stage cache selection contradicts its final poll.",
            )
            for index, reference in enumerate(result["attempts"]):
                exports[reference["file"]] = self._export(
                    reference,
                    "b",
                    ["conntrackd", "-C", f"{SAFE_BASE}/b.conf", "-e", "-x"],
                    (operation["startNs"], operation["endNs"]),
                    as_json=False,
                    filename=f"stage-b-cache-{index}.xml",
                )
            reference = result["internal"]
            exports[reference["file"]] = self._export(
                reference,
                "a",
                ["conntrackd", "-C", f"{SAFE_BASE}/a.conf", "-i", "-x"],
                (operation["startNs"], operation["endNs"]),
                as_json=False,
                filename="stage-a-internal.xml",
            )
        elif event["type"] == "barrier":
            reference = result["qdisc"]
            interface = "cal" if name == "primary-barrier" else "cbl"
            exports[reference["file"]] = self._export(
                reference,
                "client",
                [SAFE_TC, "-j", "-s", "-d", "qdisc", "show", "dev", interface],
                (operation["startNs"], operation["endNs"]),
                filename=f"{name}-{interface}-qdisc.json",
            )
        for index in event["commands"]:
            if index not in self.used_commands:
                self._command(index, window=(operation["startNs"], operation["endNs"]))
        return {**operation, "exports": exports}

    def _poll(self, admission, source_actor, marker, sender):
        reference = admission["result"]["admission"]
        index = reference["poll"]
        require(
            set(reference) == {"poll", "source"}
            and type(index) is int
            and 0 <= index < len(self.polls)
            and index not in self.used_polls
            and admission["polls"] == [index],
            "Admission poll is invalid, reused, or omitted from its event.",
        )
        poll = self.polls[index]
        require(
            set(poll) == {"actor", "payloadHex", "startNs", "endNs", "attempts", "source", "record"}
            and poll["actor"] == source_actor
            and poll["payloadHex"] == marker
            and reference["source"] == poll["source"],
            "Admission poll identity contradicts its socket input.",
        )
        replication.interval(poll, sender["endNs"], admission["endNs"])
        filename, number = poll["source"].split(":")
        require(
            filename == f"{source_actor}-nflog.jsonl" and number.isdecimal(),
            "Admission poll source is misbound.",
        )
        number = int(number)
        require(
            1 <= number <= len(self.raw_logs[source_actor])
            and poll["record"] == self.raw_logs[source_actor][number - 1],
            "Admission poll rewrites its unchanged NFLOG source record.",
        )
        previous = poll["startNs"]
        require(poll["attempts"], "Admission poll has no actual read attempts.")
        for position, attempt in enumerate(poll["attempts"]):
            _, previous = replication.interval(attempt, previous, poll["endNs"])
            require(
                set(attempt) == {"startNs", "endNs", "lineCount", "selectedLine"}
                and type(attempt["lineCount"]) is int
                and 0 <= attempt["lineCount"] <= len(self.raw_logs[source_actor]),
                "Admission poll read inventory disagrees.",
            )
            require(
                all(
                    row["timeNs"] <= attempt["endNs"]
                    for row in self.raw_logs[source_actor][: attempt["lineCount"]]
                ),
                "Admission poll includes future raw log records.",
            )
            final = position == len(poll["attempts"]) - 1
            require(
                attempt["selectedLine"] == (number if final else None)
                and (number <= attempt["lineCount"] if final else number > attempt["lineCount"]),
                "Admission selection contradicts the available raw log prefix.",
            )
        require(
            poll["record"]["timeNs"] <= previous <= poll["endNs"],
            "Admission poll predates its actual raw source read.",
        )
        logged = self.logs[source_actor][number - 1]
        require(
            sender["response"]["startNs"] <= logged["timeNs"],
            "Admission observation predates its actual endpoint send.",
        )
        require(
            logged["packet"]["dataHex"] == marker,
            "Admission NFLOG payload contradicts the socket request.",
        )
        self.used_polls.add(index)
        self.used_sources.add(logged["source"])
        return logged, poll

    def packet(self, ticket, window):
        require(ticket in self.packets, "Unknown packet reference.")
        selected = self.packets[ticket]
        admit, serve = selected["admit"], selected["serve"]
        checked_window(admit["startNs"], serve["endNs"], window)
        sender, receiver = admit["result"]["sender"], serve["result"]["receiver"]
        request, response = sender["request"], sender["response"]["result"]
        marker = request["payloadHex"]
        original = request.get("peer") == ["203.0.113.2", 8080]
        source_actor, destination_actor = ("client", "server") if original else ("server", "client")
        local = ["192.0.2.2", 41000] if original else ["198.51.100.2", 9000]
        expected_input, expected_output = (
            (replication.ORIGINAL, replication.WIRE)
            if original
            else (replication.WIRE_REPLY, replication.PEER_REPLY)
        )
        require(
            request
            == {
                "operation": "send",
                "peer": [expected_input["destination"], expected_input["destinationPort"]],
                "payloadHex": marker,
                "ttl": 64,
            }
            and response
            == {
                "bytesSent": len(bytes.fromhex(marker)),
                "payloadHex": marker,
                "local": local,
                "peer": request["peer"],
                "ttl": 64,
            },
            "Endpoint send request or result disagrees with supported UDP input.",
        )
        admission, poll = self._poll(admit, source_actor, marker, sender)
        if admit is serve:
            require(
                poll["endNs"] < receiver["startNs"],
                "Atomic packet receive precedes the actual admission read.",
            )
        packet = admission["packet"]
        require(
            packet["header"] == expected_input and packet["ttl"] == 64,
            "Earlier route admission tuple or TTL disagrees.",
        )
        interfaces = [
            name
            for name, index in self.indices[source_actor].items()
            if index == admission["outputIndex"]
        ]
        require(len(interfaces) == 1, "Route admission output ifindex is unknown.")
        endpoint_interface = interfaces[0]
        gateway = "a" if endpoint_interface in ("cal", "sal") else "b"
        ingress_interface = replication.OPPOSITE[endpoint_interface]
        output_interface = (
            ("sar" if original else "car") if gateway == "a" else ("sbr" if original else "cbr")
        )
        require(
            (admit["gateway"], admit["leg"])
            == (serve["gateway"], serve["leg"])
            == (gateway, "original" if original else "reply"),
            "Selected ticket gateway or leg contradicts actual route admission.",
        )
        frames = [row for row in self.frames if row["payloadHex"] == marker]
        gateway_inputs = [
            row for row in frames if row["namespace"] == gateway and row["packetType"] == 0
        ]
        gateway_outputs = [
            row for row in frames if row["namespace"] == gateway and row["packetType"] == 4
        ]
        require(
            len(gateway_inputs) == 1 and len(gateway_outputs) <= 1,
            "Missing or ambiguous actual gateway packet path.",
        )
        incoming = gateway_inputs[0]
        outgoing = gateway_outputs[0] if gateway_outputs else None
        require(
            len(frames) == (4 if outgoing else 2)
            and all(
                sender["response"]["startNs"] <= row["timeNs"] < serve["endNs"] for row in frames
            ),
            "Missing, additional, or mistimed selected AF observations.",
        )
        require(
            admit is serve or all(receiver["startNs"] <= row["timeNs"] for row in frames),
            "Held AF observation precedes its actual queue service interval.",
        )
        require(
            incoming["header"] == expected_input
            and incoming["interface"] == ingress_interface
            and bytes.fromhex(incoming["hex"])[14 : 14 + incoming["ipLength"]].hex()
            == packet["raw"],
            "Earlier route-admission bytes disagree with actual later gateway ingress.",
        )
        source_frames = [row for row in frames if row["namespace"] == source_actor]
        destination_frames = [row for row in frames if row["namespace"] == destination_actor]
        require(
            len(source_frames) == 1
            and source_frames[0]["packetType"] == 4
            and source_frames[0]["interface"] == endpoint_interface
            and source_frames[0]["hex"] == incoming["hex"]
            and len(destination_frames) == int(outgoing is not None),
            "Endpoint AF bytes or physical interface disagree with the selected gateway.",
        )
        if outgoing:
            require(
                outgoing["header"] == expected_output
                and outgoing["interface"] == output_interface
                and outgoing["ttl"] == 63
                and outgoing["ipId"] == incoming["ipId"]
                and outgoing["ipLength"] == incoming["ipLength"]
                and outgoing["udpLength"] == incoming["udpLength"]
                and outgoing["payloadHex"] == marker
                and destination_frames[0]["packetType"] == 0
                and destination_frames[0]["interface"] == replication.OPPOSITE[output_interface]
                and destination_frames[0]["hex"] == outgoing["hex"],
                "Gateway output, endpoint delivery, or preserved datagram fields disagree.",
            )
            source_ip, output_ip = (
                bytes.fromhex(incoming["hex"])[14:34],
                bytes.fromhex(outgoing["hex"])[14:34],
            )
            require(
                source_ip[:8] == output_ip[:8] and source_ip[9] == output_ip[9],
                "Forwarding changed preserved IPv4 fields.",
            )
            expected_receive = {
                "payloadHex": marker,
                "peer": [expected_output["source"], expected_output["sourcePort"]],
                "local": [expected_output["destination"], expected_output["destinationPort"]],
            }
            require(
                receiver["response"]["result"] == expected_receive,
                "Socket delivery contradicts actual NAT egress.",
            )
        else:
            require(
                receiver["response"]["result"] is None
                and receiver["response"]["endNs"] - receiver["response"]["startNs"]
                >= int(receiver["request"]["timeout"] * 1_000_000_000),
                "Denied packet lacks its bounded complete receive observation.",
            )
        require(
            receiver["request"]
            == {
                "operation": "receive",
                "timeout": 0.3 if admit is serve else 4 if gateway == "a" else 2,
            },
            "Unexpected native receive operation.",
        )
        logs = [row for row in self.logs[gateway] if row["packet"]["payloadHex"] == marker]
        require(
            [row["prefix"] for row in logs]
            == (["INGRESS", "TRACKED", "EGRESS"] if outgoing else ["INGRESS", "TRACKED"]),
            "Missing or additional gateway NFLOG observations.",
        )
        for row in logs:
            comparison = incoming if row["prefix"] != "EGRESS" else outgoing
            frame = bytes.fromhex(comparison["hex"])
            require(
                admit is serve or receiver["startNs"] <= row["timeNs"],
                "Held gateway observation precedes its actual service interval.",
            )
            require(
                row["source"] not in self.used_sources
                and sender["response"]["startNs"] <= row["timeNs"] < serve["endNs"]
                and bytes.fromhex(row["packet"]["raw"])[14:]
                == frame[14 : 14 + comparison["ipLength"]]
                and row["hardwareHex"] == incoming["hex"][:28]
                and row["inputIndex"] == self.indices[gateway][ingress_interface]
                and row["outputIndex"]
                == (self.indices[gateway][output_interface] if row["prefix"] == "EGRESS" else None),
                "Gateway NFLOG bytes, interface, or timing contradicts actual AF evidence.",
            )
            self.used_sources.add(row["source"])
        candidates = [
            row
            for row in self.traces[gateway]
            if row["stages"][0]["ipId"] == incoming["ipId"]
            and row["stages"][0]["packet"] == incoming["header"]
        ]
        require(len(candidates) == 1, "Missing or ambiguous selected gateway trace.")
        trace = candidates[0]
        before_key = serve["id"] + ":before"
        require(
            before_key in self.read_boundaries,
            "Read the actual service boundary before binding its packet.",
        )
        before = self.read_boundaries[before_key]
        records = before["conntrack"][gateway]
        require(len(records) <= 1, "Unsupported selected gateway conntrack inventory.")
        fresh = not records
        state = "new" if fresh or (original and not records[0]["status"] & 2) else "established"
        _verify_gateway_path(
            trace,
            incoming,
            outgoing,
            before["tables"][gateway],
            state,
            fresh,
            ingress_interface,
            output_interface,
        )
        trace_source = f"{gateway}-trace.txt:{trace['stages'][0]['line']}"
        require(trace_source not in self.used_sources, "Native trace was reused.")
        self.used_sources.add(trace_source)
        for row in frames:
            require(
                row["source"] not in self.used_sources, "Selected AF packet observation was reused."
            )
            self.used_sources.add(row["source"])
        if admit is not serve:
            require(
                sender["endNs"] < poll["endNs"] < admit["endNs"] < serve["startNs"]
                and receiver["startNs"] <= incoming["timeNs"],
                "Held packet admission and later service intervals overlap or run backward.",
            )
        value = {
            "id": admit["id"],
            "ticket": ticket,
            "admitEvent": admit["id"],
            "serveEvent": serve["id"],
            "gateway": gateway,
            "leg": "original" if original else "reply",
            "classification": state,
            "fresh": fresh,
            "admission": {
                **packet,
                "point": "endpoint-postrouting",
                "source": admission["source"],
                "inputIndex": None,
                "outputIndex": admission["outputIndex"],
                "observedNs": admission["timeNs"],
                "readEndNs": poll["endNs"],
                "interface": endpoint_interface,
            },
            "inputHex": packet["raw"],
            "outputHex": bytes.fromhex(outgoing["hex"])[14 : 14 + outgoing["ipLength"]].hex()
            if outgoing
            else None,
            "outputEthernetHex": outgoing["hex"] if outgoing else None,
            "incoming": incoming,
            "outgoing": outgoing,
            "trace": trace,
            "ingressSource": logs[0]["source"],
            "postSource": logs[-1]["source"] if outgoing else None,
            "frameSources": [row["source"] for row in frames],
            "outputFrameSource": outgoing["source"] if outgoing else None,
            "sender": sender,
            "receiver": receiver,
            "operation": {
                "admit": self.operations[admit["id"]],
                "serve": self.operations[serve["id"]],
            },
            "disposition": "forwarded" if outgoing else "forwardDrop",
        }
        self.packet_reports[ticket] = value
        return value

    def finish(self):
        require(
            len(self.packet_reports) == len(self.packets)
            and self.used_polls == set(range(len(self.polls))),
            "Unconsumed packet or admission poll observations remain.",
        )
        required_sources = (
            {row["source"] for row in self.frames}
            | {row["source"] for rows in self.logs.values() for row in rows}
            | {
                f"{actor}-trace.txt:{row['stages'][0]['line']}"
                for actor, rows in self.traces.items()
                for row in rows
            }
        )
        require(
            self.used_sources == required_sources,
            "Unconsumed selected AF, NFLOG, or trace observations remain.",
        )
        self._sync_audit()
        initial = self.read_boundaries["initial"]
        final = self.read_boundaries["final"]
        first_event = self.manifest["events"][0]["startNs"]
        cache_views = {"initial": {}, "final": {}}
        statistics = {}
        for name, window in (
            ("initial", (initial["endNs"], first_event)),
            ("final", (final["endNs"], self.manifest["endNs"])),
        ):
            require(
                set(self.manifest[name + "Caches"]) == set(replication.GATEWAYS),
                "Missing gateway cache readbacks.",
            )
            for actor, reference in self.manifest[name + "Caches"].items():
                text = self._export(
                    reference,
                    actor,
                    ["conntrackd", "-C", f"{SAFE_BASE}/{actor}.conf", "-e", "-x"],
                    window,
                    as_json=False,
                    filename=f"{name}-{actor}-cache.xml",
                )
                cache_views[name][actor] = replication.decode_cache_xml(text)
        for actor in replication.GATEWAYS:
            statistics[actor] = {}
            require(
                set(self.manifest["statistics"][actor]) == {"cache", "network", "runtime", "ct"},
                "Missing gateway daemon statistics.",
            )
            for kind, reference in self.manifest["statistics"][actor].items():
                text = self._export(
                    reference,
                    actor,
                    ["conntrackd", "-C", f"{SAFE_BASE}/{actor}.conf", "-s", kind],
                    (final["endNs"], self.manifest["endNs"]),
                    as_json=False,
                    filename=f"{actor}-{kind}-statistics.txt",
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
                            "Daemon reports failed or lost observations.",
                        )
            log = (self.directory / f"{actor}.log").read_text()
            require(
                not re.search(
                    r"\[error\]|can't be committed|commit-create:|commit-destroy:", log, re.I
                )
                and (actor != "b" or "Committed 1 new entries" in log),
                "Daemon reports failed replication or commit.",
            )
            require(
                (self.directory / f"{actor}.conf").read_text()
                == replication.configuration(actor).replace(replication.BASE, SAFE_BASE),
                "Daemon configuration contradicts selected FTFW external cache profile.",
            )
        require(
            set(self.manifest["settings"]) == set(replication.ACTORS), "Missing namespace settings."
        )
        for actor, reference in self.manifest["settings"].items():
            values = {
                "net.ipv4.ip_forward": int(actor in replication.GATEWAYS),
                "net.ipv4.conf.all.rp_filter": 0,
                "net.ipv4.conf.default.rp_filter": 0,
                "net.ipv6.conf.all.disable_ipv6": 1,
                "net.ipv6.conf.default.disable_ipv6": 1,
                "net.netfilter.nf_conntrack_udp_timeout": 30,
                "net.netfilter.nf_conntrack_udp_timeout_stream": 120,
                **{
                    f"net.ipv4.conf.{interface}.rp_filter": 0
                    for interface in replication.LINKS[actor]
                },
            }
            text = self._export(
                reference,
                actor,
                ["sysctl", *values],
                (self.manifest["startNs"], initial["startNs"]),
                as_json=False,
                filename=f"{actor}-settings.txt",
            )
            require(
                text == "".join(f"{key} = {value}\n" for key, value in values.items()),
                "Native namespace sysctl readback disagrees.",
            )
        self._provenance(initial, first_event)
        return {
            "schema": 1,
            "profile": self.manifest["profile"],
            "packetCount": len(self.packets),
            "snapshotCount": len(self.boundaries) * 2,
            "frameCount": len(self.frames),
            "nflogCount": sum(len(rows) for rows in self.logs.values()),
            "syncFrameCount": len(self.sync),
            "initial": initial,
            "final": final,
            "cacheViews": cache_views,
            "statistics": statistics,
            "operations": self.operations,
            "syncData": self.sync_data,
        }

    def _sync_audit(self):
        sent = Counter(row["hex"] for row in self.sync if row["packetType"] == 4)
        received = Counter(row["hex"] for row in self.sync if row["packetType"] == 0)
        require(
            sent == received, "Synchronization sender and receiver raw bytes or counts disagree."
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
                        for record in possible[actor]
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
            "/task/safe-handoff/exercise.py": root / "examples/safe-handoff/exercise.py",
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
                    SAFE_TASK,
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


def _digests(path):
    result = {}
    for line in path.read_text().splitlines():
        digest, name = line.split("  ")
        require(
            name not in result and re.fullmatch(r"[0-9a-f]{64}", digest),
            "Invalid or duplicate source digest entry.",
        )
        result[name] = digest
    return result


def _offload(row):
    result = json.loads(row["stdout"])
    require(
        result["interface"] == row["arguments"][-1]
        and set(result["before"]) == set(result["after"]) == set(replication.wire.FEATURES)
        and all(type(value) is int and value in (0, 1) for value in result["before"].values())
        and all(type(value) is int and value == 0 for value in result["after"].values())
        and len(result["operations"]) == 12,
        "Offload readbacks are incomplete or remain enabled.",
    )
    previous = row["startNs"]
    for index, (feature, (get, set_)) in enumerate(replication.wire.FEATURES.items()):
        triple = result["operations"][3 * index : 3 * index + 3]
        require(
            [item["command"] for item in triple] == [get, set_, get]
            and [item["result"] for item in triple] == [result["before"][feature], 0, 0],
            "Offload ioctl sequence contradicts readbacks.",
        )
        for item in triple:
            _, previous = replication.interval(item, previous, row["endNs"])


def _safe_setup_commands():
    setup, shutdown = [], []
    for actor in replication.ACTORS:
        prefix = ["ip", "netns", "exec", actor]
        setup.extend([["ip", "netns", "add", actor], prefix + ["ip", "link", "set", "lo", "up"]])
        for key, value in (
            ("net.ipv6.conf.all.disable_ipv6", 1),
            ("net.ipv6.conf.default.disable_ipv6", 1),
            ("net.ipv4.conf.all.rp_filter", 0),
            ("net.ipv4.conf.default.rp_filter", 0),
            ("net.ipv4.ip_forward", int(actor in replication.GATEWAYS)),
        ):
            setup.append(
                prefix
                + ["sh", "-c", f"echo {value} > /tmp/netlib-proc/sys/{key.replace('.', '/')}"]
            )
    for left, right in (
        ("cal", "car"),
        ("cbl", "cbr"),
        ("sal", "sar"),
        ("sbl", "sbr"),
        ("syncl", "syncr"),
    ):
        setup.append(["ip", "link", "add", left, "type", "veth", "peer", "name", right])
        for name in (left, right):
            actor = replication.INTERFACES[name]
            address, mac = replication.LINKS[actor][name]
            prefix = ["ip", "netns", "exec", actor]
            peer = replication.OPPOSITE[name]
            peer_address, peer_mac = replication.LINKS[replication.INTERFACES[peer]][peer]
            setup.extend(
                [
                    ["ip", "link", "set", name, "netns", actor],
                    prefix + ["ip", "link", "set", name, "address", mac],
                    prefix + ["ip", "address", "add", address + "/24", "dev", name],
                    prefix + ["ip", "link", "set", name, "mtu", "1500", "up"],
                    prefix + ["python3", "/task/wire/exercise.py", "offload", name],
                    prefix
                    + [
                        "ip",
                        "neigh",
                        "replace",
                        peer_address,
                        "lladdr",
                        peer_mac,
                        "nud",
                        "permanent",
                        "dev",
                        name,
                    ],
                ]
            )
    setup.extend(
        [
            [
                "ip",
                "netns",
                "exec",
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
            ],
            [
                "ip",
                "netns",
                "exec",
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
            ],
            [
                "ip",
                "netns",
                "exec",
                "b",
                "ip",
                "route",
                "add",
                "192.0.2.2/32",
                "via",
                "192.0.3.2",
                "dev",
                "cbr",
            ],
            [
                "ip",
                "netns",
                "exec",
                "b",
                "ip",
                "route",
                "add",
                "198.51.100.2/32",
                "via",
                "198.51.101.2",
                "dev",
                "sbr",
            ],
        ]
    )
    for actor in replication.GATEWAYS:
        prefix = ["ip", "netns", "exec", actor]
        setup.extend(
            [
                prefix + ["ip", "route", "add", "blackhole", "203.0.113.1/32"],
                prefix + ["nft", "-f", f"{SAFE_BASE}/{actor}-initial.nft"],
                prefix + ["conntrackd", "-C", f"{SAFE_BASE}/{actor}.conf", "-d"],
                prefix + ["conntrackd", "-C", f"{SAFE_BASE}/{actor}.conf", "-s", "runtime"],
            ]
        )
        shutdown.append(prefix + ["conntrackd", "-C", f"{SAFE_BASE}/{actor}.conf", "-k"])
    for actor in ("client", "server"):
        setup.append(
            ["ip", "netns", "exec", actor, "nft", "-f", f"{SAFE_BASE}/{actor}-admission.nft"]
        )
    return setup, shutdown


def _verify_gateway_path(
    trace, incoming, outgoing, document, classification, fresh, ingress_interface, output_interface
):
    expected = [
        ("replication_observe", "ingress"),
        ("sync_untracked", "prerouting"),
        ("replication_observe", "tracked"),
    ]
    if fresh:
        expected.append(("netlib_nat", "prerouting"))
    expected.append(("netlib", "forward"))
    if outgoing:
        if fresh:
            expected.append(("netlib_nat", "postrouting"))
        expected.extend([("netlib_late", "late"), ("replication_observe", "egress")])
    require(
        [(row["table"], row["chain"]) for row in trace["stages"]] == expected,
        "Gateway hook path contradicts actual entry freshness or outcome.",
    )
    translated = (
        replication.admission.REQUEST
        if incoming["header"] == replication.ORIGINAL
        else replication.admission.REPLY
    )
    for stage in trace["stages"]:
        late = stage["chain"] in ("late", "egress")
        forwarded = late or stage["chain"] in ("forward", "postrouting")
        header = outgoing["header"] if late else translated if forwarded else incoming["header"]
        checksum = replication.reassembly.expected_udp_checksum(
            header, bytes.fromhex(incoming["payloadHex"]), False
        )
        require(
            stage["packet"] == header
            and stage["iif"] == ingress_interface
            and stage["oif"] == (output_interface if forwarded else None)
            and stage["ipId"] == incoming["ipId"]
            and stage["ttl"] == (63 if forwarded else 64)
            and stage["ipLength"] == incoming["ipLength"]
            and stage["udpLength"] == incoming["udpLength"]
            and stage["udpChecksum"] == checksum,
            "Gateway trace tuple, interface, identity, length, TTL, or checksum disagrees.",
        )
        replication.check_trace_rules(stage, document, classification)


class CaptureEvidence:
    def __init__(self, adapter):
        self._adapter = adapter
        self._boundaries = set()
        self._packets = set()
        self._finished = False

    @classmethod
    def open(cls, directory, profile):
        require(profile in ("replication", "safe-handoff"), "Unknown capture profile.")
        adapter = _ReplicationAdapter if profile == "replication" else _SafeHandoffAdapter
        return cls(adapter(Path(directory)))

    def read_boundary(self, reference, window=None):
        require(not self._finished, "Capture evidence is already finished.")
        require(reference not in self._boundaries, "Boundary observation was reused.")
        result = self._adapter.boundary(reference, window)
        self._boundaries.add(reference)
        return copy.deepcopy(result)

    def bind_packet(self, ticket, window=None):
        require(not self._finished, "Capture evidence is already finished.")
        require(ticket not in self._packets, "Packet observation was reused.")
        result = self._adapter.packet(ticket, window)
        self._packets.add(ticket)
        return copy.deepcopy(result)

    def finish(self):
        require(not self._finished, "Capture evidence is already finished.")
        require(
            self._boundaries == set(self._adapter.boundaries)
            and self._packets == set(self._adapter.packets),
            "Unconsumed boundary or packet observations remain.",
        )
        self._finished = True
        return copy.deepcopy(self._adapter.finish())
