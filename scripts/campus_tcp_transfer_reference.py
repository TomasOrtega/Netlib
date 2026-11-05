"""Independent calculations for planned transfer of the selected campus TCP flow.

All bytes are constructed. This module does not execute Lean or send packets.
"""

import copy
import json
from dataclasses import dataclass, field
from pathlib import Path

import campus_tcp_reference as base

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/campus-tcp-transfer"
FIXTURES = DIRECTORY / "fixtures.json"


@dataclass(frozen=True)
class TrackedRecord(base.Record):
    source_nat: bool = False
    destination_nat: bool = False


def tracked_candidate(record, configuration):
    def selected(hook, header, kind):
        _, rules = base.selected_chain(configuration["nat"], hook)
        for rule in rules:
            if all(
                base.expression_match(item, header, "new")
                for item in rule["expr"]
                if "match" in item
            ):
                return any(kind in item for item in rule["expr"])
        return False

    return TrackedRecord(
        record.original,
        record.translated,
        record.zone,
        record.seen_reply,
        selected("postrouting", record.after_destination("original"), "snat"),
        selected("prerouting", record.original, "dnat"),
    )


@dataclass(frozen=True)
class Image:
    records: tuple = ()
    admission: base.Admission = field(default_factory=base.Admission)
    transitions: int = 0

    @property
    def empty(self):
        return not self.records and self.admission == base.Admission()


@dataclass(frozen=True)
class Checkpoint:
    id: int
    staged_at: int
    image: Image


@dataclass
class Transfer:
    paused: bool = False
    installed: bool = False
    sealed: bool = False
    fenced: bool = False
    owners: dict = field(default_factory=lambda: {"client": "primary", "server": "primary"})
    cache: Checkpoint | None = None
    checkpoints: int = 0
    route_epoch: int = 0
    installation: dict | None = None
    installed_image: Image | None = None

    def control(self, event, index, primary, standby, primary_pending):
        kind = event["kind"]
        if kind == "pause":
            if self.paused or self.sealed or self.fenced:
                raise ValueError("The selected transfer has already paused or sealed its source.")
            self.paused = True
        elif kind == "stageCheckpoint":
            if self.sealed or self.fenced:
                raise ValueError("The primary source is sealed.")
            if primary.admission.phase != "data":
                raise ValueError("Checkpoint staging requires established TCP history.")
            if not any(
                entry_json(record) == entry_json(primary.admission.record)
                for record in primary.records
            ):
                raise ValueError("The selected TCP history has no exact confirmed source entry.")
            self.cache = Checkpoint(self.checkpoints, index, primary)
            self.checkpoints += 1
        elif kind == "installCheckpoint":
            if not self.paused:
                raise ValueError("Pause assignments before checkpoint installation.")
            if primary_pending:
                raise ValueError("The primary still has pending immutable tickets.")
            if self.cache is None or self.cache.image != primary:
                raise ValueError("The cached source cut is absent or stale.")
            if self.sealed or not standby.empty:
                raise ValueError("The target is not empty or the source is already sealed.")
            self.installed = self.sealed = True
            standby = self.cache.image
            self.installed_image = standby
            self.installation = {
                "index": index,
                "checkpoint": self.cache.id,
                "stagedAt": self.cache.staged_at,
                "historyTransitions": standby.transitions,
            }
        elif kind == "switchRoute":
            if not self.paused or not self.installed or event["gateway"] != "standby":
                raise ValueError("The route requires a paused installed standby transfer.")
            if primary != self.installed_image or standby != self.installed_image:
                raise ValueError("The source or target changed before route transfer.")
            self.owners[event["actor"]] = "standby"
            self.route_epoch += 1
        elif kind == "fencePrimary":
            if (
                not self.paused
                or not self.installed
                or primary_pending
                or set(self.owners.values()) != {"standby"}
            ):
                raise ValueError("Move the two owners and clear primary tickets before fencing.")
            self.fenced = True
        elif kind == "resume":
            if (
                not self.paused
                or not self.installed
                or not self.fenced
                or set(self.owners.values()) != {"standby"}
            ):
                raise ValueError("Resume requires installed standby ownership and primary fencing.")
            if primary != self.installed_image or standby != self.installed_image:
                raise ValueError("The source or target changed before resuming assignments.")
            self.paused = False
        else:
            raise ValueError("The transfer control is unknown.")
        return primary, standby


def records_json(records):
    return [
        {
            "zone": row.zone,
            "original": row.original.to_dict(),
            "translated": row.translated.to_dict(),
            "seenReply": row.seen_reply,
        }
        for row in records
    ]


def lane_json(lane):
    return {
        "base": lane.base,
        "observed": lane.observed,
        "acknowledged": lane.acknowledged,
        "peerWindow": lane.peer_window,
        "windowSequence": lane.window_sequence,
        "windowAcknowledgment": lane.window_acknowledgment,
    }


def entry_json(record):
    return {
        "original": record.original.to_dict(),
        "reply": base.reverse(record.translated).to_dict(),
        "originalZone": record.zone,
        "replyZone": record.zone,
        "sourceNAT": record.source_nat,
        "destinationNAT": record.destination_nat,
    }


def source_packets(admission):
    seen_reply = False
    packets = []
    for zone, raw, header, _segment, direction, fresh in admission.observations:
        classification = "established" if direction == "reply" or seen_reply else "new"
        seen_reply |= direction == "reply"
        packets.append(
            {
                "zone": zone,
                "rawIPv4Hex": raw.hex(),
                "header": header.to_dict(),
                "segment": base.wire.decode_packet(raw).to_dict()["segment"],
                "entry": entry_json(admission.record),
                "direction": direction,
                "classification": classification,
                "fresh": fresh,
            }
        )
    return packets


def admission_json(admission):
    result = {
        "phase": admission.phase,
        "observations": len(admission.observations),
        "sourcePackets": source_packets(admission),
    }
    if admission.phase != "empty":
        result.update(
            entry=entry_json(admission.record),
            clientISS=admission.client_iss,
            clientWindow=admission.client_window,
        )
    if admission.phase in ("synAck", "data"):
        result.update(serverISS=admission.server_iss, serverWindow=admission.server_window)
    if admission.phase == "data":
        result.update(original=lane_json(admission.original), reply=lane_json(admission.reply))
    return result


def image_json(image):
    return {
        "records": records_json(image.records),
        "confirmed": [
            {**entry_json(record), "seenReply": record.seen_reply} for record in image.records
        ],
        "admission": admission_json(image.admission),
        "historyTransitions": image.transitions,
    }


@dataclass
class Gateway:
    deployment: dict
    configuration: str
    guard: str
    image: Image = field(default_factory=Image)
    attachments: list = field(default_factory=list)

    @property
    def configurations(self):
        return {row["id"]: row for row in self.deployment["configs"]}

    @property
    def guards(self):
        return {row["id"]: row["source"] for row in self.deployment["guards"]}


CONTROLS = {
    "pause",
    "stageCheckpoint",
    "installCheckpoint",
    "switchRoute",
    "fencePrimary",
    "resume",
}


def replay(value):
    if "standby" not in value:
        return base.replay(value)
    authentication = value["authentication"]
    context, link = authentication["context"], authentication["link"]
    active = base.handshake.Local.from_dict(value["active"])
    passive = base.handshake.Local.from_dict(value["passive"])
    if not active.valid or not passive.valid:
        raise ValueError("The endpoint configuration is invalid.")
    gateways = {
        name: Gateway(deployment, deployment["initialConfig"], deployment["initialGuard"])
        for name, deployment in (("primary", value), ("standby", value["standby"]))
    }
    events = [base.canonical_event(event) for event in value["events"]]
    transfer = Transfer()
    auth, after = base.Authentication(), 0
    startup = base.handshake.State()
    endpoints = {"client": None, "server": None}
    established = {"client": None, "server": None}
    outputs, tickets, services, steps, reads = [], [], [], [], []
    supported = compliant = True

    def comparisons(gateway):
        deployment = gateway.deployment
        allowed = [
            row["match"]
            for row in value["intent"]["requirements"]
            if auth.permits(context, row["scope"])
        ]
        attachments = [
            row["specification"]
            for row in gateway.attachments
            if row["round"] == auth.round
            and row["after"] <= after
            and deployment["authenticationPort"] in deployment["live"]
            and row["specification"]["ingress"] in deployment["live"]
            and row["specification"]["ingress"]["namespace"] == deployment["namespace"]
            and auth.permits(context, value["application"])
        ]
        return {
            "forward": base.forward_equivalent(
                json.dumps(
                    gateway.configurations[gateway.configuration]["forward"], sort_keys=True
                ),
                json.dumps(allowed, sort_keys=True),
            ),
            "ingress": base.ingress_equivalent(
                json.dumps(gateway.guards[gateway.guard], sort_keys=True),
                json.dumps(attachments, sort_keys=True),
            ),
        }

    def snapshot():
        primary = gateways["primary"]
        state = {
            "after": after,
            "configuration": primary.configuration,
            "guard": primary.guard,
            "activePhase": startup.active_phase,
            "passivePhase": startup.passive_phase,
            "activeEstablishedAt": established["client"],
            "passiveEstablishedAt": established["server"],
            "client": None if endpoints["client"] is None else endpoints["client"].to_dict(),
            "server": None if endpoints["server"] is None else endpoints["server"].to_dict(),
            "admissionPhase": primary.image.admission.phase,
            "admissionObservations": len(primary.image.admission.observations),
            "records": records_json(primary.image.records),
            "outputs": len(outputs),
            "pendingTickets": [row["id"] for row in tickets if row["pending"]],
            "services": len(services),
            "gateways": {
                name: {
                    "configuration": gateway.configuration,
                    "guard": gateway.guard,
                    **image_json(gateway.image),
                }
                for name, gateway in gateways.items()
            },
            "transfer": {
                "paused": transfer.paused,
                "installed": transfer.installed,
                "primarySealed": transfer.sealed,
                "primaryFenced": transfer.fenced,
                "owners": dict(transfer.owners),
                "routeEpoch": transfer.route_epoch,
                "installation": transfer.installation,
                "cache": None
                if transfer.cache is None
                else {
                    "id": transfer.cache.id,
                    "stagedAt": transfer.cache.staged_at,
                    **image_json(transfer.cache.image),
                },
            },
        }
        return state

    initial = snapshot()
    for index, event in enumerate(events):
        kind, before = event["kind"], snapshot()
        decision, passed = {"kind": "accepted", "operation": kind}, True
        output = decoded = service = startup_operation = None
        read = b""
        actor = event.get("actor")
        if kind in CONTROLS:
            if kind == "stageCheckpoint" and startup.passive_phase != "ESTABLISHED":
                raise ValueError("Finish startup before checkpoint staging.")
            if kind == "installCheckpoint":
                target = gateways["standby"]
                if (
                    event["namespace"] != target.deployment["namespace"]
                    or target.guards[target.guard]["namespace"] != target.deployment["namespace"]
                ):
                    raise ValueError(
                        "The checkpoint target namespace lifetime differs from the declared standby."
                    )
            primary_pending = any(row["pending"] and row["gateway"] == "primary" for row in tickets)
            primary, standby = transfer.control(
                event, index, gateways["primary"].image, gateways["standby"].image, primary_pending
            )
            gateways["primary"].image, gateways["standby"].image = primary, standby
        elif kind == "authentication":
            if event["index"] != after or after >= len(authentication["events"]):
                raise ValueError("Consume authentication events in their actual order.")
            auth, passed = base.authentication_step(
                auth, context, link, authentication["events"][after]
            )
            after += 1
        elif kind in ("install", "installGuard", "stage"):
            gateway = gateways[event.get("gateway", "primary")]
            if kind == "install":
                if event["configuration"] not in gateway.configurations:
                    raise ValueError("The gateway configuration has no source.")
                gateway.configuration = event["configuration"]
                passed = comparisons(gateway)["forward"]
            elif kind == "installGuard":
                if event["guard"] not in gateway.guards:
                    raise ValueError("The gateway ingress guard has no source.")
                gateway.guard = event["guard"]
                passed = comparisons(gateway)["ingress"]
            else:
                specification = next(
                    row
                    for row in gateway.deployment["specifications"]
                    if row["id"] == event["specification"]
                )
                if (
                    gateway.deployment["authenticationPort"] not in gateway.deployment["live"]
                    or specification["ingress"] not in gateway.deployment["live"]
                ):
                    raise ValueError("The attachment interface lifetime is not current.")
                if not auth.permits(context, value["application"]):
                    raise ValueError("The current session does not permit attachment staging.")
                gateway.attachments.append(
                    {"specification": specification, "after": after, "round": auth.round}
                )
        elif kind == "open":
            if startup.passive_phase == "ESTABLISHED":
                decision = {"kind": "unsupported", "reason": "startupCopy"}
            else:
                result = base.handshake.evaluate(
                    active,
                    passive,
                    startup,
                    {
                        "kind": "activeOpen",
                        "remote": event["remote"],
                        "policyPermitted": event["policyPermitted"],
                    },
                    index,
                )
                startup, decision, output = result.state, result.decision, result.output
            actor, startup_operation = "client", "activeOpen"
        elif kind in ("write", "send", "read", "emitAck"):
            if endpoints[actor] is None or startup.passive_phase != "ESTABLISHED":
                decision = {"kind": "unsupported", "reason": "phase"}
            else:
                result = base.endpoint.evaluate(
                    endpoints[actor], {key: item for key, item in event.items() if key != "actor"}
                )
                endpoints[actor], decision, output, read = (
                    result.state,
                    result.decision,
                    result.output,
                    result.read,
                )
                if kind == "read" and decision["kind"] == "accepted":
                    reads.append({"index": index, "actor": actor, "readHex": read.hex()})
        elif kind == "assign":
            if transfer.paused:
                raise ValueError("Assignments are paused.")
            if not 0 <= event["output"] < len(outputs):
                raise ValueError("The assignment has no earlier endpoint output.")
            owner = transfer.owners[outputs[event["output"]]["actor"]]
            if owner == "primary" and (transfer.sealed or transfer.fenced):
                raise ValueError("The primary source is sealed.")
            tickets.append(
                {
                    "id": len(tickets),
                    "output": event["output"],
                    "gateway": owner,
                    "routeEpoch": transfer.route_epoch,
                    "ingress": event["ingress"],
                    "assignedAt": index,
                    "pending": True,
                }
            )
        elif kind == "serve":
            if not 0 <= event["ticket"] < len(tickets) or not tickets[event["ticket"]]["pending"]:
                raise ValueError("The service has no pending immutable ticket.")
            ticket = tickets[event["ticket"]]
            name = ticket["gateway"]
            if name == "primary" and (transfer.sealed or transfer.fenced):
                raise ValueError("The primary source is sealed.")
            if name == "standby" and (transfer.paused or not transfer.installed):
                raise ValueError("Resume the installed standby before service.")
            gateway = gateways[name]
            deployment, image = gateway.deployment, gateway.image
            source = outputs[ticket["output"]]
            ingress, raw = ticket["ingress"], source["rawIPv4Hex"]
            if ingress not in deployment["live"] or ingress["namespace"] != deployment["namespace"]:
                raise ValueError(
                    "The service ingress lifetime is not current for its assigned gateway."
                )
            packet = base.wire.decode_packet(raw)
            checks = comparisons(gateway)
            checks["coverage"] = any(
                base.traffic_matches(row["match"], packet.header)
                for row in deployment["specifications"]
            )
            if not base.ingress_permits(
                gateway.guards[gateway.guard], ingress["ifindex"], packet.header
            ):
                disposition, service_output, direction, hop = "earlyDrop", None, None, None
            else:
                _, selected, direction, fresh = base.attachment(
                    image.records,
                    gateway.configurations[gateway.configuration],
                    packet.header,
                    value["zone"],
                )
                if fresh:
                    selected = tracked_candidate(
                        selected, gateway.configurations[gateway.configuration]
                    )
                candidate, reason = base.admit(image.admission, selected, direction, fresh, raw)
                if reason:
                    decision = {"kind": "unsupported", "reason": reason}
                    disposition, service_output, hop = "unsupported", None, None
                else:
                    result = base.forward(
                        image.records,
                        deployment["routing"],
                        gateway.configurations[gateway.configuration],
                        raw,
                        value["zone"],
                    )
                    admission, reason = base.commit_admission(
                        candidate, selected, fresh, result.records
                    )
                    if reason:
                        decision = {"kind": "unsupported", "reason": reason}
                        disposition, service_output, hop = "unsupported", None, None
                    else:
                        actual_records = tuple(
                            selected if fresh and base.same_binding(record, selected) else record
                            for record in result.records
                        )
                        gateway.image = Image(actual_records, admission, image.transitions + 1)
                        disposition, service_output, hop = (
                            result.disposition,
                            result.output,
                            result.next_hop,
                        )
            if decision["kind"] != "unsupported":
                matched = event["observed"] is None or event["observed"] == {
                    "inputHex": raw,
                    "outputHex": None if service_output is None else service_output["rawIPv4Hex"],
                }
                role_ok = service_output is None or hop == (
                    "server" if source["actor"] == "client" else "client"
                )
                service = {
                    "id": len(services),
                    "index": index,
                    "ticket": ticket["id"],
                    "gateway": name,
                    "routeEpoch": ticket["routeEpoch"],
                    "outputID": source["id"],
                    "actor": source["actor"],
                    "sourceKind": source["kind"],
                    "inputHex": raw,
                    "output": service_output,
                    "disposition": disposition,
                    "direction": direction,
                    "nextHop": hop,
                    "checks": checks,
                    "observationsMatch": matched,
                    "routeRoleMatch": role_ok,
                }
                services.append(service)
                ticket["pending"] = False
                passed = all(checks.values()) and matched and role_ok
        elif kind == "deliver":
            if not 0 <= event["service"] < len(services):
                raise ValueError("The delivery has no earlier actual service.")
            delivered = services[event["service"]]
            if (
                delivered["output"] is None
                or event["rawIPv4Hex"] != delivered["output"]["rawIPv4Hex"]
            ):
                raise ValueError("The receipt differs from the actual earlier service emission.")
            decoded = base.wire.decode_packet(event["rawIPv4Hex"]).to_dict()
            actor = "server" if delivered["actor"] == "client" else "client"
            if startup.passive_phase != "ESTABLISHED":
                produced = outputs[delivered["outputID"]]
                operation = {
                    "activeOpen": "listenSyn",
                    "listenSyn": "synSentSynAck",
                    "synSentSynAck": "synReceivedAck",
                }.get(produced["startupOperation"], "invalid")
                result = base.handshake.evaluate(
                    active,
                    passive,
                    startup,
                    {
                        "kind": operation,
                        "rawIPv4Hex": event["rawIPv4Hex"],
                        "path": "rewrite",
                        "policyPermitted": event["policyPermitted"],
                    },
                    index,
                )
                startup, decision, output = result.state, result.decision, result.output
                startup_operation = operation
                if startup.active_seed is not None and endpoints["client"] is None:
                    endpoints["client"], established["client"] = startup.active_seed, index
                if startup.passive_seed is not None and endpoints["server"] is None:
                    endpoints["server"], established["server"] = startup.passive_seed, index
            elif delivered["sourceKind"] not in ("send", "emitAck"):
                decision = {"kind": "unsupported", "reason": "startupCopy"}
            else:
                result = base.endpoint.evaluate(
                    endpoints[actor], {"kind": "receive", "rawIPv4Hex": event["rawIPv4Hex"]}
                )
                endpoints[actor], decision = result.state, result.decision
        else:
            raise ValueError("The campus transfer event kind is unknown.")
        if output is not None:
            outputs.append(
                {
                    "id": len(outputs),
                    "index": index,
                    "actor": actor,
                    "kind": kind if kind != "deliver" else "startup",
                    "startupOperation": startup_operation,
                    **output,
                }
            )
        steps.append(
            {
                "index": index,
                "event": event,
                "before": before,
                "decision": decision,
                "supported": decision["kind"] != "unsupported",
                "passed": passed,
                "output": output,
                "decodedInput": decoded,
                "readHex": read.hex(),
                "service": service,
                "state": snapshot(),
            }
        )
        compliant &= passed
        if decision["kind"] == "unsupported":
            supported = compliant = False
            break
    return {
        "supported": supported,
        "compliant": bool(compliant),
        "inputEvents": len(events),
        "evaluatedEvents": len(steps),
        "initial": initial,
        "steps": steps,
        "final": snapshot(),
        "outputs": outputs,
        "services": services,
        "reads": reads,
        "remainingEvents": events[len(steps) :],
    }


def compact(value):
    if isinstance(value, dict):
        return {key: compact(item) for key, item in value.items() if key != "sourcePackets"}
    if isinstance(value, list):
        return [compact(item) for item in value]
    return value


def projection(report):
    return {
        "supported": report["supported"],
        "compliant": report["compliant"],
        "evaluatedEvents": report["evaluatedEvents"],
        "final": compact(report["final"]),
        "outputs": [
            {key: row[key] for key in ("id", "index", "actor", "kind", "rawIPv4Hex")}
            for row in report["outputs"]
        ],
        "services": [
            {
                "id": row["id"],
                "index": row["index"],
                "ticket": row["ticket"],
                "gateway": row["gateway"],
                "routeEpoch": row["routeEpoch"],
                "inputHex": row["inputHex"],
                "outputHex": None if row["output"] is None else row["output"]["rawIPv4Hex"],
                "disposition": row["disposition"],
                "checks": row["checks"],
                "observationsMatch": row["observationsMatch"],
                "routeRoleMatch": row["routeRoleMatch"],
            }
            for row in report["services"]
        ],
        "reads": report["reads"],
        "decisions": [row["decision"] for row in report["steps"]],
        "cuts": [
            {
                "index": row["index"],
                "event": row["event"],
                "gateways": compact(row["state"]["gateways"]),
                "transfer": compact(row["state"]["transfer"]),
            }
            for row in report["steps"]
            if row["event"]["kind"] in CONTROLS
        ],
        "remainingEvents": report["remainingEvents"],
    }


def load_fixtures():
    data = json.loads(FIXTURES.read_text())

    def expand(case):
        value = copy.deepcopy(data["input"])
        for replacement in case.get("replacements", []):
            target = value
            for key in replacement["path"][:-1]:
                target = target[key]
            target[replacement["path"][-1]] = copy.deepcopy(replacement["value"])
        return {**case, "input": value}

    return {
        "schema": data["schema"],
        "cases": [expand(case) for case in data["cases"]],
        "inputErrors": [expand(case) for case in data["inputErrors"]],
    }
