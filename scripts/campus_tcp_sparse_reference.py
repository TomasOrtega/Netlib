"""Independent sparse gateway observation coverage with actual packet sources.

The oracle forwards each admitted packet immediately. It does not execute Lean.
"""

import copy
import ipaddress
import json
from dataclasses import dataclass, replace

import campus_tcp_gap_reference as gaps

transfer = gaps.recovery.transfer
base = transfer.base
wire = gaps.wire
DIRECTORY = transfer.ROOT / "examples/tcp-sparse-admission"
FIXTURES = DIRECTORY / "fixtures.json"
RAW_ASSUMPTIONS = [
    "Raw packets are supplied inputs. This report does not derive endpoint writes or campus authentication.",
    "The NAT mapping is declared. The checker uses fixed permit routes to the two declared data endpoints.",
    "The checked trace starts with empty tracking and admission state.",
    "The remaining hex strings have valid syntax. Later transport bytes are not decoded after a selected stop.",
    "Gateway observation coverage is distinct from endpoint receive storage.",
    "This selected model does not prove native TCP tracking or eventual delivery.",
]


class Scope(ValueError):
    pass


@dataclass(frozen=True)
class Source:
    id: int
    start: int
    payload: bytes
    observation: int


@dataclass(frozen=True)
class CoverageResult:
    state: object
    novel: int
    source: Source
    offset: int


@dataclass(frozen=True)
class Coverage:
    cells: tuple = ()
    sources: tuple = ()

    @property
    def positions(self):
        return dict(self.cells)

    @property
    def frontier(self):
        position = 0
        present = self.positions
        while position in present:
            position += 1
        return position

    @property
    def high_end(self):
        return max((position + 1 for position, _ in self.cells), default=0)

    @property
    def unique(self):
        return len(self.cells)

    @property
    def next_id(self):
        return len(self.sources)

    @property
    def sparse_seen(self):
        prefix = 0
        for source in self.sources:
            if source.start != prefix:
                return True
            prefix += len(source.payload)
        return False

    def insert(self, start, payload, observation):
        if start < 0 or not payload:
            raise Scope("range")
        end = start + len(payload)
        cells = self.positions
        present = [position for position in range(start, end) if position in cells]
        if present:
            owners = {cells[position].receipt for position in present}
            if len(present) == len(payload) and len(owners) == 1:
                source = self.sources[next(iter(owners))]
                offset = start - source.start
                if source.payload[offset : offset + len(payload)] == payload:
                    return CoverageResult(self, 0, source, offset)
                raise Scope("conflict")
            raise Scope("overlap")
        source = Source(self.next_id, start, payload, observation)
        for index, value in enumerate(payload):
            cells[start + index] = gaps.Byte(value, source.id, index)
        state = Coverage(tuple(sorted(cells.items())), (*self.sources, source))
        return CoverageResult(state, len(payload), source, 0)


@dataclass(frozen=True)
class Lane(base.Lane):
    coverage: Coverage = Coverage()

    @property
    def high_end(self):
        return self.coverage.high_end

    @property
    def outstanding(self):
        return self.high_end - self.acknowledged

    @property
    def valid(self):
        return (
            self.observed == self.coverage.frontier
            and self.acknowledged <= self.observed
            and self.high_end + 2 < wire.HALF_SPACE
            and self.outstanding <= 65535
        )


def data_admission(sender, peer, segment, observation):
    if segment.options:
        return None, "options"
    if segment.flags not in (16, 24):
        return None, "flags"
    start = (segment.sequence - sender.base) % wire.MODULUS
    if start >= wire.HALF_SPACE:
        return None, "sequence"
    if segment.payload:
        try:
            inserted = sender.coverage.insert(start, segment.payload, observation)
        except Scope as reason:
            return None, str(reason)
        novel = inserted.novel > 0
        coverage = inserted.state
    else:
        if start > sender.high_end:
            return None, "sequence"
        inserted, novel, coverage = None, True, sender.coverage
    if len(segment.payload) > sender.data_limit:
        return None, "data" if novel else "sequence"
    offset = base.endpoint.signed_offset(peer.base, segment.acknowledgment)
    if not 0 <= offset <= peer.observed or peer.acknowledged - offset > 65535:
        return None, "acknowledgment" if novel else "sequence"
    if inserted is not None and inserted.novel:
        if start + len(segment.payload) > sender.acknowledged + sender.peer_window:
            return None, "window"
    after_sender = replace(sender, observed=coverage.frontier, coverage=coverage)
    after_peer = replace(peer, acknowledged=max(peer.acknowledged, offset))
    sequence_age = base.endpoint.signed_offset(peer.window_sequence, segment.sequence)
    ack_age = base.endpoint.signed_offset(peer.window_acknowledgment, segment.acknowledgment)
    if offset >= peer.acknowledged and (sequence_age > 0 or sequence_age == 0 and ack_age >= 0):
        after_peer = replace(
            after_peer,
            peer_window=segment.window,
            window_sequence=segment.sequence,
            window_acknowledgment=segment.acknowledgment,
        )
    if not after_sender.valid or not after_peer.valid:
        return None, "epoch" if novel else "sequence"
    return (after_sender, after_peer), None


def admit(before, record, direction, fresh, raw):
    if before.phase != "data":
        result, reason = base.admit(before, record, direction, fresh, raw)
        if result is not None and result.phase == "data":
            result = replace(
                result,
                original=Lane(**result.original.__dict__),
                reply=Lane(**result.reply.__dict__),
            )
        return result, reason
    if fresh or not base.same_binding(before.record, record):
        return None, "replacement"
    packet = wire.decode_packet(raw)
    sender, peer = (
        (before.original, before.reply)
        if direction == "original"
        else (before.reply, before.original)
    )
    lanes, reason = data_admission(sender, peer, packet.segment, len(before.observations))
    if reason:
        return None, reason
    after = (
        replace(before, original=lanes[0], reply=lanes[1])
        if direction == "original"
        else replace(before, original=lanes[1], reply=lanes[0])
    )
    observation = (record.zone, bytes.fromhex(raw), packet.header, packet.segment, direction, fresh)
    return replace(after, observations=(*before.observations, observation)), None


def coverage_json(coverage):
    return {
        "highEnd": coverage.high_end,
        "uniqueBytes": coverage.unique,
        "nextID": coverage.next_id,
        "runs": [
            {
                "position": source.start,
                "end": source.start + len(source.payload),
                "sourceID": source.id,
                "payloadHex": source.payload.hex(),
                "observationIndex": source.observation,
            }
            for source in sorted(coverage.sources, key=lambda source: source.start)
        ],
    }


def image_json(image):
    value = transfer.image_json(image)
    if image.admission.phase == "data":
        for direction in ("original", "reply"):
            lane = getattr(image.admission, direction)
            if lane.coverage.sparse_seen:
                value["admission"][direction]["coverage"] = coverage_json(lane.coverage)
    return value


class Driver(gaps.Driver):
    admit = staticmethod(admit)
    image_json = staticmethod(image_json)


def replay(value):
    return gaps.replay(value, driver=Driver(value))


def projection(report):
    return gaps.projection(report)


def gateway_admissions(report):
    if "gateways" in report["final"]:
        return {name: gateway["admission"] for name, gateway in report["final"]["gateways"].items()}
    if report["final"]["admissionPhase"] != "data":
        return {"primary": {"phase": "empty"}, "standby": {"phase": "empty"}}
    mapping = report["final"]["records"][0]
    original = wire.Header.from_dict(mapping["original"])
    translated = wire.Header.from_dict(mapping["translated"])
    record = transfer.TrackedRecord(
        original,
        translated,
        mapping["zone"],
        False,
        (original.source, original.source_port) != (translated.source, translated.source_port),
        (original.destination, original.destination_port)
        != (translated.destination, translated.destination_port),
    )
    state = base.Admission()
    for service in report["services"]:
        if service["disposition"] == "earlyDrop":
            continue
        state, reason = admit(
            state, record, service["direction"], state.phase == "empty", service["inputHex"]
        )
        assert reason is None
    return {
        "primary": image_json(transfer.Image((record,), state))["admission"],
        "standby": {"phase": "empty"},
    }


def sparse_assurance(report):
    admissions = gateway_admissions(report)
    if not any(
        admission["phase"] == "data"
        and any("coverage" in admission[direction] for direction in ("original", "reply"))
        for admission in admissions.values()
    ):
        return None
    value = {"scope": "gateway-observation-sources"}
    if not report["compliant"]:
        return {**value, "status": "failed", "reason": "The actual joint replay is not compliant."}
    gateways = []
    for gateway in ("primary", "standby"):
        admission = admissions[gateway]
        summary = {"gateway": gateway, "original": None, "reply": None}
        if admission["phase"] == "data":
            for direction in ("original", "reply"):
                coverage = Coverage()
                for index, observed in enumerate(admission["sourcePackets"]):
                    packet = wire.decode_packet(observed["rawIPv4Hex"])
                    if observed["direction"] == direction and packet.segment.payload:
                        start = (
                            packet.segment.sequence - admission[direction]["base"]
                        ) % wire.MODULUS
                        coverage = coverage.insert(start, packet.segment.payload, index).state
                summary[direction] = {
                    "frontier": coverage.frontier,
                    "highEnd": coverage.high_end,
                    "uniqueBytes": coverage.unique,
                    "sources": coverage.next_id,
                    "prefixComplete": coverage.frontier == coverage.high_end,
                }
        gateways.append(summary)
    return {**value, "status": "checked", "gateways": gateways}


def load_fixtures():
    data = json.loads(FIXTURES.read_text())
    for case in data["cases"] + data["inputErrors"]:
        value = copy.deepcopy(data["input"])
        for item in case.get("replacements", []):
            if not item["path"]:
                value = copy.deepcopy(item["value"])
                continue
            target = value
            for key in item["path"][:-1]:
                target = target[key]
            target[item["path"][-1]] = copy.deepcopy(item["value"])
        case["input"] = value
    return data


def raw_replay(value):
    fields = {"schema", "zone", "original", "translated", "packetsHex"}
    if set(value) != fields or type(value["schema"]) is not int or value["schema"] != 1:
        raise ValueError("Use admission schema 1 with an explicit mapping and packet history.")
    if type(value["zone"]) is not int or not 0 <= value["zone"] < 65536:
        raise ValueError("The admission zone must fit in 16 bits.")

    def header(value):
        fields = {"source", "destination", "protocol", "sourcePort", "destinationPort"}
        if set(value) != fields:
            raise ValueError("The mapping header has unknown or missing fields.")
        if any(type(value[key]) is not str for key in ("source", "destination")):
            raise ValueError("The mapping addresses must be IPv4 strings.")
        for key, maximum in (("protocol", 255), ("sourcePort", 65535), ("destinationPort", 65535)):
            if type(value[key]) is not int or not 0 <= value[key] <= maximum:
                raise ValueError("The mapping header field is outside its wire bounds.")
        return wire.Header.from_dict(
            {
                **value,
                "source": str(ipaddress.IPv4Address(value["source"])),
                "destination": str(ipaddress.IPv4Address(value["destination"])),
            }
        )

    original = header(value["original"])
    translated = header(value["translated"])
    if original.protocol != 6 or translated.protocol != 6:
        raise ValueError("The selected mapping must use TCP.")
    record = transfer.TrackedRecord(
        original,
        translated,
        value["zone"],
        False,
        (original.source, original.source_port) != (translated.source, translated.source_port),
        (original.destination, original.destination_port)
        != (translated.destination, translated.destination_port),
    )
    if not isinstance(value["packetsHex"], list):
        raise ValueError("The packet history must be an array of checked packet bytes.")
    packets = [wire.hex_bytes(raw).hex() for raw in value["packetsHex"]]
    before, records, transitions = base.Admission(), (), 0

    def state(admission):
        image = image_json(transfer.Image(records, admission, transitions))
        return {"tracker": image["confirmed"], "admission": image["admission"]}

    initial = state(before)
    steps = []
    for index, raw in enumerate(packets):
        packet = wire.decode_packet(raw)
        if packet.header == record.input("original"):
            direction = "original"
        elif packet.header == record.input("reply"):
            direction = "reply"
        else:
            raise ValueError("The packet header is outside the declared TCP mapping.")
        before_json = state(before)
        after, reason = admit(before, record, direction, not records, raw)
        output = None
        if reason is None:
            if direction == "reply":
                record = replace(record, seen_reply=True)
            if packet.ttl > 1:
                records = (record,)
                output = base.rewrite_packet(raw, record.output(direction), packet.ttl - 1)
            elif not records:
                after = base.Admission()
            transitions += 1
        else:
            after = before
        steps.append(
            {
                "index": index,
                "decoded": packet.to_dict(),
                "before": before_json,
                "decision": {"kind": "accepted"}
                if reason is None
                else {"kind": "unsupported", "reason": reason},
                "outputHex": None if output is None else output["rawIPv4Hex"],
                "after": state(after),
            }
        )
        before = after
        if reason is not None:
            break
    return {
        "scope": "tcp-gateway-admission",
        "supported": not steps or steps[-1]["decision"]["kind"] != "unsupported",
        "inputPackets": len(packets),
        "evaluatedPackets": len(steps),
        "initial": initial,
        "steps": steps,
        "final": state(before),
        "remainingPacketsHex": packets[len(steps) :],
        "assumptions": RAW_ASSUMPTIONS,
    }
