"""Independent receive gaps with byte-position storage and actual packet metadata.

The oracle uses static packets and local clocks. It does not execute Lean.
"""

import copy
import json
from dataclasses import dataclass, replace

import campus_tcp_ack_reference as ack

application = ack.application
recovery = ack.recovery
wire = ack.wire
MODULUS = 1 << 32
HALF_SPACE = MODULUS // 2
EVENTS = ack.EVENTS
DIRECTORY = recovery.transfer.ROOT / "examples/tcp-receive-gaps"
FIXTURES = DIRECTORY / "fixtures.json"


def signed_distance(start, target):
    distance = (target - start) % MODULUS
    return distance if distance < HALF_SPACE else distance - MODULUS


class Scope(ValueError):
    pass


@dataclass(frozen=True)
class Receipt:
    id: int
    start: int
    payload: bytes
    header: object
    arrived_at: int


@dataclass(frozen=True)
class Byte:
    value: int
    receipt: int
    payload_index: int


@dataclass(frozen=True)
class Stored:
    state: object
    receipt: Receipt
    novel: int
    released: tuple
    immediate: bool
    duplicate: bool


@dataclass(frozen=True)
class Store:
    origin: int
    capacity: int
    outgoing_mss: int
    position: int = 0
    edge: int | None = None
    unread: tuple = ()
    held: tuple = ()
    receipts: tuple = ()
    next_id: int = 0
    seen_gap: bool = False

    def __post_init__(self):
        if self.edge is None:
            object.__setattr__(self, "edge", self.capacity)
        if not self.valid:
            raise ValueError("The receive store violates its position or capacity bounds.")

    @property
    def byte_map(self):
        return dict(self.held)

    @property
    def held_size(self):
        return len(self.held)

    @property
    def physical_free(self):
        return self.capacity - len(self.unread) - self.held_size

    @property
    def reservation_free(self):
        return self.capacity - len(self.unread)

    @property
    def width(self):
        return self.edge - self.position

    @property
    def valid(self):
        positions = [position for position, _ in self.held]
        return (
            0 <= self.origin < MODULUS
            and 0 <= self.capacity <= 65535
            and 0 < self.outgoing_mss <= 65535
            and 0 <= self.position <= self.edge
            and len(self.unread) + self.held_size <= self.capacity
            and self.width <= self.reservation_free
            and len(set(positions)) == len(positions)
            and all(self.position < position < self.edge for position in positions)
        )

    @property
    def sequence(self):
        return (self.origin + self.position) % MODULUS

    @property
    def threshold(self):
        return min((self.capacity + 1) // 2, self.outgoing_mss)

    @property
    def candidate(self):
        reduction = self.reservation_free - self.width
        return self.reservation_free if reduction >= self.threshold else self.width

    def receive(self, sequence, payload, header=(), arrived_at=0):
        if not payload:
            raise ValueError("The receive store accepts nonempty packet payloads only.")
        start = self.position + signed_distance(self.sequence, sequence)
        end = start + len(payload)
        if end <= self.position or start >= self.edge:
            raise Scope("sequence")
        if start < self.position or end > self.edge:
            raise Scope("trimming")
        previous = self.byte_map
        overlap = [position for position in range(start, end) if position in previous]
        exact = False
        if overlap:
            owners = {previous[position].receipt for position in overlap}
            if len(overlap) == len(payload) and len(owners) == 1:
                owner = next(iter(owners))
                old = next(row for row in self.receipts if row.id == owner)
                exact = old.start == start and old.payload == payload
            if not exact:
                same_bounds = len(overlap) == len(payload) and any(
                    row.start == start and row.start + len(row.payload) == end
                    for row in self.receipts
                    if row.id in owners
                )
                raise Scope("conflict" if same_bounds else "overlap")
        receipt = Receipt(self.next_id, start, payload, header, arrived_at)
        if exact:
            state = replace(self, receipts=(*self.receipts, receipt), next_id=self.next_id + 1)
            return Stored(state, receipt, 0, (), True, True)
        if len(payload) > self.physical_free:
            raise Scope("storage")
        pending = previous.copy()
        for index, value in enumerate(payload):
            pending[start + index] = Byte(value, receipt.id, index)
        frontier = self.position
        released = []
        while frontier in pending:
            released.append(pending.pop(frontier))
            frontier += 1
        state = replace(
            self,
            position=frontier,
            unread=(*self.unread, *released),
            held=tuple(sorted(pending.items())),
            receipts=(*self.receipts, receipt),
            next_id=self.next_id + 1,
            seen_gap=self.seen_gap or start > self.position,
        )
        return Stored(
            state,
            receipt,
            len(payload),
            tuple(released),
            start > self.position or bool(previous),
            False,
        )

    def read(self, count):
        if not 0 <= count <= len(self.unread):
            raise Scope("read")
        return self.unread[:count], replace(self, unread=self.unread[count:])

    def output(self):
        return replace(self, edge=self.position + self.candidate)

    def origin_for(self, cell):
        receipt = next(row for row in self.receipts if row.id == cell.receipt)
        assert receipt.payload[cell.payload_index] == cell.value
        return receipt


@dataclass(frozen=True)
class Metadata:
    header: object
    segment: object


def run_json(receipt):
    header = receipt.header.header
    segment = receipt.header.segment.to_dict()
    segment = {
        **segment,
        "sourcePort": header.source_port,
        "destinationPort": header.destination_port,
    }
    return {
        "position": receipt.start,
        "end": receipt.start + len(receipt.payload),
        "receiptID": receipt.id,
        "payloadHex": receipt.payload.hex(),
        "header": header.to_dict(),
        "segment": segment,
        "receivedAt": receipt.arrived_at,
    }


def owners(cells):
    identities = []
    for cell in cells:
        if not identities or identities[-1] != cell.receipt:
            identities.append(cell.receipt)
    return identities


def receipt_by_id(store, identity):
    return next(row for row in store.receipts if row.id == identity)


@dataclass(frozen=True)
class Endpoint(ack.Endpoint):
    receive_store: Store | None = None

    @property
    def valid(self):
        return super().valid and (
            self.receive_store is None
            or (
                self.receive_store.valid
                and self.receive_store.capacity == self.core.capacity
                and self.receive_store.sequence == self.core.receive_next
                and bytes(cell.value for cell in self.receive_store.unread) == self.core.received
            )
        )

    def to_dict(self):
        value = super().to_dict()
        store = self.receive_store
        if store is not None and store.seen_gap:
            value["receiveStore"] = {
                "frontier": store.position,
                "nextID": store.next_id,
                "heldBytes": store.held_size,
                "reservationFree": store.reservation_free,
                "physicalFree": store.physical_free,
                "held": [
                    run_json(receipt_by_id(store, identity))
                    for identity in owners([cell for _, cell in store.held])
                ],
            }
            if self.ack_state is not None:
                advertisement = value["ackReaction"]["advertisement"]
                advertisement.pop("free")
                advertisement["reservationFree"] = store.reservation_free
                advertisement["physicalFree"] = store.physical_free
        return value


def wrapped(state):
    unread = tuple(Byte(value, -1, index) for index, value in enumerate(state.core.received))
    store = Store(
        state.core.receive_next,
        state.core.capacity,
        state.effective_mss,
        edge=state.core.window,
        unread=unread,
    )
    return Endpoint(**state.__dict__, receive_store=store)


@dataclass(frozen=True)
class Result(application.Result):
    reassembly: dict | None = None

    def to_dict(self):
        value = super().to_dict()
        if self.reassembly is not None:
            value["reassembly"] = self.reassembly
        return value


class HeaderFailure(Exception):
    def __init__(self, receipt, before, reason, check="header"):
        self.receipt = receipt
        self.before = before
        self.reason = reason
        self.check = check
        super().__init__(reason["reason"])


def failure_json(before, failure):
    return {
        "source": "queued" if failure.receipt.id < before.receive_store.next_id else "current",
        "check": failure.check,
        "receipt": run_json(failure.receipt),
        "beforeHeader": failure.before.to_dict(),
        "reason": failure.reason,
    }


def receive_result(before, result, stored=None, headers=(), failure=None):
    detail = None
    if before.receive_store.seen_gap or result.state.receive_store.seen_gap:
        detail = {
            "receiptID": None if stored is None else stored.receipt.id,
            "novelBytes": 0 if stored is None else stored.novel,
            "releasedHex": ""
            if stored is None
            else bytes(cell.value for cell in stored.released).hex(),
            "releasedRuns": []
            if stored is None
            else [
                run_json(receipt_by_id(stored.state, identity))
                for identity in owners(stored.released)
            ],
            "headers": list(headers),
            "failure": None if failure is None else failure_json(before, failure),
        }
    return Result(result.state, result.decision, result.output, result.read, result.ack, detail)


def acknowledge_at(timer, count, arrived_at):
    if not 0 <= arrived_at <= timer.now:
        raise recovery.Stop("ledger")
    if count == 0:
        return timer
    left = count
    for entry in timer.outstanding:
        if left == 0:
            break
        if arrived_at < entry.sent_at:
            raise recovery.Stop("ledger")
        left -= min(left, entry.count)
    after = replace(timer, now=arrived_at).acknowledge(count)
    return replace(
        after, now=timer.now, deadline=timer.now + after.rto if after.outstanding else None
    )


def issue_gap(acknowledgment, now, cursor, novel, advanced, immediate):
    window = acknowledgment.window.receive(advanced)
    full = acknowledgment.full_segments + (novel >= acknowledgment.rmss)
    new_bytes = acknowledgment.data_bytes + novel
    delay = 0 if immediate or full >= 2 or new_bytes >= 2 * acknowledgment.rmss else 499
    demand = ack.AckDemand("data", cursor, window.frontier, novel)
    return replace(
        acknowledgment,
        window=window,
        full_segments=full,
        data_bytes=new_bytes,
        work=acknowledgment.work.issue(now, demand, delay),
    )


def process_header(state, receipt):
    metadata = receipt.header
    segment = metadata.segment
    if metadata.header != state.core.inbound:
        raise HeaderFailure(receipt, state.core, {"kind": "reject", "reason": "tuple"})
    if not segment.flags & 16:
        raise HeaderFailure(receipt, state.core, {"kind": "reject", "reason": "missingAck"})
    count = wire.acknowledged_count(state.core, segment.acknowledgment)
    if count is None:
        raise HeaderFailure(receipt, state.core, {"kind": "reject", "reason": "acknowledgment"})
    timer = state.recovery
    if timer is not None:
        timer = replace(acknowledge_at(timer, count, receipt.arrived_at), duplicate_acks=0)
    after = replace(
        state,
        core=replace(
            state.core,
            receive_next=(state.core.receive_next + len(receipt.payload)) % MODULUS,
            received=state.core.received + receipt.payload,
            send_una=(state.core.send_una + count) % MODULUS,
            sent=state.core.sent[count:],
        ),
        recovery=timer,
        last_ack_window=segment.window if timer is not None else state.last_ack_window,
    )
    if application.window_eligible(state, segment):
        after = replace(
            after,
            send_window=segment.window,
            send_wl1=segment.sequence,
            send_wl2=segment.acknowledgment,
        )
    return after, count


def evaluate(state, event):
    kind = event["kind"]
    if kind != "receive":
        result = ack.evaluate(state, event)
        if kind == "read" and result.decision["kind"] == "accepted":
            _, store = state.receive_store.read(event["count"])
            result = replace(result, state=replace(result.state, receive_store=store))
        if result.output is not None and result.decision["kind"] == "accepted":
            store = result.state.receive_store
            edge = (
                store.position + result.state.core.window
                if result.state.ack_state is None
                else result.state.ack_state.window.edge
            )
            result = replace(
                result, state=replace(result.state, receive_store=replace(store, edge=edge))
            )
        return result
    before = state

    def rejected(reason):
        return receive_result(
            before, application.Result(before, {"kind": "reject", "reason": reason})
        )

    def unsupported(reason):
        return receive_result(
            before, application.Result(before, {"kind": "unsupported", "reason": reason})
        )

    if not state.valid:
        return rejected("invalidSeed")
    if not state.coherent:
        return rejected("recovery.ledger")
    if state.ack_state is not None and not state.ack_coherent:
        return rejected("ack.ledger")
    packet = wire.decode_packet(wire.hex_bytes(event["rawIPv4Hex"]))
    segment = packet.segment
    if packet.header != state.core.inbound or wire.control(segment) or not segment.payload:
        return receive_result(before, ack.evaluate(state, event))
    width = state.core.window if state.ack_state is None else state.ack_state.window.width
    if not wire.sequence_accepts(
        state.core.receive_next, width, segment.sequence, segment.occupied_length
    ):
        return receive_result(before, ack.evaluate(state, event))
    now = 0 if state.recovery is None else state.recovery.now
    try:
        selected_store = replace(state.receive_store, edge=state.receive_store.position + width)
        stored = selected_store.receive(
            segment.sequence, segment.payload, Metadata(packet.header, segment), now
        )
        after = state
        acknowledged = 0
        effects = []
        for identity in owners(stored.released):
            receipt = receipt_by_id(stored.state, identity)
            before_header = after.core
            try:
                after, count = process_header(after, receipt)
            except HeaderFailure as failure:
                if receipt.id == stored.receipt.id:
                    return receive_result(before, ack.evaluate(before, event), failure=failure)
                result = application.Result(
                    before, {"kind": "unsupported", "reason": "queuedHeader"}
                )
                return receive_result(before, result, failure=failure)
            except recovery.Stop as stopped:
                if receipt.id == stored.receipt.id:
                    result = application.Result(
                        before, {"kind": "reject", "reason": "recovery." + str(stopped)}
                    )
                else:
                    result = application.Result(
                        before, {"kind": "unsupported", "reason": "queuedHeader"}
                    )
                failure = HeaderFailure(
                    receipt,
                    before_header,
                    {"kind": "reject", "reason": "recovery." + str(stopped)},
                    "recovery",
                )
                return receive_result(before, result, failure=failure)
            effects.append(
                {
                    "receiptID": receipt.id,
                    "receivedAt": receipt.arrived_at,
                    "acknowledged": count,
                    "beforeSendUna": before_header.send_una,
                    "afterSendUna": after.core.send_una,
                }
            )
            acknowledged += count
        acknowledgment = after.ack_state
        if acknowledgment is not None:
            acknowledgment = issue_gap(
                acknowledgment,
                now,
                after.core.receive_next,
                stored.novel,
                len(stored.released),
                stored.immediate,
            )
        after = replace(after, receive_store=stored.state, ack_state=acknowledgment)
        assert after.valid
        request = wire.request(after.core, "data")
        request["window"] = width - len(stored.released)
        result = application.Result(
            after,
            {
                "kind": "accepted",
                "operation": "receive",
                "acknowledged": acknowledged,
                "received": stored.novel,
            },
            ack=request,
        )
        return receive_result(before, result, stored, effects)
    except Scope as failure:
        return unsupported(str(failure))
    except recovery.Stop as failure:
        reason = str(failure)
        result = application.Result(
            before,
            {
                "kind": "unsupported"
                if reason in ("fastRecovery", "failureHandling", "persist")
                else "reject",
                "reason": "recovery." + reason,
            },
        )
        return receive_result(before, result)


class Driver(ack.Driver):
    def __init__(self, value):
        super().__init__(value)
        self.records = []

    def wrap(self, state):
        return wrapped(super().wrap(state))

    def evaluate(self, state, event):
        kind = event["kind"]
        if kind == "enableAck" and state.ack_state is None and self.started[state.actor]:
            raise ValueError(
                "Enable ACK reactions before this endpoint's send or receive operations."
            )
        if kind in ("send", "receive"):
            self.started[state.actor] = True
        result = evaluate(state, event)
        self.records.append((state.actor, kind, event, state.to_dict(), result))
        return result


def replay(value):
    driver = Driver(value)
    report = recovery.transfer.replay(value, driver=driver)
    pending = iter(driver.records)
    current = next(pending, None)
    for step in report["steps"]:
        if current is None:
            break
        actor, kind, event, before, result = current
        actual = step["event"]
        matches = kind == actual["kind"] and actual.get("actor") == actor
        if kind == "receive":
            matches = (
                actual["kind"] == "deliver"
                and actual["rawIPv4Hex"] == event["rawIPv4Hex"]
                and report["services"][actual["service"]]["sourceKind"]
                in ("send", "emitAck", "dispatchAck", "retry")
            )
        if not matches or step["before"][actor] != before:
            continue
        if isinstance(result, Result) and result.reassembly is not None:
            step["reassembly"] = result.reassembly
        current = next(pending, None)
    assert current is None, "An actual endpoint operation is absent from the joint replay."
    return report


def projection(report):
    return recovery.projection(report)


def receive_gap_assurance(report):
    actors = ("client", "server")
    endpoints = {actor: report["final"][actor] for actor in actors}
    if not any(state is not None and "receiveStore" in state for state in endpoints.values()):
        return None
    value = {"scope": "ordered-receive-storage"}
    if not report["compliant"]:
        return {
            **value,
            "status": "failed",
            "reason": "The actual joint replay is not compliant.",
        }
    assert report["final"]["passivePhase"] == "ESTABLISHED"
    totals = {actor: {"receipts": 0, "released": 0, "read": 0} for actor in actors}
    for step in report["steps"]:
        event = step["event"]
        if event["kind"] != "deliver" or step["decision"]["kind"] != "accepted":
            continue
        if step["before"]["passivePhase"] != "ESTABLISHED":
            continue
        service = report["services"][event["service"]]
        if service["sourceKind"] not in ("send", "retry", "emitAck", "dispatchAck"):
            continue
        actor = "server" if service["actor"] == "client" else "client"
        payload = wire.decode_packet(event["rawIPv4Hex"]).segment.payload
        if payload:
            totals[actor]["receipts"] += 1
            totals[actor]["released"] += len(
                bytes.fromhex(step["state"][actor]["core"]["receivedHex"])
            ) - len(bytes.fromhex(step["before"][actor]["core"]["receivedHex"]))
    for read in report["reads"]:
        totals[read["actor"]]["read"] += len(bytes.fromhex(read["readHex"]))
    held = {actor: endpoints[actor].get("receiveStore", {}).get("heldBytes", 0) for actor in actors}
    value["status"] = "pending" if any(held.values()) else "checked"
    for actor in actors:
        store = endpoints[actor].get("receiveStore")
        if store is not None:
            assert store["nextID"] == totals[actor]["receipts"]
        value[actor + "Receipts"] = totals[actor]["receipts"]
        value[actor + "HeldBytes"] = held[actor]
        value[actor + "ReleasedBytes"] = totals[actor]["released"]
        value[actor + "ReadBytes"] = totals[actor]["read"]
    return value


def load_fixtures():
    data = json.loads(FIXTURES.read_text())
    for key in ("cases", "inputErrors"):
        for case in data[key]:
            value = copy.deepcopy(data["input"])
            for replacement in case.get("replacements", []):
                if not replacement["path"]:
                    value = copy.deepcopy(replacement["value"])
                    continue
                target = value
                for name in replacement["path"][:-1]:
                    target = target[name]
                target[replacement["path"][-1]] = copy.deepcopy(replacement["value"])
            case["input"] = value
    return data


def raw_event(value):
    kind = value["kind"]
    fields = {
        "write": {"kind", "payloadHex"},
        "receive": {"kind", "rawIPv4Hex"},
        "send": {"kind", "count", "policyPermitted"},
        "read": {"kind", "count"},
        "emitAck": {"kind", "policyPermitted"},
        "enableRecovery": {"kind"},
        "enableAck": {"kind"},
        "advanceClock": {"kind", "millis"},
        "dispatchAck": {"kind", "policyPermitted"},
        "timeout": {"kind", "policyPermitted"},
    }
    if kind not in fields or set(value) != fields[kind]:
        raise ValueError("The endpoint event has unknown or missing fields.")
    result = dict(value)
    for key in ("count", "millis"):
        if key in value and (type(value[key]) is not int or value[key] < 0):
            raise ValueError("The endpoint count or clock must be a natural number.")
    if "policyPermitted" in value and type(value["policyPermitted"]) is not bool:
        raise ValueError("The output policy must be Boolean.")
    for key in ("payloadHex", "rawIPv4Hex"):
        if key in result:
            result[key] = wire.hex_bytes(result[key]).hex()
    return result


def raw_state(seed):
    fields = {
        "core",
        "pendingHex",
        "pendingLimit",
        "sendWindow",
        "sendWL1",
        "sendWL2",
        "effectiveMSS",
        "ipSendLimit",
    }
    if set(seed) != fields:
        raise ValueError("The endpoint seed has unknown or missing fields.")
    base = application.State.from_dict(seed)
    return wrapped(ack.Endpoint(**base.__dict__))


def raw_replay(value):
    if (
        set(value) != {"schema", "seed", "events"}
        or type(value["schema"]) is not int
        or value["schema"] != 1
    ):
        raise ValueError("Use endpoint schema 1 with seed and events.")
    before = raw_state(value["seed"])
    if not before.valid:
        raise ValueError("Seed state is invalid.")
    seed = before
    canonical = [raw_event(item) for item in value["events"]]
    started = False
    steps = []
    for index, selected in enumerate(canonical):
        kind = selected["kind"]
        if kind == "enableAck" and started and before.ack_state is None:
            raise ValueError(
                "Enable ACK reactions before this endpoint's send or receive operations."
            )
        if kind in ("send", "receive"):
            started = True
        result = evaluate(before, selected)
        steps.append(
            {
                "index": index,
                "event": selected,
                "before": before.to_dict(),
                "decodedInput": wire.decode_packet(selected["rawIPv4Hex"]).to_dict()
                if kind == "receive"
                else None,
                **result.to_dict(),
            }
        )
        before = result.state
        if result.decision["kind"] == "unsupported":
            break
    return {
        "scope": "tcp-application-projection",
        "supported": not steps or steps[-1]["decision"]["kind"] != "unsupported",
        "inputEvents": len(canonical),
        "evaluatedEvents": len(steps),
        "seed": seed.to_dict(),
        "steps": steps,
        "final": before.to_dict(),
        "remainingEvents": canonical[len(steps) :],
        "finalStateValid": before.valid,
    }
