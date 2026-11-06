"""Independent ACK reactions with offered windows in stream coordinates.

The oracle uses constructed packets and local clocks. It does not execute Lean.
"""

import copy
import json
import struct
from dataclasses import dataclass, replace

import campus_tcp_recovery_reference as recovery

application = recovery.application
wire = recovery.wire
MODULUS = 1 << 32
EVENTS = (*recovery.EVENTS, "enableAck", "dispatchAck")
DIRECTORY = recovery.transfer.ROOT / "examples/tcp-ack"
FIXTURES = DIRECTORY / "fixtures.json"


def receive_offered(core, packet, width):
    segment = packet.segment
    if not core.valid or packet.header != core.inbound or wire.control(segment):
        return wire.receive(core, packet)
    if not wire.sequence_accepts(
        core.receive_next, width, segment.sequence, segment.occupied_length
    ):
        return wire.Result(
            core,
            {"kind": "reject", "reason": "sequence"},
            {**wire.request(core, "sequence"), "window": width},
        )
    if not segment.flags & 16 or wire.acknowledged_count(core, segment.acknowledgment) is None:
        result = wire.receive(core, packet)
    elif len(segment.payload) > width:
        return wire.Result(core, {"kind": "unsupported", "reason": "trimming"})
    else:
        result = wire.receive(core, packet)
    if result.ack is not None:
        consumed = result.decision.get("received", 0)
        result = replace(result, ack={**result.ack, "window": width - consumed})
    return result


@dataclass(frozen=True)
class Cause:
    id: int
    issued_at: int
    due: int
    demand: object

    def to_dict(self):
        return {
            "id": self.id,
            "issuedAt": self.issued_at,
            "due": self.due,
            "demand": self.demand.to_dict(),
        }


@dataclass(frozen=True)
class Discharge:
    id: int
    time: int
    output: int
    causes: tuple

    def to_dict(self):
        return {
            "id": self.id,
            "time": self.time,
            "output": self.output.to_dict(),
            "causes": [cause.to_dict() for cause in self.causes],
        }


@dataclass(frozen=True)
class Reaction:
    next_id: int = 0
    next_discharge: int = 0
    pending: tuple = ()
    completed: tuple = ()

    def to_dict(self):
        return {
            "nextID": self.next_id,
            "nextDischarge": self.next_discharge,
            "pendingDue": self.deadline,
            "credit": len(self.pending),
            "pending": [cause.to_dict() for cause in self.pending],
            "completed": [row.to_dict() for row in self.completed],
        }

    @property
    def deadline(self):
        return min((cause.due for cause in self.pending), default=None)

    def issue(self, now, demand, delay):
        if min(now, delay) < 0:
            raise ValueError("A cause requires nonnegative time and delay.")
        cause = Cause(self.next_id, now, now + delay, demand)
        return replace(self, next_id=self.next_id + 1, pending=(*self.pending, cause))

    def check_time(self, now):
        if any(now < cause.issued_at for cause in self.pending):
            raise ValueError("clock")
        if any(now > cause.due for cause in self.pending):
            raise ValueError("deadline")

    def complete(self, now, output, demand=None, *, covers=None):
        if not self.pending:
            raise ValueError("noCredit")
        self.check_time(now)
        covered = (lambda owed: owed <= demand) if covers is None else covers
        if any(not covered(cause.demand) for cause in self.pending):
            raise ValueError("coverage")
        discharge = Discharge(self.next_discharge, now, output, self.pending)
        return replace(
            self,
            next_discharge=self.next_discharge + 1,
            pending=(),
            completed=(*self.completed, discharge),
        )


@dataclass(frozen=True)
class ReceiveWindow:
    capacity: int
    outgoing_mss: int
    frontier: int
    edge: int
    buffered: int

    def to_dict(self):
        return {
            "frontier": self.frontier,
            "edge": self.edge,
            "window": self.width,
            "candidate": self.output_width,
            "free": self.free,
            "threshold": self.threshold,
        }

    @classmethod
    def initial(cls, capacity, outgoing_mss):
        if not 0 <= capacity <= 65535 or not 0 < outgoing_mss <= 65535:
            raise ValueError("Invalid receive-window configuration.")
        return cls(capacity, outgoing_mss, 0, capacity, 0)

    @property
    def free(self):
        return self.capacity - self.buffered

    @property
    def width(self):
        return self.edge - self.frontier

    @property
    def withheld(self):
        return self.free - self.width

    @property
    def valid(self):
        return (
            0 <= self.capacity <= 65535
            and 0 < self.outgoing_mss <= 65535
            and 0 <= self.buffered <= self.capacity
            and 0 <= self.frontier <= self.edge
            and 0 <= self.width <= self.free
        )

    @property
    def threshold(self):
        return min((self.capacity + 1) // 2, self.outgoing_mss)

    @property
    def output_width(self):
        return self.free if self.withheld >= self.threshold else self.width

    @property
    def window_update(self):
        return self.output_width > self.width

    def receive(self, count):
        if not 0 <= count <= self.width:
            raise ValueError("The data exceeds the offered receive window.")
        return replace(self, frontier=self.frontier + count, buffered=self.buffered + count)

    def read(self, count):
        if not 0 <= count <= self.buffered:
            raise ValueError("The read exceeds the buffered bytes.")
        return replace(self, buffered=self.buffered - count)

    def commit_output(self):
        return replace(self, edge=self.frontier + self.output_width)

    def sequence(self, initial):
        return (initial + self.frontier) % MODULUS

    def right_edge(self, initial):
        return (initial + self.edge) % MODULUS


@dataclass(frozen=True)
class AckDemand:
    kind: str
    cursor: int
    position: int
    bytes: int
    minimum_edge: int = 0

    def to_dict(self):
        return {
            "kind": self.kind,
            "cursor": self.cursor,
            "position": self.position,
            "bytes": self.bytes,
            "minimumEdge": self.minimum_edge,
        }


@dataclass(frozen=True)
class Acknowledgment:
    cursor: int
    position: int
    window: int

    def to_dict(self):
        return {"cursor": self.cursor, "position": self.position, "window": self.window}


@dataclass(frozen=True)
class AckState:
    origin: int
    rmss: int
    window: ReceiveWindow
    work: Reaction = Reaction()
    full_segments: int = 0
    data_bytes: int = 0

    def to_dict(self):
        return {
            "origin": self.origin,
            "rmss": self.rmss,
            "advertisement": self.window.to_dict(),
            "work": self.work.to_dict(),
            "fullSegments": self.full_segments,
            "dataBytes": self.data_bytes,
        }

    @classmethod
    def initial(cls, origin, capacity, outgoing_mss, rmss):
        if not 0 <= origin < MODULUS or not 0 < rmss < 65536:
            raise ValueError("Invalid own receive MSS or activation cursor.")
        return cls(origin, rmss, ReceiveWindow.initial(capacity, outgoing_mss))

    def receive_data(self, now, cursor, count):
        window = self.window.receive(count)
        full_segments = self.full_segments + (count >= self.rmss)
        data_bytes = self.data_bytes + count
        delay = 0 if full_segments >= 2 or data_bytes >= 2 * self.rmss else 499
        demand = AckDemand("data", cursor, window.frontier, count)
        return replace(
            self,
            window=window,
            full_segments=full_segments,
            data_bytes=data_bytes,
            work=self.work.issue(now, demand, delay),
        )

    def receive_sequence(self, now, cursor):
        demand = AckDemand("sequence", cursor, self.window.frontier, 0)
        return replace(self, work=self.work.issue(now, demand, 0))

    def read(self, now, cursor, count):
        after = self.window.read(count)
        work = self.work
        if after.output_width > self.window.output_width:
            demand = AckDemand(
                "window", cursor, after.frontier, 0, after.frontier + after.output_width
            )
            work = work.issue(now, demand, 0)
        return replace(self, window=after, work=work)

    def complete(self, now, cursor):
        self.work.check_time(now)
        output = Acknowledgment(cursor, self.window.frontier, self.window.output_width)
        work = self.work
        if work.pending:
            work = work.complete(
                now,
                output,
                covers=lambda owed: (
                    owed.position <= output.position
                    and owed.minimum_edge <= output.position + output.window
                ),
            )
        return replace(
            self,
            window=self.window.commit_output(),
            work=work,
            full_segments=0,
            data_bytes=0,
        )


@dataclass(frozen=True)
class Endpoint(recovery.Endpoint):
    local_receive_mss: int | None = None
    ack_state: AckState | None = None
    actor: str | None = None

    def to_dict(self):
        value = super().to_dict()
        if self.ack_state is not None:
            value["localReceiveMSS"] = (
                {"kind": "absent"}
                if self.local_receive_mss is None
                else {"kind": "present", "value": self.local_receive_mss}
            )
            value["ackReaction"] = self.ack_state.to_dict()
        return value

    @property
    def ack_coherent(self):
        if self.ack_state is None:
            return True
        ack = self.ack_state
        return (
            self.recovery is not None
            and ack.window.valid
            and ack.window.capacity == self.core.capacity
            and ack.window.buffered == len(self.core.received)
            and ack.window.sequence(ack.origin) == self.core.receive_next
            and ack.rmss == (536 if self.local_receive_mss is None else self.local_receive_mss)
            and all(
                cause.demand.position <= ack.window.frontier
                and cause.demand.cursor == (ack.origin + cause.demand.position) % MODULUS
                for cause in ack.work.pending
            )
        )


def emit_window(state, sequence, payload, window):
    previous = recovery.emit_at(state, sequence, payload)
    raw = bytearray.fromhex(previous["rawIPv4Hex"])
    raw[34:36] = struct.pack("!H", window)
    raw[36:38] = b"\0\0"
    header = wire.Header.from_dict(previous["decoded"]["header"])
    raw[36:38] = struct.pack(
        "!H", wire.checksum(wire.pseudoheader(header, len(raw) - 20) + raw[20:])
    )
    return {"rawIPv4Hex": raw.hex(), "decoded": wire.decode_packet(raw).to_dict()}


def evaluate(state, event):
    kind = event["kind"]

    def reject(reason):
        return application.Result(state, {"kind": "reject", "reason": reason})

    def blocked(reason):
        reason = "ledger" if reason in ("clock", "coverage") else reason
        return application.Result(
            state,
            {
                "kind": "unsupported" if reason in ("deadline", "challenge") else "reject",
                "reason": "ack." + reason,
            },
        )

    if not state.valid:
        return reject("invalidSeed")
    if kind == "enableAck":
        if not state.coherent:
            return reject("recovery.ledger")
        if state.ack_state is not None:
            return blocked("alreadyEnabled")
        if state.recovery is None:
            return blocked("disabled")
        if state.core.received or state.core.sent:
            return blocked("ledger")
        ack = AckState.initial(
            state.core.receive_next,
            state.core.capacity,
            state.effective_mss,
            536 if state.local_receive_mss is None else state.local_receive_mss,
        )
        return application.Result(
            replace(state, ack_state=ack), {"kind": "accepted", "operation": kind}
        )
    ack = state.ack_state
    if ack is None:
        if kind == "dispatchAck":
            return reject("policy") if not event["policyPermitted"] else blocked("disabled")
        return recovery.evaluate(state, event)
    now = 0 if state.recovery is None else state.recovery.now
    try:
        if kind == "receive":
            if not state.coherent:
                return reject("recovery.ledger")
            if not state.ack_coherent:
                return blocked("ledger")
            packet = wire.decode_packet(event["rawIPv4Hex"])
            result = receive_offered(state.core, packet, ack.window.width)
            if result.decision["kind"] == "unsupported":
                return application.Result(state, result.decision, ack=result.ack)
            if result.decision["kind"] == "reject":
                if result.ack is not None:
                    if result.ack["kind"] == "challenge":
                        return blocked("challenge")
                    ack = ack.receive_sequence(now, state.core.receive_next)
                return application.Result(
                    replace(state, ack_state=ack),
                    {"kind": "reject", "reason": "input." + result.decision["reason"]},
                    ack=result.ack,
                )
            segment = packet.segment
            count = result.decision["acknowledged"]
            timer = state.recovery.acknowledge(count)
            if (
                count == 0
                and state.core.sent
                and not segment.payload
                and segment.acknowledgment == state.core.send_una
                and segment.window == state.last_ack_window
            ):
                timer = timer.duplicate()
            else:
                timer = replace(timer, duplicate_acks=0)
            if segment.payload:
                ack = ack.receive_data(now, result.state.receive_next, len(segment.payload))
            after = replace(
                state,
                core=result.state,
                recovery=timer,
                ack_state=ack,
                last_ack_window=segment.window,
            )
            if application.window_eligible(state, segment):
                after = replace(
                    after,
                    send_window=segment.window,
                    send_wl1=segment.sequence,
                    send_wl2=segment.acknowledgment,
                )
            return application.Result(
                after, {**result.decision, "operation": "receive"}, ack=result.ack
            )
        if kind in ("emitAck", "dispatchAck"):
            if not event["policyPermitted"]:
                return reject("policy")
            ack.work.check_time(now)
            if not ack.work.pending:
                return blocked("noCredit")
            if kind == "dispatchAck" and now < ack.work.deadline:
                return blocked("early")
            if not state.ack_coherent:
                return blocked("ledger")
            after = ack.complete(now, state.core.receive_next)
            return application.Result(
                replace(state, ack_state=after),
                {"kind": "accepted", "operation": kind},
                emit_window(state, state.core.send_next, b"", ack.window.output_width),
            )
        result = recovery.evaluate(state, event)
        if result.decision["kind"] != "accepted":
            return result
        if kind == "advanceClock":
            ack.work.check_time(result.state.recovery.now)
        if kind == "read":
            result = replace(
                result,
                state=replace(
                    result.state,
                    ack_state=ack.read(now, state.core.receive_next, event["count"]),
                ),
            )
        if result.output is not None:
            if not state.ack_coherent:
                return blocked("ledger")
            segment = wire.decode_packet(result.output["rawIPv4Hex"]).segment
            result = replace(
                result,
                state=replace(result.state, ack_state=ack.complete(now, state.core.receive_next)),
                output=emit_window(
                    state, segment.sequence, segment.payload, ack.window.output_width
                ),
            )
        return result
    except recovery.Stop as failure:
        reason = str(failure)
        return application.Result(
            state,
            {
                "kind": "unsupported"
                if reason in ("fastRecovery", "failureHandling", "persist")
                else "reject",
                "reason": "recovery." + reason,
            },
        )
    except ValueError as failure:
        if str(failure) not in ("clock", "deadline", "coverage", "noCredit"):
            raise
        return blocked(str(failure))


def canonical_event(event):
    if event["kind"] not in ("enableAck", "dispatchAck"):
        return recovery.canonical_event(event)
    result = {"kind": event["kind"], "actor": event["actor"]}
    if result["actor"] not in ("client", "server"):
        raise ValueError("The ACK actor is unknown.")
    if event["kind"] == "dispatchAck":
        if type(event["policyPermitted"]) is not bool:
            raise ValueError("The ACK output policy must be Boolean.")
        result["policyPermitted"] = event["policyPermitted"]
    if set(event) != set(result):
        raise ValueError("The ACK event contains unknown fields.")
    return result


class Driver:
    EVENTS = EVENTS
    canonical_event = staticmethod(canonical_event)
    attempt = staticmethod(recovery.attempt)
    output_kind = staticmethod(recovery.Driver.output_kind)

    def __init__(self, value):
        self.configurations = {
            "client": recovery.base.handshake.Local.from_dict(value["active"]),
            "server": recovery.base.handshake.Local.from_dict(value["passive"]),
        }
        self.started = {actor: False for actor in self.configurations}
        self.wrapped = []

    def wrap(self, state):
        actor = ("client", "server")[len(self.wrapped)]
        self.wrapped.append(actor)
        local = self.configurations[actor]
        if (
            state.core.inbound.destination != local.socket.address
            or state.core.inbound.destination_port != local.socket.port
            or state.core.send_una != (local.iss + 1) % MODULUS
        ):
            raise ValueError("The established seed differs from its checked local startup.")
        return Endpoint(
            **state.__dict__,
            actor=actor,
            local_receive_mss=None if local.receive_mss is None else local.receive_mss.value,
        )

    def evaluate(self, state, event):
        kind = event["kind"]
        if kind == "enableAck" and state.ack_state is None and self.started[state.actor]:
            raise ValueError(
                "Enable ACK reactions before this endpoint's send or receive operations."
            )
        if kind in ("send", "receive"):
            self.started[state.actor] = True
        return evaluate(state, event)


def replay(value):
    import campus_tcp_gap_reference as gaps

    return gaps.replay(value)


def projection(report):
    return recovery.projection(report)


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
