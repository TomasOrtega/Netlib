"""Independent bounded TCP recovery with unique bytes and separate attempts.

The oracle uses exact fractions and constructed packets. It does not execute Lean.
"""

import copy
import json
import struct
from dataclasses import dataclass, replace
from fractions import Fraction

import campus_tcp_transfer_reference as transfer

base = transfer.base
application = base.endpoint
wire = base.wire
DIRECTORY = transfer.ROOT / "examples/tcp-recovery"
FIXTURES = DIRECTORY / "fixtures.json"
EVENTS = ("enableRecovery", "advanceClock", "timeout")


class Stop(ValueError):
    pass


@dataclass(frozen=True)
class Outstanding:
    id: int
    start: int
    count: int
    sent_at: int
    last_at: int
    retried: bool = False

    def to_dict(self):
        return {
            "id": self.id,
            "start": self.start,
            "count": self.count,
            "sentAt": self.sent_at,
            "lastAt": self.last_at,
            "retried": self.retried,
        }


@dataclass(frozen=True)
class Recovery:
    smss: int
    now: int = 0
    outstanding: tuple = ()
    next_id: int = 0
    frontier: int = 0
    srtt: Fraction | None = None
    variance: Fraction | None = None
    last_sample: tuple | None = None
    rto: int = 1000
    deadline: int | None = None
    cwnd: int = 0
    ssthresh: int = 65535
    last_timed_out: int | None = None
    timeout_count: int = 0
    duplicate_acks: int = 0

    @classmethod
    def initial(cls, smss):
        return cls(smss, cwnd=smss)

    @property
    def flight(self):
        return sum(entry.count for entry in self.outstanding)

    @property
    def valid(self):
        return (
            self.smss > 0
            and self.rto >= 1000
            and self.cwnd == self.smss
            and self.flight <= self.smss
        )

    def to_dict(self):
        def rat(value):
            return {"num": value.numerator, "den": value.denominator}

        return {
            "now": self.now,
            "smss": self.smss,
            "outstanding": [entry.to_dict() for entry in self.outstanding],
            "nextId": self.next_id,
            "frontier": self.frontier,
            "estimator": None
            if self.srtt is None
            else {"srtt": rat(self.srtt), "variance": rat(self.variance)},
            "lastSample": None
            if self.last_sample is None
            else dict(zip(("id", "sentAt", "acknowledgedAt"), self.last_sample, strict=True)),
            "rto": self.rto,
            "deadline": self.deadline,
            "cwnd": self.cwnd,
            "ssthresh": self.ssthresh,
            "lastTimedOut": self.last_timed_out,
            "timeoutCount": self.timeout_count,
            "duplicateAcks": self.duplicate_acks,
            "flight": self.flight,
        }

    def advance(self, now):
        if now < self.now:
            raise Stop("backwardClock")
        return replace(self, now=now)

    def sent(self, count):
        if not 0 < count <= min(self.smss, self.cwnd) - self.flight:
            raise Stop("ledger")
        entry = Outstanding(self.next_id, self.frontier, count, self.now, self.now)
        return replace(
            self,
            outstanding=(*self.outstanding, entry),
            next_id=self.next_id + 1,
            frontier=self.frontier + count,
            deadline=self.deadline if self.deadline is not None else self.now + self.rto,
        )

    def acknowledge(self, count):
        if not 0 <= count <= self.flight:
            raise Stop("ledger")
        if count == 0:
            return self
        remaining, retired, left = [], [], count
        for entry in self.outstanding:
            removed = min(left, entry.count)
            left -= removed
            if removed == entry.count:
                retired.append(entry)
            else:
                remaining.append(
                    replace(entry, start=entry.start + removed, count=entry.count - removed)
                )
        srtt, variance, sample, rto = self.srtt, self.variance, self.last_sample, self.rto
        if retired and not any(entry.retried for entry in retired):
            entry = retired[0]
            elapsed = Fraction(self.now - entry.sent_at)
            if srtt is None:
                srtt, variance = elapsed, elapsed / 2
            else:
                old = srtt
                variance = Fraction(3, 4) * variance + abs(old - elapsed) / 4
                srtt = Fraction(7, 8) * old + elapsed / 8
            exact = srtt + max(Fraction(1), 4 * variance)
            rto = max(1000, -(-exact.numerator // exact.denominator))
            sample = (entry.id, entry.sent_at, self.now)
        return replace(
            self,
            outstanding=tuple(remaining),
            srtt=srtt,
            variance=variance,
            last_sample=sample,
            rto=rto,
            deadline=self.now + rto if remaining else None,
            last_timed_out=self.last_timed_out if remaining else None,
            timeout_count=self.timeout_count if remaining else 0,
            duplicate_acks=0,
        )

    def duplicate(self):
        if self.duplicate_acks >= 2:
            raise Stop("fastRecovery")
        return replace(self, duplicate_acks=self.duplicate_acks + 1)

    def timeout(self):
        if not self.outstanding or self.deadline is None:
            raise Stop("idle")
        entry = self.outstanding[0]
        if not entry.count:
            raise Stop("ledger")
        if self.now < max(self.deadline, entry.last_at + self.rto):
            raise Stop("early")
        repeated = self.last_timed_out == entry.id
        if repeated and self.timeout_count >= 2:
            raise Stop("failureHandling")
        after = replace(
            self,
            outstanding=(replace(entry, last_at=self.now, retried=True), *self.outstanding[1:]),
            rto=2 * self.rto,
            deadline=self.now + 2 * self.rto,
            cwnd=self.smss,
            ssthresh=self.ssthresh if repeated else max(self.flight // 2, 2 * self.smss),
            last_timed_out=entry.id,
            timeout_count=self.timeout_count + 1 if repeated else 1,
            duplicate_acks=0,
        )
        return entry.count, after


@dataclass(frozen=True)
class Endpoint(application.State):
    recovery: Recovery | None = None
    last_ack_window: int | None = None

    @property
    def coherent(self):
        return self.recovery is None or (
            self.recovery.valid
            and self.recovery.smss == self.effective_mss
            and self.recovery.flight == len(self.core.sent)
        )

    def to_dict(self):
        value = super().to_dict()
        if self.recovery is not None:
            value["recovery"] = self.recovery.to_dict()
            value["lastAckWindow"] = self.last_ack_window
        return value


def wrap(state):
    return Endpoint(**state.__dict__)


def emit_at(state, sequence, payload):
    inbound = state.core.inbound
    header = wire.Header(
        inbound.destination, inbound.source, 6, inbound.destination_port, inbound.source_port
    )
    raw = bytearray(
        wire.fixture_packet(
            header,
            wire.Segment(
                sequence, state.core.receive_next, 16, window=state.core.window, payload=payload
            ),
        )
    )
    raw[1] = 0
    raw[4:6] = b"\0\0"
    raw[10:12] = b"\0\0"
    raw[10:12] = struct.pack("!H", wire.checksum(raw[:20]))
    return {"rawIPv4Hex": raw.hex(), "decoded": wire.decode_packet(raw).to_dict()}


def evaluate(state, event):
    operation = event["kind"]

    def blocked(reason):
        kind = (
            "unsupported" if reason in ("fastRecovery", "failureHandling", "persist") else "reject"
        )
        return application.Result(state, {"kind": kind, "reason": "recovery." + reason})

    if not state.valid:
        return application.Result(state, {"kind": "reject", "reason": "invalidSeed"})
    if operation == "enableRecovery":
        if state.recovery is not None or state.core.sent:
            return blocked("ledger")
        return application.Result(
            replace(
                state,
                recovery=Recovery.initial(state.effective_mss),
                last_ack_window=state.send_window,
            ),
            {"kind": "accepted", "operation": operation},
        )
    if operation in ("advanceClock", "timeout", "receive") and not state.coherent:
        return blocked("ledger")
    recovery = state.recovery
    try:
        if operation in ("advanceClock", "timeout"):
            if recovery is None:
                return blocked("idle")
            if operation == "advanceClock":
                after = recovery.advance(event["millis"])
                return application.Result(
                    replace(state, recovery=after), {"kind": "accepted", "operation": operation}
                )
            count, after = recovery.timeout()
            if not event["policyPermitted"]:
                return application.Result(state, {"kind": "reject", "reason": "policy"})
            if count > state.send_window:
                return blocked("persist")
            if count > min(len(state.core.sent), state.effective_mss, state.ip_send_limit - 40):
                return blocked("ledger")
            return application.Result(
                replace(state, recovery=after),
                {"kind": "accepted", "operation": "retry", "count": count},
                emit_at(state, state.core.send_una, state.core.sent[:count]),
            )
        if operation == "send" and recovery is not None and event["policyPermitted"]:
            if state.send_window == 0:
                return blocked("persist")
            if (
                not state.coherent
                or not 0 < event["count"] <= min(recovery.smss, recovery.cwnd) - recovery.flight
            ):
                return application.Result(state, {"kind": "reject", "reason": "sendBounds"})
        result = application.evaluate(state, event)
        if result.decision["kind"] != "accepted" or recovery is None:
            return result
        if operation == "send":
            return replace(
                result, state=replace(result.state, recovery=recovery.sent(event["count"]))
            )
        if operation == "receive":
            count = result.decision["acknowledged"]
            segment = wire.decode_packet(event["rawIPv4Hex"]).segment
            after = recovery.acknowledge(count)
            if (
                count == 0
                and state.core.sent
                and not segment.payload
                and segment.acknowledgment == state.core.send_una
                and segment.window == state.last_ack_window
            ):
                after = after.duplicate()
            else:
                after = replace(after, duplicate_acks=0)
            return replace(
                result, state=replace(result.state, recovery=after, last_ack_window=segment.window)
            )
        return result
    except Stop as failure:
        return blocked(str(failure))


def canonical_event(event):
    if event["kind"] not in EVENTS:
        return base.canonical_event(event)
    result = {"kind": event["kind"], "actor": event["actor"]}
    if result["actor"] not in ("client", "server"):
        raise ValueError("The recovery actor is unknown.")
    if event["kind"] == "advanceClock":
        if type(event["millis"]) is not int or event["millis"] < 0:
            raise ValueError("The local clock must be a natural number of milliseconds.")
        result["millis"] = event["millis"]
    if event["kind"] == "timeout":
        if type(event["policyPermitted"]) is not bool:
            raise ValueError("The timeout policy value must be Boolean.")
        result["policyPermitted"] = event["policyPermitted"]
    if set(event) != set(result):
        raise ValueError("The recovery event contains unknown fields.")
    return result


def attempt(state, event):
    if state is None or state.recovery is None:
        return None
    recovery = state.recovery
    kind = event["kind"]
    original, start, count = None, recovery.frontier, 0
    if kind == "send":
        original, count = recovery.next_id, event["count"]
    if kind == "timeout":
        entry = recovery.outstanding[0]
        original, start, count = entry.id, entry.start, entry.count
    return {
        "kind": "original" if kind == "send" else "retry" if kind == "timeout" else "ack",
        "clockMillis": recovery.now,
        "originalID": original,
        "start": start,
        "count": count,
    }


class Driver:
    EVENTS = EVENTS
    canonical_event = staticmethod(canonical_event)
    evaluate = staticmethod(evaluate)
    wrap = staticmethod(wrap)
    attempt = staticmethod(attempt)
    output_kind = staticmethod(
        lambda event: (
            "retry"
            if event["kind"] == "timeout"
            else ("startup" if event["kind"] == "deliver" else event["kind"])
        )
    )


def replay(value):
    if not any(event.get("kind") in EVENTS for event in value["events"]):
        return transfer.replay(value)
    return transfer.replay(value, driver=Driver)


def projection(report):
    if "transfer" not in report["final"]:
        return {
            **{
                key: report[key]
                for key in (
                    "supported",
                    "compliant",
                    "evaluatedEvents",
                    "final",
                    "outputs",
                    "services",
                    "reads",
                    "remainingEvents",
                    "packets",
                    "custodyAssurance",
                )
            },
            "decisions": [row["decision"] for row in report["steps"]],
        }
    value = transfer.projection(report)
    for observed, actual in zip(value["outputs"], report["outputs"], strict=True):
        if "attempt" in actual:
            observed["attempt"] = actual["attempt"]
    return value


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
