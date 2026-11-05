"""Independent static oracle for the selected TCP application path.

The oracle uses constructed bytes. It does not execute Lean or send packets.
"""

import json
import struct
from dataclasses import dataclass, replace
from pathlib import Path

import tcp_receive_reference as wire

MODULUS = wire.MODULUS
HALF_SPACE = wire.HALF_SPACE
FIXTURES = Path(__file__).resolve().parent.parent / "examples/tcp-endpoint/fixtures.json"


def signed_offset(origin, value):
    return (value - origin + HALF_SPACE) % MODULUS - HALF_SPACE


@dataclass(frozen=True)
class State:
    core: wire.State
    pending: bytes
    pending_limit: int
    send_window: int
    send_wl1: int
    send_wl2: int
    effective_mss: int
    ip_send_limit: int

    @property
    def valid(self):
        return (
            self.core.valid
            and len(self.pending) <= self.pending_limit <= 65535
            and 0 <= self.send_window <= 65535
            and 0 < self.effective_mss
            and 40 + self.effective_mss <= self.ip_send_limit <= 65535
        )

    @classmethod
    def from_dict(cls, value):
        return cls(
            wire.State.from_dict(value["core"]),
            wire.hex_bytes(value["pendingHex"]),
            value["pendingLimit"],
            value["sendWindow"],
            value["sendWL1"],
            value["sendWL2"],
            value["effectiveMSS"],
            value["ipSendLimit"],
        )

    def to_dict(self):
        return {
            "core": self.core.to_dict(),
            "pendingHex": self.pending.hex(),
            "pendingLimit": self.pending_limit,
            "sendWindow": self.send_window,
            "sendWL1": self.send_wl1,
            "sendWL2": self.send_wl2,
            "effectiveMSS": self.effective_mss,
            "ipSendLimit": self.ip_send_limit,
        }

    def seed_dict(self):
        return {**self.to_dict(), "core": self.core.seed_dict()}


@dataclass(frozen=True)
class Result:
    state: State
    decision: dict
    output: dict | None = None
    read: bytes = b""
    ack: dict | None = None

    def to_dict(self):
        return {
            "state": self.state.to_dict(),
            "decision": self.decision,
            "output": self.output,
            "readHex": self.read.hex(),
            "ack": self.ack,
        }


def emit(state, payload):
    core = state.core
    inbound = core.inbound
    header = wire.Header(
        inbound.destination,
        inbound.source,
        6,
        inbound.destination_port,
        inbound.source_port,
    )
    blank = (
        wire.TCP_HEADER.pack(
            header.source_port,
            header.destination_port,
            core.send_next,
            core.receive_next,
            0x50,
            16,
            core.window,
            0,
            0,
        )
        + payload
    )
    tcp_crc = wire.checksum(wire.pseudoheader(header, len(blank)) + blank)
    tcp = blank[:16] + struct.pack("!H", tcp_crc) + blank[18:]
    ip = wire.IP_HEADER.pack(
        0x45,
        0,
        len(tcp) + 20,
        0,
        0x4000,
        64,
        6,
        0,
        int(wire.ipaddress.IPv4Address(header.source)),
        int(wire.ipaddress.IPv4Address(header.destination)),
    )
    raw = ip[:10] + struct.pack("!H", wire.checksum(ip)) + ip[12:] + tcp
    packet = wire.decode_packet(raw)
    return {"rawIPv4Hex": raw.hex(), "decoded": packet.to_dict()}


def window_eligible(state, segment):
    ack_offset = signed_offset(state.core.send_una, segment.acknowledgment)
    sequence_offset = signed_offset(state.send_wl1, segment.sequence)
    ack_history_offset = signed_offset(state.send_wl2, segment.acknowledgment)
    forward_ack = 0 <= ack_offset <= len(state.core.sent)
    fresh = sequence_offset > 0 or (sequence_offset == 0 and ack_history_offset >= 0)
    return forward_ack and fresh


def evaluate(state, event):
    def reject(reason):
        return Result(state, {"kind": "reject", "reason": reason})

    def accepted(operation, after, **fields):
        return Result(after, {"kind": "accepted", "operation": operation, **fields})

    if not state.valid:
        return reject("invalidSeed")
    operation = event["kind"]
    if operation == "write":
        payload = wire.hex_bytes(event["payloadHex"])
        if len(state.pending) + len(payload) > state.pending_limit:
            return reject("pendingCapacity")
        return accepted(
            "write", replace(state, pending=state.pending + payload), count=len(payload)
        )
    if operation == "read":
        count = event["count"]
        if count > len(state.core.received):
            return reject("readBounds")
        after = replace(state, core=replace(state.core, received=state.core.received[count:]))
        return replace(accepted("read", after, count=count), read=state.core.received[:count])
    if operation in ("send", "emitAck"):
        if not event["policyPermitted"]:
            return reject("policy")
        if operation == "emitAck":
            return replace(accepted("emitAck", state), output=emit(state, b""))
        count = event["count"]
        maximum = min(
            len(state.pending),
            state.send_window - len(state.core.sent),
            65535 - len(state.core.sent),
            state.effective_mss,
            state.ip_send_limit - 40,
        )
        if not 0 < count <= maximum:
            return reject("sendBounds")
        payload = state.pending[:count]
        output = emit(state, payload)
        core = replace(
            state.core,
            sent=state.core.sent + payload,
            send_next=(state.core.send_next + count) % MODULUS,
        )
        after = replace(state, core=core, pending=state.pending[count:])
        return replace(accepted("send", after, count=count), output=output)
    if operation == "receive":
        packet = wire.decode_packet(wire.hex_bytes(event["rawIPv4Hex"]))
        result = wire.receive(state.core, packet)
        kind = result.decision["kind"]
        if kind == "reject":
            return replace(reject("input." + result.decision["reason"]), ack=result.ack)
        if kind == "unsupported":
            return Result(state, result.decision, ack=result.ack)
        fields = {key: value for key, value in result.decision.items() if key != "kind"}
        after = replace(state, core=result.state)
        if window_eligible(state, packet.segment):
            after = replace(
                after,
                send_window=packet.segment.window,
                send_wl1=packet.segment.sequence,
                send_wl2=packet.segment.acknowledgment,
            )
        return replace(accepted("receive", after, **fields), ack=result.ack)
    raise ValueError("Event kind is outside the selected profile.")


def canonical_event(event):
    kind = event["kind"]
    if kind == "write":
        return {"kind": kind, "payloadHex": wire.hex_bytes(event["payloadHex"]).hex()}
    if kind == "receive":
        return {"kind": kind, "rawIPv4Hex": wire.hex_bytes(event["rawIPv4Hex"]).hex()}
    if kind == "send":
        return {"kind": kind, "count": event["count"], "policyPermitted": event["policyPermitted"]}
    if kind == "read":
        return {"kind": kind, "count": event["count"]}
    if kind == "emitAck":
        return {"kind": kind, "policyPermitted": event["policyPermitted"]}
    raise ValueError("Event kind is outside the selected profile.")


def replay(seed, events):
    state = State.from_dict(seed)
    if not state.valid:
        raise ValueError("Seed state is invalid.")
    events = [canonical_event(event) for event in events]
    initial = state
    steps = []
    supported = True
    for index, event in enumerate(events):
        before = state
        result = evaluate(state, event)
        steps.append(
            {
                "index": index,
                "event": event,
                "before": before.to_dict(),
                "decodedInput": wire.decode_packet(event["rawIPv4Hex"]).to_dict()
                if event["kind"] == "receive"
                else None,
                **result.to_dict(),
            }
        )
        state = result.state
        if result.decision["kind"] == "unsupported":
            supported = False
            break
    return {
        "scope": "tcp-application-projection",
        "supported": supported,
        "inputEvents": len(events),
        "evaluatedEvents": len(steps),
        "seed": initial.to_dict(),
        "steps": steps,
        "final": state.to_dict(),
        "remainingEvents": events[len(steps) :],
        "finalStateValid": state.valid,
    }


def load_fixtures(path=FIXTURES):
    return json.loads(Path(path).read_text())


def check_fixtures(data):
    assert data["schema"] == 1, "Fixture schema is not supported."
    counts = {"events": 0, "window": 0, "traces": 0}
    for case in data["cases"]:
        state = State.from_dict(case["seed"])
        result = evaluate(state, case["event"])
        assert result.to_dict() == case["expected"], case["name"]
        assert case["coreOnly"] == (not state.valid), case["name"]
        if state.valid:
            assert result.state.valid, case["name"]
        counts["events"] += 1
    for case in data["windowCases"]:
        state = State.from_dict(case["seed"])
        packet = wire.decode_packet(case["rawIPv4Hex"])
        assert window_eligible(state, packet.segment) == case["eligible"], case["name"]
        counts["window"] += 1
    for trace in data["traces"]:
        observed = replay(trace["input"]["seed"], trace["input"]["events"])
        assert observed == trace["expected"], trace["name"]
        counts["traces"] += 1
    return counts


def main():
    print(
        json.dumps(
            {"scope": "static application projection only", **check_fixtures(load_fixtures())}
        )
    )


if __name__ == "__main__":
    main()
