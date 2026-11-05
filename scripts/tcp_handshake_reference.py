"""Independent static oracle for the selected TCP handshake.

The oracle constructs byte strings. It does not execute Lean or send packets.
"""

import ipaddress
import json
import struct
from dataclasses import dataclass, replace
from pathlib import Path

import tcp_endpoint_reference as application
import tcp_receive_reference as wire

MODULUS = 1 << 32
DEFAULT_MSS = 536
FIXTURES = Path(__file__).resolve().parent.parent / "examples/tcp-handshake/fixtures.json"


@dataclass(frozen=True)
class Socket:
    address: str
    port: int

    @classmethod
    def from_dict(cls, value):
        return cls(value["address"], value["port"])

    def to_dict(self):
        return {"address": self.address, "port": self.port}


@dataclass(frozen=True)
class ReceiveMSS:
    ip_receive_limit: int
    value: int

    @property
    def valid(self):
        return (
            0 < self.value < 65536
            and 576 <= self.ip_receive_limit <= 65535
            and 40 + self.value <= self.ip_receive_limit
        )

    def to_dict(self):
        return {"ipReceiveLimit": self.ip_receive_limit, "value": self.value}


@dataclass(frozen=True)
class Local:
    socket: Socket
    iss: int
    capacity: int
    pending_limit: int
    ip_send_limit: int
    receive_mss: ReceiveMSS | None = None

    @property
    def valid(self):
        return (
            0 <= self.iss < MODULUS
            and 0 <= self.capacity <= 65535
            and 0 <= self.pending_limit <= 65535
            and 40 < self.ip_send_limit <= 65535
            and (self.receive_mss is None or self.receive_mss.valid and 44 <= self.ip_send_limit)
        )

    @property
    def effective_mss(self):
        return min(DEFAULT_MSS, self.ip_send_limit - 40)

    def send_mss(self, peer_offer):
        return min(DEFAULT_MSS if peer_offer is None else peer_offer, self.ip_send_limit - 40)

    @classmethod
    def from_dict(cls, value):
        offer = value.get("receiveMSS")
        if "receiveMSS" in value and (
            not isinstance(offer, dict)
            or set(offer) != {"ipReceiveLimit", "value"}
            or any(type(offer[field]) is not int for field in ("ipReceiveLimit", "value"))
        ):
            raise ValueError("The local MSS advertisement is invalid.")
        return cls(
            Socket.from_dict(value["socket"]),
            value["iss"],
            value["capacity"],
            value["pendingLimit"],
            value["ipSendLimit"],
            None if offer is None else ReceiveMSS(offer["ipReceiveLimit"], offer["value"]),
        )

    def to_dict(self):
        result = {
            "socket": self.socket.to_dict(),
            "iss": self.iss,
            "capacity": self.capacity,
            "pendingLimit": self.pending_limit,
            "ipSendLimit": self.ip_send_limit,
        }
        if self.receive_mss is not None:
            result["receiveMSS"] = self.receive_mss.to_dict()
        return result


def header(source, destination):
    return wire.Header(source.address, destination.address, 6, source.port, destination.port)


def control_output(local, remote, sequence, acknowledgment, flags, ttl=64):
    outbound = header(local.socket, remote)
    options = (
        struct.pack("!BBH", 2, 4, local.receive_mss.value)
        if flags & 2 and local.receive_mss is not None
        else b""
    )
    blank = (
        wire.TCP_HEADER.pack(
            outbound.source_port,
            outbound.destination_port,
            sequence,
            acknowledgment,
            (5 + len(options) // 4) << 4,
            flags,
            local.capacity,
            0,
            0,
        )
        + options
    )
    tcp_crc = wire.checksum(wire.pseudoheader(outbound, len(blank)) + blank)
    tcp = blank[:16] + struct.pack("!H", tcp_crc) + blank[18:]
    ip = wire.IP_HEADER.pack(
        0x45,
        0,
        len(tcp) + 20,
        0,
        0x4000,
        ttl,
        6,
        0,
        int(ipaddress.IPv4Address(outbound.source)),
        int(ipaddress.IPv4Address(outbound.destination)),
    )
    raw = ip[:10] + struct.pack("!H", wire.checksum(ip)) + ip[12:] + tcp
    packet = wire.decode_packet(raw)
    return {"rawIPv4Hex": raw.hex(), "decoded": packet.to_dict()}


def rewrite_output(output, target, ttl):
    packet = wire.decode_packet(output["rawIPv4Hex"])
    segment = packet.segment
    blank = (
        wire.TCP_HEADER.pack(
            target.source_port,
            target.destination_port,
            segment.sequence,
            segment.acknowledgment,
            (5 + len(segment.options) // 4) << 4 | segment.reserved,
            segment.flags,
            segment.window,
            0,
            segment.urgent_pointer,
        )
        + segment.options
        + segment.payload
    )
    tcp_crc = wire.checksum(wire.pseudoheader(target, len(blank)) + blank)
    tcp = blank[:16] + struct.pack("!H", tcp_crc) + blank[18:]
    ip = wire.IP_HEADER.pack(
        0x45,
        packet.tos,
        len(tcp) + 20,
        packet.identification,
        0x4000 if packet.dont_fragment else 0,
        ttl,
        6,
        0,
        int(ipaddress.IPv4Address(target.source)),
        int(ipaddress.IPv4Address(target.destination)),
    )
    raw = ip[:10] + struct.pack("!H", wire.checksum(ip)) + ip[12:] + tcp
    return {"rawIPv4Hex": raw.hex(), "decoded": wire.decode_packet(raw).to_dict()}


def endpoint_seed(local, remote, receive_next, window_packet, peer_offer=None):
    segment = window_packet.segment
    next_send = (local.iss + 1) % MODULUS
    return application.State(
        wire.State(
            header(remote, local.socket),
            receive_next,
            local.capacity,
            b"",
            next_send,
            next_send,
            b"",
        ),
        b"",
        local.pending_limit,
        segment.window,
        segment.sequence,
        segment.acknowledgment,
        local.send_mss(peer_offer),
        local.ip_send_limit,
    )


def startup_mss(options):
    values = wire.option_framing(options)
    if len(values) > 1 or values and values[0] == 0:
        raise ValueError("The selected MSS value is zero or duplicated.")
    position = 0
    while position < len(options):
        kind = options[position]
        if kind == 0:
            break
        if kind == 1:
            position += 1
        elif kind == 2:
            position += 4
        else:
            raise ValueError("The startup options exceed the selected MSS scope.")
    return values[0] if values else None


def profile_failure(packet, expected_flags):
    try:
        if expected_flags & 2:
            startup_mss(packet.segment.options)
        elif packet.segment.options:
            raise ValueError("The final ACK options exceed the selected scope.")
    except ValueError:
        return {"kind": "unsupported", "reason": "options"}
    if packet.segment.payload:
        return {"kind": "unsupported", "reason": "data"}
    if packet.segment.flags != expected_flags:
        return {"kind": "unsupported", "reason": "flags"}
    return None


@dataclass(frozen=True)
class State:
    active_phase: str = "CLOSED"
    passive_phase: str = "LISTEN"
    remote: Socket | None = None
    syn: dict | None = None
    syn_index: int | None = None
    passive_syn: wire.Packet | None = None
    syn_ack: dict | None = None
    syn_ack_index: int | None = None
    final_ack: dict | None = None
    final_ack_index: int | None = None
    active_seed: application.State | None = None
    passive_seed: application.State | None = None
    active_established_at: int | None = None
    passive_established_at: int | None = None

    def to_dict(self):
        return {
            "activePhase": self.active_phase,
            "passivePhase": self.passive_phase,
            "activeSeed": self.active_seed.to_dict() if self.active_seed is not None else None,
            "passiveSeed": self.passive_seed.to_dict() if self.passive_seed is not None else None,
            "activeEstablishedAt": self.active_established_at,
            "passiveEstablishedAt": self.passive_established_at,
        }


@dataclass(frozen=True)
class Result:
    state: State
    decision: dict
    output: dict | None = None
    decoded_input: dict | None = None
    source: dict | None = None

    def to_dict(self):
        return {
            "state": self.state.to_dict(),
            "decision": self.decision,
            "output": self.output,
            "decodedInput": self.decoded_input,
            "delivery": self.source,
        }


def source_path(output, output_index, event, packet):
    if output is None:
        raise ValueError("A successful receipt requires an earlier peer output.")
    raw = event["rawIPv4Hex"]
    if event["path"] == "direct":
        expected = output
    elif event["path"] == "rewrite":
        expected = rewrite_output(output, packet.header, packet.ttl)
    else:
        raise ValueError("The selected byte path is unknown.")
    if raw != expected["rawIPv4Hex"]:
        raise ValueError("The receipt does not match the earlier output and selected byte path.")
    return {"sourceIndex": output_index, "path": event["path"]}


def evaluate(active, passive, state, event, index):
    kind = event["kind"]

    def failure(reason, unsupported=False, packet=None):
        return Result(
            state,
            {"kind": "unsupported" if unsupported else "reject", "reason": reason},
            decoded_input=packet.to_dict() if packet is not None else None,
        )

    def accepted(after, output=None, packet=None, source=None):
        return Result(
            after,
            {"kind": "accepted", "operation": kind},
            output,
            packet.to_dict() if packet is not None else None,
            source,
        )

    expected_kind = {
        ("CLOSED", "LISTEN"): "activeOpen",
        ("SYN-SENT", "LISTEN"): "listenSyn",
        ("SYN-SENT", "SYN-RECEIVED"): "synSentSynAck",
        ("ESTABLISHED", "SYN-RECEIVED"): "synReceivedAck",
    }.get((state.active_phase, state.passive_phase))
    if kind != expected_kind:
        return failure("phase", unsupported=True)
    if kind == "activeOpen":
        if not active.valid:
            return failure("invalidConfig")
        if not event["policyPermitted"]:
            return failure("policy")
        remote = Socket.from_dict(event["remote"])
        output = control_output(active, remote, active.iss, 0, 2)
        after = replace(state, active_phase="SYN-SENT", remote=remote, syn=output, syn_index=index)
        return accepted(after, output)
    packet = wire.decode_packet(wire.hex_bytes(event["rawIPv4Hex"]))
    segment = packet.segment
    if kind == "listenSyn":
        if not passive.valid:
            return failure("invalidConfig", packet=packet)
        if (
            packet.header.destination != passive.socket.address
            or packet.header.destination_port != passive.socket.port
        ):
            return failure("tuple", packet=packet)
        excluded = profile_failure(packet, 2)
        if excluded:
            return failure(excluded["reason"], unsupported=True, packet=packet)
        if not event["policyPermitted"]:
            return failure("policy", packet=packet)
        source = source_path(state.syn, state.syn_index, event, packet)
        remote = Socket(packet.header.source, packet.header.source_port)
        output = control_output(passive, remote, passive.iss, (segment.sequence + 1) % MODULUS, 18)
        after = replace(
            state,
            passive_phase="SYN-RECEIVED",
            passive_syn=packet,
            syn_ack=output,
            syn_ack_index=index,
        )
        return accepted(after, output, packet, source)
    if kind == "synSentSynAck":
        if packet.header != header(state.remote, active.socket):
            return failure("tuple", packet=packet)
        excluded = profile_failure(packet, 18)
        if excluded:
            return failure(excluded["reason"], unsupported=True, packet=packet)
        if segment.acknowledgment != (active.iss + 1) % MODULUS:
            return failure("acknowledgment", unsupported=True, packet=packet)
        if not event["policyPermitted"]:
            return failure("policy", packet=packet)
        source = source_path(state.syn_ack, state.syn_ack_index, event, packet)
        seed = endpoint_seed(
            active,
            state.remote,
            (segment.sequence + 1) % MODULUS,
            packet,
            startup_mss(segment.options),
        )
        output = control_output(
            active, state.remote, seed.core.send_next, seed.core.receive_next, 16
        )
        after = replace(
            state,
            active_phase="ESTABLISHED",
            active_seed=seed,
            final_ack=output,
            final_ack_index=index,
            active_established_at=index,
        )
        return accepted(after, output, packet, source)
    if packet.header != state.passive_syn.header:
        return failure("tuple", packet=packet)
    excluded = profile_failure(packet, 16)
    if excluded:
        return failure(excluded["reason"], unsupported=True, packet=packet)
    if segment.sequence != (state.passive_syn.segment.sequence + 1) % MODULUS:
        return failure("sequence", unsupported=True, packet=packet)
    if segment.acknowledgment != (passive.iss + 1) % MODULUS:
        return failure("acknowledgment", unsupported=True, packet=packet)
    source = source_path(state.final_ack, state.final_ack_index, event, packet)
    remote = Socket(packet.header.source, packet.header.source_port)
    seed = endpoint_seed(
        passive,
        remote,
        (state.passive_syn.segment.sequence + 1) % MODULUS,
        packet,
        startup_mss(state.passive_syn.segment.options),
    )
    after = replace(
        state,
        passive_phase="ESTABLISHED",
        passive_seed=seed,
        passive_established_at=index,
    )
    return accepted(after, packet=packet, source=source)


def canonical_event(event):
    kind = event["kind"]
    if kind == "activeOpen":
        return {
            "kind": kind,
            "remote": Socket.from_dict(event["remote"]).to_dict(),
            "policyPermitted": event["policyPermitted"],
        }
    if kind not in ("listenSyn", "synSentSynAck", "synReceivedAck"):
        raise ValueError("The startup event kind is unknown.")
    if event["path"] not in ("direct", "rewrite"):
        raise ValueError("The selected byte path is unknown.")
    result = {
        "kind": kind,
        "rawIPv4Hex": wire.hex_bytes(event["rawIPv4Hex"]).hex(),
        "path": event["path"],
    }
    if kind != "synReceivedAck":
        result["policyPermitted"] = event["policyPermitted"]
    return result


def replay(value):
    active = Local.from_dict(value["active"])
    passive = Local.from_dict(value["passive"])
    if not active.valid or not passive.valid:
        raise ValueError("Local TCP configuration is invalid.")
    events = [canonical_event(event) for event in value["events"]]
    initial = state = State()
    steps = []
    supported = True
    for index, event in enumerate(events):
        before = state
        result = evaluate(active, passive, state, event, index)
        steps.append(
            {"index": index, "event": event, "before": before.to_dict(), **result.to_dict()}
        )
        state = result.state
        if result.decision["kind"] == "unsupported":
            supported = False
            break
    return {
        "scope": "tcp-startup-projection",
        "supported": supported,
        "exchangeComplete": state.active_seed is not None and state.passive_seed is not None,
        "inputEvents": len(events),
        "evaluatedEvents": len(steps),
        "active": active.to_dict(),
        "passive": passive.to_dict(),
        "initial": initial.to_dict(),
        "steps": steps,
        "final": state.to_dict(),
        "remainingEvents": events[len(steps) :],
    }


def load_fixtures(path=FIXTURES):
    return json.loads(Path(path).read_text())


def check_fixtures(data):
    assert data["schema"] == 1, "Fixture schema is not supported."
    counts = {"traces": 0, "complete": 0, "unsupported": 0, "errors": 0}
    for case in data["traces"]:
        observed = replay(case["input"])
        assert observed == case["expected"], case["name"]
        counts["traces"] += 1
        counts["complete"] += observed["exchangeComplete"]
        counts["unsupported"] += not observed["supported"]
    for case in data["errorCases"]:
        try:
            replay(case["input"])
        except ValueError:
            counts["errors"] += 1
        else:
            raise AssertionError(case["name"])
    return counts


def main():
    print(json.dumps({"scope": "static ordinary startup only", **check_fixtures(load_fixtures())}))


if __name__ == "__main__":
    main()
