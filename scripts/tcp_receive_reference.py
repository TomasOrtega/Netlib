"""Independent static oracle for the selected TCP receive projection.

The oracle does not execute Lean, use sockets, or send packets.
"""

import ipaddress
import json
import struct
from dataclasses import dataclass, replace
from pathlib import Path

MODULUS = 1 << 32
HALF_SPACE = 1 << 31
MAX_SEND_WINDOW = 65535
FIXTURES = Path(__file__).resolve().parent.parent / "examples/tcp-receive/fixtures.json"
TCP_HEADER = struct.Struct("!HHIIBBHHH")
IP_HEADER = struct.Struct("!BBHHHBBHII")
FLAG_NAMES = ("CWR", "ECE", "URG", "ACK", "PSH", "RST", "SYN", "FIN")


def sum_words(raw):
    padded = bytes(raw) + bytes(len(raw) % 2)
    total = sum(struct.unpack(f"!{len(padded) // 2}H", padded))
    while total > 65535:
        total = (total & 65535) + (total >> 16)
    return total


def checksum(raw):
    return 65535 - sum_words(raw)


@dataclass(frozen=True)
class Header:
    source: str
    destination: str
    protocol: int
    source_port: int
    destination_port: int

    @classmethod
    def from_dict(cls, value):
        return cls(
            value["source"],
            value["destination"],
            value["protocol"],
            value["sourcePort"],
            value["destinationPort"],
        )

    def to_dict(self):
        return {
            "source": self.source,
            "destination": self.destination,
            "protocol": self.protocol,
            "sourcePort": self.source_port,
            "destinationPort": self.destination_port,
        }


@dataclass(frozen=True)
class Segment:
    sequence: int
    acknowledgment: int
    flags: int = 16
    window: int = 8192
    reserved: int = 0
    urgent_pointer: int = 0
    options: bytes = b""
    payload: bytes = b""
    checksum: int = 0

    @property
    def occupied_length(self):
        return len(self.payload) + bool(self.flags & 2) + bool(self.flags & 1)

    def to_dict(self):
        mss = option_framing(self.options)
        return {
            "sequence": self.sequence,
            "acknowledgment": self.acknowledgment,
            "flags": self.flags,
            "window": self.window,
            "reserved": self.reserved,
            "urgentPointer": self.urgent_pointer,
            "optionsHex": self.options.hex(),
            "payloadHex": self.payload.hex(),
            "checksum": self.checksum,
            "sequenceSpaceLength": self.occupied_length,
            "headerLength": 20 + len(self.options),
            "dataOffset": 5 + len(self.options) // 4,
            "flagNames": [
                name for index, name in enumerate(FLAG_NAMES) if self.flags & (128 >> index)
            ],
            "mssValues": list(mss),
            "selectedOptionSemantics": not mss or bool(self.flags & 2),
        }


@dataclass(frozen=True)
class Packet:
    header: Header
    segment: Segment
    padding: bytes = b""
    ttl: int = 64
    tos: int = 40
    identification: int = 0x4321
    dont_fragment: bool = True
    ipv4_checksum: int = 0

    def to_dict(self):
        return {
            "header": self.header.to_dict(),
            "segment": {
                **self.segment.to_dict(),
                "sourcePort": self.header.source_port,
                "destinationPort": self.header.destination_port,
            },
            "ipv4PaddingHex": self.padding.hex(),
            "ttl": self.ttl,
            "tos": self.tos,
            "identification": self.identification,
            "dontFragment": self.dont_fragment,
            "ipv4Checksum": self.ipv4_checksum,
        }


@dataclass(frozen=True)
class State:
    inbound: Header
    receive_next: int
    capacity: int
    received: bytes
    send_una: int
    send_next: int
    sent: bytes

    @property
    def window(self):
        return max(0, self.capacity - len(self.received))

    @property
    def valid(self):
        return (
            self.inbound.protocol == 6
            and 0 <= len(self.received) <= self.capacity <= 65535
            and len(self.sent) <= MAX_SEND_WINDOW
            and (self.send_una + len(self.sent)) % MODULUS == self.send_next
            and len(self.sent) + MAX_SEND_WINDOW < HALF_SPACE
        )

    @classmethod
    def from_dict(cls, value):
        return cls(
            Header.from_dict(value["inbound"]),
            value["receiveNext"],
            value["capacity"],
            bytes.fromhex(value["receivedHex"]),
            value["sendUna"],
            value["sendNext"],
            bytes.fromhex(value["sentHex"]),
        )

    def to_dict(self):
        return {
            "inbound": self.inbound.to_dict(),
            "receiveNext": self.receive_next,
            "capacity": self.capacity,
            "receivedHex": self.received.hex(),
            "sendUna": self.send_una,
            "sendNext": self.send_next,
            "sentHex": self.sent.hex(),
            "window": self.window,
        }

    def seed_dict(self):
        return {key: value for key, value in self.to_dict().items() if key != "window"}


@dataclass(frozen=True)
class Result:
    state: State
    decision: dict
    ack: dict | None = None

    def to_dict(self):
        return {
            "state": self.state.to_dict(),
            "decision": self.decision,
            "ack": self.ack,
        }


def option_framing(raw):
    position = 0
    mss = []
    while position < len(raw):
        kind = raw[position]
        if kind == 0:
            if any(raw[position + 1 :]):
                raise ValueError("EOL padding is not zero.")
            return tuple(mss)
        if kind == 1:
            position += 1
            continue
        if position + 1 >= len(raw):
            raise ValueError("Option length byte is absent.")
        size = raw[position + 1]
        if size < 2 or position + size > len(raw):
            raise ValueError("Option length is invalid.")
        if kind == 2 and size != 4:
            raise ValueError("MSS length is not four.")
        if kind == 2:
            mss.append(int.from_bytes(raw[position + 2 : position + size], "big"))
        position += size
    return tuple(mss)


def pseudoheader(header, length):
    return struct.pack(
        "!IIBBH",
        int(ipaddress.IPv4Address(header.source)),
        int(ipaddress.IPv4Address(header.destination)),
        0,
        6,
        length,
    )


def fixture_packet(header, segment, padding=b"", checksum_override=None):
    if len(segment.options) % 4 or len(segment.options) > 40:
        raise ValueError("Option region length is invalid.")
    control = (5 + len(segment.options) // 4) << 4 | segment.reserved
    blank = (
        TCP_HEADER.pack(
            header.source_port,
            header.destination_port,
            segment.sequence,
            segment.acknowledgment,
            control,
            segment.flags,
            segment.window,
            0,
            segment.urgent_pointer,
        )
        + segment.options
        + segment.payload
    )
    crc = checksum(pseudoheader(header, len(blank)) + blank)
    if checksum_override is not None:
        crc = checksum_override
    tcp = blank[:16] + crc.to_bytes(2, "big") + blank[18:]
    ip = IP_HEADER.pack(
        69,
        40,
        20 + len(tcp),
        0x4321,
        0x4000,
        64,
        header.protocol,
        0,
        int(ipaddress.IPv4Address(header.source)),
        int(ipaddress.IPv4Address(header.destination)),
    )
    return ip[:10] + checksum(ip).to_bytes(2, "big") + ip[12:] + tcp + padding


def decode_packet(raw):
    raw = bytes.fromhex(raw) if isinstance(raw, str) else bytes(raw)
    if len(raw) < 20:
        raise ValueError("IPv4 header is truncated.")
    (
        version,
        tos,
        size,
        identification,
        bits,
        ttl,
        protocol,
        ipv4_crc,
        source,
        destination,
    ) = IP_HEADER.unpack_from(raw)
    if version != 69 or size < 20 or size > len(raw) or bits not in (0, 0x4000):
        raise ValueError("IPv4 framing is outside the selected profile.")
    if sum_words(raw[:20]) != 65535:
        raise ValueError("IPv4 checksum is invalid.")
    if protocol != 6:
        raise ValueError("IPv4 protocol is not TCP.")
    tcp = raw[20:size]
    if len(tcp) < 20:
        raise ValueError("TCP header is truncated.")
    (
        source_port,
        destination_port,
        sequence,
        acknowledgment,
        control,
        flags,
        window,
        crc,
        urgent,
    ) = TCP_HEADER.unpack_from(tcp)
    offset = (control >> 4) * 4
    if offset < 20 or offset > len(tcp):
        raise ValueError("TCP Data Offset is invalid.")
    options = tcp[20:offset]
    option_framing(options)
    header = Header(
        str(ipaddress.IPv4Address(source)),
        str(ipaddress.IPv4Address(destination)),
        protocol,
        source_port,
        destination_port,
    )
    if sum_words(pseudoheader(header, len(tcp)) + tcp) != 65535:
        raise ValueError("TCP checksum is invalid.")
    return Packet(
        header,
        Segment(
            sequence,
            acknowledgment,
            flags,
            window,
            control & 15,
            urgent,
            options,
            tcp[offset:],
            crc,
        ),
        raw[size:],
        ttl,
        tos,
        identification,
        bool(bits & 0x4000),
        ipv4_crc,
    )


def inside(left, width, position):
    if width == 0:
        return False
    if width >= MODULUS:
        return True
    end = left + width
    if end <= MODULUS:
        return left <= position < end
    return left <= position or position < end - MODULUS


def sequence_accepts(next_sequence, window, sequence, length):
    if length == 0:
        return sequence == next_sequence if window == 0 else inside(next_sequence, window, sequence)
    if window == 0:
        return False
    last = (sequence + length - 1) % MODULUS
    return inside(next_sequence, window, sequence) or inside(next_sequence, window, last)


def acknowledged_count(state, acknowledgment):
    offset = (acknowledgment - state.send_una + HALF_SPACE) % MODULUS - HALF_SPACE
    if -MAX_SEND_WINDOW <= offset <= len(state.sent):
        return max(0, offset)
    return None


def request(state, kind):
    return {
        "kind": kind,
        "sequence": state.send_next,
        "acknowledgment": state.receive_next,
        "window": state.window,
    }


def control(segment):
    for bit, reason in (
        (4, "reset"),
        (2, "synchronize"),
        (1, "finish"),
        (32, "urgent"),
        (192, "congestion"),
    ):
        if segment.flags & bit:
            return reason
    return "options" if segment.options else None


def receive(state, packet):
    def block(kind, reason, ack_kind=None):
        return Result(
            state,
            {"kind": kind, "reason": reason},
            request(state, ack_kind) if ack_kind else None,
        )

    segment = packet.segment
    if not state.valid:
        return block("reject", "invalidSeed")
    if packet.header != state.inbound:
        return block("reject", "tuple")
    excluded = control(segment)
    if excluded:
        return block("unsupported", excluded)
    if not sequence_accepts(
        state.receive_next, state.window, segment.sequence, segment.occupied_length
    ):
        return block("reject", "sequence", "sequence")
    if not segment.flags & 16:
        return block("reject", "missingAck")
    count = acknowledged_count(state, segment.acknowledgment)
    if count is None:
        return block("reject", "acknowledgment", "challenge")
    if segment.payload and segment.sequence != state.receive_next:
        forward_gap = (state.receive_next - segment.sequence) % MODULUS
        return block("unsupported", "trimming" if 0 < forward_gap < HALF_SPACE else "outOfOrder")
    if len(segment.payload) > state.window:
        return block("unsupported", "trimming")
    after = replace(
        state,
        receive_next=(state.receive_next + len(segment.payload)) % MODULUS,
        received=state.received + segment.payload,
        send_una=(state.send_una + count) % MODULUS,
        sent=state.sent[count:],
    )
    return Result(
        after,
        {"kind": "accepted", "acknowledged": count, "received": len(segment.payload)},
        request(after, "data") if segment.payload else None,
    )


def hex_bytes(text):
    if (
        not isinstance(text, str)
        or len(text) % 2
        or any(char not in "0123456789abcdefABCDEF" for char in text)
    ):
        raise ValueError("Hex text is invalid.")
    return bytes.fromhex(text)


def replay(seed, packets_hex):
    state = State.from_dict(seed)
    if not state.valid:
        raise ValueError("Seed state is invalid.")
    raw_packets = [hex_bytes(text) for text in packets_hex]
    initial = state
    steps = []
    supported = True
    for index, raw in enumerate(raw_packets):
        packet = decode_packet(raw)
        result = receive(state, packet)
        steps.append(
            {
                "index": index,
                "rawIPv4Hex": raw.hex(),
                "decoded": packet.to_dict(),
                "before": state.to_dict(),
                "decision": result.decision,
                "ack": result.ack,
                "state": result.state.to_dict(),
            }
        )
        state = result.state
        if result.decision["kind"] == "unsupported":
            supported = False
            break
    return {
        "scope": "tcp-established-receive-projection",
        "supported": supported,
        "inputPackets": len(raw_packets),
        "evaluatedPackets": len(steps),
        "seed": initial.to_dict(),
        "remainingPacketsHex": [raw.hex() for raw in raw_packets[len(steps) :]],
        "final": state.to_dict(),
        "finalStateValid": state.valid,
        "steps": steps,
    }


def load_fixtures(path=FIXTURES):
    return json.loads(Path(path).read_text())


def check_fixtures(data):
    assert data["schema"] == 1, "Fixture schema is not supported."
    counts = {"receive": 0, "window": 0, "ack": 0, "traces": 0}
    for case in data["cases"]:
        packet = decode_packet(case["rawIPv4Hex"])
        assert packet.to_dict() == case["decoded"], f"{case['name']}: decoded input differs."
        state = State.from_dict(case["seed"])
        assert state.seed_dict() == case["seed"], f"{case['name']}: seed fields differ."
        observed = receive(state, packet)
        assert observed.to_dict() == case["expected"], f"{case['name']}: result differs."
        if state.valid:
            assert observed.state.valid, f"{case['name']}: state bounds differ."
            reported = replay(case["seed"], [case["rawIPv4Hex"]])
            assert reported["final"] == case["expected"]["state"], case["name"]
        assert case["coreOnly"] == (not state.valid), case["name"]
        counts["receive"] += 1
    for case in data["windowCases"]:
        observed = sequence_accepts(case["next"], case["window"], case["sequence"], case["length"])
        assert observed == case["accepted"], f"{case['name']}: sequence result differs."
        counts["window"] += 1
    for case in data["ackCases"]:
        state = State.from_dict(case["seed"])
        assert acknowledged_count(state, case["acknowledgment"]) == case["count"], case["name"]
        counts["ack"] += 1
    for trace in data["traces"]:
        observed = replay(trace["input"]["seed"], trace["input"]["packetsHex"])
        assert observed == trace["expected"], f"{trace['name']}: replay differs."
        counts["traces"] += 1
    return counts


def main():
    print(
        json.dumps(
            {
                "scope": "static receive projection only",
                **check_fixtures(load_fixtures()),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
