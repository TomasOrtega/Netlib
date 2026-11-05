"""Independent RFC 9293 IPv4 TCP framing oracle for static model fixtures.

This module does not use sockets, subprocesses, captures, or native transport operations.
https://www.rfc-editor.org/rfc/rfc9293.html#section-3.1
"""

import argparse
import ipaddress
import json
import struct
from dataclasses import dataclass, replace
from pathlib import Path

FIXTURES = Path(__file__).resolve().parent.parent / "examples/tcp/fixtures.json"
FLAG_NAMES = ("CWR", "ECE", "URG", "ACK", "PSH", "RST", "SYN", "FIN")
FIXED_HEADER = struct.Struct("!HHIIBBHHH")
SEQUENCE_MODULUS = 1 << 32
HALF_SPACE = 1 << 31


class TCPError(ValueError):
    def __init__(self, code, message):
        self.code = code
        super().__init__(f"{code}: {message}")


def folded_sum(raw):
    padded = bytes(raw) + bytes(len(raw) % 2)
    total = sum(
        int.from_bytes(padded[index : index + 2], "big") for index in range(0, len(padded), 2)
    )
    while total > 65535:
        total = (total & 65535) + (total >> 16)
    return total


def checksum(raw):
    return folded_sum(raw) ^ 65535


def pseudoheader(source, destination, size):
    if not 20 <= size <= 65535:
        raise TCPError("segmentLength", "TCP length must fit the IPv4 pseudoheader length field.")
    return struct.pack(
        "!4s4sBBH",
        ipaddress.IPv4Address(source).packed,
        ipaddress.IPv4Address(destination).packed,
        0,
        6,
        size,
    )


@dataclass(frozen=True)
class Option:
    kind: int
    data: bytes = b""


def parse_options(raw):
    raw = bytes(raw)
    parsed = []
    position = 0
    while position < len(raw):
        kind = raw[position]
        if kind == 0:
            if any(raw[position + 1 :]):
                raise TCPError("eolPadding", "Bytes after EOL must be zero padding.")
            parsed.append(Option(0))
            break
        if kind == 1:
            parsed.append(Option(1))
            position += 1
            continue
        if position + 1 == len(raw):
            raise TCPError("optionLengthMissing", "A non-singleton option needs a length byte.")
        size = raw[position + 1]
        if size < 2:
            raise TCPError("optionLength", "Option length includes kind and length bytes.")
        if position + size > len(raw):
            raise TCPError("optionTruncated", "An option extends beyond the TCP header.")
        if kind == 2 and size != 4:
            raise TCPError("mssLength", "The MSS option length must be four.")
        parsed.append(Option(kind, raw[position + 2 : position + size]))
        position += size
    return tuple(parsed)


@dataclass(frozen=True)
class Segment:
    source_port: int = 49152
    destination_port: int = 443
    sequence: int = 0x01020304
    acknowledgment: int = 0
    reserved: int = 0
    flags: int = 2
    window: int = 4096
    checksum: int = 0
    urgent_pointer: int = 0
    options: bytes = b""
    payload: bytes = b""

    @property
    def header_length(self):
        return 20 + len(self.options)

    @property
    def parsed_options(self):
        return parse_options(self.options)

    @property
    def flag_names(self):
        return tuple(name for bit, name in enumerate(FLAG_NAMES) if self.flags & (128 >> bit))


def encode_segment(segment):
    if len(segment.options) > 40 or len(segment.options) % 4:
        raise TCPError("optionsSize", "The options region must use zero to forty aligned bytes.")
    widths = {
        "source_port": 16,
        "destination_port": 16,
        "sequence": 32,
        "acknowledgment": 32,
        "reserved": 4,
        "flags": 8,
        "window": 16,
        "checksum": 16,
        "urgent_pointer": 16,
    }
    for field, width in widths.items():
        if not 0 <= getattr(segment, field) < 1 << width:
            raise TCPError("fieldRange", f"{field} must fit its unsigned wire field.")
    size = segment.header_length + len(segment.payload)
    if size > 65535:
        raise TCPError("segmentLength", "TCP length exceeds the IPv4 pseudoheader length field.")
    fixed = FIXED_HEADER.pack(
        segment.source_port,
        segment.destination_port,
        segment.sequence,
        segment.acknowledgment,
        segment.header_length // 4 << 4 | segment.reserved,
        segment.flags,
        segment.window,
        segment.checksum,
        segment.urgent_pointer,
    )
    return fixed + segment.options + segment.payload


def rechecksum(source, destination, segment):
    blank = replace(segment, checksum=0)
    raw = encode_segment(blank)
    return replace(blank, checksum=checksum(pseudoheader(source, destination, len(raw)) + raw))


def computed_segment(source, destination, **fields):
    return rechecksum(source, destination, replace(Segment(**fields), reserved=0))


def decode_segment(source, destination, raw):
    raw = bytes.fromhex(raw) if isinstance(raw, str) else bytes(raw)
    if len(raw) < FIXED_HEADER.size:
        raise TCPError("truncatedFixedHeader", "A TCP fixed header requires twenty bytes.")
    if len(raw) > 65535:
        raise TCPError("segmentLength", "TCP length exceeds the IPv4 pseudoheader length field.")
    source_port, destination_port, sequence, ack, offset, flags, window, crc, urgent = (
        FIXED_HEADER.unpack_from(raw)
    )
    header_length = (offset >> 4) * 4
    if header_length < FIXED_HEADER.size:
        raise TCPError("dataOffset", "The TCP Data Offset must be at least five.")
    if header_length > len(raw):
        raise TCPError("truncatedHeader", "Data Offset exceeds the TCP segment length.")
    options = raw[FIXED_HEADER.size : header_length]
    parse_options(options)
    if folded_sum(pseudoheader(source, destination, len(raw)) + raw) != 65535:
        raise TCPError("checksum", "The mandatory TCP pseudoheader checksum is invalid.")
    return Segment(
        source_port,
        destination_port,
        sequence,
        ack,
        offset & 15,
        flags,
        window,
        crc,
        urgent,
        options,
        raw[header_length:],
    )


def semantic_issues(segment):
    issues = []
    if not segment.flags & 2 and any(option.kind == 2 for option in segment.parsed_options):
        issues.append("mssRequiresSyn")
    return tuple(issues)


def generation_issues(segment):
    return ("reservedBits",) if segment.reserved else ()


def seq_distance(first, second):
    if not 0 <= first < SEQUENCE_MODULUS or not 0 <= second < SEQUENCE_MODULUS:
        raise ValueError("Sequence numbers must fit unsigned 32-bit fields.")
    return (second - first) % SEQUENCE_MODULUS


def seq_before(first, second):
    return 0 < seq_distance(first, second) < HALF_SPACE


def seq_within(start, length, value):
    if not 0 <= length < HALF_SPACE:
        raise ValueError("An interval length must be shorter than a sequence half-space.")
    return seq_distance(start, value) < length


def fields(segment):
    return {
        "sourcePort": segment.source_port,
        "destinationPort": segment.destination_port,
        "sequence": segment.sequence,
        "acknowledgment": segment.acknowledgment,
        "reserved": segment.reserved,
        "flags": segment.flags,
        "flagNames": list(segment.flag_names),
        "window": segment.window,
        "checksum": segment.checksum,
        "urgentPointer": segment.urgent_pointer,
        "headerLength": segment.header_length,
        "optionsHex": segment.options.hex(),
        "payloadHex": segment.payload.hex(),
    }


def load_fixtures(path=FIXTURES):
    return json.loads(Path(path).read_text())


def check_fixtures(data):
    assert data["schema"] == 1, "Unsupported TCP fixture schema."
    counts = {"accepted": 0, "rejected": 0, "semanticRejected": 0}
    names = set()
    for case in data["cases"]:
        name = case["name"]
        assert name not in names, f"Duplicate TCP fixture: {name}"
        names.add(name)
        raw = bytes.fromhex(case["segmentHex"])
        try:
            segment = decode_segment(data["source"], data["destination"], raw)
        except TCPError as error:
            assert not case["structural"], f"{name}: unexpected rejection: {error}"
            assert case["semantic"] is None, f"{name}: rejected bytes have no semantic verdict."
            assert case["error"] == error.code, (
                f"{name}: expected {case['error']}, got {error.code}."
            )
            counts["rejected"] += 1
            continue
        assert case["structural"], f"{name}: unexpected structural acceptance."
        assert fields(segment) == case["expected"], f"{name}: expected decoded fields differ."
        assert encode_segment(segment) == raw, f"{name}: accepted bytes did not round trip."
        issues = semantic_issues(segment)
        assert case["semantic"] == (not issues), f"{name}: semantic profile differs."
        assert case["semanticIssues"] == list(issues), f"{name}: semantic issue details differ."
        assert case["generationIssues"] == list(generation_issues(segment)), (
            f"{name}: generation issue details differ."
        )
        counts["accepted"] += 1
        counts["semanticRejected"] += bool(issues)
    for case in data["sequenceCases"]:
        first, second = case["first"], case["second"]
        assert seq_distance(first, second) == case["distance"], case["name"]
        assert seq_before(first, second) == case["before"], case["name"]
        assert seq_before(second, first) == case["reverseBefore"], case["name"]
    for case in data["intervalCases"]:
        assert seq_within(case["start"], case["length"], case["value"]) == case["contains"], case[
            "name"
        ]
    for case in data["arcCases"]:
        first, second, third = case["points"]
        inside = all(seq_within(case["start"], case["length"], point) for point in case["points"])
        assert inside == case["inside"], case["name"]
        premise = seq_before(first, second) and seq_before(second, third)
        assert premise == case["orderedPremise"], case["name"]
        assert seq_before(first, third) == case["orderedConclusion"], case["name"]
        assert not (inside and premise) or seq_before(first, third), case["name"]
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixtures", nargs="?", type=Path, default=FIXTURES)
    arguments = parser.parse_args()
    counts = check_fixtures(load_fixtures(arguments.fixtures))
    print(json.dumps({"scope": "static model fixtures only", **counts}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
