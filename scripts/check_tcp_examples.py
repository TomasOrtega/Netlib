"""Compare the compiled TCP CLI with independent static standards-model fixtures.

The manual checker compares local codec and arithmetic results. It does not use a network.
"""

import ipaddress
import json
import struct
import tempfile
from pathlib import Path

import tcp_reference as tcp
from check_cli import invoke

ETHERNET = bytes.fromhex("000102030405060708090a0b0800")


def write(path, value):
    path.write_text(json.dumps(value))
    return path


def compare_segment(report, case):
    observed = report["segment"]
    for field, expected in case["expected"].items():
        assert observed[field] == expected, (case["name"], field, observed[field], expected)
    assert observed["selectedOptionSemantics"] == case["semantic"], case["name"]
    raw = bytes.fromhex(case["segmentHex"])
    assert observed["dataOffset"] == raw[12] >> 4, case["name"]
    assert observed["sequenceSpaceLength"] == len(bytes.fromhex(observed["payloadHex"])) + bool(
        raw[13] & 2
    ) + bool(raw[13] & 1), case["name"]
    options = tcp.parse_options(bytes.fromhex(observed["optionsHex"]))
    assert observed["mssValues"] == [
        int.from_bytes(option.data, "big") for option in options if option.kind == 2
    ], case["name"]


def segment_checks(path, fixtures):
    for case in fixtures["cases"]:
        value = {
            "schema": 1,
            "source": fixtures["source"],
            "destination": fixtures["destination"],
            "raw": case["segmentHex"],
        }
        output = invoke(
            "tcp-segment", write(path, value), "--json", code=0 if case["structural"] else 2
        )
        if case["structural"]:
            report = json.loads(output)
            assert report["scope"] == "ipv4-tcp-segment-framing"
            assert report["valid"] and report["checksumVerified"] and report["assumptions"]
            assert report["source"] == fixtures["source"]
            assert report["destination"] == fixtures["destination"]
            assert report["bytes"] == len(bytes.fromhex(case["segmentHex"]))
            compare_segment(report, case)
    return len(fixtures["cases"])


def sequence_report(path, first, second, length):
    value = {"schema": 1, "first": first, "second": second, "length": length}
    report = json.loads(invoke("tcp-sequence", write(path, value), "--json"))
    distance = (second - first) % (1 << 32)
    assert report["scope"] == "tcp-serial-arithmetic"
    assert report["first"] == first and report["second"] == second and report["length"] == length
    assert report["distance"] == distance
    assert report["before"] == (0 < distance < 1 << 31)
    assert report["reverseBefore"] == (0 < (first - second) % (1 << 32) < 1 << 31)
    assert report["equal"] == (first == second)
    assert report["contains"] == (distance < length)
    assert report["shortArc"] == (length < 1 << 31) and report["assumption"]
    return report


def sequence_checks(path, fixtures):
    count = 0
    for case in fixtures["sequenceCases"]:
        report = sequence_report(path, case["first"], case["second"], 0)
        for field in ("distance", "before", "reverseBefore"):
            assert report[field] == case[field], case["name"]
        count += 1
    for case in fixtures["intervalCases"]:
        report = sequence_report(path, case["start"], case["value"], case["length"])
        assert report["contains"] == case["contains"], case["name"]
        count += 1
    for case in fixtures["arcCases"]:
        first, second, third = case["points"]
        left = sequence_report(path, first, second, 0)
        right = sequence_report(path, second, third, 0)
        full = sequence_report(path, first, third, 0)
        assert (left["before"] and right["before"]) == case["orderedPremise"], case["name"]
        assert full["before"] == case["orderedConclusion"], case["name"]
        count += 3
    for length in (1 << 31, 1 << 32):
        report = sequence_report(path, 0xFFFFFFFF, 0x7FFFFFFF, length)
        assert not report["shortArc"]
        count += 1
    return count


def ipv4(segment, source, destination, protocol=6, flags=0x4000, ttl=64):
    header = struct.pack(
        "!BBHHHBBH4s4s",
        69,
        0x28,
        20 + len(segment),
        0x4321,
        flags,
        ttl,
        protocol,
        0,
        ipaddress.IPv4Address(source).packed,
        ipaddress.IPv4Address(destination).packed,
    )
    return header[:10] + tcp.checksum(header).to_bytes(2, "big") + header[12:] + segment


def wire_checks(path, fixtures):
    count = 0
    padding = bytes.fromhex("00ff00")
    source, destination = fixtures["source"], fixtures["destination"]
    accepted = [case for case in fixtures["cases"] if case["structural"]]
    for case in accepted:
        raw = bytes.fromhex(case["segmentHex"])
        packet = ipv4(raw, source, destination)
        frame = ETHERNET + packet + padding
        report = json.loads(
            invoke("tcp-wire", write(path, {"schema": 1, "raw": frame.hex()}), "--json")
        )
        assert report["scope"] == "untagged-ipv4-tcp-framing"
        assert report["valid"] and report["tcpChecksumVerified"] and report["assumptions"]
        assert report["bytes"] == len(frame)
        assert report["header"] == {
            "source": source,
            "destination": destination,
            "protocol": 6,
            "sourcePort": case["expected"]["sourcePort"],
            "destinationPort": case["expected"]["destinationPort"],
        }
        assert report["sourceMAC"] == "06:07:08:09:0a:0b"
        assert report["destinationMAC"] == "00:01:02:03:04:05"
        assert report["ttl"] == 64 and report["tos"] == 0x28
        assert report["identification"] == 0x4321 and report["dontFragment"]
        assert report["ipv4Checksum"] == int.from_bytes(packet[10:12], "big")
        assert report["ethernetPaddingHex"] == padding.hex()
        compare_segment(report, case)
        count += 1
    raw = bytes.fromhex(accepted[0]["segmentHex"])
    packet = ipv4(raw, source, destination)
    bad_checksum = bytearray(packet)
    bad_checksum[10] ^= 1
    malformed = [
        ETHERNET + bytes(bad_checksum),
        ETHERNET + packet[:-1],
        ETHERNET + ipv4(raw, source, destination, protocol=17),
        ETHERNET + ipv4(raw, "192.0.2.2", destination),
        ETHERNET + ipv4(raw, source, "198.51.100.3"),
        ETHERNET + ipv4(raw, source, destination, flags=0x6000),
        ETHERNET + ipv4(raw, source, destination, flags=0x8000),
        ETHERNET[:12] + bytes.fromhex("810000010800") + packet,
        ETHERNET[:12] + bytes.fromhex("0806") + packet,
        ETHERNET + ipv4(raw[:19], source, destination),
    ]
    for frame in malformed:
        invoke("tcp-wire", write(path, {"schema": 1, "raw": frame.hex()}), "--json", code=2)
        count += 1
    return count


def input_checks(path, fixtures):
    valid_segment = {
        "schema": 1,
        "source": fixtures["source"],
        "destination": fixtures["destination"],
        "raw": fixtures["cases"][0]["segmentHex"],
    }
    invalid = [
        ("tcp-segment", {**valid_segment, "schema": 2}),
        ("tcp-segment", {**valid_segment, "header": {}}),
        ("tcp-segment", {**valid_segment, "source": "192.000.2.1"}),
        ("tcp-segment", {**valid_segment, "destination": "2001:db8::1"}),
        ("tcp-segment", {**valid_segment, "raw": "0"}),
        ("tcp-segment", {**valid_segment, "raw": "gg"}),
        ("tcp-sequence", {"schema": 1, "first": -1, "second": 0, "length": 0}),
        ("tcp-sequence", {"schema": 1, "first": 1 << 32, "second": 0, "length": 0}),
        ("tcp-sequence", {"schema": 1, "first": 0, "second": 1 << 32, "length": 0}),
        ("tcp-sequence", {"schema": 1, "first": 0, "second": 0, "length": (1 << 32) + 1}),
        ("tcp-wire", {"schema": 2, "raw": ""}),
        ("tcp-wire", {"schema": 1, "raw": "", "header": {}}),
    ]
    for command, value in invalid:
        invoke(command, write(path, value), "--json", code=2)
    return len(invalid)


def dual_zero_checks(path, fixtures):
    zero = next(case for case in fixtures["cases"] if case["name"] == "checksum-zero")
    raw = bytearray.fromhex(zero["segmentHex"])
    raw[16:18] = bytes.fromhex("ffff")
    source, destination = fixtures["source"], fixtures["destination"]
    decoded = tcp.decode_segment(source, destination, raw)
    assert decoded.checksum == 65535 and tcp.encode_segment(decoded) == raw
    assert tcp.rechecksum(source, destination, decoded).checksum == 0
    alternate = {
        **zero,
        "name": "alternate-valid-checksum-ffff",
        "segmentHex": raw.hex(),
        "expected": {**zero["expected"], "checksum": 65535},
    }
    segment = {"schema": 1, "source": source, "destination": destination, "raw": raw.hex()}
    report = json.loads(invoke("tcp-segment", write(path, segment), "--json"))
    assert report["valid"] and report["checksumVerified"]
    compare_segment(report, alternate)
    frame = ETHERNET + ipv4(raw, source, destination)
    report = json.loads(
        invoke("tcp-wire", write(path, {"schema": 1, "raw": frame.hex()}), "--json")
    )
    assert report["valid"] and report["tcpChecksumVerified"]
    compare_segment(report, alternate)
    return 2


def check():
    fixtures = tcp.load_fixtures()
    tcp.check_fixtures(fixtures)
    with tempfile.TemporaryDirectory(prefix="netlib-static-tcp-") as directory:
        path = Path(directory) / "input.json"
        return {
            "segments": segment_checks(path, fixtures),
            "sequences": sequence_checks(path, fixtures),
            "wire": wire_checks(path, fixtures),
            "invalidInputs": input_checks(path, fixtures),
            "dualZero": dual_zero_checks(path, fixtures),
        }


def main():
    print(json.dumps({"scope": "static model conformance only", **check()}, sort_keys=True))


if __name__ == "__main__":
    main()
