"""Compare synthetic CLI executions with the pinned-source IPv4 queue oracle."""

import copy
import ipaddress
import itertools
import json
import subprocess
import tempfile
from dataclasses import replace
from pathlib import Path

from reassembly_reference import (
    NANOSECONDS,
    IPPacket,
    ReassemblyOracle,
    checksum,
    decode_packet,
    encode_packet,
    folded_sum,
)

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / ".lake/build/bin/netlib"
PEER = int(ipaddress.IPv4Address("192.0.2.2"))
VIP = int(ipaddress.IPv4Address("203.0.113.2"))
SNAT = int(ipaddress.IPv4Address("203.0.113.1"))
SERVER = int(ipaddress.IPv4Address("198.51.100.2"))
ETHERNET = bytes.fromhex("02000000ea0402000000ea030800")
PERMIT, DENY = "credential-permitted", "unauthenticated"


def udp(source, destination, source_port, destination_port, payload, omitted=False):
    size = 8 + len(payload)
    header = (
        source_port.to_bytes(2, "big")
        + destination_port.to_bytes(2, "big")
        + size.to_bytes(2, "big")
        + bytes(2)
    )
    pseudo = (
        source.to_bytes(4, "big")
        + destination.to_bytes(4, "big")
        + bytes((0, 17))
        + size.to_bytes(2, "big")
    )
    checked = 0 if omitted else checksum(pseudo + header + payload) or 65535
    return header[:6] + checked.to_bytes(2, "big") + payload


def packet(identifier, application=33, omitted=False):
    payload = bytes((index * 17 + identifier) % 256 for index in range(application))
    return IPPacket(PEER, VIP, udp(PEER, VIP, 41000, 8080, payload, omitted), identifier)


def part(ip, start, count, more, **changes):
    return replace(
        ip,
        payload=ip.payload[start : start + count],
        offset=start,
        more_fragments=more,
        raw=b"",
        **changes,
    )


def packet_json(ip):
    return {
        "tos": ip.tos,
        "identification": ip.identification,
        "ttl": ip.ttl,
        "dontFragment": ip.dont_fragment,
        "source": ip.source,
        "destination": ip.destination,
        "payloadHex": ip.payload.hex(),
    }


def header(source, destination, source_port, destination_port):
    return {
        "source": str(ipaddress.IPv4Address(source)),
        "destination": str(ipaddress.IPv4Address(destination)),
        "protocol": 17,
        "sourcePort": source_port,
        "destinationPort": destination_port,
    }


def record(zone):
    return {
        "original": header(PEER, VIP, 41000, 8080),
        "reply": header(SERVER, SNAT, 9000, 40000),
        "originalZone": zone,
        "replyZone": zone,
        "sourceNAT": True,
        "destinationNAT": True,
        "seenReply": False,
    }


def output_family(ip, budget, df, lengths=None):
    if lengths is None:
        lengths = []
        remaining = len(ip.payload)
        while remaining > budget - 20:
            size = (budget - 20) // 8 * 8
            lengths.append(size)
            remaining -= size
        lengths.append(remaining)
    assert sum(lengths) == len(ip.payload) and all(0 < size for size in lengths)
    result, start = [], 0
    for index, size in enumerate(lengths):
        fragment = part(ip, start, size, index + 1 < len(lengths), dont_fragment=df)
        assert fragment.wire_length <= budget
        assert not fragment.more_fragments or size % 8 == 0
        result.append((ETHERNET + encode_packet(fragment)).hex())
        start += size
    return result


def fixture(mtu):
    source = json.loads((ROOT / "examples/icmp/replay.json").read_text())
    result = {key: copy.deepcopy(source[key]) for key in ("schema", "routing", "mtus")}
    result["configs"] = [
        {key: config[key] for key in ("id", "forward", "late", "nat")}
        for config in source["configs"]
        if config["id"] in (PERMIT, DENY)
    ]
    for binding in result["mtus"]:
        if binding["nextHop"] == "service":
            binding["mtu"] = mtu
    result.update(
        initial=None,
        reassembly={
            "userBase": 2,
            "policies": [
                {"id": "normal", "timeout": 30 * NANOSECONDS},
                {"id": "short", "timeout": NANOSECONDS},
            ],
        },
        events=[],
    )
    return result


class ReferenceTrace:
    def __init__(self, mtu=600):
        self.document = fixture(mtu)
        self.oracle = ReassemblyOracle()
        self.mtu = mtu
        self.rows = []
        self.records = {}
        self.clock = 0

    def _now(self, now):
        if now is None:
            now = self.clock + 1_000_000
        self.clock = now
        return now

    def _save(self, event, reassembled=None, expected=None, status=None):
        self.document["events"].append(event)
        self.rows.append(
            {
                "reassembled": None if reassembled is None else packet_json(reassembled),
                "expected": expected,
                "pendingQueues": len(self.oracle.queues),
                "expectedState": list(self.records.values()),
                "status": status,
            }
        )

    def fragment(
        self,
        ip,
        *,
        now=None,
        zone=0,
        vif=0,
        config=PERMIT,
        policy="normal",
        df=None,
        lengths=None,
        status=None,
    ):
        now = self._now(now)
        result = self.oracle.arrive(
            encode_packet(ip),
            now,
            zone,
            vif,
            NANOSECONDS if policy == "short" else 30 * NANOSECONDS,
        )
        if status is not None:
            assert result.status == status, (result.status, status)
        completed, forwarded = None, []
        if result.output is not None:
            source = result.output
            segment = source.payload
            size = int.from_bytes(segment[4:6], "big")
            pseudo = (
                source.source.to_bytes(4, "big")
                + source.destination.to_bytes(4, "big")
                + bytes((0, 17))
                + size.to_bytes(2, "big")
            )
            assert size == len(segment) >= 8
            assert int.from_bytes(segment[6:8], "big") == 0 or folded_sum(pseudo + segment) == 65535
            fresh = zone not in self.records
            cap = min(self.mtu, result.max_size) if result.reassembled else self.mtu
            expired = source.ttl <= 1
            oversized = (
                source.dont_fragment
                and source.wire_length > self.mtu
                and (not result.reassembled or result.max_size > self.mtu)
            )
            disposition = (
                "ttlExpired"
                if expired
                else "mtuExceeded"
                if oversized
                else "forwardDrop"
                if config == DENY
                else "forwarded"
            )
            emission = None
            if disposition == "forwarded":
                emission = replace(
                    source,
                    source=SNAT,
                    destination=SERVER,
                    ttl=source.ttl - 1,
                    payload=udp(SNAT, SERVER, 40000, 9000, segment[8:], segment[6:8] == bytes(2)),
                    raw=b"",
                )
                selected_df = (
                    source.dont_fragment if not result.reassembled else False if df is None else df
                )
                forwarded = output_family(emission, cap, selected_df, lengths)
                self.records[zone] = record(zone)
            completed = {
                "classification": "new",
                "fresh": fresh,
                "afterDestination": header(PEER, SERVER, 41000, 9000),
                "afterSource": header(SNAT, SERVER, 40000, 9000) if emission else None,
                "nextHop": "service",
                "disposition": disposition,
                "routeMTU": None if expired else self.mtu,
                "fragmentSizeCap": None if expired or oversized else cap,
                "reassembled": result.reassembled,
                "maxSize": result.max_size,
                "maxDFSize": result.max_df_size,
                "output": None if emission is None else packet_json(emission),
            }
        event = {
            "type": "fragment",
            "at": now,
            "config": config,
            "queuePolicy": policy,
            "zone": zone,
            "vif": vif,
            "rawIPv4": encode_packet(ip).hex(),
            "observed": {
                "reassembled": None if result.packet is None else result.packet.hex(),
                "forwarded": forwarded,
            },
            "state": None,
        }
        self._save(event, result.output, completed, result.status)
        return result

    def wait(self, now):
        now = self._now(now)
        expired = self.oracle.advance(now)
        self._save({"type": "wait", "at": now, "state": None})
        return expired

    def erase(self, ip, *, now=None, zone=0):
        now = self._now(now)
        self.oracle.advance(now)
        self.records.pop(zone, None)
        self._save(
            {
                "type": "erase",
                "at": now,
                "zone": zone,
                "rawIPv4": encode_packet(ip).hex(),
                "state": None,
            }
        )


def _records(values):
    return {json.dumps(value, sort_keys=True) for value in values}


def _run(document, path, binary, code=0):
    path.write_text(json.dumps(document))
    result = subprocess.run(
        [str(binary), "wire-reassembly", str(path), "--json"],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    assert result.returncode == code, (code, result.returncode, result.stdout, result.stderr)
    return None if code == 2 else json.loads(result.stdout)


def _compare(trace, report):
    assert report["compliant"] and report["eventCount"] == len(trace.rows)
    for index, (expected, actual) in enumerate(zip(trace.rows, report["findings"], strict=True)):
        assert actual["source"] == f"/events/{index}" and actual["matched"]
        for key in ("reassembled", "expected", "pendingQueues"):
            assert actual[key] == expected[key], (index, key, actual[key], expected[key])
        assert _records(actual["expectedState"]) == _records(expected["expectedState"]), index
    assert report["pendingQueues"] == len(trace.oracle.queues)
    assert _records(report["final"]) == _records(list(trace.records.values()))


def _normal_orders():
    trace = ReferenceTrace()
    identifier = 0x5000
    for lengths in ((16, 16, 9), (8, 8, 8, 1)):
        for order in itertools.permutations(range(len(lengths))):
            ip = packet(identifier, sum(lengths) - 8, omitted=bool(identifier & 1))
            offsets = list(itertools.accumulate((0,) + lengths))[:-1]
            for position, index in enumerate(order):
                trace.fragment(
                    part(ip, offsets[index], lengths[index], index + 1 < len(lengths)),
                    status="complete" if position + 1 == len(lengths) else "buffered",
                )
            identifier += 1
    return trace


def _duplicate_and_overlap():
    trace = ReferenceTrace()
    ip = packet(0x5100)
    for start in (0, 8, 24):
        trace.fragment(part(ip, start, 8, True), status="buffered")
    trace.fragment(
        replace(
            part(ip, 0, 16, True), payload=b"wrong duplicate!", ttl=1, tos=0xFF, dont_fragment=True
        ),
        status="duplicate",
    )
    trace.fragment(part(ip, 16, 8, True), status="buffered")
    trace.fragment(part(ip, 32, 9, False), status="complete")
    ip = packet(0x5101)
    for start in (0, 16, 8):
        trace.fragment(part(ip, start, 8, True), status="buffered")
    trace.fragment(part(ip, 0, 16, True), status="overlap")
    for start in (32, 24, 16, 8, 0):
        trace.fragment(
            part(ip, start, 9 if start == 32 else 8, start != 32),
            status="complete" if start == 0 else "buffered",
        )
    ip = packet(0x5102, 16)
    trace.fragment(part(ip, 0, 8, True), status="buffered")
    trace.fragment(part(ip, 16, 8, True), status="buffered")
    trace.fragment(part(ip, 16, 8, False, tos=3, dont_fragment=True), status="duplicate")
    trace.fragment(part(ip, 8, 8, True), status="complete")
    ip = packet(0x5103)
    trace.fragment(part(ip, 0, 16, True), status="buffered")
    trace.fragment(part(ip, 8, 16, True), status="overlap")
    return trace


def _lengths_and_ecn():
    trace = ReferenceTrace()
    ip = packet(0x5200)
    trace.fragment(
        replace(part(ip, 0, 16, True), payload=ip.payload[:16] + b"odd"), status="buffered"
    )
    trace.fragment(part(ip, 16, 16, True), status="buffered")
    trace.fragment(part(ip, 32, 9, False), status="complete")
    for identifier, invalid in ((0x5201, "zero"), (0x5202, "final"), (0x5203, "beyond")):
        ip = packet(identifier)
        trace.fragment(part(ip, 0, 16, True), status="buffered")
        if invalid == "zero":
            trace.fragment(part(ip, 16, 3, True), status="empty")
        else:
            trace.fragment(part(ip, 32, 9, False), status="buffered")
            fragment = (
                part(ip, 16, 8, False)
                if invalid == "final"
                else replace(part(ip, 40, 1, True), payload=bytes(8))
            )
            trace.fragment(fragment, status="inconsistentLength")
    for index, values in enumerate(itertools.product(range(4), repeat=3)):
        ip = packet(0x5300 + index)
        for position, (start, size, ecn) in enumerate(
            zip((0, 16, 32), (16, 16, 9), values, strict=True)
        ):
            invalid = 0 in values and len(set(values)) != 1
            trace.fragment(
                part(
                    ip,
                    start,
                    size,
                    position != 2,
                    tos=(0x24 if position == 0 else 0xC0) | ecn,
                    ttl=37 if position == 0 else 11,
                ),
                status=("invalidECN" if invalid else "complete") if position == 2 else "buffered",
            )
    oversized = replace(packet(0x53FF), offset=65528, payload=bytes(8), more_fragments=True)
    trace.fragment(oversized, status="buffered")
    return trace


def _domains_and_clock():
    trace = ReferenceTrace()
    for field in ("zone", "vif", "identification"):
        a, b = packet(0x5400), packet(0x5400, omitted=True)
        if field == "identification":
            b = replace(b, identification=b.identification + 1)
        options = ({field: 10}, {field: 20}) if field != "identification" else ({}, {})
        for ip, args, start, size, more in (
            (a, options[0], 0, 16, True),
            (b, options[1], 16, 16, True),
            (a, options[0], 32, 9, False),
            (b, options[1], 32, 9, False),
            (a, options[0], 16, 16, True),
            (b, options[1], 0, 16, True),
        ):
            trace.fragment(part(ip, start, size, more), **args)
        trace.wait(trace.clock + 31 * NANOSECONDS)
    ip = packet(0x5410, 17)
    start = trace.clock + NANOSECONDS
    trace.fragment(part(ip, 0, 8, True), now=start, policy="short", status="buffered")
    trace.fragment(
        part(ip, 0, 8, True), now=start + 900_000_000, policy="short", status="duplicate"
    )
    expired = trace.wait(start + NANOSECONDS)
    assert len(expired) == 1 and expired[0].first.ip.raw == encode_packet(part(ip, 0, 8, True))
    trace.fragment(
        part(ip, 8, 17, False), now=start + NANOSECONDS + 1, policy="short", status="buffered"
    )
    trace.fragment(
        part(ip, 0, 8, True), now=start + NANOSECONDS + 2, policy="short", status="complete"
    )
    ip = packet(0x5411, 17)
    trace.fragment(part(ip, 0, 8, True), config=DENY, status="buffered")
    trace.fragment(
        part(ip, 8, 17, False), now=trace.clock + 2 * NANOSECONDS, policy="short", status="complete"
    )
    ip = packet(0x5412, 17)
    trace.fragment(part(ip, 0, 8, True), status="buffered")
    trace.erase(ip)
    assert trace.oracle.queues
    trace.fragment(part(ip, 8, 17, False), config=DENY, status="complete")
    return trace


def _size_and_df():
    trace = ReferenceTrace()
    for identifier, lengths, flags, output_df in (
        (0x5500, (8, 8, 8, 1), (False, False, False, False), False),
        (0x5501, (8, 9), (False, False), False),
        (0x5502, (16, 16, 9), (True, False, False), True),
        (0x5503, (16, 16, 9), (True, False, False), False),
        (0x5504, (8, 16, 17), (True, False, False), False),
    ):
        ip, start = packet(identifier, sum(lengths) - 8), 0
        for index, (size, df) in enumerate(zip(lengths, flags, strict=True)):
            trace.fragment(
                part(ip, start, size, index + 1 < len(lengths), dont_fragment=df), df=output_df
            )
            start += size
    for df in (False, True):
        trace.fragment(replace(packet(0x5510 + int(df), 17), dont_fragment=df), status="whole")
    small_route = ReferenceTrace(mtu=68)
    for index, df in enumerate((False, True)):
        ip = packet(0x5520 + index, 1200)
        for start, size, more in ((0, 576, True), (576, 576, True), (1152, 56, False)):
            small_route.fragment(part(ip, start, size, more, dont_fragment=df))
    return trace, small_route


def synthetic_checks(binary=None):
    binary = Path(binary or BINARY)
    traces = [
        _normal_orders(),
        _duplicate_and_overlap(),
        _lengths_and_ecn(),
        _domains_and_clock(),
        *_size_and_df(),
    ]
    comparisons = sum(len(trace.rows) for trace in traces)
    with tempfile.TemporaryDirectory(prefix="netlib-reassembly-oracle-") as directory:
        path = Path(directory) / "replay.json"
        reports = []
        for trace in traces:
            report = _run(trace.document, path, binary)
            _compare(trace, report)
            reports.append(report)
        _mismatch_checks(path, binary)
        _invalid_checks(path, binary)
    return comparisons


def _mismatch_checks(path, binary):
    trace = ReferenceTrace()
    for identifier in (0x5600, 0x5601):
        ip = packet(identifier)
        for start, size, more in ((0, 16, True), (16, 16, True), (32, 9, False)):
            trace.fragment(part(ip, start, size, more))
    original = _run(trace.document, path, binary)
    event = trace.document["events"][2]
    first = event["observed"]["forwarded"][0]
    changed_ip = replace(decode_packet(bytes.fromhex(first)[14:]), ttl=17)
    variants = [
        {"forwarded": []},
        {"forwarded": event["observed"]["forwarded"] + [first]},
        {
            "forwarded": [(ETHERNET + encode_packet(changed_ip)).hex()]
            + event["observed"]["forwarded"][1:]
        },
        {"reassembled": None},
    ]
    for changes in variants:
        changed = copy.deepcopy(trace.document)
        changed["events"][2]["observed"].update(changes)
        report = _run(changed, path, binary, code=1)
        assert (
            report["final"] == original["final"]
            and report["pendingQueues"] == original["pendingQueues"]
        )
        assert [row["expected"] for row in report["findings"]] == [
            row["expected"] for row in original["findings"]
        ]
        assert [index for index, row in enumerate(report["findings"]) if not row["matched"]] == [2]
    whole = ReferenceTrace()
    whole.fragment(replace(packet(0x5610, 17), dont_fragment=True))
    changed = copy.deepcopy(whole.document)
    expected = whole.rows[0]["expected"]["output"]
    translated = IPPacket(
        expected["source"],
        expected["destination"],
        bytes.fromhex(expected["payloadHex"]),
        expected["identification"],
        expected["tos"],
        expected["ttl"],
        dont_fragment=True,
    )
    changed["events"][0]["observed"]["forwarded"] = output_family(translated, 600, True, [8, 8, 9])
    _run(changed, path, binary, code=1)


def _invalid_checks(path, binary):
    trace = ReferenceTrace()
    ip = packet(0x5700)
    trace.fragment(part(ip, 0, 16, True))
    trace.fragment(part(ip, 16, 16, True))
    trace.fragment(part(ip, 32, 9, False))
    mutations = []
    for index, replacement in ((10, 1), (0, 0x46)):
        changed = copy.deepcopy(trace.document)
        raw = bytearray.fromhex(changed["events"][0]["rawIPv4"])
        raw[index] = raw[index] ^ replacement if index == 10 else replacement
        changed["events"][0]["rawIPv4"] = raw.hex()
        mutations.append(changed)
    changed = copy.deepcopy(trace.document)
    changed["events"][1]["at"] = 0
    mutations.append(changed)
    changed = copy.deepcopy(trace.document)
    changed["reassembly"]["policies"][0]["timeout"] = 0
    mutations.append(changed)
    changed = copy.deepcopy(trace.document)
    changed["events"][0]["zone"] = 65536
    mutations.append(changed)
    changed = copy.deepcopy(trace.document)
    raw = decode_packet(changed["events"][-1]["rawIPv4"])
    raw = replace(raw, payload=raw.payload[:-1] + bytes((raw.payload[-1] ^ 1,)))
    changed["events"][-1]["rawIPv4"] = encode_packet(raw).hex()
    mutations.append(changed)
    for document in mutations:
        _run(document, path, binary, code=2)


def main():
    print(
        f"Independent IPv4 reassembly CLI checks passed for {synthetic_checks()} arrival and control prefixes."
    )


if __name__ == "__main__":
    main()
