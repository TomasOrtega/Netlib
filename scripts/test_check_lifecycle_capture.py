"""Offline trace parsing and native-evidence contradiction regressions."""

import copy
import json
import tempfile
import unittest
from pathlib import Path

import check_lifecycle_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/lifecycle/native"
PACKET = 'iif "inside0" ip saddr 192.0.2.2 ip daddr 203.0.113.2 udp sport 31000 udp dport 8080'


def line(body, *, trace="12345678", table="table", chain="chain"):
    return f"trace id {trace} ip {table} {chain} {body}\n"


def complete_packet(**options):
    return line("packet: " + PACKET, **options) + line("policy accept", **options)


class TraceTests(unittest.TestCase):
    def test_packet_fields_and_unknown_rule_handle(self):
        text = line("packet: " + PACKET) + line("unknown rule handle 6 (verdict drop)")
        (trace,) = check.parse_trace(text)
        (stage,) = trace["stages"]
        self.assertEqual(stage["packet"]["sourcePort"], 31000)
        self.assertEqual(stage["packet"]["destination"], "203.0.113.2")
        self.assertEqual(stage["verdicts"][0]["handle"], 6)
        self.assertEqual(stage["verdicts"][0]["verdict"], "drop")

    def test_interleaved_trace_ids_and_repeated_chain_visits_retained(self):
        text = line("packet: " + PACKET)
        text += complete_packet(trace="87654321")
        text += line("policy accept") + complete_packet()
        traces = check.parse_trace(text)
        self.assertEqual([trace["id"] for trace in traces], ["12345678", "87654321"])
        self.assertEqual(len(traces[0]["stages"]), 2)

    def test_missing_and_conflicting_transport_fields_rejected(self):
        for packet in (
            PACKET.replace(" udp dport 8080", ""),
            PACKET + " udp sport 1",
            PACKET + " tcp sport 1 tcp dport 2",
            PACKET.replace("31000", "65536"),
            PACKET.replace("192.0.2.2", "300.0.2.2"),
        ):
            with self.subTest(packet=packet):
                with self.assertRaises(check.EvidenceError):
                    check.parse_trace(line("packet: " + packet) + line("policy accept"))

    def test_orphan_incomplete_unknown_and_drop_continuation_rejected(self):
        texts = (
            line("policy accept"),
            line("packet: " + PACKET),
            line("packet: " + PACKET) + line("rule foo (verdict continue)"),
            "unrecognized native output\n",
            line("packet: " + PACKET) + line("policy drop") + complete_packet(chain="later"),
        )
        for text in texts:
            with self.subTest(text=text):
                with self.assertRaises(check.EvidenceError):
                    check.parse_trace(text)


class SnapshotTests(unittest.TestCase):
    def test_independent_decode_matches_retained_capture(self):
        data = json.loads((CAPTURE / "opened-state.json").read_text())
        (entry,) = check.decode_snapshot(data)
        self.assertEqual(entry["status"], 440)
        self.assertEqual(entry["original"]["destinationPort"], 8080)
        self.assertEqual(entry["reply"]["sourcePort"], 9000)

    def test_structured_status_and_raw_message_disagreement_rejected(self):
        data = json.loads((CAPTURE / "opened-state.json").read_text())
        data["entries"][0]["status"] = 442
        with self.assertRaisesRegex(check.EvidenceError, "structured"):
            check.decode_snapshot(data)

    def test_incomplete_interrupted_and_sequence_mismatch_rejected(self):
        baseline = json.loads((CAPTURE / "opened-state.json").read_text())
        for mutation in ("missing-done", "interrupted", "sequence"):
            data = copy.deepcopy(baseline)
            if mutation == "missing-done":
                data["messages"].pop()
            else:
                raw = bytearray.fromhex(data["messages"][0])
                raw[6 if mutation == "interrupted" else 8] ^= 0x10
                data["messages"][0] = raw.hex()
            with self.subTest(mutation=mutation):
                with self.assertRaises(check.EvidenceError):
                    check.decode_snapshot(data)

    def test_empty_capture_requires_real_completion(self):
        data = json.loads((CAPTURE / "deleted-state.json").read_text())
        self.assertEqual(check.decode_snapshot(data), [])
        data["messages"] = []
        with self.assertRaises(check.EvidenceError):
            check.decode_snapshot(data)


class CaptureTests(unittest.TestCase):
    def test_native_capture(self):
        report = check.check_capture(CAPTURE)
        self.assertEqual(report["traceCount"], 9)
        self.assertEqual(report["packetCount"], 30)
        self.assertEqual(report["snapshotCount"], 8)
        self.assertEqual(len(report["phases"]), 9)
        cached = next(
            row for row in report["phases"] if row["phase"] == "unreplied-after-nat-update"
        )
        self.assertEqual((cached["state"], cached["fresh"]), ("new", False))
        dropped = next(row for row in report["phases"] if row["phase"] == "late-drop")
        self.assertEqual(dropped["afterSource"]["sourcePort"], 40000)
        self.assertIsNone(dropped["output"])

    def test_socket_and_trace_contradiction_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "observations.json"
            observations = json.loads((CAPTURE / "observations.json").read_text())
            next(row for row in observations if row["phase"] == "first-original")["server"][
                "packet"
            ]["sourcePort"] = 40001
            path.write_text(json.dumps(observations))
            with self.assertRaisesRegex(check.EvidenceError, "socket"):
                check.check_capture(CAPTURE, observations_path=path)

    def test_unknown_rule_handle_cannot_be_treated_as_implicit_acceptance(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "trace.txt"
            text = (CAPTURE / "trace.txt").read_text()
            text = text.replace("unknown rule handle 6", "unknown rule handle 999", 1)
            path.write_text(text)
            with self.assertRaisesRegex(check.EvidenceError, "handle"):
                check.check_capture(CAPTURE, trace_path=path)


if __name__ == "__main__":
    unittest.main()
