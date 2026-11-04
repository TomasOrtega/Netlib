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
    def reject_trace_change(self, change):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "trace.txt"
            original = (CAPTURE / "trace.txt").read_text()
            changed = change(original)
            self.assertNotEqual(original, changed)
            path.write_text(changed)
            with self.assertRaises(check.EvidenceError):
                check.check_capture(CAPTURE, trace_path=path)

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

    def test_filter_predicate_change_with_same_comment_is_rejected(self):
        self.reject_trace_change(
            lambda text: text.replace(
                'udp dport 9000 accept comment "SERVICE"',
                'udp dport 9999 accept comment "SERVICE"',
                1,
            )
        )

    def test_filter_missing_predicates_with_same_comment_is_rejected(self):
        self.reject_trace_change(
            lambda text: text.replace(
                'ct state new ip saddr 192.0.2.0/24 ip daddr 198.51.100.2 udp dport 9000 accept comment "SERVICE"',
                'ct state new accept comment "SERVICE"',
                1,
            )
        )

    def test_filter_statement_change_with_same_comment_is_rejected(self):
        self.reject_trace_change(
            lambda text: text.replace('accept comment "SERVICE"', 'drop comment "SERVICE"', 1)
        )

    def test_filter_selected_rule_cannot_become_policy(self):
        self.reject_trace_change(
            lambda text: text.replace(
                'rule ct state new udp dport 9002 drop comment "FORWARD_DROP" (verdict drop)',
                "policy drop",
                1,
            )
        )

    def test_dnat_target_contradiction_is_rejected(self):
        self.reject_trace_change(
            lambda text: text.replace("dnat to 198.51.100.2:9002", "dnat to 198.51.100.2:9003", 1)
        )

    def test_snat_target_contradiction_is_rejected(self):
        self.reject_trace_change(
            lambda text: text.replace("snat to 203.0.113.1:40000", "snat to 203.0.113.1:40001", 1)
        )

    def test_nat_selected_rule_cannot_become_policy_accept(self):
        self.reject_trace_change(
            lambda text: text.replace(
                "rule ip daddr 203.0.113.2 udp dport 8082 dnat to 198.51.100.2:9002 (verdict accept)",
                "policy accept",
                1,
            )
        )

    def test_nat_unknown_handle_must_match_export(self):
        self.reject_trace_change(
            lambda text: text.replace(
                "netlib_nat destination unknown rule handle 7",
                "netlib_nat destination unknown rule handle 999",
                1,
            )
        )

    def test_nat_predicate_change_is_rejected(self):
        self.reject_trace_change(
            lambda text: text.replace("udp dport 8082 dnat to", "udp dport 8083 dnat to", 1)
        )

    def test_nat_visit_input_must_match_ingress(self):
        def change(text):
            stage = check.parse_trace(text)[0]["stages"][1]
            lines = text.splitlines()
            index = stage["line"] - 1
            port = stage["packet"]["sourcePort"]
            lines[index] = lines[index].replace(f"udp sport {port}", f"udp sport {port + 1}")
            return "\n".join(lines) + "\n"

        self.reject_trace_change(change)

    def test_extra_filter_side_effect_verdict_is_rejected(self):
        def change(text):
            stage = check.parse_trace(text)[0]["stages"][-1]
            lines = text.splitlines()
            index = stage["verdicts"][0]["line"] - 1
            prefix = lines[index].split(" rule ", 1)[0]
            lines.insert(index, prefix + " rule meta mark set 1 (verdict continue)")
            return "\n".join(lines) + "\n"

        self.reject_trace_change(change)

    def test_extra_nat_side_effect_verdict_is_rejected(self):
        def change(text):
            stage = check.parse_trace(text)[0]["stages"][1]
            lines = text.splitlines()
            index = stage["verdicts"][0]["line"] - 1
            prefix = lines[index].split(" rule ", 1)[0]
            lines.insert(index, prefix + " rule meta mark set 1 (verdict continue)")
            return "\n".join(lines) + "\n"

        self.reject_trace_change(change)

    def test_instrumentation_side_effect_is_rejected(self):
        self.reject_trace_change(
            lambda text: text.replace("rule meta nftrace set 1", "rule meta mark set 1", 1)
        )


if __name__ == "__main__":
    unittest.main()
