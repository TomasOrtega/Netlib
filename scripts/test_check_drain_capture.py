"""Retained queue evidence and contradiction regressions."""

import json
import shutil
import tempfile
import unittest
from pathlib import Path

import check_drain_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/drain/native"


class CaptureTests(unittest.TestCase):
    def reject_json_change(self, filename, change, pattern=None):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(CAPTURE, directory)
            path = directory / filename
            document = json.loads(path.read_text())
            change(document)
            path.write_text(json.dumps(document))
            with self.assertRaisesRegex(check.EvidenceError, pattern or "."):
                check.check_capture(directory)

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
        self.assertEqual((report["traceCount"], report["packetCount"]), (2, 8))
        self.assertEqual(report["snapshotCount"], 4)
        self.assertEqual(
            [row["disposition"] for row in report["phases"]], ["forwarded", "lateDrop"]
        )
        self.assertEqual([row["fresh"] for row in report["phases"]], [True, False])
        self.assertEqual(report["queueCounts"], [0, 1, 1, 0])
        self.assertTrue(report["oldReceivedAfterInstall"])

    def test_delivery_before_install_rejected(self):
        def change(document):
            document["old"]["server"]["endNs"] = document["install"]["startNs"] - 1

        self.reject_json_change("observations.json", change, "after installation")

    def test_new_send_before_install_rejected(self):
        def change(document):
            document["blocked"]["sent"]["startNs"] = document["install"]["startNs"] - 1

        self.reject_json_change("observations.json", change)

    def test_pending_snapshot_after_install_rejected(self):
        def change(document):
            document["qdisc"]["pending"]["endNs"] = document["install"]["endNs"] + 1

        self.reject_json_change("observations.json", change)

    def test_payload_and_header_contradictions_rejected(self):
        changes = (
            lambda value: value["old"]["server"].update(payload="other"),
            lambda value: value["blocked"]["sent"].update(payload="drain-old-already-queued"),
            lambda value: value["old"]["server"]["packet"].update(sourcePort=40001),
            lambda value: value["blocked"].update(server=value["old"]["server"]),
        )
        for change in changes:
            with self.subTest(change=change):
                self.reject_json_change("observations.json", change)

    def test_queue_count_backlog_and_config_contradictions_rejected(self):
        changes = (
            ("qdisc-pending.json", lambda value: value[0].update(qlen=0)),
            ("qdisc-pending.json", lambda value: value[0].update(backlog=0)),
            ("qdisc-drained.json", lambda value: value[0].update(qlen=1)),
            ("qdisc-drained.json", lambda value: value[0].update(packets=2)),
            ("qdisc-pending.json", lambda value: value[0]["options"].update(limit=999)),
            ("qdisc-pending.json", lambda value: value[0]["options"]["delay"].update(delay=0)),
            ("qdisc-blocked.json", lambda value: value[0]["options"].update(loss=0.5)),
        )
        for filename, change in changes:
            with self.subTest(filename=filename, change=change):
                self.reject_json_change(filename, change)

    def test_wrong_queue_command_rejected(self):
        self.reject_json_change("queue-command.json", lambda value: value.__setitem__(-1, "1ms"))

    def test_boolean_and_numeric_fields_are_not_interchangeable(self):
        changes = (
            ("qdisc-pending.json", lambda value: value[0].update(root=1)),
            ("qdisc-pending.json", lambda value: value[0]["options"]["delay"].update(jitter=False)),
            ("observations.json", lambda value: value.update(schema=True)),
        )
        for filename, change in changes:
            with self.subTest(filename=filename):
                self.reject_json_change(filename, change)

    def test_structured_status_cannot_override_raw_bytes(self):
        def change(document):
            document["entries"][0]["status"] = 442

        self.reject_json_change("pending-state.json", change, "structured")

    def test_raw_status_and_corresponding_record_must_be_confirmed_unreplied(self):
        def change(document):
            raw = bytes.fromhex(document["messages"][0])
            self.assertIn(bytes.fromhex("08000300000001b8"), raw)
            raw = raw.replace(
                bytes.fromhex("08000300000001b8"), bytes.fromhex("08000300000001ba"), 1
            )
            document["messages"][0] = raw.hex()
            document["entries"][0].update(status=442, raw=raw.hex())

        self.reject_json_change("pending-state.json", change, "unreplied")

    def test_missing_raw_completion_rejected(self):
        self.reject_json_change("initial-state.json", lambda value: value["messages"].clear())

    def test_missing_trace_and_wrong_drop_handle_rejected(self):
        self.reject_trace_change(lambda text: "\n".join(text.splitlines()[:-2]) + "\n")
        self.reject_trace_change(
            lambda text: text.replace("unknown rule handle 2", "unknown rule handle 999")
        )

    def test_trace_rule_text_must_match_active_export(self):
        self.reject_trace_change(
            lambda text: text.replace("udp dport 9000 accept", "udp dport 9999 accept", 1)
        )
        self.reject_trace_change(
            lambda text: text.replace("dnat to 198.51.100.2:9000", "dnat to 198.51.100.2:9001", 1)
        )
        self.reject_trace_change(
            lambda text: text.replace("snat to 203.0.113.1:40000", "snat to 203.0.113.1:40001", 1)
        )

    def test_wrong_late_policy_and_verdict_rejected(self):
        self.reject_trace_change(
            lambda text: text.replace("late policy accept", "late policy drop")
        )
        self.reject_trace_change(
            lambda text: text.replace("handle 2 (verdict drop)", "handle 2 (verdict accept)")
        )
        self.reject_trace_change(
            lambda text: text.replace("unknown rule handle 2 (verdict drop)", "policy drop")
        )

    def test_barrier_must_cover_udp_any_port(self):
        def change(document):
            rule = next(value["rule"] for value in document["nftables"] if "rule" in value)
            rule["expr"].insert(
                -1,
                {
                    "match": {
                        "op": "==",
                        "left": {"payload": {"protocol": "udp", "field": "dport"}},
                        "right": 9000,
                    }
                },
            )

        self.reject_json_change("late-after.json", change, "barrier")

    def test_trace_payload_length_must_agree_with_socket_payload(self):
        self.reject_trace_change(lambda text: text.replace("udp length 32", "udp length 33"))

    def test_route_and_instrumentation_export_contradictions_rejected(self):
        def route_change(document):
            next(row for row in document if row["dst"] == "198.51.100.0/24")["dev"] = "inside0"

        self.reject_json_change("routes.json", route_change)

        def change(document):
            rule = next(value["rule"] for value in document["nftables"] if "rule" in value)
            rule["expr"][0]["mangle"]["value"] = 0

        self.reject_json_change("instrumentation.json", change)


if __name__ == "__main__":
    unittest.main()
