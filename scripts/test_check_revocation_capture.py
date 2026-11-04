"""Contradiction tests for the independent native revocation evidence check."""

import json
import shutil
import tempfile
import unittest
from pathlib import Path

import check_revocation_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/revocation/native"


class CaptureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name) / "native"
        shutil.copytree(CAPTURE, self.directory)

    def change_json(self, name, change):
        path = self.directory / name
        value = json.loads(path.read_text())
        change(value)
        path.write_text(json.dumps(value))

    def test_genuine_capture(self):
        result = check.check_capture(self.directory)
        self.assertEqual(
            (result["traceCount"], result["packetCount"], result["snapshotCount"]), (6, 22, 7)
        )
        self.assertEqual([phase["phase"] for phase in result["phases"]], check.PHASES)
        barrier = result["phases"][3]
        self.assertEqual(barrier["config"], "barrier")
        self.assertEqual(barrier["disposition"], "lateDrop")
        self.assertEqual(barrier["afterSource"]["destinationPort"], 9000)
        self.assertIsNone(barrier["output"])
        fresh = result["phases"][-1]
        self.assertEqual(fresh["afterSource"]["destinationPort"], 9003)
        self.assertEqual(fresh["disposition"], "lateDrop")

    def test_barrier_must_cover_every_backend_udp_port(self):
        def narrow(document):
            rule = next(item["rule"] for item in document["nftables"] if "rule" in item)
            rule["expr"].insert(
                1,
                {
                    "match": {
                        "op": "==",
                        "left": {"payload": {"protocol": "udp", "field": "dport"}},
                        "right": 9000,
                    }
                },
            )

        self.change_json("barrier-closed.json", narrow)
        with self.assertRaisesRegex(check.EvidenceError, "every UDP port"):
            check.check_capture(self.directory)

    def test_barrier_priority_must_follow_source_nat(self):
        def early(document):
            next(item["chain"] for item in document["nftables"] if "chain" in item)["prio"] = 99

        self.change_json("barrier-closed.json", early)
        with self.assertRaisesRegex(check.EvidenceError, "Hook order"):
            check.check_capture(self.directory)

    def test_trace_drop_cannot_be_replaced_by_accept(self):
        result = check.check_capture(self.directory)
        barrier = result["phases"][3]["stages"][-1]
        path = self.directory / "trace.txt"
        lines = path.read_text().splitlines()
        index = barrier["verdicts"][-1]["line"] - 1
        lines[index] = lines[index].replace("verdict drop", "verdict accept")
        path.write_text("\n".join(lines) + "\n")
        with self.assertRaisesRegex(check.EvidenceError, "verdict"):
            check.check_capture(self.directory)

    def change_first_nat_trace(self, stage_index, change):
        result = check.check_capture(self.directory)
        stage = result["phases"][0]["stages"][stage_index]
        path = self.directory / "trace.txt"
        lines = path.read_text().splitlines()
        index = stage["verdicts"][-1]["line"] - 1
        lines[index] = change(lines[index])
        path.write_text("\n".join(lines) + "\n")

    def test_destination_trace_target_must_match_export(self):
        self.change_first_nat_trace(
            1, lambda line: line.replace("dnat to 198.51.100.2:9000", "dnat to 198.51.100.2:9001")
        )
        with self.assertRaises(check.EvidenceError):
            check.check_capture(self.directory)

    def test_source_trace_target_must_match_export(self):
        self.change_first_nat_trace(
            3, lambda line: line.replace("snat to 203.0.113.1:40000", "snat to 203.0.113.1:40001")
        )
        with self.assertRaises(check.EvidenceError):
            check.check_capture(self.directory)

    def test_matching_nat_rule_cannot_be_a_policy_verdict(self):
        self.change_first_nat_trace(1, lambda line: line[: line.index("rule ")] + "policy accept")
        with self.assertRaises(check.EvidenceError):
            check.check_capture(self.directory)

    def test_nat_trace_predicate_must_match_export(self):
        self.change_first_nat_trace(
            1, lambda line: line.replace("udp dport 8080", "udp dport 8081")
        )
        with self.assertRaises(check.EvidenceError):
            check.check_capture(self.directory)

    def test_destination_nat_visit_must_receive_the_sent_header(self):
        result = check.check_capture(self.directory)
        stage = result["phases"][0]["stages"][1]
        path = self.directory / "trace.txt"
        lines = path.read_text().splitlines()
        index = stage["line"] - 1
        lines[index] = lines[index].replace("udp sport 31000", "udp sport 31002")
        path.write_text("\n".join(lines) + "\n")
        with self.assertRaisesRegex(check.EvidenceError, "Destination NAT input"):
            check.check_capture(self.directory)

    def test_barrier_must_observe_the_cached_post_nat_header(self):
        result = check.check_capture(self.directory)
        barrier = result["phases"][3]["stages"][-1]
        path = self.directory / "trace.txt"
        lines = path.read_text().splitlines()
        index = barrier["line"] - 1
        lines[index] = lines[index].replace("udp sport 40000", "udp sport 40001")
        path.write_text("\n".join(lines) + "\n")
        with self.assertRaisesRegex(check.EvidenceError, "post-SNAT"):
            check.check_capture(self.directory)

    def test_raw_status_must_agree_with_structured_record(self):
        self.change_json("barrier-state.json", lambda value: value["entries"][0].update(status=440))
        with self.assertRaisesRegex(check.EvidenceError, "structured"):
            check.check_capture(self.directory)

    def test_cached_record_must_retain_seen_reply(self):
        shutil.copyfile(self.directory / "opened-state.json", self.directory / "barrier-state.json")
        with self.assertRaisesRegex(check.EvidenceError, "Seen-reply"):
            check.check_capture(self.directory)

    def test_fresh_late_drop_must_not_add_a_visible_record(self):
        shutil.copyfile(
            self.directory / "replied-state.json", self.directory / "fresh-barrier-state.json"
        )
        with self.assertRaisesRegex(check.EvidenceError, "unexpected visible"):
            check.check_capture(self.directory)

    def test_drop_must_not_have_a_socket_delivery(self):
        def delivered(rows):
            rows[3]["received"] = rows[2]["received"]

        self.change_json("observations.json", delivered)
        with self.assertRaisesRegex(check.EvidenceError, "traced drop"):
            check.check_capture(self.directory)

    def test_native_dump_requires_successful_completion(self):
        self.change_json("fresh-barrier-state.json", lambda value: value["messages"].clear())
        with self.assertRaisesRegex(check.EvidenceError, "DONE"):
            check.check_capture(self.directory)

    def test_missing_packet_trace_is_rejected(self):
        result = check.check_capture(self.directory)
        trace_id = result["phases"][-1]["traceId"]
        path = self.directory / "trace.txt"
        path.write_text(
            "\n".join(
                line
                for line in path.read_text().splitlines()
                if not line.startswith(f"trace id {trace_id} ")
            )
            + "\n"
        )
        with self.assertRaisesRegex(check.EvidenceError, "packet traces"):
            check.check_capture(self.directory)

    def test_first_trace_must_match_the_confirmed_original(self):
        result = check.check_capture(self.directory)
        trace_id = result["phases"][0]["traceId"]
        path = self.directory / "trace.txt"
        path.write_text(
            "\n".join(
                line.replace("udp sport 31000", "udp sport 31002")
                if line.startswith(f"trace id {trace_id} ")
                else line
                for line in path.read_text().splitlines()
            )
            + "\n"
        )
        self.change_json(
            "observations.json", lambda rows: rows[0]["sent"]["packet"].update(sourcePort=31002)
        )
        with self.assertRaisesRegex(check.EvidenceError, "confirmed original"):
            check.check_capture(self.directory)


if __name__ == "__main__":
    unittest.main()
