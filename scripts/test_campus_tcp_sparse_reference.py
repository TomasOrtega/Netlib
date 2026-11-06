"""Test sparse byte coverage, current headers, and actual campus packet sources."""

import copy
import itertools
import json
import unittest
from dataclasses import replace

import campus_tcp_sparse_reference as reference
import check_tcp_gap_examples as gap_checks
import check_tcp_sparse_examples as sparse_checks


class CoverageTests(unittest.TestCase):
    def test_two_holes_keep_prefix_high_end_and_unique_count_separate(self):
        state = reference.Coverage().insert(600, b"d" * 200, 3).state
        state = state.insert(200, b"b" * 200, 5).state
        self.assertEqual((state.frontier, state.high_end, state.unique), (0, 800, 400))
        first = state.insert(0, b"a" * 200, 7)
        self.assertEqual((first.novel, first.source.id), (200, 2))
        self.assertEqual(
            (first.state.frontier, first.state.high_end, first.state.unique), (400, 800, 600)
        )
        final = first.state.insert(400, b"c" * 200, 9).state
        self.assertEqual((final.frontier, final.high_end, final.unique), (800, 800, 800))
        self.assertTrue(final.sparse_seen)

    def test_exact_contained_repeat_retains_the_first_source(self):
        payload = bytes(range(200))
        original = reference.Coverage().insert(600, payload, 3)
        repeated = original.state.insert(650, payload[50:90], 99)
        self.assertEqual((repeated.novel, repeated.offset), (0, 50))
        self.assertEqual(repeated.state, original.state)
        self.assertEqual(repeated.source, original.source)
        self.assertEqual((repeated.state.next_id, repeated.source.observation), (1, 3))

    def test_changed_and_mixed_overlap_have_explicit_scope_stops(self):
        state = reference.Coverage().insert(4, b"abcd", 3).state
        for start, payload, reason in ((5, b"XX", "conflict"), (2, b"1234", "overlap")):
            with self.subTest(start=start), self.assertRaisesRegex(reference.Scope, reason):
                state.insert(start, payload, 4)

    def test_all_four_span_orders_preserve_unique_first_byte_sources(self):
        for order in itertools.permutations(range(4)):
            state = reference.Coverage()
            for identity, span in enumerate(order):
                state = state.insert(span * 200, bytes([span]) * 200, identity + 3).state
            self.assertEqual((state.frontier, state.high_end, state.unique), (800, 800, 800))
            for position, cell in state.cells:
                source = state.sources[cell.receipt]
                self.assertEqual(source.payload[cell.payload_index], position // 200)
                self.assertEqual(source.start + cell.payload_index, position)
            self.assertEqual(state.sparse_seen, order != (0, 1, 2, 3))


class HeaderTests(unittest.TestCase):
    def lanes(self):
        sender = reference.Lane(100, 0, 0, 8, 199, 100, 800)
        peer = reference.Lane(200, 0, 0, 8, 99, 200, 1200)
        return sender, peer

    def segment(self, sequence, acknowledgment=200, payload=b"", window=8):
        return reference.wire.Segment(sequence, acknowledgment, 16, window=window, payload=payload)

    def test_new_data_uses_its_end_instead_of_unique_coverage(self):
        sender, peer = self.lanes()
        lanes, reason = reference.data_admission(sender, peer, self.segment(106, payload=b"ab"), 3)
        self.assertIsNone(reason)
        sender, peer = lanes
        lanes, reason = reference.data_admission(sender, peer, self.segment(102, payload=b"cd"), 4)
        self.assertIsNone(reason)
        self.assertEqual(
            (lanes[0].observed, lanes[0].high_end, lanes[0].coverage.unique), (0, 8, 4)
        )
        rejected, reason = reference.data_admission(*lanes, self.segment(108, payload=b"x"), 5)
        self.assertIsNone(rejected)
        self.assertEqual(reason, "window")

    def test_empty_ack_uses_the_bounded_epoch_without_adding_coverage(self):
        sender, peer = self.lanes()
        sender = replace(sender, coverage=reference.Coverage().insert(6, b"ab", 3).state)
        for sequence in (100, 103, 108):
            with self.subTest(sequence=sequence):
                lanes, reason = reference.data_admission(sender, peer, self.segment(sequence), 4)
                self.assertIsNone(reason)
                self.assertEqual(lanes[0].coverage, sender.coverage)
        for sequence in (99, 109):
            self.assertEqual(
                reference.data_admission(sender, peer, self.segment(sequence), 4)[1], "sequence"
            )

    def test_ack_cannot_use_high_end_to_cross_an_unobserved_hole(self):
        sender, peer = self.lanes()
        peer = replace(peer, coverage=reference.Coverage().insert(6, b"ab", 3).state)
        self.assertEqual(peer.high_end, 8)
        self.assertEqual(
            reference.data_admission(sender, peer, self.segment(100, 208), 4)[1], "acknowledgment"
        )
        coverage = peer.coverage.insert(0, b"abcd", 5).state
        peer = replace(peer, observed=coverage.frontier, coverage=coverage)
        self.assertIsNone(reference.data_admission(sender, peer, self.segment(100, 204), 6)[1])
        self.assertEqual(
            reference.data_admission(sender, peer, self.segment(100, 205), 6)[1], "acknowledgment"
        )

    def test_known_repeat_keeps_its_source_outside_a_shrunken_window(self):
        sender, peer = self.lanes()
        sender = replace(
            sender, coverage=reference.Coverage().insert(6, b"ab", 3).state, peer_window=0
        )
        lanes, reason = reference.data_admission(sender, peer, self.segment(106, payload=b"ab"), 4)
        self.assertIsNone(reason)
        self.assertEqual(lanes[0].coverage, sender.coverage)

    def test_lower_new_range_does_not_replace_a_newer_window_header(self):
        sender, peer = self.lanes()
        lanes, reason = reference.data_admission(
            sender, peer, self.segment(106, payload=b"ab", window=7), 3
        )
        self.assertIsNone(reason)
        after, reason = reference.data_admission(
            *lanes, self.segment(102, payload=b"cd", window=1), 4
        )
        self.assertIsNone(reason)
        self.assertEqual((after[1].peer_window, after[1].window_sequence), (7, 106))

    def test_old_ack_keeps_the_exact_65535_position_bound(self):
        sender, peer = self.lanes()
        coverage = reference.Coverage().insert(0, b"a" * 32768, 3).state
        coverage = coverage.insert(32768, b"b" * 32768, 5).state
        peer = replace(peer, coverage=coverage, observed=65536, acknowledged=65536)
        self.assertTrue(peer.valid)
        self.assertIsNone(reference.data_admission(sender, peer, self.segment(100, 201), 6)[1])
        self.assertEqual(
            reference.data_admission(sender, peer, self.segment(100, 200), 6)[1], "acknowledgment"
        )


class ActualCampusTests(unittest.TestCase):
    def test_actual_landmarks_keep_both_holes_through_exact_transfer(self):
        for filename, actor in (
            ("trace.json", "client"),
            ("reverse.json", "server"),
            ("wrap.json", "client"),
        ):
            with self.subTest(filename=filename):
                value = json.loads((reference.DIRECTORY / filename).read_text())
                report = reference.replay(value)
                self.assertTrue(report["supported"] and report["compliant"])
                self.assertEqual(len(report["steps"]), 81)
                gap_checks.audit(report, filename)
                direction = "original" if actor == "client" else "reply"
                installed = report["steps"][53]["state"]["gateways"]["standby"]["admission"][
                    direction
                ]
                self.assertEqual(
                    (
                        installed["observed"],
                        installed["coverage"]["highEnd"],
                        installed["coverage"]["uniqueBytes"],
                    ),
                    (0, 800, 400),
                )
                self.assertEqual(
                    len(bytes.fromhex(report["steps"][63]["reassembly"]["releasedHex"])), 400
                )
                self.assertEqual(report["steps"][68]["decision"]["acknowledged"], 400)
                self.assertEqual(len(bytes.fromhex(report["reads"][0]["readHex"])), 800)
                self.assertEqual(report["final"][actor]["recovery"]["flight"], 0)
                self.assertIsNone(report["final"][actor]["recovery"]["lastSample"])


class CorpusAndAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = reference.load_fixtures()
        cls.main = reference.replay(cls.data["input"])

    def test_all_campus_cases_keep_actual_sources_and_saved_results(self):
        for case in self.data["cases"]:
            with self.subTest(case=case["id"]):
                report = reference.replay(case["input"])
                self.assertEqual(reference.projection(report), case["expected"])
                sparse_checks.audit_campus(report, case["id"])

    def test_raw_cases_keep_checked_prehistory_and_selected_stops(self):
        for case in self.data["admissionCases"]:
            with self.subTest(case=case["id"]):
                report = reference.raw_replay(case["input"])
                self.assertEqual(report, case["expected"])
                for step in report["steps"]:
                    sparse_checks.audit_admission(step["after"]["admission"], case["id"])
                    if step["decision"]["kind"] == "unsupported":
                        self.assertEqual(step["before"], step["after"])

    def test_default_gap_driver_uses_sparse_admission_without_recursion(self):
        self.assertEqual(reference.gaps.replay(self.data["input"]), self.main)

    def test_one_old_gap_case_moves_with_its_actual_supported_continuation(self):
        old_id = "fresh-ingress-reordering-is-still-outside-gateway-profile"
        old = reference.gaps.load_fixtures()
        self.assertNotIn(old_id, {case["id"] for case in old["cases"]})
        moved = [case for case in self.data["cases"] if case.get("migratedFrom")]
        self.assertEqual(len(moved), 1)
        self.assertEqual(moved[0]["previousID"], old_id)
        report = reference.replay(moved[0]["input"])
        self.assertTrue(report["supported"] and report["compliant"])
        self.assertEqual(report["evaluatedEvents"], 37)

    def test_current_logoff_keeps_unseen_prefix_and_two_host_spans(self):
        case = next(
            case
            for case in self.data["cases"]
            if case["id"] == "current-logoff-denies-the-unseen-prefix"
        )
        report = reference.replay(case["input"])
        self.assertEqual(report["services"][-1]["disposition"], "earlyDrop")
        self.assertEqual(report["final"]["server"]["receiveStore"]["heldBytes"], 400)
        self.assertEqual(report["final"]["server"]["core"]["receivedHex"], "")

    def test_stale_cut_and_raw_input_errors_are_not_profile_stops(self):
        for case in self.data["inputErrors"]:
            with self.subTest(case=case["id"]), self.assertRaises(ValueError):
                reference.replay(case["input"])
        for case in self.data["admissionInputErrors"]:
            with self.subTest(case=case["id"]), self.assertRaises(ValueError):
                reference.raw_replay(case["input"])

    def test_greatest_end_cannot_supply_missing_prefix_coverage(self):
        report = copy.deepcopy(self.main)
        lane = report["steps"][53]["state"]["gateways"]["standby"]["admission"]["original"]
        lane["observed"] = lane["coverage"]["highEnd"]
        with self.assertRaises(AssertionError):
            sparse_checks.audit_campus(report, "invented covered hole")

    def test_original_source_metadata_cannot_be_replaced_by_a_repeat(self):
        report = copy.deepcopy(self.main)
        coverage = report["steps"][74]["state"]["gateways"]["standby"]["admission"]["original"][
            "coverage"
        ]
        coverage["runs"][0]["observationIndex"] = 9
        with self.assertRaises(AssertionError):
            sparse_checks.audit_campus(report, "changed first observation")

    def test_unique_coverage_cannot_count_a_known_repeat_again(self):
        case = next(
            case
            for case in self.data["admissionCases"]
            if case["id"] == "repeat-slice-retains-original-source"
        )
        report = reference.raw_replay(case["input"])
        admission = copy.deepcopy(report["final"]["admission"])
        admission["original"]["coverage"]["uniqueBytes"] += 50
        with self.assertRaises(AssertionError):
            sparse_checks.audit_admission(admission, "counted repeat bytes")

    def test_source_assurance_can_be_checked_with_archived_gateway_holes(self):
        assurance = reference.sparse_assurance(self.main)
        self.assertEqual(assurance["status"], "checked")
        primary, standby = assurance["gateways"]
        self.assertEqual(primary["gateway"], "primary")
        self.assertEqual(
            primary["original"],
            {
                "frontier": 0,
                "highEnd": 800,
                "uniqueBytes": 400,
                "sources": 2,
                "prefixComplete": False,
            },
        )
        self.assertEqual(
            standby["original"],
            {
                "frontier": 800,
                "highEnd": 800,
                "uniqueBytes": 800,
                "sources": 4,
                "prefixComplete": True,
            },
        )
        self.assertEqual(
            primary["reply"],
            {"frontier": 0, "highEnd": 0, "uniqueBytes": 0, "sources": 0, "prefixComplete": True},
        )

    def test_sparse_assurance_is_mandatory_and_has_no_pending_state(self):
        with self.assertRaises(AssertionError):
            sparse_checks.check_sparse_assurance(self.main, self.main, "missing source assurance")
        report = {**self.main, "sparseAssurance": reference.sparse_assurance(self.main)}
        sparse_checks.check_sparse_assurance(report, self.main, "actual source assurance")
        report["sparseAssurance"]["status"] = "pending"
        with self.assertRaises(AssertionError):
            sparse_checks.check_sparse_assurance(report, self.main, "packet-queue status")

    def test_stale_permit_cannot_claim_sparse_source_assurance(self):
        case = next(
            case
            for case in self.data["cases"]
            if case["id"] == "stale-permit-after-logoff-fails-sparse-source-assurance"
        )
        oracle = reference.replay(case["input"])
        assurance = reference.sparse_assurance(oracle)
        self.assertEqual(
            assurance,
            {
                "scope": "gateway-observation-sources",
                "status": "failed",
                "reason": "The actual joint replay is not compliant.",
            },
        )
        report = {**oracle, "sparseAssurance": reference.sparse_assurance(self.main)}
        with self.assertRaises(AssertionError):
            sparse_checks.check_sparse_assurance(report, oracle, "stale current permission")

    def test_no_sparse_history_has_no_assurance_object(self):
        case = reference.gaps.ack.load_fixtures()["cases"][0]
        oracle = reference.replay(case["input"])
        self.assertIsNone(reference.sparse_assurance(oracle))
        sparse_checks.check_sparse_assurance(oracle, oracle, "in-order gateway history")
        report = {**oracle, "sparseAssurance": {"status": "absent"}}
        with self.assertRaises(AssertionError):
            sparse_checks.check_sparse_assurance(report, oracle, "unexpected source assurance")


if __name__ == "__main__":
    unittest.main()
