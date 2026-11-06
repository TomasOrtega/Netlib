"""Check packet creation, copies, and one-use link resolution."""

import copy
import unittest

import campus_tcp_custody_reference as reference
import check_campus_tcp_examples as checks

Custody = reference.Custody


class CustodyTests(unittest.TestCase):
    def test_pending_is_not_loss(self):
        state = Custody()
        state.mint("ingress", 0, "abcd")
        self.assertEqual(state.snapshot()["pending"], [0])
        self.assertEqual(state.snapshot()["resolved"], [])

    def test_resolve_once(self):
        state = Custody()
        state.mint("ingress", 0, "abcd")
        state.consume("ingress", 0, "assigned")
        with self.assertRaisesRegex(ValueError, "No pending ingress"):
            state.consume("ingress", 0, "assigned")
        with self.assertRaisesRegex(ValueError, "not pending"):
            state.resolve(0, "dropped")

    def test_copy_keeps_actual_historical_source(self):
        state = Custody()
        first = state.mint("link", 4, "abcd")
        state.resolve(first.id, "delivered")
        second = state.copy(first.id)
        self.assertEqual((second.id, second.parent, second.raw), (1, 0, "abcd"))
        self.assertEqual((second.stage, second.source), ("link", 4))
        state.consume("link", 4, "delivered")
        self.assertEqual(state.snapshot()["copies"], 1)
        self.assertEqual(state.snapshot()["pending"], [])

    def test_only_actual_sources_can_be_copied(self):
        state = Custody()
        for identity in (-1, 0, True):
            with self.assertRaisesRegex(ValueError, "does not exist"):
                state.copy(identity)

    def test_drop_consumes_only_selected_identity(self):
        state = Custody()
        state.mint("ingress", 0, "aa")
        state.mint("link", 1, "bb")
        state.resolve(1, "dropped")
        self.assertEqual(state.snapshot()["pending"], [0])
        self.assertEqual(state.snapshot()["resolved"], [{"packet": 1, "kind": "dropped"}])
        with self.assertRaisesRegex(ValueError, "not pending"):
            state.resolve(7, "dropped")

    def test_consume_selects_oldest_live_copy(self):
        state = Custody()
        state.mint("link", 1, "bb")
        state.copy(0)
        state.copy(1)
        self.assertEqual(state.consume("link", 1, "delivered").id, 0)
        self.assertEqual(state.consume("link", 1, "delivered").id, 1)
        self.assertEqual(state.consume("link", 1, "delivered").id, 2)


class CampusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = reference.load_fixtures()
        cls.report = reference.replay(cls.data["input"])

    def test_frozen_independent_expectations(self):
        for case in self.data["cases"]:
            with self.subTest(case=case["id"]):
                report = reference.replay(case["input"])
                self.assertEqual(reference.projection(report), case["expected"])
                checks.audit_custody(report, case["id"])

    def test_actual_data_and_ack_drops_have_real_packet_sources(self):
        report = self.report
        dropped = [
            row["packet"]
            for row in report["final"]["custody"]["resolved"]
            if row["kind"] == "dropped"
        ]
        self.assertEqual(dropped, [15, 17, 21, 29])
        self.assertEqual(report["final"]["custody"]["pending"], [43])
        for identity, size in ((15, 800), (17, 1200), (21, 0), (29, 0)):
            packet = report["packets"][identity]
            service = report["services"][packet["source"]]
            self.assertEqual(packet["stage"], "link")
            self.assertEqual(packet["rawIPv4Hex"], service["output"]["rawIPv4Hex"])
            self.assertEqual(len(bytes.fromhex(packet["rawIPv4Hex"])) - 40, size)

    def test_current_policy_denial_creates_no_link_or_loss(self):
        service = self.report["services"][-1]
        self.assertIsNone(service["output"])
        self.assertFalse(
            any(
                packet["stage"] == "link" and packet["source"] == service["id"]
                for packet in self.report["packets"]
            )
        )
        self.assertEqual(self.report["custodyAssurance"]["dropped"], 4)

    def test_pending_cannot_be_reported_as_drop(self):
        report = copy.deepcopy(self.report)
        report["custodyAssurance"]["dropped"] += 1
        with self.assertRaises(AssertionError):
            checks.audit_custody(report, "invented loss")

    def test_copy_cannot_replace_bytes_or_parent(self):
        case = next(row for row in self.data["cases"] if row["id"] == "historical-link-copy-chain")
        for key, replacement in (("rawIPv4Hex", "00"), ("parent", 999)):
            report = reference.replay(case["input"])
            report["packets"][-1][key] = replacement
            with self.subTest(field=key), self.assertRaises(AssertionError):
                checks.audit_custody(report, "changed copy source")

    def test_resolved_identity_cannot_be_used_twice(self):
        for name in (
            "assigned-output-needs-explicit-copy",
            "delivered-link-needs-explicit-copy",
            "absent-drop",
            "assigned-packet-cannot-be-dropped",
            "drop-is-one-use",
            "copy-needs-actual-source",
        ):
            case = next(row for row in self.data["inputErrors"] if row["id"] == name)
            with self.subTest(case=name), self.assertRaises(ValueError):
                reference.replay(case["input"])


if __name__ == "__main__":
    unittest.main()
