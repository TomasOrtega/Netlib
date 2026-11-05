"""Static regressions for the selected TCP checkpoint and planned transfer."""

import copy
import json
import unittest
from dataclasses import replace

import campus_tcp_transfer_reference as reference
import check_campus_tcp_examples as byte_comparison
import check_campus_tcp_transfer_examples as transfer_comparison


class ComponentTests(unittest.TestCase):
    def setUp(self):
        self.initial = reference.Image()
        config = next(row for row in reference.base.load("configs") if row["id"] == "permit")
        routing = reference.base.load("routing")
        h = reference.base.handshake
        client = h.Local(h.Socket("192.0.2.2", 41000), 1000, 8, 16, 576)
        server = h.Local(h.Socket("198.51.100.2", 9000), 5000, 8, 16, 576)
        packets = [
            h.control_output(client, h.Socket("203.0.113.2", 8080), 1000, 0, 2),
            h.control_output(server, h.Socket("203.0.113.1", 40000), 5000, 1001, 18),
            h.control_output(client, h.Socket("203.0.113.2", 8080), 1001, 5001, 16),
        ]
        records, admission = (), reference.base.Admission()
        for output in packets:
            raw = output["rawIPv4Hex"]
            packet = reference.base.wire.decode_packet(raw)
            _, record, direction, fresh = reference.base.attachment(records, config, packet.header)
            if fresh:
                record = reference.tracked_candidate(record, config)
            candidate, reason = reference.base.admit(admission, record, direction, fresh, raw)
            self.assertIsNone(reason)
            result = reference.base.forward(records, routing, config, raw)
            records = tuple(record if fresh else row for row in result.records)
            admission, reason = reference.base.commit_admission(candidate, record, fresh, records)
            self.assertIsNone(reason)
        self.source = reference.Image(records, admission, 3)
        self.transfer = reference.Transfer(paused=True)
        self.transfer.control({"kind": "stageCheckpoint"}, 10, self.source, self.initial, False)

    def test_cache_is_an_immutable_actual_source_cut(self):
        self.assertEqual(self.transfer.cache.staged_at, 10)
        self.assertEqual(self.transfer.cache.image, self.source)
        later = replace(self.source, transitions=4)
        self.assertEqual(self.transfer.cache.image.transitions, 3)
        with self.assertRaisesRegex(ValueError, "stale"):
            self.transfer.control({"kind": "installCheckpoint"}, 11, later, self.initial, False)

    def test_a_changed_transition_cut_invalidates_the_same_transport_pair(self):
        processed_drop = replace(self.source, transitions=4)
        with self.assertRaisesRegex(ValueError, "stale"):
            self.transfer.control(
                {"kind": "installCheckpoint"}, 12, processed_drop, self.initial, False
            )

    def test_a_changed_mss_offer_invalidates_the_exact_source_image(self):
        changed = replace(
            self.source,
            admission=replace(
                self.source.admission,
                server_mss=800,
                original=replace(self.source.admission.original, peer_mss=800),
            ),
        )
        with self.assertRaisesRegex(ValueError, "stale"):
            self.transfer.control({"kind": "installCheckpoint"}, 11, changed, self.initial, False)
        self.assertEqual(self.transfer.cache.image.admission.server_mss, None)

    def test_present_default_is_distinct_from_absent_in_the_checkpoint(self):
        absent = self.source.admission
        present = replace(absent, server_mss=536, original=replace(absent.original, peer_mss=536))
        self.assertEqual(absent.original.data_limit, present.original.data_limit)
        self.assertNotEqual(absent, present)
        with self.assertRaisesRegex(ValueError, "stale"):
            self.transfer.control(
                {"kind": "installCheckpoint"},
                11,
                replace(self.source, admission=present),
                self.initial,
                False,
            )

    def test_policy_changes_and_early_drop_do_not_change_the_transport_cut(self):
        _, installed = self.transfer.control(
            {"kind": "installCheckpoint"}, 12, self.source, self.initial, False
        )
        self.assertEqual(installed, self.source)
        self.assertTrue(self.transfer.sealed)

    def test_install_requires_paused_assignments_and_no_actual_primary_ticket(self):
        self.transfer.paused = False
        with self.assertRaisesRegex(ValueError, "Pause"):
            self.transfer.control(
                {"kind": "installCheckpoint"}, 11, self.source, self.initial, False
            )
        self.transfer.paused = True
        with self.assertRaisesRegex(ValueError, "pending"):
            self.transfer.control(
                {"kind": "installCheckpoint"}, 11, self.source, self.initial, True
            )

    def test_target_collision_and_source_replacement_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "target is not empty"):
            self.transfer.control(
                {"kind": "installCheckpoint"},
                11,
                self.source,
                self.source,
                False,
            )
        replaced = replace(
            self.source, admission=reference.base.Admission(phase="syn", client_iss=9)
        )
        with self.assertRaisesRegex(ValueError, "stale"):
            self.transfer.control({"kind": "installCheckpoint"}, 11, replaced, self.initial, False)

    def test_each_owner_must_move_before_fence_and_resume(self):
        self.transfer.control({"kind": "installCheckpoint"}, 11, self.source, self.initial, False)
        self.transfer.control(
            {"kind": "switchRoute", "actor": "client", "gateway": "standby"},
            12,
            self.source,
            self.source,
            False,
        )
        with self.assertRaisesRegex(ValueError, "two owners"):
            self.transfer.control({"kind": "fencePrimary"}, 13, self.source, self.source, False)
        with self.assertRaisesRegex(ValueError, "Resume"):
            self.transfer.control({"kind": "resume"}, 13, self.source, self.source, False)
        self.transfer.control(
            {"kind": "switchRoute", "actor": "server", "gateway": "standby"},
            14,
            self.source,
            self.source,
            False,
        )
        self.transfer.control({"kind": "fencePrimary"}, 15, self.source, self.source, False)
        self.transfer.control({"kind": "resume"}, 16, self.source, self.source, False)
        self.assertFalse(self.transfer.paused)
        self.assertTrue(self.transfer.fenced)

    def test_capture_requires_data_phase_and_its_exact_confirmed_entry(self):
        transfer = reference.Transfer()
        with self.assertRaisesRegex(ValueError, "established TCP history"):
            transfer.control({"kind": "stageCheckpoint"}, 1, self.initial, self.initial, False)
        with self.assertRaisesRegex(ValueError, "confirmed source entry"):
            transfer.control(
                {"kind": "stageCheckpoint"},
                1,
                replace(self.source, records=()),
                self.initial,
                False,
            )

    def test_an_entry_only_copy_cannot_supply_existing_tcp_admission(self):
        raw = self.source.admission.observations[-1][1].hex()
        _state, reason = reference.base.admit(
            reference.base.Admission(), self.source.records[0], "original", False, raw
        )
        self.assertEqual(reason, "missingHistory")


class TraceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.value = json.loads((reference.DIRECTORY / "trace.json").read_text())

    def test_full_continuation_reads_span_primary_and_standby(self):
        report = reference.replay(self.value)
        self.assertTrue(report["supported"])
        self.assertTrue(report["compliant"])
        self.assertEqual(
            [(row["actor"], row["readHex"]) for row in report["reads"]],
            [("server", "616263646566"), ("client", "78797a77")],
        )
        self.assertEqual(
            [row["gateway"] for row in report["services"]], ["primary"] * 6 + ["standby"] * 4
        )
        byte_comparison.audit_bytes(report, "planned transfer")

    def test_capture_and_install_keep_a_nonzero_unacknowledged_peer_epoch(self):
        report = reference.replay(self.value)
        installed = next(
            row for row in report["steps"] if row["event"]["kind"] == "installCheckpoint"
        )
        state = installed["state"]
        self.assertEqual(state["gateways"]["primary"]["historyTransitions"], 6)
        self.assertEqual(state["gateways"]["primary"], state["gateways"]["standby"])
        reply = state["gateways"]["standby"]["admission"]["reply"]
        self.assertEqual((reply["observed"], reply["acknowledged"]), (3, 0))
        received = next(row for row in report["steps"] if row["event"].get("service") == 6)
        self.assertEqual(received["decision"]["acknowledged"], 3)
        self.assertEqual(received["state"]["server"]["core"]["sentHex"], "")

    def test_standby_updates_do_not_mutate_the_sealed_primary_or_cache(self):
        report = reference.replay(self.value)
        primary = report["final"]["gateways"]["primary"]
        standby = report["final"]["gateways"]["standby"]
        self.assertEqual(primary["historyTransitions"], 6)
        self.assertEqual(standby["historyTransitions"], 9)
        self.assertEqual(primary["admission"]["reply"]["observed"], 3)
        self.assertEqual(standby["admission"]["reply"]["observed"], 4)
        self.assertEqual(report["final"]["transfer"]["cache"]["admission"], primary["admission"])

    def test_current_standby_denial_preserves_cached_transport_state(self):
        report = reference.replay(self.value)
        last = report["steps"][-1]
        self.assertEqual(last["service"]["disposition"], "earlyDrop")
        self.assertIsNone(last["service"]["output"])
        self.assertEqual(
            last["before"]["gateways"]["standby"], last["state"]["gateways"]["standby"]
        )
        self.assertEqual(
            report["final"]["transfer"]["owners"], {"client": "standby", "server": "standby"}
        )
        self.assertTrue(report["final"]["transfer"]["primarySealed"])
        self.assertTrue(report["final"]["transfer"]["primaryFenced"])

    def test_stale_allow_on_standby_preserves_the_actual_emission(self):
        value = copy.deepcopy(self.value)
        value["events"] = [
            event
            for event in value["events"]
            if not (
                event["kind"] in ("install", "installGuard")
                and event.get("gateway") == "standby"
                and (event.get("configuration") == "deny" or event.get("guard") == "deny")
            )
        ]
        report = reference.replay(value)
        self.assertTrue(report["supported"])
        self.assertFalse(report["compliant"])
        last = report["services"][-1]
        self.assertEqual(last["gateway"], "standby")
        self.assertFalse(last["checks"]["forward"])
        self.assertFalse(last["checks"]["ingress"])
        self.assertEqual(last["output"]["decoded"]["segment"]["payloadHex"], "676869")

    def test_install_cannot_use_wrong_target_namespace_lifetime(self):
        value = copy.deepcopy(self.value)
        next(event for event in value["events"] if event["kind"] == "installCheckpoint")[
            "namespace"
        ]["birth"] = 2
        with self.assertRaisesRegex(ValueError, "namespace lifetime"):
            reference.replay(value)

    def test_cached_cut_before_the_actual_drain_is_stale(self):
        value = copy.deepcopy(self.value)
        checkpoint = [
            index
            for index, event in enumerate(value["events"])
            if event["kind"] == "stageCheckpoint"
        ][-1]
        del value["events"][checkpoint]
        with self.assertRaisesRegex(ValueError, "stale"):
            reference.replay(value)

    def test_assigning_during_pause_cannot_change_ticket_gateway(self):
        value = copy.deepcopy(self.value)
        pause = next(
            index for index, event in enumerate(value["events"]) if event["kind"] == "pause"
        )
        value["events"] = value["events"][: pause + 1] + [copy.deepcopy(value["events"][37])]
        with self.assertRaisesRegex(ValueError, "Assignments are paused"):
            reference.replay(value)

    def test_old_schema_delegates_without_any_added_projection(self):
        old = json.loads(reference.base.FIXTURES.read_text())
        for case in old["cases"]:
            with self.subTest(case=case["id"]):
                self.assertEqual(
                    reference.replay(case["input"]), reference.base.replay(case["input"])
                )

    def test_frozen_new_expectations_and_actual_gateway_ancestry(self):
        for case in reference.load_fixtures()["cases"]:
            with self.subTest(case=case["id"]):
                report = reference.replay(case["input"])
                self.assertEqual(reference.projection(report), case["expected"])
                transfer_comparison.audit_transfer(report, case["id"])

    def test_partial_transfer_prefixes_remain_pending(self):
        data = reference.load_fixtures()
        pending = {
            "cached-before-queued-primary-drain",
            "drained-and-restaged-before-install",
            "installed-with-primary-owners",
            "installed-with-one-owner-away",
            "two-owners-away-before-fence",
            "fenced-before-resume",
        }
        for case in data["cases"]:
            if case["id"] in pending:
                with self.subTest(case=case["id"]):
                    self.assertEqual(
                        transfer_comparison.expected_transfer(reference.replay(case["input"])),
                        {"status": "pending"},
                    )

    def test_final_stage_can_precede_pause_without_changing_the_cut(self):
        case = next(
            case
            for case in reference.load_fixtures()["cases"]
            if case["id"] == "final-checkpoint-staged-before-assignment-pause"
        )
        report = reference.replay(case["input"])
        self.assertEqual(
            report["final"]["transfer"]["installation"],
            {"index": 43, "checkpoint": 1, "stagedAt": 41, "historyTransitions": 6},
        )
        status = transfer_comparison.expected_transfer(report)
        self.assertEqual(status["status"], "checked")
        self.assertEqual(
            (status["pausedAt"], status["stagedAt"], status["installedAt"]), (42, 41, 43)
        )
        self.assertTrue(status["sourcePreserved"])

    def test_checked_status_fields_come_from_actual_controls_and_source_cut(self):
        report = reference.replay(self.value)
        self.assertEqual(
            transfer_comparison.expected_transfer(report),
            {
                "status": "checked",
                "pausedAt": 38,
                "stagedAt": 42,
                "installedAt": 43,
                "clientRouteAt": 44,
                "serverRouteAt": 45,
                "fencedAt": 46,
                "resumedAt": 47,
                "historyTransitions": 6,
                "sourcePreserved": True,
            },
        )
        report["final"]["gateways"]["primary"]["historyTransitions"] += 1
        self.assertEqual(transfer_comparison.expected_transfer(report), {"status": "failed"})

    def test_checked_transfer_does_not_assume_nonempty_application_reads(self):
        case = next(
            case
            for case in reference.load_fixtures()["cases"]
            if case["id"] == "resumed-with-empty-read-ledgers"
        )
        report = reference.replay(case["input"])
        self.assertEqual(transfer_comparison.expected_transfer(report)["status"], "checked")
        self.assertEqual(report["reads"], [])


if __name__ == "__main__":
    unittest.main()
