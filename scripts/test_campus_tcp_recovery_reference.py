"""Independent tests for bounded recovery and actual campus packet histories."""

import unittest
from dataclasses import replace
from fractions import Fraction

import campus_tcp_recovery_reference as reference
import check_tcp_recovery_examples as comparison


class TimerTests(unittest.TestCase):
    def test_retry_preserves_unique_frontier_and_karn_estimate(self):
        initial = reference.Recovery.initial(800)
        first = initial.advance(100).sent(800)
        learned = first.advance(356).acknowledge(800)
        self.assertEqual((learned.srtt, learned.variance, learned.rto), (256, 128, 1000))
        sent = learned.advance(1400).sent(800)
        retry = sent.advance(2400).timeout()[1]
        self.assertEqual(
            (retry.frontier, retry.flight, retry.rto, retry.deadline), (1600, 800, 2000, 4400)
        )
        repeated = retry.advance(4400).timeout()[1]
        self.assertEqual(repeated.ssthresh, retry.ssthresh)
        acknowledged = repeated.advance(4450).acknowledge(800)
        self.assertEqual(
            (acknowledged.srtt, acknowledged.variance, acknowledged.rto), (256, 128, 4000)
        )
        self.assertIsNone(acknowledged.deadline)

    def test_partial_ack_clips_bytes_and_preserves_original_identity(self):
        sent = reference.Recovery.initial(800).sent(800)
        clipped = sent.advance(100).acknowledge(300)
        self.assertEqual((clipped.outstanding[0].start, clipped.outstanding[0].count), (300, 500))
        self.assertEqual(clipped.outstanding[0].id, sent.outstanding[0].id)
        self.assertIsNone(clipped.srtt)
        self.assertEqual(clipped.deadline, 1100)

    def test_early_idle_and_excessive_retries_have_distinct_results(self):
        initial = reference.Recovery.initial(1200)
        with self.assertRaisesRegex(reference.Stop, "idle"):
            initial.timeout()
        sent = initial.sent(1200)
        with self.assertRaisesRegex(reference.Stop, "early"):
            sent.advance(999).timeout()
        one = sent.advance(1000).timeout()[1]
        two = one.advance(3000).timeout()[1]
        with self.assertRaisesRegex(reference.Stop, "failureHandling"):
            two.advance(7000).timeout()

    def test_exact_fraction_update_uses_old_smoothed_rtt(self):
        initial = reference.Recovery.initial(800).sent(800).advance(256).acknowledge(800)
        later = initial.advance(1000).sent(800).advance(1300).acknowledge(800)
        self.assertEqual(later.srtt, Fraction(523, 2))
        self.assertEqual(later.variance, 107)
        self.assertEqual(later.rto, 1000)
        self.assertEqual(replace(later, rto=8000).acknowledge(0).rto, 8000)

    def test_final_interval_rounds_up_above_the_floor(self):
        initial = reference.Recovery.initial(800).sent(800).advance(1200).acknowledge(800)
        later = initial.advance(2000).sent(800).advance(3601).acknowledge(800)
        self.assertEqual((later.srtt, later.variance), (Fraction(10001, 8), Fraction(2201, 4)))
        self.assertEqual(later.rto, 3452)

    def test_partial_ack_after_retry_keeps_karn_ambiguity(self):
        sent = reference.Recovery.initial(800).sent(800).advance(1000).timeout()[1]
        partial = sent.advance(1200).acknowledge(300)
        self.assertTrue(partial.outstanding[0].retried)
        self.assertEqual((partial.flight, partial.rto, partial.deadline), (500, 2000, 3200))
        self.assertIsNone(partial.last_sample)


class CampusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = reference.load_fixtures()
        cls.report = reference.replay(cls.data["input"])

    def step(self, label):
        return self.report["steps"][self.data["labels"][label]]

    def test_all_static_expectations_and_attempt_ranges(self):
        for case in self.data["cases"]:
            with self.subTest(case=case["id"]):
                report = reference.replay(case["input"])
                self.assertEqual(reference.projection(report), case["expected"])
                comparison.audit(report, case["id"])

    def test_parser_error_fixtures_retain_their_typed_mutations(self):
        case = next(row for row in self.data["inputErrors"] if row["id"] == "timeout-policy-type")
        value = case["input"]["events"][80]["policyPermitted"]
        with self.subTest(check="numeric policy is distinct from Boolean true"):
            self.assertIs(type(value), int)
            self.assertEqual(value, 1)
        for row in self.data["inputErrors"]:
            with self.subTest(case=row["id"]):
                self.assertTrue(row.get("replacements"), "An error fixture must mutate its input.")
        with self.subTest(check="independent strict policy parsing"):
            with self.assertRaisesRegex(ValueError, "Boolean"):
                reference.replay(case["input"])

    def test_duplex_loss_recovery_reads_each_unique_range_once(self):
        self.assertTrue(self.report["supported"] and self.report["compliant"])
        self.assertEqual(self.report["evaluatedEvents"], 171)
        self.assertEqual(len(self.report["outputs"]), 23)
        self.assertEqual(
            [(row["actor"], len(row["readHex"]) // 2) for row in self.report["reads"]],
            [("server", 2400), ("client", 3600)],
        )
        self.assertEqual(self.report["final"]["client"]["recovery"]["frontier"], 3200)
        self.assertEqual(self.report["final"]["server"]["recovery"]["frontier"], 3600)

    def test_retries_have_distinct_origins_even_when_wire_bytes_are_equal(self):
        outputs = self.report["outputs"]
        self.assertEqual(outputs[7]["rawIPv4Hex"], outputs[9]["rawIPv4Hex"])
        self.assertNotEqual(outputs[7]["attempt"]["kind"], outputs[9]["attempt"]["kind"])
        self.assertEqual(outputs[7]["attempt"]["originalID"], outputs[9]["attempt"]["originalID"])
        self.assertNotEqual(outputs[8]["rawIPv4Hex"], outputs[13]["rawIPv4Hex"])
        self.assertEqual(outputs[8]["attempt"]["start"], outputs[13]["attempt"]["start"])

    def test_copied_range_can_repeat_after_gateway_acknowledgment(self):
        step = self.step("service-11")
        before = step["before"]["gateways"]["standby"]["admission"]
        after = step["state"]["gateways"]["standby"]["admission"]
        self.assertEqual(before["original"]["acknowledged"], 1600)
        self.assertEqual(after["original"]["observed"], before["original"]["observed"])
        self.assertEqual(after["observations"], before["observations"] + 1)
        for label in ("receipt-11", "receipt-15"):
            self.assertEqual(
                self.step(label)["decision"], {"kind": "reject", "reason": "input.sequence"}
            )

    def test_transfer_preserves_endpoint_timers_and_full_range_history(self):
        installed = self.step("install")
        for actor in ("client", "server"):
            self.assertEqual(installed["before"][actor], installed["state"][actor])
        self.assertEqual(installed["state"]["transfer"]["installation"]["historyTransitions"], 9)
        self.assertEqual(self.report["final"]["gateways"]["primary"]["historyTransitions"], 9)
        self.assertEqual(self.report["final"]["gateways"]["standby"]["historyTransitions"], 22)

    def test_karn_retains_estimate_until_a_fresh_actual_ack(self):
        for actor, label, expected in (
            ("client", "ack-client-recovery", 4000),
            ("server", "ack-server-recovery", 10752),
        ):
            recovery = self.step(label)["state"][actor]["recovery"]
            self.assertEqual(recovery["rto"], expected)
            self.assertEqual(recovery["lastSample"]["id"], 0)
            self.assertIsNone(recovery["deadline"])
        final = self.report["final"]
        self.assertEqual(
            final["client"]["recovery"]["estimator"]["variance"], {"num": 96, "den": 1}
        )
        self.assertEqual(
            final["server"]["recovery"]["estimator"]["variance"], {"num": 336, "den": 1}
        )

    def test_long_rtt_samples_use_network_delay_after_ack_emission(self):
        outputs = self.report["outputs"]
        self.assertEqual(outputs[6]["attempt"]["clockMillis"], 400)
        self.assertEqual(self.report["steps"][52]["before"]["server"]["recovery"]["now"], 1296)
        self.assertEqual(outputs[20]["attempt"]["clockMillis"], 10300)
        self.assertEqual(self.report["steps"][154]["before"]["server"]["recovery"]["now"], 11196)
        self.assertLess(outputs[6]["index"], self.report["steps"][52]["index"])

    def test_denial_blocks_queued_retry_without_erasing_received_bytes(self):
        last = self.report["services"][-1]
        self.assertEqual((last["sourceKind"], last["disposition"]), ("retry", "earlyDrop"))
        self.assertIsNone(last["output"])
        self.assertTrue(self.report["final"]["gateways"]["standby"]["records"])
        client = self.report["final"]["client"]["recovery"]
        self.assertEqual((client["flight"], client["rto"], client["deadline"]), (800, 2000, 14250))

    def test_duplicate_ack_uses_last_incoming_window_after_a_stale_ack(self):
        seed = reference.wrap(
            reference.application.State.from_dict(self.report["steps"][24]["state"]["client"])
        )
        state = reference.evaluate(seed, {"kind": "enableRecovery"}).state
        state = reference.evaluate(state, {"kind": "write", "payloadHex": "61626364"}).state
        state = reference.evaluate(
            state, {"kind": "send", "count": 4, "policyPermitted": True}
        ).state

        def incoming(before, acknowledgment, window):
            packet = reference.wire.fixture_packet(
                before.core.inbound,
                reference.wire.Segment(before.core.receive_next, acknowledgment, 16, window=window),
            )
            return reference.evaluate(before, {"kind": "receive", "rawIPv4Hex": packet.hex()})

        state = incoming(state, (state.core.send_una + 2) % reference.wire.MODULUS, 4096).state
        stale = incoming(state, (state.core.send_una - 1) % reference.wire.MODULUS, 4000).state
        self.assertEqual(stale.send_window, 4096)
        self.assertEqual(stale.to_dict().get("lastAckWindow"), 4000)
        counted = incoming(stale, stale.core.send_una, 4000).state
        self.assertEqual(counted.recovery.duplicate_acks, 1)
        not_counted = incoming(stale, stale.core.send_una, 4096).state
        self.assertEqual(not_counted.recovery.duplicate_acks, 0)
        self.assertEqual(counted.recovery.deadline, stale.recovery.deadline)

    def test_later_denial_preserves_buffers_and_stale_allow_preserves_actual_output(self):
        cases = {case["id"]: case for case in self.data["cases"]}
        buffered = reference.replay(cases["buffered-recovery-reads-after-logoff"]["input"])
        logoff = next(
            row["index"]
            for row in buffered["steps"]
            if row["event"] == {"kind": "authentication", "index": 7}
        )
        self.assertTrue(all(row["index"] > logoff for row in buffered["reads"]))
        self.assertEqual([len(row["readHex"]) // 2 for row in buffered["reads"]], [2400, 3600])
        stale = reference.replay(cases["stale-allow-retains-actual-retry-output"]["input"])
        service = stale["services"][-1]
        self.assertTrue(stale["supported"])
        self.assertFalse(stale["compliant"])
        self.assertEqual(service["disposition"], "forwarded")
        self.assertFalse(service["checks"]["forward"] or service["checks"]["ingress"])
        self.assertEqual(len(service["output"]["decoded"]["segment"]["payloadHex"]) // 2, 800)


if __name__ == "__main__":
    unittest.main()
