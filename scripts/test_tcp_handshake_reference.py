"""Static tests for ordinary TCP startup and derived application state."""

import copy
import unittest
from dataclasses import replace

import tcp_handshake_reference as reference
import tcp_receive_reference as wire


class HandshakeTests(unittest.TestCase):
    def setUp(self):
        self.active = reference.Local(reference.Socket("192.0.2.1", 12345), 1000, 8, 8, 576)
        self.passive = reference.Local(reference.Socket("198.51.100.2", 80), 5000, 6, 8, 1500)
        self.syn = reference.control_output(self.active, self.passive.socket, 1000, 0, 2)
        self.syn_ack = reference.control_output(self.passive, self.active.socket, 5000, 1001, 18)
        self.ack = reference.control_output(self.active, self.passive.socket, 1001, 5001, 16)
        self.value = {
            "schema": 1,
            "active": self.active.to_dict(),
            "passive": self.passive.to_dict(),
            "events": [
                {
                    "kind": "activeOpen",
                    "remote": self.passive.socket.to_dict(),
                    "policyPermitted": True,
                },
                self.event("listenSyn", self.syn),
                self.event("synSentSynAck", self.syn_ack),
                self.event("synReceivedAck", self.ack),
            ],
        }

    def event(self, kind, output):
        result = {"kind": kind, "rawIPv4Hex": output["rawIPv4Hex"], "path": "direct"}
        if kind != "synReceivedAck":
            result["policyPermitted"] = True
        return result

    def packet_event(self, kind, sequence, acknowledgment, flags, **fields):
        outbound = (
            reference.header(self.passive.socket, self.active.socket)
            if kind == "synSentSynAck"
            else reference.header(self.active.socket, self.passive.socket)
        )
        raw = wire.fixture_packet(outbound, wire.Segment(sequence, acknowledgment, flags, **fields))
        result = {"kind": kind, "rawIPv4Hex": raw.hex(), "path": "direct"}
        if kind != "synReceivedAck":
            result["policyPermitted"] = True
        return result

    def test_ordinary_exchange_derives_empty_valid_application_states(self):
        report = reference.replay(self.value)
        self.assertTrue(report["supported"])
        self.assertTrue(report["exchangeComplete"])
        for role in ("activeSeed", "passiveSeed"):
            seed = reference.application.State.from_dict(report["final"][role])
            self.assertTrue(seed.valid)
            self.assertEqual((seed.pending, seed.core.sent, seed.core.received), (b"", b"", b""))

    def test_active_and_passive_establishment_times_differ(self):
        report = reference.replay(self.value)
        final = report["final"]
        self.assertEqual(final["activeEstablishedAt"], 2)
        self.assertEqual(final["passiveEstablishedAt"], 3)
        self.assertEqual(report["steps"][2]["state"]["activePhase"], "ESTABLISHED")
        self.assertEqual(report["steps"][2]["state"]["passivePhase"], "SYN-RECEIVED")
        self.assertIsNone(report["steps"][2]["state"]["passiveSeed"])

    def test_lost_final_ack_leaves_passive_seed_absent(self):
        value = copy.deepcopy(self.value)
        value["events"] = value["events"][:3]
        report = reference.replay(value)
        self.assertTrue(report["supported"])
        self.assertFalse(report["exchangeComplete"])
        self.assertIsNotNone(report["final"]["activeSeed"])
        self.assertIsNone(report["final"]["passiveSeed"])

    def test_control_positions_do_not_become_application_bytes(self):
        report = reference.replay(self.value)
        active = report["final"]["activeSeed"]
        passive = report["final"]["passiveSeed"]
        self.assertEqual((active["core"]["sendUna"], active["core"]["sendNext"]), (1001, 1001))
        self.assertEqual((passive["core"]["sendUna"], passive["core"]["sendNext"]), (5001, 5001))
        self.assertEqual(active["core"]["receiveNext"], passive["core"]["sendNext"])
        self.assertEqual(passive["core"]["receiveNext"], active["core"]["sendNext"])

    def test_peer_windows_and_history_use_the_selected_startup_inputs(self):
        final = reference.replay(self.value)["final"]
        active = final["activeSeed"]
        passive = final["passiveSeed"]
        self.assertEqual(
            (active["sendWindow"], active["sendWL1"], active["sendWL2"]), (6, 5000, 1001)
        )
        self.assertEqual(
            (passive["sendWindow"], passive["sendWL1"], passive["sendWL2"]), (8, 1001, 5001)
        )
        self.assertEqual(active["core"]["capacity"], 8)
        self.assertEqual(passive["core"]["capacity"], 6)

    def test_default_mss_comes_from_no_option_startup(self):
        final = reference.replay(self.value)["final"]
        self.assertEqual(final["activeSeed"]["effectiveMSS"], 536)
        self.assertEqual(final["passiveSeed"]["effectiveMSS"], 536)
        for output in (self.syn, self.syn_ack, self.ack):
            self.assertEqual(output["decoded"]["segment"]["optionsHex"], "")

    def test_local_ip_limit_can_reduce_default_mss(self):
        for limit, expected in ((41, 1), (42, 2), (575, 535), (576, 536), (65535, 536)):
            local = replace(self.active, ip_send_limit=limit)
            self.assertTrue(local.valid)
            self.assertEqual(local.effective_mss, expected)
            self.assertLessEqual(40 + local.effective_mss, limit)
        self.assertFalse(replace(self.active, ip_send_limit=40).valid)

    def test_directional_mss_uses_actual_syn_and_syn_ack(self):
        active = reference.Local.from_dict(
            {
                **self.active.to_dict(),
                "ipSendLimit": 1000,
                "receiveMSS": {"ipReceiveLimit": 1240, "value": 1200},
            }
        )
        passive = reference.Local.from_dict(
            {
                **self.passive.to_dict(),
                "ipSendLimit": 1500,
                "receiveMSS": {"ipReceiveLimit": 840, "value": 800},
            }
        )
        value = copy.deepcopy(self.value)
        value.update(active=active.to_dict(), passive=passive.to_dict())
        outputs = (
            reference.control_output(active, passive.socket, 1000, 0, 2),
            reference.control_output(passive, active.socket, 5000, 1001, 18),
            reference.control_output(active, passive.socket, 1001, 5001, 16),
        )
        for index, output in enumerate(outputs, 1):
            value["events"][index] = self.event(value["events"][index]["kind"], output)
        report = reference.replay(value)
        self.assertEqual(report["final"]["activeSeed"]["effectiveMSS"], 800)
        self.assertEqual(report["final"]["passiveSeed"]["effectiveMSS"], 1200)
        self.assertEqual([len(bytes.fromhex(o["rawIPv4Hex"])) for o in outputs], [44, 44, 40])
        self.assertEqual(outputs[0]["decoded"]["segment"]["mssValues"], [1200])
        self.assertEqual(outputs[1]["decoded"]["segment"]["mssValues"], [800])

    def test_positive_mss_receipt_still_requires_actual_output_options(self):
        value = copy.deepcopy(self.value)
        value["events"][1] = self.packet_event(
            "listenSyn", 1000, 0, 2, options=bytes.fromhex("02040320")
        )
        with self.assertRaises(ValueError):
            reference.replay(value)

    def test_receive_evidence_and_control_limit_have_separate_bounds(self):
        local = reference.Local.from_dict(
            {
                **self.active.to_dict(),
                "ipSendLimit": 44,
                "receiveMSS": {"ipReceiveLimit": 1240, "value": 1200},
            }
        )
        self.assertTrue(local.valid)
        self.assertEqual(local.send_mss(800), 4)
        self.assertFalse(replace(local, ip_send_limit=43).valid)
        self.assertTrue(replace(local, capacity=0).valid)
        for receive, value in ((575, 1), (65536, 1), (1240, 0), (1239, 1200)):
            self.assertFalse(replace(local, receive_mss=reference.ReceiveMSS(receive, value)).valid)

    def test_option_selection_keeps_absence_zero_and_duplicates_distinct(self):
        for options, expected in (
            ("", None),
            ("00000000", None),
            ("01010101", None),
            ("02040001", 1),
            ("010204ffff000000", 65535),
        ):
            self.assertEqual(reference.startup_mss(bytes.fromhex(options)), expected)
        for options in ("02040000", "0204032002040320", "02030000", "03030000"):
            with self.assertRaises(ValueError):
                reference.startup_mss(bytes.fromhex(options))

    def test_mss_fixtures_remain_independent(self):
        import check_tcp_mss_examples as comparison

        counts = comparison.check_static()
        self.assertGreater(counts["handshakes"], 15)
        self.assertGreater(counts["campus"], 5)

    def test_output_flags_fields_and_checksums_are_exact(self):
        for output, sequence, acknowledgment, flags, window in (
            (self.syn, 1000, 0, 2, 8),
            (self.syn_ack, 5000, 1001, 18, 6),
            (self.ack, 1001, 5001, 16, 8),
        ):
            raw = bytes.fromhex(output["rawIPv4Hex"])
            packet = wire.decode_packet(raw)
            self.assertEqual(len(raw), 40)
            self.assertEqual(packet.to_dict(), output["decoded"])
            self.assertEqual(
                (packet.segment.sequence, packet.segment.acknowledgment), (sequence, acknowledgment)
            )
            self.assertEqual((packet.segment.flags, packet.segment.window), (flags, window))
            self.assertEqual((packet.segment.reserved, packet.segment.urgent_pointer), (0, 0))
            self.assertEqual(
                (packet.segment.options, packet.segment.payload, packet.padding), (b"", b"", b"")
            )
            self.assertEqual((packet.tos, packet.identification, packet.ttl), (0, 0, 64))
            self.assertTrue(packet.dont_fragment)

    def test_computed_zero_control_checksum_is_not_omitted(self):
        output = reference.control_output(self.active, self.passive.socket, 0, 0, 2)
        zero_sequence = output["decoded"]["segment"]["checksum"]
        output = reference.control_output(self.active, self.passive.socket, zero_sequence, 0, 2)
        self.assertEqual(output["decoded"]["segment"]["checksum"], 0)
        wire.decode_packet(output["rawIPv4Hex"])
        changed = bytearray.fromhex(output["rawIPv4Hex"])
        changed[23] ^= 1
        with self.assertRaises(ValueError):
            wire.decode_packet(changed)

    def test_one_step_policy_rejection_can_retry_without_phase_change(self):
        for index in range(3):
            value = copy.deepcopy(self.value)
            rejected = {**value["events"][index], "policyPermitted": False}
            value["events"].insert(index, rejected)
            report = reference.replay(value)
            step = report["steps"][index]
            self.assertEqual(step["decision"], {"kind": "reject", "reason": "policy"})
            self.assertEqual(step["state"], step["before"])
            self.assertIsNone(step["output"])
            self.assertIsNone(step["delivery"])
            self.assertTrue(report["exchangeComplete"])

    def test_missing_earlier_open_stops_before_transport_decode(self):
        value = copy.deepcopy(self.value)
        value["events"] = [
            {"kind": "listenSyn", "rawIPv4Hex": "00", "path": "direct", "policyPermitted": True}
        ]
        report = reference.replay(value)
        self.assertFalse(report["supported"])
        self.assertEqual(report["steps"][0]["decision"], {"kind": "unsupported", "reason": "phase"})
        self.assertIsNone(report["steps"][0]["decodedInput"])
        self.assertIsNone(report["final"]["passiveSeed"])

    def test_wrong_ack_stops_without_an_assumed_established_seed(self):
        for index, event in (
            (2, self.packet_event("synSentSynAck", 5000, 1000, 18)),
            (3, self.packet_event("synReceivedAck", 1001, 5000, 16)),
        ):
            value = copy.deepcopy(self.value)
            value["events"][index] = event
            report = reference.replay(value)
            self.assertFalse(report["supported"])
            self.assertEqual(
                report["steps"][-1]["decision"], {"kind": "unsupported", "reason": "acknowledgment"}
            )
            self.assertEqual(report["steps"][-1]["state"], report["steps"][-1]["before"])

    def test_final_ack_sequence_is_tested_before_acknowledgment(self):
        value = copy.deepcopy(self.value)
        value["events"][3] = self.packet_event("synReceivedAck", 1000, 5000, 16)
        report = reference.replay(value)
        self.assertEqual(
            report["steps"][-1]["decision"], {"kind": "unsupported", "reason": "sequence"}
        )

    def test_simultaneous_open_and_syn_data_are_profile_limits(self):
        for event, reason in (
            (self.packet_event("synSentSynAck", 5000, 0, 2), "flags"),
            (self.packet_event("synSentSynAck", 5000, 1001, 18, payload=b"x"), "data"),
        ):
            value = copy.deepcopy(self.value)
            value["events"][2] = event
            report = reference.replay(value)
            self.assertEqual(
                report["steps"][-1]["decision"], {"kind": "unsupported", "reason": reason}
            )

    def test_profile_options_precede_data_and_flags(self):
        event = self.packet_event(
            "listenSyn", 1000, 0, 4, payload=b"x", options=bytes.fromhex("03030000")
        )
        value = copy.deepcopy(self.value)
        value["events"][1] = event
        report = reference.replay(value)
        self.assertEqual(
            report["steps"][-1]["decision"], {"kind": "unsupported", "reason": "options"}
        )

    def test_successful_receipt_needs_actual_earlier_output_bytes(self):
        value = copy.deepcopy(self.value)
        value["events"][1] = self.packet_event("listenSyn", 1001, 0, 2)
        with self.assertRaises(ValueError):
            reference.replay(value)

    def test_valid_final_ack_cannot_replace_the_actual_peer_output(self):
        value = copy.deepcopy(self.value)
        value["events"][3] = self.packet_event("synReceivedAck", 1001, 5001, 16, window=3)
        with self.assertRaises(ValueError):
            reference.replay(value)

    def test_passive_seed_window_calculation_uses_final_ack(self):
        initial_syn = wire.decode_packet(self.syn["rawIPv4Hex"])
        raw = wire.fixture_packet(
            reference.header(self.active.socket, self.passive.socket),
            wire.Segment(1001, 5001, 16, window=3),
        )
        final_ack = wire.decode_packet(raw)
        seed = reference.endpoint_seed(
            self.passive, self.active.socket, initial_syn.segment.sequence + 1, final_ack
        )
        self.assertEqual(seed.send_window, 3)
        self.assertNotEqual(seed.send_window, initial_syn.segment.window)

    def test_uppercase_events_report_canonical_bytes(self):
        value = copy.deepcopy(self.value)
        for event in value["events"][1:]:
            event["rawIPv4Hex"] = event["rawIPv4Hex"].upper()
        self.assertEqual(reference.replay(value), reference.replay(self.value))

    def test_unsupported_retains_canonical_unread_hex_without_decode(self):
        value = copy.deepcopy(self.value)
        value["events"][1] = self.packet_event("listenSyn", 1000, 0, 20)
        value["events"][2:] = [
            {
                "kind": "synSentSynAck",
                "rawIPv4Hex": "ABCD",
                "path": "direct",
                "policyPermitted": True,
            }
        ]
        report = reference.replay(value)
        self.assertEqual(report["evaluatedEvents"], 2)
        self.assertEqual(report["remainingEvents"][0]["rawIPv4Hex"], "abcd")

    def test_bad_hex_after_unsupported_is_still_an_input_error(self):
        value = copy.deepcopy(self.value)
        value["events"][1] = self.packet_event("listenSyn", 1000, 0, 20)
        value["events"][2]["rawIPv4Hex"] = "gg"
        with self.assertRaises(ValueError):
            reference.replay(value)

    def test_static_fixtures_match_all_results(self):
        counts = reference.check_fixtures(reference.load_fixtures())
        self.assertGreater(counts["traces"], 30)
        self.assertGreater(counts["errors"], 5)

    def test_changed_fixture_expectation_is_detected(self):
        data = copy.deepcopy(reference.load_fixtures())
        data["traces"][0]["expected"]["exchangeComplete"] = False
        with self.assertRaises(AssertionError):
            reference.check_fixtures(data)


if __name__ == "__main__":
    unittest.main()
