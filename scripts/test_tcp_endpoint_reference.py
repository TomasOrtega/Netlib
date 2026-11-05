"""Static tests for the selected TCP application path."""

import copy
import unittest
from dataclasses import replace

import tcp_endpoint_reference as reference
import tcp_receive_reference as wire


class EndpointTests(unittest.TestCase):
    def setUp(self):
        self.seed = reference.State(
            wire.State(
                wire.Header("192.0.2.1", "198.51.100.2", 6, 12345, 80),
                100,
                8,
                b"xy",
                1000,
                1006,
                b"abcdef",
            ),
            b"ghi",
            8,
            10,
            100,
            1000,
            536,
            576,
        )

    def event(self, sequence=100, acknowledgment=1000, **fields):
        segment = wire.Segment(sequence, acknowledgment, **fields)
        raw = wire.fixture_packet(self.seed.core.inbound, segment)
        return {"kind": "receive", "rawIPv4Hex": raw.hex()}

    def run_event(self, event, state=None):
        return reference.evaluate(self.seed if state is None else state, event)

    def send(self, count=3, policy=True, state=None):
        return self.run_event({"kind": "send", "count": count, "policyPermitted": policy}, state)

    def test_application_write_only_queues_bytes(self):
        result = self.run_event({"kind": "write", "payloadHex": "6a6b"})
        self.assertEqual(result.state.pending, b"ghijk")
        self.assertEqual(result.state.core, self.seed.core)
        self.assertIsNone(result.output)

    def test_pending_capacity_has_an_exact_limit(self):
        fitting = self.run_event({"kind": "write", "payloadHex": bytes(5).hex()})
        self.assertEqual(len(fitting.state.pending), 8)
        excessive = self.run_event({"kind": "write", "payloadHex": bytes(6).hex()})
        self.assertEqual(excessive.decision, {"kind": "reject", "reason": "pendingCapacity"})
        self.assertEqual(excessive.state, self.seed)

    def test_send_selects_the_exact_application_prefix(self):
        result = self.send(2)
        self.assertEqual(result.state.pending, b"i")
        self.assertEqual(result.state.core.sent, b"abcdefgh")
        self.assertEqual(result.state.core.send_next, 1008)
        self.assertEqual(result.state.core.send_una, 1000)
        self.assertEqual(result.state.core.received, b"xy")
        self.assertEqual(result.output["decoded"]["segment"]["payloadHex"], "6768")

    def test_output_bytes_use_current_reverse_tuple_and_cursors(self):
        output = self.send().output
        packet = wire.decode_packet(output["rawIPv4Hex"])
        self.assertEqual(packet.header.source, self.seed.core.inbound.destination)
        self.assertEqual(packet.header.destination, self.seed.core.inbound.source)
        self.assertEqual(packet.header.source_port, 80)
        self.assertEqual(packet.header.destination_port, 12345)
        self.assertEqual(packet.segment.sequence, 1006)
        self.assertEqual(packet.segment.acknowledgment, 100)
        self.assertEqual(packet.segment.window, 6)
        self.assertEqual(packet.segment.flags, 16)
        self.assertEqual(packet.segment.reserved, 0)
        self.assertEqual(packet.segment.options, b"")
        self.assertEqual(packet.segment.urgent_pointer, 0)
        self.assertEqual((packet.tos, packet.identification, packet.ttl), (0, 0, 64))
        self.assertTrue(packet.dont_fragment)
        self.assertEqual(packet.padding, b"")
        self.assertEqual(packet.to_dict(), output["decoded"])

    def test_output_checksums_reject_changed_ip_and_payload_bytes(self):
        raw = bytearray.fromhex(self.send().output["rawIPv4Hex"])
        for offset in (8, 39, len(raw) - 1):
            changed = raw.copy()
            changed[offset] ^= 1
            with self.assertRaises(ValueError):
                wire.decode_packet(changed)

    def test_computed_zero_checksum_remains_a_mandatory_checksum(self):
        blank = reference.emit(self.seed, bytes(2))
        word = blank["decoded"]["segment"]["checksum"]
        state = replace(self.seed, pending=word.to_bytes(2, "big"))
        result = self.send(2, state=state)
        self.assertEqual(result.output["decoded"]["segment"]["checksum"], 0)
        wire.decode_packet(result.output["rawIPv4Hex"])
        changed = bytearray.fromhex(result.output["rawIPv4Hex"])
        changed[-1] ^= 1
        with self.assertRaises(ValueError):
            wire.decode_packet(changed)

    def test_send_bounds_include_pending_peer_window_and_mss(self):
        for count in (0, 4):
            with self.subTest(count=count):
                self.assertEqual(
                    self.send(count).decision, {"kind": "reject", "reason": "sendBounds"}
                )
        for state in (
            replace(self.seed, send_window=8),
            replace(self.seed, effective_mss=2),
            replace(self.seed, send_window=0),
        ):
            with self.subTest(state=state):
                self.assertEqual(self.send(state=state).state, state)
                self.assertIsNone(self.send(state=state).output)

    def test_ip_size_limit_can_bind_the_effective_mss(self):
        state = replace(self.seed, effective_mss=2, ip_send_limit=42)
        exact = self.send(2, state=state)
        self.assertEqual(len(bytes.fromhex(exact.output["rawIPv4Hex"])), 42)
        self.assertEqual(
            self.send(3, state=state).decision, {"kind": "reject", "reason": "sendBounds"}
        )

    def test_policy_blocks_send_and_ack_without_changes(self):
        sent = self.send(policy=False)
        ack = self.run_event({"kind": "emitAck", "policyPermitted": False})
        for result in (sent, ack):
            self.assertEqual(result.decision, {"kind": "reject", "reason": "policy"})
            self.assertEqual(result.state, self.seed)
            self.assertIsNone(result.output)

    def test_policy_precedes_send_bounds(self):
        self.assertEqual(
            self.send(0, policy=False).decision, {"kind": "reject", "reason": "policy"}
        )

    def test_read_returns_a_prefix_and_opens_exact_local_space(self):
        result = self.run_event({"kind": "read", "count": 1})
        self.assertEqual(result.read, b"x")
        self.assertEqual(result.state.core.received, b"y")
        self.assertEqual(result.state.core.window, self.seed.core.window + 1)
        self.assertEqual(result.state.core.receive_next, 100)
        self.assertEqual(replace(result.state, core=self.seed.core), self.seed)
        self.assertEqual(result.state.core.sent, self.seed.core.sent)

    def test_read_bounds_preserve_storage(self):
        result = self.run_event({"kind": "read", "count": 3})
        self.assertEqual(result.decision, {"kind": "reject", "reason": "readBounds"})
        self.assertEqual(result.state, self.seed)
        self.assertEqual(result.read, b"")

    def test_empty_write_and_zero_read_succeed_without_outputs(self):
        for event in ({"kind": "write", "payloadHex": ""}, {"kind": "read", "count": 0}):
            result = self.run_event(event)
            self.assertEqual(result.decision["kind"], "accepted")
            self.assertEqual(result.state, self.seed)
            self.assertIsNone(result.output)

    def test_old_data_ack_preserves_every_window_field(self):
        result = self.run_event(self.event(acknowledgment=999, payload=b"z", window=0))
        self.assertEqual(
            result.decision,
            {"kind": "accepted", "operation": "receive", "acknowledged": 0, "received": 1},
        )
        self.assertEqual(result.state.core.received, b"xyz")
        self.assertEqual(result.state.core.sent, b"abcdef")
        self.assertEqual(result.state.send_window, 10)
        self.assertEqual(result.state.send_wl1, 100)
        self.assertEqual(result.state.send_wl2, 1000)

    def test_duplicate_una_ack_updates_with_newer_sequence(self):
        result = self.run_event(self.event(sequence=101, window=0))
        self.assertEqual(result.state.send_window, 0)
        self.assertEqual(result.state.send_wl1, 101)
        self.assertEqual(result.state.send_wl2, 1000)
        self.assertEqual(result.state.core.sent, self.seed.core.sent)

    def test_equal_sequence_equal_ack_updates_window(self):
        result = self.run_event(self.event(window=0))
        self.assertEqual(result.state.send_window, 0)
        self.assertTrue(result.state.valid)

    def test_equal_sequence_older_history_ack_keeps_window(self):
        state = replace(self.seed, send_wl2=1001)
        result = self.run_event(self.event(window=0), state)
        self.assertEqual(result.state.send_window, 10)

    def test_equal_sequence_newer_history_ack_updates_window(self):
        state = replace(self.seed, send_wl2=999)
        result = self.run_event(self.event(window=0), state)
        self.assertEqual(result.state.send_window, 0)

    def test_older_sequence_keeps_window_even_with_new_ack(self):
        state = replace(self.seed, send_wl1=101)
        result = self.run_event(self.event(acknowledgment=1006, window=0), state)
        self.assertEqual(result.state.send_window, 10)
        self.assertEqual(result.state.core.sent, b"")

    def test_window_guard_uses_the_state_before_ack_removal(self):
        result = self.run_event(self.event(acknowledgment=1003, window=1))
        self.assertEqual(result.state.core.sent, b"def")
        self.assertEqual(result.state.core.send_una, 1003)
        self.assertEqual(result.state.send_window, 1)
        self.assertTrue(result.state.valid)
        blocked = self.send(1, state=result.state)
        self.assertEqual(blocked.decision, {"kind": "reject", "reason": "sendBounds"})

    def test_geometry_failure_does_not_commit_window_or_ack(self):
        result = self.run_event(
            self.event(sequence=101, acknowledgment=1006, payload=b"z", window=0)
        )
        self.assertEqual(result.decision, {"kind": "unsupported", "reason": "outOfOrder"})
        self.assertEqual(result.state, self.seed)
        self.assertIsNone(result.ack)

    def test_half_space_history_is_not_ordered(self):
        sequence_half = replace(
            self.seed, send_wl1=(100 + reference.HALF_SPACE) % reference.MODULUS
        )
        ack_half = replace(self.seed, send_wl2=(1000 + reference.HALF_SPACE) % reference.MODULUS)
        for state in (sequence_half, ack_half):
            packet = wire.decode_packet(self.event()["rawIPv4Hex"])
            self.assertFalse(reference.window_eligible(state, packet.segment))

    def test_window_freshness_uses_circular_coordinates(self):
        state = replace(self.seed, send_wl1=0xFFFFFFFF, send_wl2=0xFFFFFFFF)
        packet = wire.Segment(0, 0)
        state = replace(state, core=replace(state.core, send_una=0xFFFFFFFE, send_next=4))
        self.assertTrue(reference.window_eligible(state, packet))
        state = replace(state, send_wl1=1)
        self.assertFalse(reference.window_eligible(state, packet))

    def test_send_advances_across_sequence_wrap(self):
        core = replace(self.seed.core, send_una=0xFFFFFFF8, send_next=0xFFFFFFFE)
        state = replace(self.seed, core=core)
        result = self.send(state=state)
        self.assertEqual(result.state.core.send_next, 1)
        self.assertEqual(result.output["decoded"]["segment"]["sequence"], 0xFFFFFFFE)
        self.assertTrue(result.state.valid)

    def test_ack_emission_reads_current_fields_after_read(self):
        received = self.run_event(self.event(payload=b"z"))
        saved_request = received.ack
        read = self.run_event({"kind": "read", "count": 2}, received.state)
        ack = self.run_event({"kind": "emitAck", "policyPermitted": True}, read.state)
        segment = ack.output["decoded"]["segment"]
        self.assertEqual(segment["window"], 7)
        self.assertEqual(segment["acknowledgment"], 101)
        self.assertNotEqual(segment["window"], saved_request["window"])
        self.assertEqual(ack.state, read.state)

    def test_invalid_seed_precedes_all_events(self):
        bad = replace(self.seed, effective_mss=0)
        events = (
            {"kind": "write", "payloadHex": ""},
            {"kind": "read", "count": 0},
            {"kind": "send", "count": 0, "policyPermitted": False},
            {"kind": "emitAck", "policyPermitted": False},
            self.event(flags=4),
        )
        for event in events:
            self.assertEqual(
                self.run_event(event, bad).decision, {"kind": "reject", "reason": "invalidSeed"}
            )

    def test_stop_retains_unread_event_bytes(self):
        events = [
            self.event(flags=4),
            {"kind": "receive", "rawIPv4Hex": "00"},
            {"kind": "write", "payloadHex": "7a"},
        ]
        report = reference.replay(self.seed.seed_dict(), events)
        self.assertFalse(report["supported"])
        self.assertEqual(report["evaluatedEvents"], 1)
        self.assertEqual(report["remainingEvents"], events[1:])
        self.assertEqual(report["final"], self.seed.to_dict())

    def test_hex_syntax_is_examined_after_the_stop(self):
        events = [self.event(flags=4), {"kind": "receive", "rawIPv4Hex": "gg"}]
        with self.assertRaises(ValueError):
            reference.replay(self.seed.seed_dict(), events)

    def test_rejected_event_does_not_stop_replay(self):
        events = [{"kind": "read", "count": 3}, {"kind": "read", "count": 1}]
        report = reference.replay(self.seed.seed_dict(), events)
        self.assertTrue(report["supported"])
        self.assertEqual(report["evaluatedEvents"], 2)
        self.assertEqual(report["final"]["core"]["receivedHex"], "79")

    def test_report_event_hex_uses_canonical_bytes(self):
        receive = self.event(payload=bytes.fromhex("abcd"))
        events = [
            {"kind": "write", "payloadHex": "A1B2"},
            {"kind": "receive", "rawIPv4Hex": receive["rawIPv4Hex"].upper()},
        ]
        original = copy.deepcopy(events)
        report = reference.replay(self.seed.seed_dict(), events)
        canonical = [
            {"kind": "write", "payloadHex": "a1b2"},
            receive,
        ]
        self.assertEqual([step["event"] for step in report["steps"]], canonical)
        self.assertEqual(report["final"]["pendingHex"], "676869a1b2")
        self.assertEqual(report["steps"][1]["decodedInput"]["segment"]["payloadHex"], "abcd")
        self.assertEqual(events, original)

    def test_unread_event_hex_is_canonical_without_transport_decode(self):
        reset = self.event(flags=4)
        events = [
            {"kind": "receive", "rawIPv4Hex": reset["rawIPv4Hex"].upper()},
            {"kind": "receive", "rawIPv4Hex": "ABCD"},
            {"kind": "write", "payloadHex": "A1B2"},
        ]
        report = reference.replay(self.seed.seed_dict(), events)
        self.assertFalse(report["supported"])
        self.assertEqual(report["evaluatedEvents"], 1)
        self.assertEqual(
            report["remainingEvents"],
            [
                {"kind": "receive", "rawIPv4Hex": "abcd"},
                {"kind": "write", "payloadHex": "a1b2"},
            ],
        )
        self.assertEqual(report["steps"][0]["event"], reset)

    def test_static_fixtures_match_all_results(self):
        data = reference.load_fixtures()
        self.assertGreater(reference.check_fixtures(data)["events"], 40)

    def test_trace_ledgers_conserve_application_bytes(self):
        for trace in reference.load_fixtures()["traces"]:
            seed = reference.State.from_dict(trace["input"]["seed"])
            written = emitted = acknowledged = accepted = read = b""
            for step in trace["expected"]["steps"]:
                decision = step["decision"]
                if decision["kind"] == "accepted":
                    operation = decision["operation"]
                    if operation == "write":
                        written += bytes.fromhex(step["event"]["payloadHex"])
                    elif operation == "send":
                        emitted += bytes.fromhex(step["output"]["decoded"]["segment"]["payloadHex"])
                    elif operation == "receive":
                        acknowledged += bytes.fromhex(step["before"]["core"]["sentHex"])[
                            : decision["acknowledged"]
                        ]
                        accepted += bytes.fromhex(step["decodedInput"]["segment"]["payloadHex"])
                read += bytes.fromhex(step["readHex"])
                state = reference.State.from_dict(step["state"])
                self.assertEqual(seed.pending + written, emitted + state.pending, trace["name"])
                self.assertEqual(
                    seed.core.sent + emitted, acknowledged + state.core.sent, trace["name"]
                )
                self.assertEqual(
                    seed.core.received + accepted, read + state.core.received, trace["name"]
                )

    def test_fixture_change_is_detected(self):
        data = copy.deepcopy(reference.load_fixtures())
        data["cases"][0]["expected"]["readHex"] = "ff"
        with self.assertRaises(AssertionError):
            reference.check_fixtures(data)


if __name__ == "__main__":
    unittest.main()
