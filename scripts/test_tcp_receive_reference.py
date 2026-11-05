"""Static tests for the selected TCP receive projection."""

import copy
import unittest
from dataclasses import replace

import tcp_receive_reference as reference


class ReceiveTests(unittest.TestCase):
    def setUp(self):
        self.seed = reference.State(
            reference.Header("192.0.2.1", "198.51.100.2", 6, 12345, 80),
            100,
            8,
            b"xy",
            1000,
            1006,
            b"abcdef",
        )

    def packet(self, **fields):
        segment = reference.Segment(100, 1000, **fields)
        return reference.decode_packet(reference.fixture_packet(self.seed.inbound, segment))

    def test_old_ack_does_not_prevent_data_progress(self):
        packet = self.packet(payload=b"abc")
        packet = replace(packet, segment=replace(packet.segment, acknowledgment=999))
        result = reference.receive(self.seed, packet)
        self.assertEqual(result.decision, {"kind": "accepted", "acknowledged": 0, "received": 3})
        self.assertEqual(result.state.received, b"xyabc")
        self.assertEqual(result.state.receive_next, 103)
        self.assertEqual(result.state.sent, b"abcdef")
        self.assertEqual(
            result.ack,
            {"kind": "data", "sequence": 1006, "acknowledgment": 103, "window": 3},
        )

    def test_ack_removes_the_exact_seed_prefix(self):
        packet = self.packet()
        packet = replace(packet, segment=replace(packet.segment, acknowledgment=1002))
        result = reference.receive(self.seed, packet)
        self.assertEqual(result.state.sent, b"cdef")
        self.assertEqual(result.state.send_una, 1002)
        self.assertEqual(result.state.send_next, 1006)
        self.assertIsNone(result.ack)

    def test_ack_boundaries_and_half_space(self):
        for offset, expected in (
            (-65535, 0),
            (-65536, None),
            (0, 0),
            (6, 6),
            (7, None),
            (1 << 31, None),
        ):
            with self.subTest(offset=offset):
                ack = (1000 + offset) % reference.MODULUS
                self.assertEqual(reference.acknowledged_count(self.seed, ack), expected)

    def test_signed_ack_reference_matches_the_rfc_arc(self):
        for una in (0, 1, 65534, 65535, 65536, 1 << 31, 0xFFFFFFFE, 0xFFFFFFFF):
            for size in (0, 1, 6, 65535):
                state = replace(
                    self.seed,
                    send_una=una,
                    send_next=(una + size) % reference.MODULUS,
                    sent=bytes(size),
                )
                for offset in (
                    -65536,
                    -65535,
                    -1,
                    0,
                    1,
                    size,
                    size + 1,
                    (1 << 31) - 1,
                    1 << 31,
                    (1 << 31) + 1,
                ):
                    ack = (una + offset) % reference.MODULUS
                    lower = (una - 65535) % reference.MODULUS
                    within = (ack - lower) % reference.MODULUS <= 65535 + size
                    self.assertEqual(reference.acknowledged_count(state, ack) is not None, within)

    def test_geometry_block_keeps_the_ack_prefix(self):
        packet = self.packet(payload=b"1234567")
        packet = replace(packet, segment=replace(packet.segment, acknowledgment=1006))
        result = reference.receive(self.seed, packet)
        self.assertEqual(result.decision, {"kind": "unsupported", "reason": "trimming"})
        self.assertEqual(result.state, self.seed)
        self.assertIsNone(result.ack)

    def test_full_local_capacity_does_not_use_peer_window(self):
        packet = self.packet(payload=b"123456", window=0)
        result = reference.receive(self.seed, packet)
        self.assertEqual(result.state.window, 0)
        self.assertEqual(result.state.received, b"xy123456")
        self.assertEqual(result.ack["window"], 0)

    def test_psh_and_received_reserved_bits_have_no_effect(self):
        ordinary = reference.receive(self.seed, self.packet(payload=b"a"))
        marked = reference.receive(self.seed, self.packet(payload=b"a", flags=24, reserved=15))
        self.assertEqual(ordinary, marked)

    def test_every_control_bit_has_an_explicit_profile_result(self):
        for flag, reason in (
            (4, "reset"),
            (2, "synchronize"),
            (1, "finish"),
            (32, "urgent"),
            (64, "congestion"),
            (128, "congestion"),
        ):
            with self.subTest(flag=flag):
                result = reference.receive(self.seed, self.packet(flags=16 | flag))
                self.assertEqual(result.decision, {"kind": "unsupported", "reason": reason})
                self.assertEqual(result.state, self.seed)

    def test_control_priority_precedes_sequence_scope(self):
        result = reference.receive(self.seed, self.packet(flags=255))
        self.assertEqual(result.decision, {"kind": "unsupported", "reason": "reset"})
        packet = self.packet(flags=4)
        packet = replace(packet, segment=replace(packet.segment, sequence=200))
        result = reference.receive(self.seed, packet)
        self.assertEqual(result.decision, {"kind": "unsupported", "reason": "reset"})
        self.assertIsNone(result.ack)

    def test_zero_window_controls_with_data_are_outside_the_profile(self):
        closed = replace(self.seed, capacity=2)
        for flags, reason in ((20, "reset"), (48, "urgent")):
            with self.subTest(flags=flags):
                result = reference.receive(closed, self.packet(flags=flags, payload=b"x"))
                self.assertEqual(result.decision, {"kind": "unsupported", "reason": reason})
                self.assertEqual(result.state, closed)
                self.assertIsNone(result.ack)

    def test_options_outside_the_window_are_outside_the_profile(self):
        packet = self.packet(options=bytes(4))
        packet = replace(packet, segment=replace(packet.segment, sequence=200))
        result = reference.receive(self.seed, packet)
        self.assertEqual(result.decision, {"kind": "unsupported", "reason": "options"})

    def test_seed_and_tuple_gates_precede_profile_scope(self):
        packet = self.packet(flags=4, payload=b"x")
        result = reference.receive(replace(self.seed, capacity=65536), packet)
        self.assertEqual(result.decision, {"kind": "reject", "reason": "invalidSeed"})
        packet = replace(packet, header=replace(packet.header, source_port=1))
        result = reference.receive(self.seed, packet)
        self.assertEqual(result.decision, {"kind": "reject", "reason": "tuple"})

    def test_seed_and_tuple_failures_do_not_change_state(self):
        invalid = replace(self.seed, capacity=65536)
        self.assertEqual(
            reference.receive(invalid, self.packet()).decision,
            {"kind": "reject", "reason": "invalidSeed"},
        )
        packet = self.packet()
        packet = replace(packet, header=replace(packet.header, source_port=54321))
        result = reference.receive(self.seed, packet)
        self.assertEqual(result.decision, {"kind": "reject", "reason": "tuple"})
        self.assertEqual(result.state, self.seed)

    def test_seed_sent_buffer_has_a_separate_fixed_bound(self):
        maximum = replace(self.seed, sent=bytes(65535), send_next=66535)
        excessive = replace(self.seed, sent=bytes(65536), send_next=66536)
        self.assertTrue(maximum.valid)
        self.assertFalse(excessive.valid)
        self.assertEqual(
            reference.receive(excessive, self.packet()).decision,
            {"kind": "reject", "reason": "invalidSeed"},
        )

    def test_each_option_region_is_outside_the_profile(self):
        for options in (
            bytes(4),
            bytes([1]) * 4,
            bytes.fromhex("020405b4"),
            bytes.fromhex("fe020000"),
        ):
            with self.subTest(options=options):
                result = reference.receive(self.seed, self.packet(options=options))
                self.assertEqual(result.decision, {"kind": "unsupported", "reason": "options"})


class WindowTests(unittest.TestCase):
    def test_four_cases_and_window_containment(self):
        self.assertTrue(reference.sequence_accepts(100, 0, 100, 0))
        self.assertFalse(reference.sequence_accepts(100, 0, 101, 0))
        self.assertFalse(reference.sequence_accepts(100, 0, 100, 1))
        self.assertTrue(reference.sequence_accepts(100, 10, 109, 0))
        self.assertFalse(reference.sequence_accepts(100, 10, 110, 0))
        self.assertTrue(reference.sequence_accepts(100, 10, 99, 11))
        self.assertFalse(reference.sequence_accepts(100, 10, 99, 12))
        self.assertTrue(all(reference.inside(99, 12, position) for position in range(100, 110)))

    def test_receive_wrap(self):
        for position in (0xFFFFFFFE, 0xFFFFFFFF, 0, 1):
            self.assertTrue(reference.sequence_accepts(0xFFFFFFFE, 4, position, 0))
        self.assertFalse(reference.sequence_accepts(0xFFFFFFFE, 4, 2, 0))


class WireTests(unittest.TestCase):
    def test_zero_and_ffff_verify_without_omission(self):
        header = reference.Header("192.0.2.1", "198.51.100.2", 6, 12345, 80)
        segment = reference.Segment(0, 0, window=4096, payload=bytes.fromhex("8312"))
        ordinary = reference.fixture_packet(header, segment)
        alternate = reference.fixture_packet(header, segment, checksum_override=65535)
        self.assertEqual(reference.decode_packet(ordinary).segment.checksum, 0)
        self.assertEqual(reference.decode_packet(alternate).segment.checksum, 65535)
        changed = bytearray(ordinary)
        changed[-1] ^= 1
        with self.assertRaisesRegex(ValueError, "TCP checksum"):
            reference.decode_packet(changed)

    def test_padding_does_not_change_payload(self):
        header = reference.Header("192.0.2.1", "198.51.100.2", 6, 12345, 80)
        decoded = reference.decode_packet(
            reference.fixture_packet(
                header, reference.Segment(0, 0, payload=b"abc"), padding=b"\x00\xff\x00"
            )
        )
        self.assertEqual(decoded.segment.payload, b"abc")
        self.assertEqual(decoded.padding, b"\x00\xff\x00")


class FixtureTests(unittest.TestCase):
    def test_static_expectations(self):
        counts = reference.check_fixtures(reference.load_fixtures())
        self.assertGreaterEqual(counts["receive"], 40)
        self.assertGreaterEqual(counts["window"], 30)
        self.assertGreaterEqual(counts["traces"], 2)

    def test_a_changed_expected_prefix_is_detected(self):
        data = copy.deepcopy(reference.load_fixtures())
        case = next(case for case in data["cases"] if case["name"] == "ack-prefix-two")
        case["expected"]["state"]["sentHex"] = ""
        with self.assertRaisesRegex(AssertionError, "ack-prefix-two"):
            reference.check_fixtures(data)

    def test_unsupported_stops_transport_decoding(self):
        data = reference.load_fixtures()
        case = next(case for case in data["cases"] if case["name"] == "control-reset")
        result = reference.replay(case["seed"], [case["rawIPv4Hex"], "00"])
        self.assertFalse(result["supported"])
        self.assertEqual(result["evaluatedPackets"], 1)
        self.assertEqual(result["remainingPacketsHex"], ["00"])
        with self.assertRaisesRegex(ValueError, "Hex text"):
            reference.replay(case["seed"], [case["rawIPv4Hex"], "0"])

    def test_rejected_input_does_not_stop_replay(self):
        data = reference.load_fixtures()
        bad = next(case for case in data["cases"] if case["name"] == "ack-beyond-next")
        good = next(case for case in data["cases"] if case["name"] == "ack-prefix-two")
        result = reference.replay(bad["seed"], [bad["rawIPv4Hex"], good["rawIPv4Hex"]])
        self.assertTrue(result["supported"])
        self.assertEqual(result["evaluatedPackets"], 2)
        self.assertEqual(result["final"]["sentHex"], b"cdef".hex())


if __name__ == "__main__":
    unittest.main()
