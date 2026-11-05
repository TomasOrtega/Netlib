"""Static TCP conformance checks, independent of Lean and native networking."""

import json
import struct
import unittest
from dataclasses import replace
from pathlib import Path

import tcp_reference as tcp

SOURCE = "192.0.2.1"
DESTINATION = "198.51.100.2"
FIXTURES = Path(__file__).resolve().parent.parent / "examples/tcp/fixtures.json"


class ChecksumTests(unittest.TestCase):
    def test_carry_and_odd_byte(self):
        self.assertEqual(tcp.folded_sum(bytes.fromhex("ffff0001")), 1)
        self.assertEqual(tcp.checksum(bytes.fromhex("010203")), 0xFBFD)

    def test_valid_zero_checksum_is_not_omission(self):
        case = next(
            case for case in tcp.load_fixtures()["cases"] if case["name"] == "checksum-zero"
        )
        segment = tcp.decode_segment(SOURCE, DESTINATION, bytes.fromhex(case["segmentHex"]))
        self.assertEqual(segment.checksum, 0)
        self.assertEqual(tcp.encode_segment(segment).hex(), case["segmentHex"])
        changed = replace(segment, destination_port=segment.destination_port + 1)
        with self.assertRaisesRegex(tcp.TCPError, "checksum"):
            tcp.decode_segment(SOURCE, DESTINATION, tcp.encode_segment(changed))

    def test_pseudoheader_addresses_are_checked(self):
        segment = tcp.computed_segment(SOURCE, DESTINATION, payload=b"odd")
        with self.assertRaisesRegex(tcp.TCPError, "checksum"):
            tcp.decode_segment("192.0.2.2", DESTINATION, tcp.encode_segment(segment))


class FramingTests(unittest.TestCase):
    def test_full_unsigned_fields_and_all_flags(self):
        segment = tcp.computed_segment(
            SOURCE,
            DESTINATION,
            source_port=65535,
            destination_port=65535,
            sequence=0xFFFFFFFF,
            acknowledgment=0x80000000,
            flags=255,
            window=65535,
            urgent_pointer=65535,
            payload=b"even",
        )
        decoded = tcp.decode_segment(SOURCE, DESTINATION, tcp.encode_segment(segment))
        self.assertEqual(decoded, segment)
        self.assertEqual(decoded.flag_names, tcp.FLAG_NAMES)

    def test_received_reserved_bits_survive_exact_encoding(self):
        segment = tcp.rechecksum(SOURCE, DESTINATION, tcp.Segment(reserved=15))
        self.assertEqual(
            tcp.decode_segment(SOURCE, DESTINATION, tcp.encode_segment(segment)), segment
        )
        self.assertEqual(tcp.generation_issues(segment), ("reservedBits",))
        generated = tcp.computed_segment(SOURCE, DESTINATION, reserved=15)
        self.assertEqual(generated.reserved, 0)

    def test_maximum_pseudoheader_length(self):
        segment = tcp.computed_segment(SOURCE, DESTINATION, payload=bytes(65515))
        self.assertEqual(len(tcp.encode_segment(segment)), 65535)
        self.assertEqual(
            tcp.decode_segment(SOURCE, DESTINATION, tcp.encode_segment(segment)), segment
        )
        with self.assertRaisesRegex(tcp.TCPError, "length"):
            tcp.decode_segment(SOURCE, DESTINATION, bytes(65536))

    def test_header_length_limits(self):
        for options in (b"", bytes([1]) * 40):
            segment = tcp.computed_segment(SOURCE, DESTINATION, options=options)
            self.assertEqual(segment.header_length, 20 + len(options))
            self.assertEqual(
                tcp.decode_segment(SOURCE, DESTINATION, tcp.encode_segment(segment)), segment
            )
        for options in (bytes(3), bytes(44)):
            with self.assertRaisesRegex(tcp.TCPError, "options"):
                tcp.computed_segment(SOURCE, DESTINATION, options=options)

    def test_wire_offset_must_fit_the_segment(self):
        segment = tcp.computed_segment(SOURCE, DESTINATION)
        raw = bytearray(tcp.encode_segment(segment))
        for offset, error in ((4, "dataOffset"), (6, "truncatedHeader")):
            raw[12] = offset << 4
            with self.assertRaises(tcp.TCPError) as caught:
                tcp.decode_segment(SOURCE, DESTINATION, raw)
            self.assertEqual(caught.exception.code, error)


class OptionTests(unittest.TestCase):
    def test_nop_unknown_and_unaligned_mss(self):
        options = bytes.fromhex("01020405b4fe0200")
        segment = tcp.computed_segment(SOURCE, DESTINATION, flags=2, options=options)
        decoded = tcp.decode_segment(SOURCE, DESTINATION, tcp.encode_segment(segment))
        self.assertEqual([option.kind for option in decoded.parsed_options], [1, 2, 254, 0])
        self.assertEqual(decoded.parsed_options[1].data, bytes.fromhex("05b4"))
        self.assertEqual(tcp.semantic_issues(decoded), ())

    def test_mss_placement_is_separate_from_byte_validity(self):
        segment = tcp.computed_segment(
            SOURCE, DESTINATION, flags=16, options=bytes.fromhex("020405b4")
        )
        self.assertEqual(
            tcp.decode_segment(SOURCE, DESTINATION, tcp.encode_segment(segment)), segment
        )
        self.assertEqual(tcp.semantic_issues(segment), ("mssRequiresSyn",))

    def test_malformed_option_boundaries(self):
        for raw, error in (
            ("fe", "optionLengthMissing"),
            ("fe00", "optionLength"),
            ("fe01", "optionLength"),
            ("fe0400", "optionTruncated"),
            ("0203ff", "mssLength"),
            ("0001", "eolPadding"),
        ):
            with self.subTest(raw=raw), self.assertRaises(tcp.TCPError) as caught:
                tcp.parse_options(bytes.fromhex(raw))
            self.assertEqual(caught.exception.code, error)

    def test_mss_zero_is_structural_without_extra_semantic_rules(self):
        segment = tcp.computed_segment(
            SOURCE, DESTINATION, flags=2, options=bytes.fromhex("02040000")
        )
        self.assertEqual(tcp.semantic_issues(segment), ())


class FixtureTests(unittest.TestCase):
    def test_retained_cases_match_independent_oracle(self):
        data = json.loads(FIXTURES.read_text())
        checked = tcp.check_fixtures(data)
        self.assertGreaterEqual(checked["accepted"], 10)
        self.assertGreaterEqual(checked["rejected"], 10)

    def test_retained_expectations_cannot_hide_field_changes(self):
        data = tcp.load_fixtures()
        case = next(case for case in data["cases"] if case["structural"])
        case["expected"]["sequence"] ^= 1
        with self.assertRaisesRegex(AssertionError, "expected"):
            tcp.check_fixtures(data)

    def test_fixed_header_layout_uses_network_byte_order(self):
        segment = tcp.computed_segment(
            SOURCE, DESTINATION, sequence=0x01020304, acknowledgment=0xA0B0C0D0
        )
        raw = tcp.encode_segment(segment)
        self.assertEqual(struct.unpack("!II", raw[4:12]), (0x01020304, 0xA0B0C0D0))


class SequenceTests(unittest.TestCase):
    def test_wrap_and_half_space(self):
        self.assertTrue(tcp.seq_before(0xFFFFFFFF, 0))
        self.assertFalse(tcp.seq_before(0, 0))
        self.assertFalse(tcp.seq_before(0, tcp.HALF_SPACE))
        self.assertFalse(tcp.seq_before(tcp.HALF_SPACE, 0))

    def test_transitivity_needs_a_common_short_arc(self):
        first, second, third = 0, 0x60000000, 0xC0000000
        self.assertTrue(tcp.seq_before(first, second))
        self.assertTrue(tcp.seq_before(second, third))
        self.assertFalse(tcp.seq_before(first, third))
        with self.assertRaisesRegex(ValueError, "half-space"):
            tcp.seq_within(first, tcp.HALF_SPACE, second)


if __name__ == "__main__":
    unittest.main()
