"""Exercise raw conntrack framing and decoding without opening a socket."""

import errno
import socket
import struct
import unittest

import capture_conntrack as capture

SEQ = 0x12345678
PORT = 31415


def attr(kind, value, *, nested=False):
    encoded = struct.pack("=HH", 4 + len(value), kind | (0x8000 if nested else 0)) + value
    return encoded + bytes((-len(encoded)) % 4)


def number(kind, value, size=4):
    return attr(kind, value.to_bytes(size, "big"))


def tuple_attrs(protocol=17, zone=None):
    addresses = attr(1, bytes([10, 0, 0, 2])) + attr(2, bytes([203, 0, 113, 9]))
    ports = number(1, protocol, 1) + number(2, 12345, 2) + number(3, 443, 2)
    result = attr(1, addresses, nested=True) + attr(2, ports, nested=True)
    return result + (number(3, zone, 2) if zone is not None else b"")


def payload(*, protocol=17, extra=b"", original_zone=None, reply_zone=None):
    return (
        bytes([2, 0, 0, 0])
        + attr(1, tuple_attrs(protocol, original_zone), nested=True)
        + attr(2, tuple_attrs(protocol, reply_zone), nested=True)
        + number(3, 0x198)
        + number(7, 0)
        + number(12, 0xAABBCCDD)
        + number(8, 0x01020304)
        + number(11, 2)
        + extra
    )


def message(data=b"", kind=0x100, *, flags=2, seq=SEQ, port=PORT):
    encoded = struct.pack("=IHHII", 16 + len(data), kind, flags, seq, port) + data
    return encoded + bytes((-len(encoded)) % 4)


def done(error=0, **options):
    return message(struct.pack("=i", error), kind=3, **options)


def decode(data):
    dump = capture.Dump(SEQ, PORT)
    dump.feed(message(data) + done())
    return dump.finish()["entries"][0]


class DecodeTests(unittest.TestCase):
    def test_udp_endianness_status_zero_timeout_and_raw(self):
        data = payload()
        entry = decode(data)
        self.assertEqual(
            entry["original"],
            {
                "source": "10.0.0.2",
                "destination": "203.0.113.9",
                "protocol": 17,
                "sourcePort": 12345,
                "destinationPort": 443,
            },
        )
        self.assertEqual(entry["reply"], entry["original"])
        self.assertEqual(entry["status"], 0x198)
        self.assertEqual(entry["id"], 0xAABBCCDD)
        self.assertEqual(entry["mark"], 0x01020304)
        self.assertEqual(entry["use"], 2)
        self.assertEqual(entry["remainingTTL"], 0)
        self.assertEqual((entry["originalZone"], entry["replyZone"]), (0, 0))
        self.assertEqual(bytes.fromhex(entry["raw"]), message(data))

    def test_tcp_and_default_or_directional_zones(self):
        entry = decode(payload(protocol=6, extra=number(18, 42, 2)))
        self.assertEqual(entry["original"]["protocol"], 6)
        self.assertEqual((entry["originalZone"], entry["replyZone"]), (42, 42))
        entry = decode(payload(original_zone=19))
        self.assertEqual((entry["originalZone"], entry["replyZone"]), (19, 0))
        entry = decode(payload(reply_zone=7))
        self.assertEqual((entry["originalZone"], entry["replyZone"]), (0, 7))

    def test_optional_metadata_is_null_not_zero(self):
        data = bytes([2, 0, 0, 0])
        data += attr(1, tuple_attrs(), nested=True) + attr(2, tuple_attrs(), nested=True)
        data += number(3, 0x4008)
        entry = decode(data)
        for name in ("remainingTTL", "id", "mark", "use"):
            self.assertIsNone(entry[name])

    def test_unknown_attributes_are_retained_and_nested_framing_checked(self):
        unknown = attr(123, attr(456, b"evidence"), nested=True)
        data = payload(extra=unknown)
        self.assertIn(unknown, bytes.fromhex(decode(data)["raw"]))
        malformed = attr(123, struct.pack("=HH", 12, 1), nested=True)
        with self.assertRaisesRegex(capture.CaptureError, "attribute"):
            decode(payload(extra=malformed))

    def test_required_duplicate_and_invalid_scalar(self):
        with self.assertRaisesRegex(capture.CaptureError, "Duplicate"):
            decode(payload(extra=number(3, 8)))
        with self.assertRaisesRegex(capture.CaptureError, "length"):
            decode(payload(extra=number(18, 1, 4)))
        with self.assertRaisesRegex(capture.CaptureError, "status"):
            decode(bytes([2, 0, 0, 0]))

    def test_protocol_family_and_zone_ambiguity_rejected(self):
        with self.assertRaisesRegex(capture.CaptureError, "protocol"):
            decode(payload(protocol=1))
        with self.assertRaisesRegex(capture.CaptureError, "family"):
            decode(bytes([10]) + payload()[1:])
        with self.assertRaisesRegex(capture.CaptureError, "zone"):
            decode(payload(original_zone=3, extra=number(18, 5, 2)))

    def test_malformed_attributes_and_tuple_protocol_mismatch(self):
        for malformed in (b"x", struct.pack("=HH", 3, 55), struct.pack("=HH", 99, 55)):
            with self.subTest(malformed=malformed):
                with self.assertRaises(capture.CaptureError):
                    decode(payload(extra=malformed))
        data = bytes([2, 0, 0, 0])
        data += attr(1, tuple_attrs(6), nested=True) + attr(2, tuple_attrs(17), nested=True)
        data += number(3, 8)
        with self.assertRaisesRegex(capture.CaptureError, "protocol"):
            decode(data)

    def test_distinct_original_and_snat_reply_and_shared_alias(self):
        def flow_tuple(source, destination, source_port, destination_port):
            addresses = attr(1, bytes(source)) + attr(2, bytes(destination))
            ports = number(1, 17, 1)
            ports += number(2, source_port, 2) + number(3, destination_port, 2)
            return attr(1, addresses, nested=True) + attr(2, ports, nested=True)

        dump = capture.Dump(SEQ, PORT)
        for remote in (9, 10):
            data = bytes([2, 0, 0, 0])
            data += attr(
                1, flow_tuple([10, 0, 0, 2], [203, 0, 113, remote], 12345, 443), nested=True
            )
            data += attr(
                2, flow_tuple([203, 0, 113, remote], [198, 51, 100, 8], 443, 40000), nested=True
            )
            data += number(3, 0x198)
            dump.feed(message(data))
        dump.feed(done())
        first, second = dump.finish()["entries"]
        self.assertEqual(first["reply"]["destination"], "198.51.100.8")
        self.assertEqual(first["reply"]["destinationPort"], 40000)
        self.assertEqual(first["reply"]["sourcePort"], 443)
        self.assertEqual(first["original"]["source"], "10.0.0.2")
        self.assertNotEqual(first["reply"]["source"], second["reply"]["source"])

    def test_deep_unknown_nesting_and_missing_nested_flag(self):
        data = attr(123, b"")
        for _ in range(34):
            data = attr(123, data, nested=True)
        with self.assertRaisesRegex(capture.CaptureError, "depth"):
            decode(payload(extra=data))
        data = bytes([2, 0, 0, 0]) + attr(1, tuple_attrs()) + number(3, 8)
        with self.assertRaisesRegex(capture.CaptureError, "nested"):
            decode(data)


class DumpTests(unittest.TestCase):
    def test_empty_success_and_multiple_datagrams(self):
        dump = capture.Dump(SEQ, PORT)
        dump.feed(done())
        self.assertEqual(dump.finish()["entries"], [])
        dump = capture.Dump(SEQ, PORT)
        dump.feed(message(payload()))
        dump.feed(message(payload(protocol=6)))
        dump.feed(done())
        result = dump.finish()
        self.assertEqual((result["schema"], result["family"]), (1, 2))
        self.assertEqual(len(result["entries"]), 2)
        self.assertEqual(len(result["messages"]), 3)

    def test_sequence_port_sender_and_interrupted_dump(self):
        bad = (
            (message(payload(), seq=SEQ + 1), "sequence"),
            (message(payload(), port=0), "port"),
            (done(flags=0x12), "interrupted"),
            (done(flags=0x22), "filtered"),
        )
        for raw, reason in bad:
            with self.subTest(reason=reason):
                with self.assertRaisesRegex(capture.CaptureError, reason):
                    capture.Dump(SEQ, PORT).feed(raw)
        with self.assertRaisesRegex(capture.CaptureError, "sender"):
            capture.Dump(SEQ, PORT).feed(done(), peer_port=4)

    def test_native_ipv4_family_filter_flag(self):
        dump = capture.Dump(SEQ, PORT)
        filtered = message(payload(), flags=0x22)
        dump.feed(filtered + done())
        result = dump.finish()
        self.assertEqual(result["family"], 2)
        self.assertEqual(result["messages"][0], filtered.hex())
        self.assertEqual(bytes.fromhex(result["request"])[16:], b"\x02\x00\x00\x00")
        with self.assertRaisesRegex(capture.CaptureError, "family"):
            capture.Dump(SEQ, PORT).feed(message(bytes([10]) + payload()[1:], flags=0x22))
        with self.assertRaisesRegex(capture.CaptureError, "interrupted"):
            capture.Dump(SEQ, PORT).feed(message(payload(), flags=0x32))

    def test_incomplete_truncated_overrun_and_done_failure(self):
        with self.assertRaisesRegex(capture.CaptureError, "DONE"):
            capture.Dump(SEQ, PORT).finish()
        cases = (
            (b"short", "header"),
            (message(payload())[:-4], "length"),
            (message(kind=4), "overrun"),
            (done(-errno.ENOBUFS), "No buffer space"),
            (message(kind=3), "DONE"),
            (done() + message(payload()), "after DONE"),
        )
        for raw, reason in cases:
            with self.subTest(reason=reason):
                with self.assertRaisesRegex(capture.CaptureError, reason):
                    capture.Dump(SEQ, PORT).feed(raw)
        with self.assertRaisesRegex(capture.CaptureError, "truncated"):
            capture.Dump(SEQ, PORT).feed(done(), recv_flags=socket.MSG_TRUNC)

    def test_error_ack_and_kernel_error(self):
        request = capture.make_request(SEQ, PORT)
        for error in (0, -errno.EPERM):
            dump = capture.Dump(SEQ, PORT)
            ack = message(struct.pack("=i", error) + request[:16], kind=2, flags=0)
            if error:
                with self.assertRaisesRegex(capture.CaptureError, "Operation not permitted"):
                    dump.feed(ack)
            else:
                dump.feed(ack + done())
                self.assertEqual(len(dump.finish()["messages"]), 2)
        with self.assertRaisesRegex(capture.CaptureError, "ERROR"):
            capture.Dump(SEQ, PORT).feed(message(b"bad", kind=2))

    def test_control_attribute_framing_and_copied_request(self):
        request = capture.make_request(SEQ, PORT)
        ack_body = struct.pack("=i", 0) + request[:16]
        dump = capture.Dump(SEQ, PORT)
        dump.feed(message(ack_body + attr(77, b"detail"), kind=2, flags=0x200) + done())
        self.assertEqual(dump.finish()["entries"], [])
        for body, flags in ((ack_body + b"bad", 0x200), (ack_body + b"tail", 0)):
            with self.subTest(body=body):
                with self.assertRaises(capture.CaptureError):
                    capture.Dump(SEQ, PORT).feed(message(body, kind=2, flags=flags))
        corrupted = bytearray(ack_body)
        corrupted[4] = 0
        with self.assertRaisesRegex(capture.CaptureError, "request"):
            capture.Dump(SEQ, PORT).feed(message(corrupted, kind=2, flags=0))

    def test_entry_and_byte_budgets_fail_without_partial_success(self):
        with self.assertRaisesRegex(capture.CaptureError, "entry budget"):
            capture.Dump(SEQ, PORT, max_entries=1).feed(message(payload()) * 2 + done())
        with self.assertRaisesRegex(capture.CaptureError, "byte budget"):
            capture.Dump(SEQ, PORT, max_bytes=4).feed(done())

    def test_failure_poisoning_and_unexpected_messages(self):
        dump = capture.Dump(SEQ, PORT)
        dump.feed(done())
        with self.assertRaises(capture.CaptureError):
            dump.feed(message(payload()))
        with self.assertRaisesRegex(capture.CaptureError, "completion"):
            dump.finish()
        for raw in (message(kind=99), message(payload(), flags=0)):
            with self.subTest(raw=raw):
                with self.assertRaises(capture.CaptureError):
                    capture.Dump(SEQ, PORT).feed(raw)


class FakeSocket:
    def __init__(self, replies):
        self.replies = iter(replies)
        self.sent = None
        self.bound = None
        self.closed = False

    def bind(self, address):
        self.bound = address

    def getsockname(self):
        return PORT, 0

    def settimeout(self, timeout):
        self.timeout = timeout

    def sendto(self, data, address):
        self.sent = data, address
        return len(data)

    def recvmsg(self, size):
        value = next(self.replies)
        if isinstance(value, Exception):
            raise value
        return value, [], 0, (0, 0)

    def close(self):
        self.closed = True


class SocketTests(unittest.TestCase):
    def test_invalid_timeout_does_not_open_socket(self):
        def forbidden_socket(*args):
            self.fail("Invalid timeout must be rejected before opening the socket.")

        for timeout in (0, -1, float("nan"), float("inf")):
            with self.subTest(timeout=timeout):
                with self.assertRaisesRegex(capture.CaptureError, "timeout"):
                    capture.capture(socket_factory=forbidden_socket, timeout=timeout)

    def test_request_constants_and_complete_capture(self):
        fake = FakeSocket([message(payload()), done()])
        result = capture.capture(socket_factory=lambda *args: fake, sequence=SEQ)
        request, destination = fake.sent
        self.assertEqual(struct.unpack("=IHHII", request[:16]), (20, 0x101, 0x301, SEQ, PORT))
        self.assertEqual(request[16:], b"\x02\x00\x00\x00")
        self.assertEqual(destination, (0, 0))
        self.assertEqual(result["request"], request.hex())
        self.assertEqual(fake.bound, (0, 0))
        self.assertTrue(fake.closed)

    def test_socket_loss_and_timeout_never_return_partial_capture(self):
        for error in (OSError(errno.ENOBUFS, "lost data"), TimeoutError("timed out")):
            fake = FakeSocket([message(payload()), error])
            with self.subTest(error=error):
                with self.assertRaises(capture.CaptureError):
                    capture.capture(socket_factory=lambda *args: fake, sequence=SEQ)
                self.assertTrue(fake.closed)


if __name__ == "__main__":
    unittest.main()
