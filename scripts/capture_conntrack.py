"""Capture IPv4 TCP/UDP conntrack tuples and full status through raw Netlink.

Run inside the isolated Linux capture container with CAP_NET_ADMIN. This is a
visible-table dump, not an atomic history or proof of packet admission. Constants
follow Linux v6.8 include/uapi/linux/{netlink.h,netfilter/nfnetlink*.h}.
"""

import argparse
import errno
import ipaddress
import json
import math
import os
import secrets
import socket
import struct
import sys
from dataclasses import dataclass
from pathlib import Path

NL_HEADER = struct.Struct("=IHHII")
ATTR_HEADER = struct.Struct("=HH")
NETLINK_NETFILTER = 12
CT_NEW = 0x100
CT_GET = 0x101
NLM_F_MULTI = 2
NLM_F_DUMP_INTR = 0x10
NLM_F_DUMP_FILTERED = 0x20
NLM_F_ACK_TLVS = 0x200
NLA_F_NESTED = 0x8000
NLA_TYPE_MASK = 0x3FFF
FAMILY = 2
MAX_NESTING = 32


class CaptureError(ValueError):
    """The dump cannot safely be represented as a successful capture."""


def aligned(length):
    return (length + 3) & ~3


@dataclass(frozen=True)
class Attribute:
    kind: int
    flags: int
    payload: bytes
    children: tuple | None


def attributes(data, *, depth=0):
    if depth > MAX_NESTING:
        raise CaptureError("Netlink attribute nesting exceeds the supported depth.")
    result = []
    offset = 0
    while offset < len(data):
        if len(data) - offset < ATTR_HEADER.size:
            raise CaptureError("Truncated Netlink attribute header.")
        length, kind = ATTR_HEADER.unpack_from(data, offset)
        if length < ATTR_HEADER.size or offset + aligned(length) > len(data):
            raise CaptureError("Invalid Netlink attribute length or padding.")
        value = data[offset + ATTR_HEADER.size : offset + length]
        nested = tuple(attributes(value, depth=depth + 1)) if kind & NLA_F_NESTED else None
        result.append(Attribute(kind & NLA_TYPE_MASK, kind & ~NLA_TYPE_MASK, value, nested))
        offset += aligned(length)
    return result


def one(attrs, kind, name, *, required=False):
    matches = [item for item in attrs if item.kind == kind]
    if len(matches) > 1:
        raise CaptureError(f"Duplicate {name} attribute.")
    if not matches:
        if required:
            raise CaptureError(f"Missing {name} attribute.")
        return None
    return matches[0]


def scalar(attrs, kind, name, size, *, required=False):
    item = one(attrs, kind, name, required=required)
    if item is None:
        return None
    if item.children is not None or len(item.payload) != size:
        raise CaptureError(f"Invalid {name} attribute length or nesting.")
    return int.from_bytes(item.payload, "big")


def nested(attrs, kind, name):
    item = one(attrs, kind, name, required=True)
    if item.children is None or item.flags != NLA_F_NESTED:
        raise CaptureError(f"Expected nested {name} attribute.")
    return item.children


def decode_tuple(attrs, kind, name):
    fields = nested(attrs, kind, name)
    addresses = nested(fields, 1, f"{name} IP")
    proto = nested(fields, 2, f"{name} protocol")
    protocol = scalar(proto, 1, f"{name} protocol number", 1, required=True)
    if protocol not in (6, 17):
        raise CaptureError(f"Unsupported {name} protocol {protocol}; expected TCP or UDP.")
    if any(item.kind in (3, 4) for item in addresses):
        raise CaptureError("IPv6 address attributes in an IPv4 tuple.")
    if any(4 <= item.kind <= 9 for item in proto):
        raise CaptureError("ICMP attributes in a TCP/UDP tuple.")
    source = scalar(addresses, 1, f"{name} source address", 4, required=True)
    destination = scalar(addresses, 2, f"{name} destination address", 4, required=True)
    header = {
        "source": str(ipaddress.IPv4Address(source)),
        "destination": str(ipaddress.IPv4Address(destination)),
        "protocol": protocol,
        "sourcePort": scalar(proto, 2, f"{name} source port", 2, required=True),
        "destinationPort": scalar(proto, 3, f"{name} destination port", 2, required=True),
    }
    return header, scalar(fields, 3, f"{name} zone", 2)


def decode_entry(raw):
    if len(raw) < NL_HEADER.size + 4:
        raise CaptureError("Truncated conntrack family header.")
    family, version, resource = struct.unpack_from("!BBH", raw, NL_HEADER.size)
    if family != FAMILY or version != 0 or resource != 0:
        raise CaptureError("Unsupported conntrack family, version, or resource ID.")
    attrs = attributes(raw[NL_HEADER.size + 4 :])
    status = scalar(attrs, 3, "status", 4, required=True)
    original, original_zone = decode_tuple(attrs, 1, "original")
    reply, reply_zone = decode_tuple(attrs, 2, "reply")
    if original["protocol"] != reply["protocol"]:
        raise CaptureError("Original and reply protocol numbers differ.")
    default_zone = scalar(attrs, 18, "default zone", 2)
    if default_zone is not None and (original_zone is not None or reply_zone is not None):
        raise CaptureError("Ambiguous default and directional zone attributes.")
    fallback = default_zone if default_zone is not None else 0
    return {
        "original": original,
        "reply": reply,
        "originalZone": original_zone if original_zone is not None else fallback,
        "replyZone": reply_zone if reply_zone is not None else fallback,
        "remainingTTL": scalar(attrs, 7, "timeout", 4),
        "status": status,
        "id": scalar(attrs, 12, "id", 4),
        "mark": scalar(attrs, 8, "mark", 4),
        "use": scalar(attrs, 11, "use", 4),
        "raw": raw.hex(),
    }


def make_request(sequence, port):
    return NL_HEADER.pack(20, CT_GET, 0x301, sequence, port) + bytes([FAMILY, 0, 0, 0])


def kernel_error(code, context):
    if code > 0:
        raise CaptureError(f"Invalid positive {context} error code {code}.")
    if code:
        raise CaptureError(f"{context}: {os.strerror(-code)} ({-code}).")


class Dump:
    def __init__(self, sequence, port, *, max_entries=100000, max_bytes=64 * 1024 * 1024):
        if not 0 < sequence <= 0xFFFFFFFF or not 0 < port <= 0xFFFFFFFF:
            raise CaptureError("Expected nonzero 32-bit sequence and port IDs.")
        if max_entries < 0 or max_bytes <= 0:
            raise CaptureError("Invalid capture budget.")
        self.sequence = sequence
        self.port = port
        self.max_entries = max_entries
        self.max_bytes = max_bytes
        self.byte_count = 0
        self.entries = []
        self.messages = []
        self.done = False
        self.failed = False

    def feed(self, data, *, peer_port=0, recv_flags=0):
        try:
            self._feed(data, peer_port=peer_port, recv_flags=recv_flags)
        except CaptureError:
            self.failed = True
            raise

    def _feed(self, data, *, peer_port, recv_flags):
        if self.failed:
            raise CaptureError("Capture already failed.")
        if peer_port != 0:
            raise CaptureError("Unexpected non-kernel Netlink sender.")
        if recv_flags & (socket.MSG_TRUNC | socket.MSG_CTRUNC):
            raise CaptureError("Netlink datagram was truncated.")
        if not data:
            raise CaptureError("Empty Netlink datagram before completion.")
        self.byte_count += len(data)
        if self.byte_count > self.max_bytes:
            raise CaptureError("Capture byte budget exceeded.")
        offset = 0
        while offset < len(data):
            if self.done:
                raise CaptureError("Unexpected message after DONE.")
            if len(data) - offset < NL_HEADER.size:
                raise CaptureError("Truncated Netlink message header.")
            length, kind, flags, sequence, port = NL_HEADER.unpack_from(data, offset)
            if length < NL_HEADER.size or offset + aligned(length) > len(data):
                raise CaptureError("Invalid Netlink message length or padding.")
            if sequence != self.sequence:
                raise CaptureError("Netlink sequence mismatch.")
            if port != self.port:
                raise CaptureError("Netlink reply port mismatch.")
            if flags & NLM_F_DUMP_INTR:
                raise CaptureError("Netlink dump was interrupted.")
            # ctnetlink marks entries filtered for our fixed AF_INET-only request.
            if flags & NLM_F_DUMP_FILTERED and kind != CT_NEW:
                raise CaptureError("Netlink dump was unexpectedly filtered.")
            raw = data[offset : offset + length]
            body = raw[NL_HEADER.size :]
            self.messages.append(raw.hex())
            if kind == 2:
                if len(body) < 4 + NL_HEADER.size:
                    raise CaptureError("Truncated NLMSG_ERROR acknowledgement.")
                kernel_error(struct.unpack_from("=i", body)[0], "NLMSG_ERROR")
                request_header = NL_HEADER.unpack_from(body, 4)
                if request_header != NL_HEADER.unpack_from(make_request(sequence, port)):
                    raise CaptureError("NLMSG_ERROR request header mismatch.")
                if flags & NLM_F_ACK_TLVS:
                    attributes(body[4 + NL_HEADER.size :])
                elif len(body) != 4 + NL_HEADER.size:
                    raise CaptureError("Unexpected NLMSG_ERROR acknowledgement payload.")
            elif kind == 3:
                if not flags & NLM_F_MULTI or len(body) < 4:
                    raise CaptureError("Malformed NLMSG_DONE message.")
                kernel_error(struct.unpack_from("=i", body)[0], "NLMSG_DONE")
                attributes(body[4:])
                self.done = True
            elif kind == 4:
                raise CaptureError("Netlink overrun; the dump lost data.")
            elif kind == CT_NEW:
                if not flags & NLM_F_MULTI:
                    raise CaptureError("Conntrack dump entry lacks multipart flag.")
                if len(self.entries) >= self.max_entries:
                    raise CaptureError("Capture entry budget exceeded.")
                self.entries.append(decode_entry(raw))
            else:
                raise CaptureError(f"Unexpected Netlink message type {kind}.")
            offset += aligned(length)

    def finish(self):
        if self.failed or not self.done:
            raise CaptureError("No successful NLMSG_DONE completion.")
        return {
            "schema": 1,
            "family": FAMILY,
            "entries": self.entries,
            "messages": self.messages,
            "request": make_request(self.sequence, self.port).hex(),
        }


def capture(*, socket_factory=socket.socket, sequence=None, timeout=10, **budgets):
    if not math.isfinite(timeout) or timeout <= 0:
        raise CaptureError("Capture timeout must be finite and positive.")
    sequence = sequence if sequence is not None else secrets.randbelow(0xFFFFFFFF) + 1
    connection = None
    try:
        connection = socket_factory(
            getattr(socket, "AF_NETLINK", 16), socket.SOCK_RAW, NETLINK_NETFILTER
        )
        connection.bind((0, 0))
        port, _ = connection.getsockname()
        dump = Dump(sequence, port, **budgets)
        connection.settimeout(timeout)
        request = make_request(sequence, port)
        if connection.sendto(request, (0, 0)) != len(request):
            raise CaptureError("Short Netlink request send.")
        while not dump.done:
            data, ancillary, flags, sender = connection.recvmsg(1024 * 1024)
            if ancillary or len(sender) != 2 or sender[1] != 0:
                raise CaptureError("Unexpected Netlink sender or ancillary metadata.")
            dump.feed(data, peer_port=sender[0], recv_flags=flags)
        return dump.finish()
    except OSError as error:
        detail = "Netlink receive buffer overrun" if error.errno == errno.ENOBUFS else str(error)
        raise CaptureError(f"Conntrack capture failed: {detail}.") from error
    finally:
        if connection is not None:
            connection.close()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write JSON here instead of stdout.")
    parser.add_argument("--max-entries", type=int, default=100000)
    parser.add_argument("--max-bytes", type=int, default=64 * 1024 * 1024)
    parser.add_argument("--timeout", type=float, default=10)
    args = parser.parse_args(argv)
    try:
        if sys.platform != "linux":
            raise CaptureError("Native capture requires the isolated Linux container.")
        result = capture(
            timeout=args.timeout, max_entries=args.max_entries, max_bytes=args.max_bytes
        )
        encoded = json.dumps(result, indent=2) + "\n"
        if args.output is None:
            sys.stdout.write(encoded)
        else:
            args.output.write_text(encoded)
    except (CaptureError, OSError) as error:
        print(f"capture_conntrack: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
