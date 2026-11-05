"""Independent IPv4 queue oracle for Ubuntu-6.8.0-117.117.

The reference follows ip_fragment.c and inet_fragment.c, with IHL five,
ipfrag_max_dist zero, successful allocation, and explicitly ordered expiry.
https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117
https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/inet_fragment.c?h=Ubuntu-6.8.0-117.117
"""

import ipaddress
import struct
from dataclasses import dataclass, field, replace

NANOSECONDS = 1_000_000_000


def folded_sum(data):
    data += bytes(len(data) % 2)
    total = sum(struct.unpack(f"!{len(data) // 2}H", data))
    while total >> 16:
        total = (total & 65535) + (total >> 16)
    return total


def checksum(data):
    return 65535 - folded_sum(data)


@dataclass(frozen=True)
class IPPacket:
    source: int
    destination: int
    payload: bytes
    identification: int = 0x4321
    tos: int = 0x28
    ttl: int = 64
    protocol: int = 17
    dont_fragment: bool = False
    more_fragments: bool = False
    offset: int = 0
    raw: bytes = field(default=b"", compare=False, repr=False)

    @property
    def wire_length(self):
        return 20 + len(self.payload)

    @property
    def source_address(self):
        return str(ipaddress.IPv4Address(self.source))

    @property
    def destination_address(self):
        return str(ipaddress.IPv4Address(self.destination))


def encode_packet(packet):
    if not 20 <= packet.wire_length <= 65535:
        raise ValueError("IPv4 total length is outside the selected profile.")
    if packet.offset % 8 or not 0 <= packet.offset // 8 < 8192:
        raise ValueError("IPv4 fragment offset is not encodable.")
    flags = packet.offset // 8 | int(packet.more_fragments) << 13 | int(packet.dont_fragment) << 14
    header = struct.pack(
        "!BBHHHBBHII",
        69,
        packet.tos,
        packet.wire_length,
        packet.identification,
        flags,
        packet.ttl,
        packet.protocol,
        0,
        packet.source,
        packet.destination,
    )
    return header[:10] + checksum(header).to_bytes(2, "big") + header[12:] + packet.payload


def decode_packet(raw):
    raw = bytes.fromhex(raw) if isinstance(raw, str) else bytes(raw)
    if len(raw) < 20 or raw[0] != 69:
        raise ValueError("Require a complete IHL-five IPv4 header.")
    _, tos, size, identification, flags, ttl, protocol, _, source, destination = struct.unpack(
        "!BBHHHBBHII", raw[:20]
    )
    if size < 20 or size > len(raw) or folded_sum(raw[:20]) != 65535 or flags & 0x8000:
        raise ValueError("Invalid IPv4 length, checksum, or reserved flag.")
    return IPPacket(
        source,
        destination,
        raw[20:size],
        identification,
        tos,
        ttl,
        protocol,
        bool(flags & 0x4000),
        bool(flags & 0x2000),
        (flags & 8191) * 8,
        raw[:size],
    )


@dataclass(frozen=True)
class Fragment:
    ip: IPPacket
    data: bytes

    @property
    def start(self):
        return self.ip.offset

    @property
    def end(self):
        return self.start + len(self.data)


@dataclass
class Run:
    pieces: list

    @property
    def start(self):
        return self.pieces[0].start

    @property
    def end(self):
        return self.start + sum(len(piece.data) for piece in self.pieces)


@dataclass
class Queue:
    key: tuple
    expires: int
    runs: list = field(default_factory=list)
    length: int = 0
    last: bool = False
    first: Fragment | None = None
    ecn: set = field(default_factory=set)
    max_size: int = 0
    max_df_size: int = 0

    @property
    def pieces(self):
        return [piece for run in self.runs for piece in run.pieces]

    @property
    def ecn_mask(self):
        return sum(1 << value for value in self.ecn)


@dataclass(frozen=True)
class Arrival:
    status: str
    output: IPPacket | None
    max_size: int
    max_df_size: int
    reassembled: bool
    expired: tuple

    @property
    def packet(self):
        return None if self.output is None else encode_packet(self.output)


class ReassemblyOracle:
    def __init__(self, user_base=2):
        self.user_base = user_base
        self.queues = {}
        self.last_time = 0

    def advance(self, now):
        if now < self.last_time:
            raise ValueError("The monotonic clock moved backwards.")
        expired = [queue for queue in self.queues.values() if queue.expires <= now]
        for queue in expired:
            del self.queues[queue.key]
        self.last_time = now
        return expired

    def arrive(self, raw, now, zone=0, vif=0, timeout=30 * NANOSECONDS):
        if timeout <= 0:
            raise ValueError("The queue timeout must be positive.")
        ip = decode_packet(raw)
        expired = tuple(self.advance(now))
        if not ip.more_fragments and ip.offset == 0:
            return Arrival("whole", ip, 0, 0, False, expired)
        key = (
            self.user_base + zone,
            vif,
            ip.source,
            ip.destination,
            ip.protocol,
            ip.identification,
        )
        queue = self.queues.get(key)
        if queue is None:
            queue = Queue(key, now + timeout)
            self.queues[key] = queue

        def discard(status):
            del self.queues[key]
            return Arrival(status, None, 0, 0, False, expired)

        data = ip.payload[: len(ip.payload) // 8 * 8] if ip.more_fragments else ip.payload
        piece = Fragment(ip, data)
        end = piece.end
        if not ip.more_fragments:
            if end < queue.length or queue.last and end != queue.length:
                return discard("inconsistentLength")
            queue.last = True
            queue.length = end
        elif end > queue.length:
            if queue.last:
                return discard("inconsistentLength")
            queue.length = end
        if not data:
            return discard("empty")

        # Linux coalesces only arrivals adjacent to the global tail.
        if not queue.runs:
            queue.runs.append(Run([piece]))
        elif end > queue.runs[-1].end:
            tail = queue.runs[-1]
            if piece.start < tail.end:
                return discard("overlap")
            if piece.start == tail.end:
                tail.pieces.append(piece)
            else:
                queue.runs.append(Run([piece]))
        else:
            index = 0
            while index < len(queue.runs) and queue.runs[index].end <= piece.start:
                index += 1
            if index < len(queue.runs):
                run = queue.runs[index]
                if run.start <= piece.start and end <= run.end:
                    return Arrival("duplicate", None, 0, 0, False, expired)
                if end > run.start:
                    return discard("overlap")
            queue.runs.insert(index, Run([piece]))

        if piece.start == 0:
            queue.first = piece
        queue.ecn.add(ip.tos & 3)
        queue.max_size = max(queue.max_size, len(data) + 20)
        if ip.dont_fragment:
            queue.max_df_size = max(queue.max_df_size, len(data) + 20)
        received = sum(len(fragment.data) for fragment in queue.pieces)
        if queue.first is None or not queue.last or received != queue.length:
            return Arrival("buffered", None, 0, 0, False, expired)
        if 0 in queue.ecn and len(queue.ecn) != 1:
            return discard("invalidECN")
        if queue.length + 20 > 65535:
            return discard("tooLarge")
        payload = b"".join(fragment.data for fragment in queue.pieces)
        position = 0
        for fragment in queue.pieces:
            if fragment.start != position:
                raise AssertionError("The source insertion rules produced an impossible gap.")
            position = fragment.end
        head = queue.first.ip
        output = replace(
            head,
            payload=payload,
            tos=(head.tos & 0xFC) | 3 if 3 in queue.ecn else head.tos,
            dont_fragment=queue.max_df_size == queue.max_size,
            more_fragments=False,
            offset=0,
            raw=b"",
        )
        output = replace(output, raw=encode_packet(output))
        result = Arrival("complete", output, queue.max_size, queue.max_df_size, True, expired)
        del self.queues[key]
        return result
