"""Retain passive NFLOG netlink messages and acknowledged capture configuration."""

import json
import select
import signal
import socket
import struct
import sys
import time
from pathlib import Path

HEADER = struct.Struct("=IHHII")


def attribute(kind, payload):
    size = 4 + len(payload)
    return struct.pack("=HH", size, kind) + payload + bytes((-size) % 4)


def configure(sock, sequence, group, fields):
    payload = struct.pack("!BBH", socket.AF_INET, 0, group) + b"".join(fields)
    request = HEADER.pack(16 + len(payload), 0x401, 5, sequence, sock.getsockname()[0]) + payload
    start = time.monotonic_ns()
    sock.sendto(request, (0, 0))
    raw, _, flags, peer = sock.recvmsg(262144)
    end = time.monotonic_ns()
    size, kind, _, received_sequence, port = HEADER.unpack_from(raw)
    if (
        peer[0]
        or flags
        or size != len(raw)
        or kind != 2
        or received_sequence != sequence
        or port != sock.getsockname()[0]
        or struct.unpack_from("=i", raw, 16)[0] != 0
        or raw[20:36] != request[:16]
    ):
        raise RuntimeError("NFLOG configuration was not acknowledged by the kernel.")
    return {
        "startNs": start,
        "endNs": end,
        "request": request.hex(),
        "acknowledgment": raw.hex(),
        "sender": list(peer),
        "flags": flags,
    }


def capture(path, group):
    active = True

    def stop(*_):
        nonlocal active
        active = False

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    sock = socket.socket(socket.AF_NETLINK, socket.SOCK_RAW, 12)
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1 << 20)
    sock.bind((0, 0))
    sock.settimeout(5)
    records = [configure(sock, 1, 0, [attribute(1, bytes((3,)))])]
    records.append(
        configure(
            sock,
            2,
            group,
            [
                attribute(1, bytes((1,))),
                attribute(2, struct.pack("!IBB", 65531, 2, 0)),
                attribute(4, struct.pack("!I", 1)),
                attribute(5, struct.pack("!I", 1)),
                attribute(6, struct.pack("!H", 3)),
            ],
        )
    )
    print(
        json.dumps(
            {
                "readyNs": time.monotonic_ns(),
                "port": sock.getsockname()[0],
                "group": group,
                "receiveBuffer": sock.getsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF),
                "configuration": records,
            }
        ),
        flush=True,
    )
    with Path(path).open("w") as stream:
        while active:
            ready, _, _ = select.select([sock], [], [], 0.1)
            if not ready:
                continue
            raw, _, flags, peer = sock.recvmsg(262144)
            stream.write(
                json.dumps(
                    {
                        "timeNs": time.monotonic_ns(),
                        "hex": raw.hex(),
                        "sender": list(peer),
                        "flags": flags,
                    }
                )
                + "\n"
            )
            stream.flush()
    sock.close()


if __name__ == "__main__":
    capture(sys.argv[1], int(sys.argv[2]))
