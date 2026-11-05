"""Exercise real UDP and TCP translation inside the capture namespaces."""

import json
import selectors
import socket
import sys
import time
from pathlib import Path

BASE = Path("/tmp/netlib-native")
FINISH = BASE / "finish"


def header(source, destination, protocol, source_port, destination_port):
    return {
        "source": source,
        "destination": destination,
        "protocol": protocol,
        "sourcePort": source_port,
        "destinationPort": destination_port,
    }


def endpoints(sock, peer, protocol):
    local = sock.getsockname()
    return header(peer[0], local[0], protocol, peer[1], local[1])


def save(name, value):
    (BASE / name).write_text(json.dumps(value, indent=2) + "\n")


def server():
    selector = selectors.DefaultSelector()
    sockets = []
    records = []
    for address, port in [("198.51.100.2", 9000), ("198.51.100.3", 9000), ("198.51.100.2", 9001)]:
        udp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        udp.bind((address, port))
        selector.register(udp, selectors.EVENT_READ, "udp")
        sockets.append(udp)
        if port == 9000:
            tcp = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            tcp.bind((address, port))
            tcp.listen()
            selector.register(tcp, selectors.EVENT_READ, "listen")
            sockets.append(tcp)
    (BASE / "server-ready").touch()
    deadline = time.monotonic() + 30
    while not FINISH.exists() and time.monotonic() < deadline:
        for key, _ in selector.select(0.05):
            sock = key.fileobj
            if key.data == "listen":
                connection, _ = sock.accept()
                selector.register(connection, selectors.EVENT_READ, "tcp")
                sockets.append(connection)
                continue
            if key.data == "udp":
                payload, peer = sock.recvfrom(4096)
                sock.sendto(payload, peer)
                protocol = 17
            else:
                payload = sock.recv(4096)
                if not payload:
                    selector.unregister(sock)
                    continue
                peer = sock.getpeername()
                sock.sendall(payload)
                protocol = 6
            records.append(
                {"payload": payload.decode("ascii"), "wire": endpoints(sock, peer, protocol)}
            )
    for sock in sockets:
        sock.close()
    save("server.json", records)


def client():
    sockets = []
    records = []
    rejected = []
    for index, remote in enumerate(["198.51.100.2", "198.51.100.3"]):
        udp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        udp.bind(("192.0.2.2", 31000 + index))
        udp.settimeout(2)
        sockets.append(udp)
        for repeat in range(2):
            payload = f"udp-{index}-{repeat}".encode("ascii")
            udp.sendto(payload, (remote, 9000))
            echoed, peer = udp.recvfrom(4096)
            assert echoed == payload
            original = header("192.0.2.2", remote, 17, 31000 + index, 9000)
            records.append(
                {
                    "payload": payload.decode(),
                    "original": original,
                    "restored": endpoints(udp, peer, 17),
                }
            )
        tcp = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        tcp.bind(("192.0.2.2", 32000 + index))
        tcp.settimeout(2)
        tcp.connect((remote, 9000))
        sockets.append(tcp)
        payload = f"tcp-{index}".encode("ascii")
        tcp.sendall(payload)
        assert tcp.recv(len(payload)) == payload
        original = header("192.0.2.2", remote, 6, 32000 + index, 9000)
        records.append(
            {
                "payload": payload.decode(),
                "original": original,
                "restored": endpoints(tcp, tcp.getpeername(), 6),
            }
        )
    for port, destination_port, name in [
        (31002, 9000, "collision"),
        (31003, 9001, "postrouting-drop"),
    ]:
        udp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        udp.bind(("192.0.2.2", port))
        udp.settimeout(0.3)
        udp.sendto(name.encode("ascii"), ("198.51.100.2", destination_port))
        try:
            udp.recvfrom(4096)
        except TimeoutError:
            rejected.append(name)
        else:
            raise RuntimeError(f"Unexpected reply for {name}.")
        udp.close()
    save("client.json", {"packets": records, "noReply": rejected})
    (BASE / "client-ready").touch()
    deadline = time.monotonic() + 20
    while not FINISH.exists() and time.monotonic() < deadline:
        time.sleep(0.05)
    for sock in sockets:
        sock.close()


if __name__ == "__main__":
    {"server": server, "client": client}[sys.argv[1]]()
