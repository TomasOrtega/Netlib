"""Capture hook order, confirmation, and policy updates in private namespaces."""

import json
import socket
import subprocess
import sys
import time
from pathlib import Path

BASE = Path("/tmp/netlib-lifecycle")


def header(source, destination, source_port, destination_port):
    return {
        "source": source,
        "destination": destination,
        "protocol": 17,
        "sourcePort": source_port,
        "destinationPort": destination_port,
    }


def endpoint(role):
    address = "192.0.2.2" if role == "client" else "198.51.100.2"
    sockets = {}
    for line in sys.stdin:
        request = json.loads(line)
        port = request["port"]
        if port not in sockets:
            sockets[port] = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sockets[port].bind((address, port))
        sock = sockets[port]
        result = None
        if request["op"] == "send":
            peer = request["peer"]
            sock.sendto(request["payload"].encode("ascii"), tuple(peer))
            result = {
                "packet": header(address, peer[0], port, peer[1]),
                "payload": request["payload"],
            }
        elif request["op"] == "receive":
            sock.settimeout(request.get("timeout", 2))
            try:
                data, peer = sock.recvfrom(4096)
                result = {
                    "packet": header(peer[0], address, peer[1], port),
                    "payload": data.decode("ascii"),
                }
            except TimeoutError:
                pass
        elif request["op"] != "bind":
            raise ValueError("Unknown endpoint operation.")
        print(json.dumps(result), flush=True)
    for sock in sockets.values():
        sock.close()


class Endpoint:
    def __init__(self, namespace):
        self.process = subprocess.Popen(
            ["ip", "netns", "exec", namespace, "python3", __file__, "endpoint", namespace],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
            bufsize=1,
        )

    def call(self, operation, port, **fields):
        self.process.stdin.write(json.dumps({"op": operation, "port": port, **fields}) + "\n")
        self.process.stdin.flush()
        response = self.process.stdout.readline()
        if not response:
            raise RuntimeError("The endpoint exited before its response.")
        return json.loads(response)

    def close(self):
        self.process.stdin.close()
        self.process.wait(timeout=5)


def native(*arguments, **options):
    return subprocess.run(["ip", "netns", "exec", "router", *arguments], check=True, **options)


def save(name, value):
    (BASE / name).write_text(json.dumps(value, indent=2) + "\n")


def load_rules(name, text):
    path = BASE / (name + ".nft")
    path.write_text(text)
    native("nft", "-f", str(path))


def export_table(table, name):
    with (BASE / (name + ".json")).open("w") as output:
        native("nft", "-j", "-nn", "list", "table", "ip", table, stdout=output)


def snapshot(name):
    native(
        "python3", "/task/scripts/capture_conntrack.py", "--output", str(BASE / (name + ".json"))
    )


def capture():
    setup = """table ip netlib_trace {
 chain trace { type filter hook prerouting priority -301; policy accept; meta nftrace set 1; }
}
table ip netlib_nat {
 chain destination { type nat hook prerouting priority -100; policy accept;
  ip daddr 203.0.113.2 udp dport 8080 dnat to 198.51.100.2:9000
  ip daddr 203.0.113.2 udp dport 8081 dnat to 198.51.100.2:9001
  ip daddr 203.0.113.2 udp dport 8082 dnat to 198.51.100.2:9002
 }
 chain source { type nat hook postrouting priority 100; policy accept;
  ip saddr 192.0.2.0/24 meta l4proto udp snat to 203.0.113.1:40000
 }
}
table ip netlib_filter {
 chain forward { type filter hook forward priority 0; policy drop;
  ct state established accept comment "ESTABLISHED"
  ct state new ip saddr 192.0.2.0/24 ip daddr 198.51.100.2 udp dport 9000 accept comment "SERVICE"
  ct state new udp dport 9001 accept comment "LATE_INPUT"
  ct state new udp dport 9002 drop comment "FORWARD_DROP"
 }
}
table ip netlib_late {
 chain late { type filter hook postrouting priority 200; policy accept;
  udp dport 9001 drop comment "LATE_DROP"
 }
}
"""
    load_rules("setup", setup)
    export_table("netlib_filter", "forward-initial")
    export_table("netlib_late", "late")
    export_table("netlib_nat", "nat-initial")
    client, server = Endpoint("client"), Endpoint("server")
    for port in [9000, 9001, 9002, 9003]:
        server.call("bind", port)
    trace_file = (BASE / "trace.txt").open("w")
    errors = (BASE / "trace-errors.txt").open("w")
    trace = subprocess.Popen(
        ["ip", "netns", "exec", "router", "nft", "monitor", "trace"],
        stdout=trace_file,
        stderr=errors,
    )
    records = []
    try:
        time.sleep(0.1)
        assert trace.poll() is None
        for source_port, destination_port, name, server_port in [
            (31002, 8082, "forward-drop", 9002),
            (31003, 8081, "late-drop", 9001),
        ]:
            sent = client.call(
                "send", source_port, peer=["203.0.113.2", destination_port], payload=name
            )
            received = server.call("receive", server_port, timeout=0.15)
            assert received is None
            snapshot(name + "-state")
            records.append({"phase": name, "sent": sent, "server": received})
        sent = client.call("send", 31000, peer=["203.0.113.2", 8080], payload="first-original")
        received = server.call("receive", 9000)
        assert received and received["payload"] == "first-original"
        snapshot("opened-state")
        records.append({"phase": "first-original", "sent": sent, "server": received})
        load_rules(
            "change-nat",
            """flush chain ip netlib_nat destination
flush chain ip netlib_nat source
add rule ip netlib_nat destination ip daddr 203.0.113.2 udp dport 8080 dnat to 198.51.100.2:9003
add rule ip netlib_nat source ip saddr 192.0.2.0/24 meta l4proto udp snat to 203.0.113.1:40001
""",
        )
        export_table("netlib_nat", "nat-changed")
        sent = client.call(
            "send", 31000, peer=["203.0.113.2", 8080], payload="unreplied-after-nat-update"
        )
        received = server.call("receive", 9000)
        assert received and received["payload"] == "unreplied-after-nat-update"
        snapshot("unreplied-updated-state")
        records.append({"phase": "unreplied-after-nat-update", "sent": sent, "server": received})
        load_rules(
            "drop-first-reply",
            """flush chain ip netlib_filter forward
add rule ip netlib_filter forward ct state established ip saddr 198.51.100.2 udp sport 9000 drop comment "REPLY_DROP"
add rule ip netlib_filter forward ct state established accept comment "ESTABLISHED"
""",
        )
        export_table("netlib_filter", "forward-drop-reply")
        reply = server.call(
            "send", 9000, peer=["203.0.113.1", 40000], payload="first-reply-dropped"
        )
        received = client.call("receive", 31000, timeout=0.15)
        assert received is None
        snapshot("reply-dropped-state")
        records.append({"phase": "first-reply-dropped", "sent": reply, "client": received})
        load_rules(
            "deny-new",
            """flush chain ip netlib_filter forward
add rule ip netlib_filter forward ct state established accept comment "ESTABLISHED"
""",
        )
        export_table("netlib_filter", "forward-established-only")
        sent = client.call(
            "send", 31000, peer=["203.0.113.2", 8080], payload="existing-after-update"
        )
        wire = server.call("receive", 9000)
        assert wire and wire["payload"] == "existing-after-update"
        reply = server.call("send", 9000, peer=["203.0.113.1", 40000], payload="reply-after-update")
        restored = client.call("receive", 31000)
        assert restored and restored["payload"] == "reply-after-update"
        records.append(
            {
                "phase": "existing-after-update",
                "sent": sent,
                "server": wire,
                "reply": reply,
                "client": restored,
            }
        )
        sent = client.call("send", 31001, peer=["203.0.113.2", 8080], payload="fresh-after-update")
        received = server.call("receive", 9003, timeout=0.15)
        assert received is None
        snapshot("updated-state")
        records.append({"phase": "fresh-after-update", "sent": sent, "server": received})
        native(
            "conntrack",
            "-D",
            "-p",
            "udp",
            "--orig-src",
            "192.0.2.2",
            "--orig-dst",
            "203.0.113.2",
            "--sport",
            "31000",
            "--dport",
            "8080",
            stdout=subprocess.DEVNULL,
        )
        snapshot("deleted-state")
        sent = client.call("send", 31000, peer=["203.0.113.2", 8080], payload="old-after-delete")
        received = server.call("receive", 9003, timeout=0.15)
        assert received is None
        snapshot("after-delete-packet-state")
        records.append({"phase": "old-after-delete", "sent": sent, "server": received})
        save("observations.json", records)
    finally:
        client.close()
        server.close()
        trace.terminate()
        trace.wait(timeout=5)
        trace_file.close()
        errors.close()


if __name__ == "__main__":
    if sys.argv[1] == "capture":
        capture()
    else:
        endpoint(sys.argv[2])
