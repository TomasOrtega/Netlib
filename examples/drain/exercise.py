"""Capture a delayed packet across a late postrouting barrier."""

import json
import socket
import subprocess
import sys
import threading
import time
from pathlib import Path

BASE = Path("/tmp/netlib-drain")
OLD = "drain-old-already-queued"
BLOCKED = "drain-new-after-barrier"


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
    port = 31000 if role == "client" else 9000
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind((address, port))
    receive_thread, received = None, []
    receive_ready = threading.Event()

    def receive(timeout):
        start = time.monotonic_ns()
        sock.settimeout(timeout)
        receive_ready.set()
        try:
            data, peer = sock.recvfrom(4096)
            result = {
                "packet": header(peer[0], address, peer[1], port),
                "payload": data.decode("ascii"),
                "startNs": start,
                "endNs": time.monotonic_ns(),
            }
        except TimeoutError:
            result = {
                "packet": None,
                "payload": None,
                "startNs": start,
                "endNs": time.monotonic_ns(),
            }
        received.append(result)

    for line in sys.stdin:
        request = json.loads(line)
        operation = request["op"]
        if operation == "send":
            peer = request["peer"]
            start = time.monotonic_ns()
            sock.sendto(request["payload"].encode("ascii"), tuple(peer))
            result = {
                "packet": header(address, peer[0], port, peer[1]),
                "payload": request["payload"],
                "startNs": start,
                "endNs": time.monotonic_ns(),
            }
        elif operation == "watch":
            if receive_thread is not None:
                raise ValueError("A receive is already active.")
            receive_thread = threading.Thread(target=receive, args=(request["timeout"],))
            receive_ready.clear()
            receive_thread.start()
            receive_ready.wait(timeout=1)
            result = {"readyNs": time.monotonic_ns()}
        elif operation == "finish":
            receive_thread.join(timeout=10)
            if receive_thread.is_alive():
                raise TimeoutError("The receiver did not finish.")
            result = received.pop()
            receive_thread = None
        else:
            raise ValueError("Unknown endpoint operation.")
        print(json.dumps(result), flush=True)
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

    def call(self, operation, **fields):
        self.process.stdin.write(json.dumps({"op": operation, **fields}) + "\n")
        self.process.stdin.flush()
        response = self.process.stdout.readline()
        if not response:
            raise RuntimeError("The endpoint exited before its response.")
        return json.loads(response)

    def close(self):
        self.process.stdin.close()
        self.process.wait(timeout=10)


def native(*arguments, **options):
    return subprocess.run(["ip", "netns", "exec", "router", *arguments], check=True, **options)


def save(name, value):
    (BASE / name).write_text(json.dumps(value, indent=2) + "\n")


def rules(name, text):
    path = BASE / (name + ".nft")
    path.write_text(text)
    start = time.monotonic_ns()
    native("nft", "-f", str(path))
    return {"startNs": start, "endNs": time.monotonic_ns(), "file": name + ".nft"}


def export_table(table, name):
    with (BASE / (name + ".json")).open("w") as output:
        native("nft", "-j", "-nn", "list", "table", "ip", table, stdout=output)


def qdisc(name):
    filename = "qdisc-" + name + ".json"
    start = time.monotonic_ns()
    with (BASE / filename).open("w") as output:
        native("tc", "-j", "-s", "-d", "qdisc", "show", "dev", "outside0", stdout=output)
    return {"startNs": start, "endNs": time.monotonic_ns(), "file": filename}


def snapshot(name):
    filename = name + "-state.json"
    start = time.monotonic_ns()
    native("python3", "/task/scripts/capture_conntrack.py", "--output", str(BASE / filename))
    return {"startNs": start, "endNs": time.monotonic_ns(), "file": filename}


def capture():
    rules(
        "setup",
        """table ip netlib_trace {
 chain trace { type filter hook prerouting priority -301; policy accept; meta nftrace set 1; }
}
table ip netlib_nat {
 chain destination { type nat hook prerouting priority -100; policy accept;
  ip daddr 203.0.113.2 udp dport 8080 dnat to 198.51.100.2:9000
 }
 chain source { type nat hook postrouting priority 100; policy accept;
  ip saddr 192.0.2.0/24 meta l4proto udp snat to 203.0.113.1:40000
 }
}
table ip netlib_filter {
 chain forward { type filter hook forward priority 0; policy drop;
  ct state new ip saddr 192.0.2.0/24 ip daddr 198.51.100.2 udp dport 9000 accept comment "SERVICE"
 }
}
table ip netlib_late {
 chain late { type filter hook postrouting priority 110; policy accept; }
}
""",
    )
    for table, name in [
        ("netlib_trace", "instrumentation"),
        ("netlib_nat", "nat"),
        ("netlib_filter", "forward"),
        ("netlib_late", "late-before"),
    ]:
        export_table(table, name)
    command = [
        "tc",
        "qdisc",
        "add",
        "dev",
        "outside0",
        "root",
        "handle",
        "10:",
        "netem",
        "limit",
        "32",
        "delay",
        "4000ms",
    ]
    save("queue-command.json", command)
    native(*command)
    observations = {
        "schema": 1,
        "qdisc": {"configured": qdisc("configured")},
        "conntrack": {"initial": snapshot("initial")},
    }
    client, server = Endpoint("client"), Endpoint("server")
    trace_file = (BASE / "trace.txt").open("w")
    errors = (BASE / "trace-errors.txt").open("w")
    trace = subprocess.Popen(
        ["ip", "netns", "exec", "router", "nft", "monitor", "trace"],
        stdout=trace_file,
        stderr=errors,
    )
    try:
        time.sleep(0.1)
        assert trace.poll() is None
        observations["receiver"] = server.call("watch", timeout=8)
        old = client.call("send", peer=["203.0.113.2", 8080], payload=OLD)
        for _ in range(100):
            pending = qdisc("pending")
            current = json.loads((BASE / pending["file"]).read_text())
            if current[0]["qlen"] == 1:
                break
            time.sleep(0.01)
        else:
            raise RuntimeError("The delayed packet did not enter the queue.")
        observations["qdisc"]["pending"] = pending
        observations["conntrack"]["pending"] = snapshot("pending")
        observations["install"] = rules(
            "install-barrier",
            """add rule ip netlib_late late ip daddr 198.51.100.2 meta l4proto udp drop comment "BARRIER"
""",
        )
        export_table("netlib_late", "late-after")
        blocked = client.call("send", peer=["203.0.113.2", 8080], payload=BLOCKED)
        observations["conntrack"]["blocked"] = snapshot("blocked")
        observations["qdisc"]["blocked"] = qdisc("blocked")
        received = server.call("finish")
        assert received["payload"] == OLD
        observations["old"] = {"sent": old, "server": received}
        observations["receiverAfterOld"] = server.call("watch", timeout=0.25)
        absent = server.call("finish")
        assert absent["payload"] is None
        observations["blocked"] = {"sent": blocked, "server": None, "timeout": absent}
        observations["qdisc"]["drained"] = qdisc("drained")
        observations["conntrack"]["drained"] = snapshot("drained")
        save("observations.json", observations)
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
