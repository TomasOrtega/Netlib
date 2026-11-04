"""Capture a late output-header barrier in private Linux namespaces."""

import importlib.util
import json
import subprocess
import time
from pathlib import Path

BASE = Path("/tmp/netlib-revocation")
HELPER = Path("/task/examples/lifecycle/exercise.py")
spec = importlib.util.spec_from_file_location("lifecycle_endpoint", HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
COMMANDS = []


def save(name, value):
    (BASE / name).write_text(json.dumps(value, indent=2) + "\n")


def native(*arguments, **options):
    command = ["ip", "netns", "exec", "router", *arguments]
    COMMANDS.append(command)
    return subprocess.run(command, check=True, **options)


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


def main():
    load_rules(
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
  ct state established accept comment "ESTABLISHED"
  ct state new ip saddr 192.0.2.0/24 ip daddr 198.51.100.2 udp dport 9000 accept comment "NEW_SERVICE"
 }
}
table ip netlib_barrier {
 chain barrier { type filter hook postrouting priority 110; policy accept; }
}
""",
    )
    for table, name in [
        ("netlib_nat", "nat-initial"),
        ("netlib_filter", "forward-initial"),
        ("netlib_barrier", "barrier-open"),
    ]:
        export_table(table, name)
    for namespace in ["client", "server"]:
        COMMANDS.append(
            ["ip", "netns", "exec", namespace, "python3", str(HELPER), "endpoint", namespace]
        )
    client, server = helper.Endpoint("client"), helper.Endpoint("server")
    for port in [9000, 9003]:
        server.call("bind", port)
    trace_file = (BASE / "trace.txt").open("w")
    errors = (BASE / "trace-errors.txt").open("w")
    command = ["ip", "netns", "exec", "router", "nft", "-j", "monitor", "trace"]
    COMMANDS.append(command)
    trace = subprocess.Popen(command, stdout=trace_file, stderr=errors)
    observations = []

    def packet(phase, sender, receiver, source_port, peer, destination_port, state, delivered):
        sent = sender.call("send", source_port, peer=peer, payload=phase)
        received = receiver.call("receive", destination_port, timeout=2 if delivered else 0.2)
        if delivered:
            if received is None or received["payload"] != phase:
                raise RuntimeError(f"Missing native delivery for {phase}.")
        elif received is not None:
            raise RuntimeError(f"Unexpected native delivery for {phase}.")
        snapshot(state)
        observations.append({"phase": phase, "sent": sent, "received": received, "state": state})

    try:
        time.sleep(0.1)
        if trace.poll() is not None:
            raise RuntimeError("The native trace monitor exited.")
        packet(
            "first-original",
            client,
            server,
            31000,
            ["203.0.113.2", 8080],
            9000,
            "opened-state",
            True,
        )
        packet(
            "first-reply",
            server,
            client,
            9000,
            ["203.0.113.1", 40000],
            31000,
            "replied-state",
            True,
        )
        load_rules(
            "tighten-and-change-nat",
            """flush chain ip netlib_filter forward
add rule ip netlib_filter forward ct state established accept comment "ESTABLISHED"
flush chain ip netlib_nat destination
flush chain ip netlib_nat source
add rule ip netlib_nat destination ip daddr 203.0.113.2 udp dport 8080 dnat to 198.51.100.2:9003
add rule ip netlib_nat source ip saddr 192.0.2.0/24 meta l4proto udp snat to 203.0.113.1:40001
""",
        )
        export_table("netlib_filter", "forward-established-only")
        export_table("netlib_nat", "nat-changed")
        packet(
            "cached-after-update",
            client,
            server,
            31000,
            ["203.0.113.2", 8080],
            9000,
            "retained-state",
            True,
        )
        load_rules(
            "install-barrier",
            """add rule ip netlib_barrier barrier ip daddr 198.51.100.2 meta l4proto udp drop comment "QUARANTINE_BACKEND"
""",
        )
        export_table("netlib_barrier", "barrier-closed")
        packet(
            "cached-after-barrier",
            client,
            server,
            31000,
            ["203.0.113.2", 8080],
            9000,
            "barrier-state",
            False,
        )
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
        packet(
            "fresh-after-delete",
            client,
            server,
            31000,
            ["203.0.113.2", 8080],
            9003,
            "fresh-denied-state",
            False,
        )
        load_rules(
            "allow-fresh",
            """add rule ip netlib_filter forward ct state new ip daddr 198.51.100.2 meta l4proto udp accept comment "NEW_BACKEND"
""",
        )
        export_table("netlib_filter", "forward-fresh-allowed")
        packet(
            "fresh-through-barrier",
            client,
            server,
            31001,
            ["203.0.113.2", 8080],
            9003,
            "fresh-barrier-state",
            False,
        )
        save("observations.json", observations)
    finally:
        client.close()
        server.close()
        time.sleep(0.1)
        trace.terminate()
        trace.wait(timeout=5)
        trace_file.close()
        errors.close()
        save("commands.json", COMMANDS)


if __name__ == "__main__":
    main()
