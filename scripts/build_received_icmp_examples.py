"""Project received ICMP and socket feedback from independently checked native evidence."""

import json
from pathlib import Path

from build_admission_examples import project
from check_received_icmp_capture import check_capture

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/received-icmp"


def build(directory=DIRECTORY):
    evidence = check_capture(directory / "native", input_directory=directory)

    def native(name):
        return json.loads((directory / "native" / name).read_text())

    observed = native("observations.json")
    _, authentication, session = project(evidence, directory)
    configs = [
        {
            "id": stage["stage"],
            **{key: native(stage["exports"][key]["file"]) for key in ["firewall", "nat", "late"]},
        }
        for stage in observed["stages"]
    ]
    configs.append(
        {
            "id": "received-probes",
            **{
                key: native(observed["probeExports"][key]["file"])
                for key in ["firewall", "nat", "late"]
            },
        }
    )
    for config in configs:
        config["forward"] = config.pop("firewall")
    samples = evidence["packetSamples"]
    last_snapshot = {sample["stateFile"]: index for index, sample in enumerate(samples)}
    events = []
    for index, sample in enumerate(samples):
        if sample["label"] == "native-df-oversize-request":
            events.append(
                {
                    "type": "erase",
                    "zone": 0,
                    "raw": samples[0]["raw"],
                    "state": native(evidence["erase"]["state"]["file"]),
                }
            )
        events.append(
            {
                "type": "udp" if sample["ingress"]["protocol"] == 17 else "icmp",
                "config": sample["config"],
                "zone": sample["zone"],
                "raw": sample["raw"],
                "observed": sample["observed"],
                "state": native(sample["stateFile"])
                if last_snapshot[sample["stateFile"]] == index
                else None,
            }
        )
    replay = {
        "schema": 1,
        "routing": {
            "version": "6.19.0",
            "bindings": [
                {"device": "auth0", "nextNode": "peer", "gateway": None},
                {"device": "service0", "nextNode": "service", "gateway": "198.51.101.254"},
                {"device": "service0", "nextNode": "transit", "gateway": None},
            ],
            "routes": native("network-auth-routes.json"),
        },
        "mtus": [
            {"nextHop": "peer", "mtu": 4096},
            {"nextHop": "service", "mtu": 1500},
            {"nextHop": "transit", "mtu": 1500},
        ],
        "configs": configs,
        "initial": native(evidence["initialFile"]),
        "events": events,
    }
    host_events = []

    def query(record):
        host_events.append(
            {
                "type": "query",
                "at": record["endNs"] // 1_000_000_000,
                "mtu": record["result"]["mtu"],
            }
        )

    by_label = {sample["label"]: sample for sample in samples}

    def receive(record):
        sample = by_label.get(record["name"])
        if not sample or not sample["outputFamily"] or record["error"]["result"] is None:
            return
        host_events.append(
            {
                "type": "receive",
                "at": record["error"]["endNs"] // 1_000_000_000,
                "raw": sample["outputFamily"]["raw"],
                "mtu": None,
            }
        )

    for record in observed["hostFeedback"]:
        query(record["mtuBefore"])
        sent = record["sent"]["result"]
        payload_size = sent.get("bytesSent", 1200)
        host_events.append(
            {
                "type": "send",
                "at": record["sent"]["endNs"] // 1_000_000_000,
                "payloadLength": payload_size,
                "df": True,
                "errorsDrained": True,
                "observed": "messageSize" if sent.get("errno") == 90 else "accepted",
            }
        )
        receive(record)
        query(record["mtu"])
    for record in observed["receivedProbes"]:
        receive(record)
        query(record["mtu"])
    host = {
        "schema": 1,
        "route": {"mtu": 4096, "locked": False},
        "policy": {"minimum": 552, "lifetime": 600},
        "socket": {
            "source": "192.0.2.2",
            "destination": "203.0.113.2",
            "protocol": 17,
            "sourcePort": 41000,
            "destinationPort": 8080,
        },
        "events": host_events,
    }
    return evidence, authentication, session, replay, host


def main():
    evidence, authentication, session, replay, host = build()
    for name, value in [
        ("checked-evidence", evidence),
        ("authentication", authentication),
        ("session", session),
        ("replay", replay),
        ("host", host),
    ]:
        (DIRECTORY / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    print(f"Built {len(replay['events'])} gateway and {len(host['events'])} host PMTU events.")


if __name__ == "__main__":
    main()
