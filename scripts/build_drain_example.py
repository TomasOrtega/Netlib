"""Project independently checked delayed delivery into a buffered replay."""

import json
from pathlib import Path

from check_drain_capture import check_capture

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/drain"
NATIVE = DIRECTORY / "native"


def read_json(path):
    return json.loads(path.read_text())


def build():
    evidence = check_capture(NATIVE)
    if "iproute2-6.19.0" not in (NATIVE / "iproute2-version.txt").read_text():
        raise ValueError("Require the recorded iproute2 6.19.0 route producer.")
    configs = [
        {
            "id": name,
            "forward": read_json(NATIVE / "forward.json"),
            "late": read_json(NATIVE / (late + ".json")),
            "nat": read_json(NATIVE / "nat.json"),
        }
        for name, late in [("before", "late-before"), ("barrier", "late-after")]
    ]
    events = []
    for phase, config, snapshot in zip(
        evidence["phases"], ["before", "barrier"], ["pending-state", "blocked-state"], strict=True
    ):
        observed = {
            key: phase[key]
            for key in [
                "fresh",
                "afterDestination",
                "afterSource",
                "nextHop",
                "disposition",
                "output",
            ]
        }
        observed["classification"] = phase["state"]
        events.append(
            {
                "type": "packet",
                "config": config,
                "zone": 0,
                "packet": phase["inputPacket"],
                "observed": observed,
                "state": read_json(NATIVE / (snapshot + ".json")),
            }
        )
    admitted = evidence["phases"][0]["output"]
    replay = {
        "schema": 1,
        "lifecycle": {
            "schema": 1,
            "routing": {
                "version": "6.19.0",
                "bindings": [
                    {"device": "inside0", "nextNode": "client", "gateway": None},
                    {"device": "outside0", "nextNode": "server", "gateway": None},
                ],
                "routes": read_json(NATIVE / "routes.json"),
            },
            "configs": configs,
            "initial": read_json(NATIVE / "initial-state.json"),
            "events": events,
        },
        "initialPending": [],
        "schedule": [
            {"type": "operation", "pending": [admitted]},
            {"type": "operation", "pending": [admitted]},
            {"type": "serve", "capacity": 1, "served": [admitted], "pending": []},
        ],
    }
    forbidden = {
        "source": None,
        "destination": {"address": 3325256706, "length": 32},
        "protocol": 17,
        "sourcePorts": None,
        "destinationPorts": None,
    }
    return evidence, replay, forbidden, 1, 3


def main():
    evidence, replay, forbidden, start, drained_at = build()
    for name, value in [
        ("checked-evidence", evidence),
        ("replay", replay),
        ("forbidden", forbidden),
    ]:
        (DIRECTORY / (name + ".json")).write_text(json.dumps(value, indent=2) + "\n")
    print(f"Built buffered replay: --from {start} --drained-at {drained_at}.")


if __name__ == "__main__":
    main()
