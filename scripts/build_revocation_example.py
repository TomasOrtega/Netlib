"""Build the barrier replay from independently checked native observations."""

import json
from pathlib import Path

from check_revocation_capture import check_capture

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/revocation"
NATIVE = DIRECTORY / "native"


def read_json(path):
    return json.loads(path.read_text())


def build():
    evidence = check_capture(NATIVE)
    if "iproute2-6.19.0" not in (NATIVE / "iproute2-version.txt").read_text():
        raise ValueError("Require the recorded iproute2 6.19.0 route producer.")
    configs = []
    for name, forward, late, nat in [
        ("initial", "forward-initial", "barrier-open", "nat-initial"),
        ("tightened", "forward-established-only", "barrier-open", "nat-changed"),
        ("barrier", "forward-established-only", "barrier-closed", "nat-changed"),
        ("fresh-allowed", "forward-fresh-allowed", "barrier-closed", "nat-changed"),
    ]:
        configs.append(
            {
                "id": name,
                "forward": read_json(NATIVE / (forward + ".json")),
                "late": read_json(NATIVE / (late + ".json")),
                "nat": read_json(NATIVE / (nat + ".json")),
            }
        )
    events = []
    erase = evidence["erase"]
    for phase in evidence["phases"]:
        if phase["phase"] == erase["beforePhase"]:
            events.append(
                {
                    "type": "erase",
                    "zone": erase["zone"],
                    "packet": erase["packet"],
                    "state": read_json(NATIVE / erase["snapshot"]),
                }
            )
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
                "config": phase["config"],
                "zone": 0,
                "packet": phase["input"],
                "observed": observed,
                "state": read_json(NATIVE / phase["snapshot"]),
            }
        )
    replay = {
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
        "initial": None,
        "events": events,
    }
    forbidden = {
        "source": None,
        "destination": {"address": 3325256706, "length": 32},
        "protocol": 17,
        "sourcePorts": None,
        "destinationPorts": None,
    }
    start = next(index for index, event in enumerate(events) if event.get("config") == "barrier")
    return evidence, replay, forbidden, start


def main():
    evidence, replay, forbidden, start = build()
    for name, value in [
        ("checked-evidence", evidence),
        ("replay", replay),
        ("forbidden", forbidden),
    ]:
        (DIRECTORY / (name + ".json")).write_text(json.dumps(value, indent=2) + "\n")
    print(f"Built {len(replay['events'])} replay operations; barrier cutover is --from {start}.")


if __name__ == "__main__":
    main()
