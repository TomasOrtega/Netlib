"""Build the replay input from independently checked native observations."""

import json
from pathlib import Path

from check_lifecycle_capture import check_capture, read_json

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/lifecycle"
NATIVE = DIRECTORY / "native"


def build():
    evidence = check_capture(NATIVE)
    if "iproute2-6.19.0" not in (NATIVE / "iproute2-version.txt").read_text():
        raise ValueError("Require the recorded iproute2 6.19.0 route producer.")
    configs = []
    for name, forward, nat in [
        ("initial", "forward-initial", "nat-initial"),
        ("nat-updated", "forward-initial", "nat-changed"),
        ("reply-drop", "forward-drop-reply", "nat-changed"),
        ("established-only", "forward-established-only", "nat-changed"),
    ]:
        configs.append(
            {
                "id": name,
                "forward": read_json(NATIVE / (forward + ".json")),
                "late": read_json(NATIVE / "late.json"),
                "nat": read_json(NATIVE / (nat + ".json")),
            }
        )
    states = {
        "forward-drop": "forward-drop-state",
        "late-drop": "late-drop-state",
        "first-original": "opened-state",
        "unreplied-after-nat-update": "unreplied-updated-state",
        "first-reply-dropped": "reply-dropped-state",
        "fresh-after-update": "updated-state",
        "old-after-delete": "after-delete-packet-state",
    }
    first_original = next(
        phase["input"] for phase in evidence["phases"] if phase["phase"] == "first-original"
    )
    events = []
    for phase in evidence["phases"]:
        name = phase["phase"]
        if name == "old-after-delete":
            events.append(
                {
                    "type": "erase",
                    "zone": 0,
                    "packet": first_original,
                    "state": read_json(NATIVE / "deleted-state.json"),
                }
            )
        config = "initial"
        if name == "unreplied-after-nat-update":
            config = "nat-updated"
        elif name == "first-reply-dropped":
            config = "reply-drop"
        elif name in {
            "existing-after-update",
            "existing-after-update:reply",
            "fresh-after-update",
            "old-after-delete",
        }:
            config = "established-only"
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
                "packet": phase["input"],
                "observed": observed,
                "state": read_json(NATIVE / (states[name] + ".json")) if name in states else None,
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
    return evidence, replay


def main():
    evidence, replay = build()
    (DIRECTORY / "checked-evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    (DIRECTORY / "replay.json").write_text(json.dumps(replay, indent=2) + "\n")
    print(
        f"Built lifecycle replay for {len(replay['events'])} operations and {evidence['traceCount']} native packet traces."
    )


if __name__ == "__main__":
    main()
