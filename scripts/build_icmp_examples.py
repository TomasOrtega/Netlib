"""Project independently checked ICMP quotation and forwarding evidence into byte-derived replay."""

import ipaddress
import json
from pathlib import Path

from build_admission_examples import project
from check_icmp_capture import check_capture

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/icmp"


def build(directory=DIRECTORY):
    evidence = check_capture(directory / "native", input_directory=directory)

    def native(name):
        return json.loads((directory / "native" / name).read_text())

    _, authentication, session = project(evidence, directory)
    routing = evidence["routing"]
    configs = [
        {
            "id": config["id"],
            "forward": native(config["forwardFile"]),
            "late": native(config["lateFile"]),
            "nat": native(config["natFile"]),
            "output": native(config["outputFile"]),
            "icmpLate": native(config["icmpLateFile"]),
        }
        for config in evidence["configs"]
    ]
    events = []
    erase = evidence["erase"]
    erased = False
    for sample in evidence["packetSamples"]:
        if sample["label"] == erase["beforeLabel"]:
            if erased:
                raise ValueError("The retained erasure must have exactly one selected boundary.")
            events.append(
                {
                    "type": "erase",
                    "zone": erase["zone"],
                    "raw": erase["raw"],
                    "state": native(erase["stateFile"]),
                }
            )
            erased = True
        events.append(
            {
                "type": "packet",
                "config": sample["config"],
                "zone": sample["zone"],
                "raw": sample["raw"],
                "observed": sample["observed"],
                "state": native(sample["stateFile"]) if sample.get("stateFile") else None,
            }
        )
    if not erased:
        raise ValueError("The native erasure boundary is missing from the packet samples.")
    profile = {
        key: value
        for key, value in evidence["icmpProfile"].items()
        if key not in {"settingsFile", "settingsReadback"}
    }
    devices = {binding["device"] for binding in routing["bindings"]}
    broadcasts = {
        ipaddress.IPv4Network(
            f"{address['local']}/{address['prefixlen']}", strict=False
        ).broadcast_address
        for link in native("network-auth-addresses.json")
        if link["ifname"] in devices
        for address in link.get("addr_info", [])
        if address["family"] == "inet" and address["prefixlen"] <= 30
    }
    profile["broadcasts"] = [str(address) for address in sorted(broadcasts)]
    replay = {
        "schema": 1,
        "routing": {
            "version": routing["version"],
            "bindings": routing["bindings"],
            "routes": native(routing["routesFile"]),
        },
        "mtus": evidence["mtus"],
        "icmpProfile": profile,
        "configs": configs,
        "initial": native(evidence["initialFile"]) if evidence.get("initialFile") else None,
        "events": events,
    }
    return evidence, authentication, session, replay


def main():
    evidence, authentication, session, replay = build()
    for name, value in (
        ("checked-evidence", evidence),
        ("authentication", authentication),
        ("session", session),
        ("replay", replay),
    ):
        (DIRECTORY / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    print(
        f"Built four session checkpoints and {len(replay['events'])} ICMP-aware forwarding events."
    )


if __name__ == "__main__":
    main()
