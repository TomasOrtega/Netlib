"""Project checked native IPv4 arrivals, completions, and timeout controls."""

import copy
import ipaddress
import json
from pathlib import Path

import check_reassembly_capture as capture
from build_admission_examples import project

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/reassembly"
OUTPUTS = ("checked-evidence", "authentication", "session", "replay", "timeout")


def _first_key(expired):
    data = bytes.fromhex(expired["firstRawIPv4"])
    return {
        "zone": expired["zone"],
        "vif": expired["vif"],
        "source": str(ipaddress.IPv4Address(data[12:16])),
        "destination": str(ipaddress.IPv4Address(data[16:20])),
        "protocol": data[9],
        "identification": int.from_bytes(data[4:6], "big"),
    }


def _allocations(event):
    allocations = []
    keys = set()
    for emission in event["timeoutEmissions"]:
        first = [
            queue
            for queue in event["expired"]
            if queue["firstSource"] == emission["quotedFirstSource"]
        ]
        capture.require(
            len(first) == 1,
            "A timeout allocation requires one exact expired first-fragment source.",
        )
        key = _first_key(first[0])
        identity = tuple(key.items())
        capture.require(identity not in keys, "A timeout queue allocation is repeated.")
        keys.add(identity)
        allocations.append({"key": key, "identification": emission["identification"]})
    return allocations


def _event_contract(events):
    last = {event["stepIndex"]: index for index, event in enumerate(events)}
    states, arrivals = set(), set()
    previous_time, previous_step = -1, -1
    for index, event in enumerate(events):
        capture.require(
            previous_time <= event["at"] and previous_step <= event["stepIndex"],
            "Checked reassembly events must retain native time and step order.",
        )
        previous_time, previous_step = event["at"], event["stepIndex"]
        terminal = index == last[event["stepIndex"]]
        capture.require(
            (event["stateFile"] is not None) == terminal,
            "Only the terminal actual event of each native step may carry its post-dump.",
        )
        if terminal:
            capture.require(
                event["stateFile"] not in states,
                "Distinct native steps cannot reuse a post-dump artifact.",
            )
            states.add(event["stateFile"])
        if event["type"] == "fragment":
            pre = event["source"]["pre"]
            identity = (pre["file"], pre["line"])
            capture.require(identity not in arrivals, "A native PRE arrival source is repeated.")
            arrivals.add(identity)
        capture.require(event["namespace"] == "auth", "Select the checked gateway namespace.")


def build(directory=DIRECTORY):
    directory = Path(directory)
    evidence = capture.check_capture(directory / "native", input_directory=directory)

    def native(name):
        return json.loads((directory / "native" / name).read_text())

    _, authentication, session = project(evidence, directory)
    samples = evidence["events"]
    _event_contract(samples)
    events = []
    for sample in samples:
        event = {
            "type": sample["type"],
            "at": sample["at"],
            "state": native(sample["stateFile"]) if sample["stateFile"] is not None else None,
        }
        if sample["type"] == "fragment":
            event.update(
                config=sample["config"],
                queuePolicy=sample["queuePolicy"],
                zone=sample["zone"],
                vif=sample["vif"],
                rawIPv4=sample["rawIPv4"],
                observed=copy.deepcopy(sample["observed"]),
            )
        elif sample["type"] == "erase":
            event.update(zone=sample["zone"], rawIPv4=sample["rawIPv4"])
        else:
            capture.require(sample["type"] == "wait", "Unsupported checked reassembly event.")
        events.append(event)
    routing = evidence["routing"]
    replay = {
        "schema": 1,
        "routing": {
            "version": routing["version"],
            "bindings": copy.deepcopy(routing["bindings"]),
            "routes": native(routing["routesFile"]),
        },
        "mtus": copy.deepcopy(evidence["mtus"]),
        "configs": [
            {
                "id": config["id"],
                "forward": native(config["forwardFile"]),
                "nat": native(config["natFile"]),
                "late": native(config["lateFile"]),
            }
            for config in evidence["configs"]
        ],
        "initial": native(evidence["initialFile"]),
        "reassembly": {
            "userBase": evidence["userBase"],
            "policies": copy.deepcopy(evidence["queuePolicies"]),
        },
        "events": events,
    }
    contexts, controls, sources = [], [], {}
    for index, sample in enumerate(samples):
        binding = (sample["outputPolicyFile"], sample["latePolicyFile"])
        if binding not in sources:
            context = f"native-timeout-{sample['stepIndex']}"
            sources[binding] = context
            contexts.append(
                {
                    "id": context,
                    **copy.deepcopy(evidence["timeoutRouting"]),
                    "output": native(binding[0]),
                    "late": native(binding[1]),
                }
            )
        controls.append(
            {
                "event": index,
                "context": sources[binding],
                "identifications": _allocations(sample),
                "observed": [emission["rawEthernet"] for emission in sample["timeoutEmissions"]],
            }
        )
    timeout = {
        "schema": 1,
        "forwarding": copy.deepcopy(replay),
        "contexts": contexts,
        "controls": controls,
    }
    return evidence, authentication, session, replay, timeout


def main():
    outputs = build()
    for name, value in zip(OUTPUTS, outputs, strict=True):
        (DIRECTORY / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    evidence, _, session, replay, timeout = outputs
    print(
        f"Built {len(replay['events'])} native reassembly events, "
        f"{len(session['snapshots'])} EAP checkpoints, and "
        f"{sum(len(row['observed']) for row in timeout['controls'])} timeout emissions "
        f"from {len(evidence['events'])} checked event sources."
    )


if __name__ == "__main__":
    main()
