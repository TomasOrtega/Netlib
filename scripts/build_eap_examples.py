"""Project checked native EAP conversations into declared session traces."""

import json
from pathlib import Path

from check_eap_capture import check_capture

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/eap"
NATIVE = DIRECTORY / "native"


def build():
    evidence = check_capture(NATIVE)
    traces = {}
    for phase in evidence["phases"]:
        terminal = phase["terminalFrame"]
        preceding = phase["frames"][:terminal]
        starts = sum(frame["eapol"]["type"] == 1 for frame in preceding)
        if starts != 1 or any(frame["eapol"]["type"] == 2 for frame in preceding):
            raise ValueError(
                "The native projection requires one initial Start and no earlier Logoff."
            )
        if any(
            frame["eap"] is not None and frame["eap"]["method"] not in (None, 1, 13)
            for frame in preceding
        ):
            raise ValueError(
                "The retained projection supports Identity followed by one TLS method."
            )
        # This is a declared tag, not an EAP wire nonce or a cryptographic observation.
        method_round = 1 + starts
        events = [{"type": "begin", "authorized": None}]
        for position, frame in enumerate(phase["frames"], start=1):
            observed = None
            if phase["name"] == "success" and position == len(phase["frames"]):
                observed = phase["logicalAuthorization"]["afterLogoff"]
            events.append({"type": "frame", "raw": frame["raw"], "authorized": observed})
            if position == terminal:
                method = phase["methodEvidence"]
                observed = (
                    phase["logicalAuthorization"]["beforeLogoff"]
                    if method["accepted"]
                    else phase["logicalAuthorization"]["afterFailure"]
                )
                events.append(
                    {
                        "type": "method",
                        "round": method_round,
                        "subject": method["subject"],
                        "method": method["method"],
                        "accepted": method["accepted"],
                        "source": "; ".join(item["source"] for item in method["source"]),
                        "authorized": observed,
                    }
                )
        traces[phase["name"]] = {
            "schema": 1,
            "context": {
                "consumer": evidence["subject"],
                "producer": "campus-application",
                "issuer": "campus-authority",
            },
            "link": evidence["link"],
            "events": events,
        }
    return evidence, traces


def main():
    evidence, traces = build()
    (DIRECTORY / "checked-evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    for name, trace in traces.items():
        (DIRECTORY / (name + ".json")).write_text(json.dumps(trace, indent=2) + "\n")
    print(
        f"Built {len(traces)} native EAP session traces from {evidence['frameCount']} raw frames."
    )


if __name__ == "__main__":
    main()
