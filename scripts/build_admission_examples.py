"""Project independently checked native admission evidence into session snapshots."""

import json
from pathlib import Path

from check_admission_capture import check_capture

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/admission"


def project(evidence, directory=DIRECTORY):
    phases = evidence["eapEvidence"]["phases"]
    if len(phases) != 1 or phases[0]["name"] != "success":
        raise ValueError("The admission projection requires one successful EAP episode.")
    phase = phases[0]
    frames = phase["frames"]
    preceding = frames[: phase["terminalFrame"]]
    starts = sum(frame["eapol"]["type"] == 1 for frame in preceding)
    if starts != 1 or any(frame["eapol"]["type"] == 2 for frame in preceding):
        raise ValueError("The admission projection requires one Start and no earlier Logoff.")
    if any(
        frame["eap"] is not None and frame["eap"]["method"] not in (None, 1, 13)
        for frame in preceding
    ):
        raise ValueError("The admission projection supports Identity followed by TLS.")
    # Local round 2 is declared from Begin and Start, not a wire freshness proof.
    method_round = 1 + starts
    events = [{"type": "begin", "authorized": None}]
    snapshots = []
    consumed = 0
    installed = False
    for stage in evidence["stages"]:
        count = stage["eapFramesBeforeSend"]
        if not consumed <= count <= len(frames):
            raise ValueError("Native stage frame prefixes must be ordered and bounded.")
        while consumed < count:
            frame = frames[consumed]
            events.append(
                {
                    "type": "frame",
                    "raw": frame["raw"],
                    "authorized": (
                        phase["logicalAuthorization"]["afterLogoff"]
                        if consumed + 1 == len(frames)
                        else None
                    ),
                }
            )
            consumed += 1
            if consumed == phase["terminalFrame"]:
                method = phase["methodEvidence"]
                events.append(
                    {
                        "type": "method",
                        "round": method_round,
                        "subject": method["subject"],
                        "method": method["method"],
                        "accepted": method["accepted"],
                        "source": "; ".join(
                            "native/eap/" + item["source"] for item in method["source"]
                        ),
                        "authorized": phase["logicalAuthorization"]["beforeLogoff"],
                    }
                )
        if stage["credentialInstalled"] and not installed:
            if consumed < phase["terminalFrame"] or consumed >= phase["logoffFrame"]:
                raise ValueError(
                    "The declared credential must be installed after EAP and before Logoff."
                )
            events.append(
                {"type": "install", "credential": evidence["credential"], "authorized": True}
            )
            installed = True
        if not stage["credentialInstalled"] and installed:
            raise ValueError(
                "The retained controller credential installation cannot move backward."
            )
        snapshots.append(
            {
                "after": len(events),
                "firewall": json.loads((directory / "native" / stage["firewallFile"]).read_text()),
            }
        )
    if consumed != len(frames) or not installed:
        raise ValueError("The stage projection must cover every frame and the declared credential.")
    authentication = {
        "schema": 1,
        "context": {
            "consumer": evidence["eapEvidence"]["subject"],
            "producer": "campus-application",
            "issuer": "campus-authority",
        },
        "link": evidence["eapEvidence"]["link"],
        "events": events,
    }
    bundle = {
        "schema": 1,
        "authentication": authentication,
        "intent": json.loads((directory / "requirements.json").read_text()),
        "snapshots": snapshots,
    }
    return evidence, authentication, bundle


def build(directory=DIRECTORY):
    evidence = check_capture(directory / "native", input_directory=directory)
    return project(evidence, directory)


def main():
    evidence, authentication, bundle = build()
    for name, value in (
        ("checked-evidence", evidence),
        ("authentication", authentication),
        ("bundle", bundle),
    ):
        (DIRECTORY / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    print(
        f"Built {len(bundle['snapshots'])} session firewall snapshots from "
        f"{evidence['eapFrameCount']} EAPOL and {evidence['frameCount']} UDP frames."
    )


if __name__ == "__main__":
    main()
