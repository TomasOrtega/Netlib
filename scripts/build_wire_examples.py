"""Project checked native wire bytes and the shared session checkpoints."""

import json
from pathlib import Path

from build_admission_examples import project
from check_wire_capture import check_capture

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/wire"


def build(directory=DIRECTORY):
    evidence = check_capture(directory / "native", input_directory=directory)
    _, authentication, bundle = project(evidence["admissionEvidence"], directory)
    frame = {"schema": 1, "raw": evidence["frames"][0]["raw"]}
    return evidence, authentication, bundle, frame


def main():
    evidence, authentication, bundle, frame = build()
    for name, value in (
        ("checked-evidence", evidence),
        ("authentication", authentication),
        ("bundle", bundle),
        ("frame", frame),
    ):
        (DIRECTORY / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    print(f"Built four session checkpoints and {evidence['frameCount']} verified UDP wire frames.")


if __name__ == "__main__":
    main()
