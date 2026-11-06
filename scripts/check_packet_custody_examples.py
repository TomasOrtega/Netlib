"""Compare automatic custody, explicit loss, copies, and retained pending packets.

This helper does not compile Lean or send packets.
"""

import argparse
import copy
import json
import subprocess
import tempfile
from pathlib import Path

import campus_tcp_custody_reference as reference
import check_campus_tcp_examples as common
import check_tcp_recovery_examples as recovery_checks

BINARY = common.BINARY


def check(binary=BINARY):
    data = reference.load_fixtures()
    with tempfile.TemporaryDirectory(prefix="netlib-packet-custody-") as directory:
        path = Path(directory) / "input.json"
        for case in data["cases"]:
            recovery_checks.report_case(binary, path, case["input"], case["expected"], case["id"])
        for case in data["inputErrors"]:
            path.write_text(json.dumps(case["input"]))
            result = subprocess.run(
                [str(binary), "campus-tcp", str(path), "--json"],
                cwd=common.ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            assert result.returncode == 2, (case["id"], result.returncode, result.stdout)
            output = result.stdout + result.stderr
            assert output.startswith("error:"), (case["id"], output[:160])
            if "error" in case:
                assert case["error"] in output, (case["id"], output[:160])
        uppercase = copy.deepcopy(data["input"])
        for event in uppercase["events"]:
            for key in ("payloadHex", "rawIPv4Hex"):
                if key in event:
                    event[key] = event[key].upper()
        recovery_checks.report_case(
            binary, path, uppercase, data["cases"][0]["expected"], "uppercase custody bytes"
        )
    counts = {"traces": len(data["cases"]), "errors": len(data["inputErrors"]), "uppercase": 1}
    print("Packet custody comparisons passed: " + json.dumps(counts, sort_keys=True))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    args = parser.parse_args()
    check(args.binary)


if __name__ == "__main__":
    main()
