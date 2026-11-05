# Netlib

[![CI](https://github.com/TomasOrtega/Netlib/actions/workflows/checks.yml/badge.svg?branch=main)](https://github.com/TomasOrtega/Netlib/actions/workflows/checks.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0-blue)](lean-toolchain)
[![uv](https://img.shields.io/badge/uv-managed-7c3aed)](https://docs.astral.sh/uv/)
[![Ruff](https://img.shields.io/badge/code%20style-Ruff-D7FF64)](https://docs.astral.sh/ruff/)

Netlib is a Lean library and CLI for network requirements and compliance checks.
It provides architecture proofs, packet and protocol models, and selected Wi-Fi and 5G security profiles.
Reports preserve source clauses, assumptions, and evidence.

## Quick start

Install [elan](https://github.com/leanprover/elan) and
[uv](https://docs.astral.sh/uv/getting-started/installation/).
Then run:

```sh
uv sync --locked
lake build
lake exe netlib demo
```

The demo checks a secure network, a failed replica, and a gateway bypass.
Lean builds run locally. CI checks source files and saved documentation.

## Documentation

| Task | Guide |
| --- | --- |
| Use the CLI and input formats | [Usage](docs/USAGE.md) |
| Check Wi-Fi settings and EAP session traces | [Wi-Fi](docs/WIFI.md), [EAP](docs/EAP.md) |
| Check packet bytes, forwarding, and identity policies | [Packet forwarding](docs/REASSEMBLY.md), [Wire bytes](docs/WIRE.md), [Data plane](docs/DATAPLANE.md) |
| Check every packet in a traffic class | [Traffic classes](docs/TRAFFIC.md) |
| Import Linux forwarding snapshots | [Linux](docs/LINUX.md) |
| Audit native conntrack records and tuple associations | [Conntrack](docs/CONNTRACK.md) |
| Check tracked forwarding and operational cutovers | [Lifecycle](docs/LIFECYCLE.md), [Stateful failover](docs/STATEFUL_FAILOVER.md), [Safe handoff](docs/SAFE_HANDOFF.md), [Campus deployment](docs/CAMPUS_DEPLOYMENT.md) |
| Compile packet or session requirements to a firewall | [Compiler](docs/COMPILER.md), [Session enforcement](docs/SESSION_FIREWALL.md) |
| Bind current sessions to input interfaces and fragment admission | [Ingress attachments](docs/INGRESS_ATTACHMENTS.md), [Fragment admission](docs/FRAGMENT_ADMISSION.md) |
| Do checks of TCP bytes and application events | [TCP application path](docs/TCP_APPLICATION.md) |
| Check rewrites and timed flow authorization | [Stateful models](docs/STATEFUL.md) |
| Check 5G admission traces | [5G](docs/FIVEG.md) |
| Analyze policies and set search budgets | [Solver](docs/SOLVER.md) |
| Inspect formal guarantees | [Proof inventory](docs/PROOFS.md) |
| Run checks or publish documentation | [Build and deployment](docs/TOOLING.md) |
| Review the model and its limits | [Specification](docs/SPECIFICATION.md) |
| Review the full research objective | [Roadmap](docs/ROADMAP.md) |

Profiles check selected requirements under their listed assumptions.
They do not certify live devices or complete security standards.
