"""Check source files. Do not run Lean."""

import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent

STATIC_HOOKS = {
    "uv run --locked ruff check .",
    "uv run --locked ruff format --check .",
    "uv run --locked python scripts/check_source.py",
    "uv run --locked python scripts/check_text.py",
    "uv run --locked python -m unittest discover -s scripts -p test_*.py",
    "uv run --locked python scripts/check_site.py",
}
STATIC_RUNS = {
    "uv sync --locked --group dev",
    "uv run --locked prek -a --quiet",
    "uv run --locked python scripts/check_site.py",
    "uv run --locked python scripts/check_site.py --extract build/site",
}
ACTIONS = {
    "actions/checkout@v7.0.1",
    "astral-sh/setup-uv@v10.3.3",
    "actions/configure-pages@v6.0.0",
    "actions/upload-pages-artifact@v5.0.0",
    "actions/deploy-pages@v5.0.1",
}


def check_ci(root):
    errors = []
    config = yaml.safe_load((root / ".pre-commit-config.yaml").read_text())
    default = config.get("default_stages", ["pre-commit"])
    for repo in config["repos"]:
        for hook in repo["hooks"]:
            if "pre-commit" not in hook.get("stages", default):
                continue
            if repo["repo"] != "local" or hook.get("language") != "system":
                errors.append("CI hooks must use a reviewed local command.")
            if hook["entry"] not in STATIC_HOOKS:
                errors.append(f"CI must not run hook {hook['id']}: {hook['entry']}")
    for path in root.joinpath(".github/workflows").glob("*.yml"):
        workflow = yaml.safe_load(path.read_text())
        for job in workflow.get("jobs", {}).values():
            for step in job.get("steps", []):
                if "uses" in step and step["uses"] not in ACTIONS:
                    errors.append(f"{path.name}: Review action {step['uses']}.")
                if "run" in step and step["run"].strip() not in STATIC_RUNS:
                    errors.append(f"{path.name}: Review command {step['run']}.")
    return errors


def without_comments(text):
    result = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            result.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            result.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError("Close each block comment.")
    return "".join(result)


def main():
    paths = [
        *ROOT.glob("*.lean"),
        *ROOT.joinpath("Netlib").rglob("*.lean"),
        *ROOT.joinpath("NetlibTest").rglob("*.lean"),
    ]
    modules = {str(p.relative_to(ROOT).with_suffix("")).replace("/", ".") for p in paths}
    errors = []
    graph = {}
    for path in sorted(paths):
        rel = path.relative_to(ROOT)
        code = without_comments(path.read_text())
        forbidden = re.search(r"\b(sorry|admit|sorryAx|native_decide|axiom)\b", code)
        if forbidden:
            errors.append(f"{rel}: Remove {forbidden.group()}.")
        imports = re.findall(r"^\s*(?:public\s+)?import\s+(\S+)", code, re.M)
        local = [m for m in imports if m == "Netlib" or m.startswith(("Netlib.", "NetlibTest."))]
        graph[str(rel.with_suffix("")).replace("/", ".")] = local
        for module in local:
            if module not in modules:
                errors.append(f"{rel}: Import {module} does not exist.")

    def visit(module, active, done):
        if module in active:
            errors.append(f"{module}: Remove the import cycle.")
            return
        if module in done:
            return
        for dependency in graph.get(module, []):
            visit(dependency, active | {module}, done)
        done.add(module)

    done = set()
    for module in graph:
        visit(module, set(), done)
    errors.extend(check_ci(ROOT))
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Source checks passed for {len(paths)} modules. CI did not run a compiler.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
