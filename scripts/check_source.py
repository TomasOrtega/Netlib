"""Check source files. Do not run Lean."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent


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
    paths = [*ROOT.glob("*.lean"), *ROOT.joinpath("Netlib").rglob("*.lean"),
             *ROOT.joinpath("NetlibTest").rglob("*.lean")]
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
    for path in ROOT.joinpath(".github/workflows").glob("*.yml"):
        text = path.read_text()
        if re.search(r"\b(lake|elan|lean|lean4|build_docs\.py)\b", text, re.I):
            errors.append(f"{path.relative_to(ROOT)}: CI must not install or run Lean tools.")
        actions = re.findall(r"uses:\s*([^\s]+)", text)
        for action in actions:
            if not action.startswith("actions/"):
                errors.append(f"{path.relative_to(ROOT)}: Review action {action} before CI can use it.")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Source checks passed for {len(paths)} modules. CI did not run a compiler.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
