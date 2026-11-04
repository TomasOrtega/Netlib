"""Check a small set of prose rules. Do not run Lean."""

import re
import sys
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BANNED = {
    "utilize": "use",
    "utilizes": "uses",
    "utilized": "used",
    "leverage": "use",
    "commence": "start",
    "aforementioned": "specified",
    "prior to": "before",
    "in order to": "to",
}
IMPERATIVES = {
    "add",
    "apply",
    "commit",
    "define",
    "disable",
    "do",
    "end",
    "give",
    "handle",
    "install",
    "keep",
    "open",
    "preserve",
    "prove",
    "put",
    "read",
    "reject",
    "remove",
    "review",
    "run",
    "save",
    "select",
    "set",
    "start",
    "state",
    "supply",
    "update",
    "use",
    "validate",
    "verify",
    "write",
}
WORDS = re.compile(r"[A-Za-z0-9]+(?:[-'][A-Za-z0-9]+)*")
CONTRACTIONS = re.compile(
    r"\b(?:[A-Za-z]+n['’]t|[A-Za-z]+['’](?:m|re|ve|ll|d)|"
    r"(?:i|you|he|she|it|we|they|that|there|here|what|who|where|when|why|how|let)"
    r"['’](?:m|re|s|ve|ll|d))\b",
    re.I,
)


@dataclass(frozen=True)
class Issue:
    line: int
    rule: str
    message: str


@dataclass(frozen=True)
class Block:
    text: str
    line: int


def literal(text):
    """Count a literal as one word. Keep its line breaks."""
    return "X" + "".join("\n" if char == "\n" else " " for char in text[1:])


def inline_text(text):
    text = re.sub(r"\{\{[^{}]+\}\}", lambda match: literal(match.group()), text)
    text = re.sub(r"(`+)(.*?)\1", lambda match: literal(match.group()), text, flags=re.S)
    text = re.sub(
        r"<!--.*?-->", lambda match: re.sub(r"[^\n]", " ", match.group()), text, flags=re.S
    )
    text = re.sub(r"<(?:https?://|mailto:)[^>]+>", lambda match: literal(match.group()), text)
    # A quoted source title is a literal, not authored prose.
    text = re.sub(
        r"(?<!\*)\*(?!\*)(.+?)(?<!\*)\*(?!\*)",
        lambda match: literal(match.group()),
        text,
        flags=re.S,
    )
    result = []
    index = 0
    while index < len(text):
        if text[index] == "[":
            end = index + 1
            depth = 1
            while end < len(text) and depth:
                if text[end] == "\\":
                    end += 2
                    continue
                if text[end] == "[":
                    depth += 1
                elif text[end] == "]":
                    depth -= 1
                end += 1
            end -= 1
            if depth == 0 and text[end + 1 : end + 2] in {"(", "["}:
                opener = text[end + 1]
                closer = ")" if opener == "(" else "]"
                depth = 1
                stop = end + 2
                while stop < len(text) and depth:
                    if text[stop] == "\\":
                        stop += 2
                        continue
                    if text[stop] == opener:
                        depth += 1
                    elif text[stop] == closer:
                        depth -= 1
                    stop += 1
                if depth == 0:
                    result.append(" " + inline_text(text[index + 1 : end]) + " ")
                    result.append(re.sub(r"[^\n]", " ", text[end + 1 : stop]))
                    index = stop
                    continue
        result.append(text[index])
        index += 1
    return "".join(result).replace("**", " ").replace("__", " ")


def markdown_blocks(text, start_line=1):
    text = re.sub(
        r"<!--.*?-->", lambda match: re.sub(r"[^\n]", " ", match.group()), text, flags=re.S
    )
    blocks = []
    pending = []
    first_line = start_line
    fence = None
    metadata = False

    def flush():
        if pending:
            blocks.append(Block("\n".join(pending), first_line))
            pending.clear()

    lines = text.splitlines()
    for index, line in enumerate(lines):
        line_number = start_line + index
        marker = re.match(r"^\s{0,3}(`{3,}|~{3,})(.*)$", line)
        if fence:
            if (
                marker
                and marker[1][0] == fence[0]
                and len(marker[1]) >= len(fence)
                and not marker[2].strip()
            ):
                fence = None
            continue
        if marker:
            flush()
            fence = marker[1]
            continue
        if line.strip() == "%%%":
            flush()
            metadata = not metadata
            continue
        if metadata:
            continue
        if index + 1 < len(lines) and re.fullmatch(r"\s*(?:=+|-+)\s*", lines[index + 1]):
            flush()
            continue
        if (
            not line.strip()
            or re.match(r"^\s*(?:#{1,6}\s|>|\[[^]]+\]:|: )", line)
            or re.fullmatch(r"\s*(?:[-*_]\s*){3,}", line)
            or re.fullmatch(r"\s*\*\*[^*]+\*\*:\s*", line)
        ):
            flush()
            continue
        if re.match(r"^\s*\|", line):
            flush()
            cells = inline_text(line).strip().strip("|").split("|")
            for cell in cells:
                if cell.strip() and not re.fullmatch(r"\s*:?-+:?\s*", cell):
                    blocks.append(Block(cell, line_number))
            continue
        item = re.match(r"^\s*(?:[-+*]|\d+[.)])\s+(.*)$", line)
        if item:
            flush()
            first_line = line_number
            pending.append(item[1])
        else:
            if not pending:
                first_line = line_number
            pending.append(line)
    flush()
    return blocks


def glossary_terms(text):
    return set(re.findall(r"^\*\*([^*]+)\*\*:\s*$", text, re.M))


def is_instruction(sentence):
    words = WORDS.findall(sentence.lower())
    return (
        bool(words)
        and words[0] in IMPERATIVES
        and (len(words) == 1 or words[1] not in {"of", "for", "from", "with"})
    )


def check_block(block, allowed_terms=()):
    text = inline_text(block.text)
    allowed = []
    for term in allowed_terms:
        allowed.extend(
            match.span() for match in re.finditer(r"\b" + re.escape(term) + r"\b", text, re.I)
        )
    issues = []

    def report(offset, rule, message):
        issues.append(Issue(block.line + text[:offset].count("\n"), rule, message))

    for match in CONTRACTIONS.finditer(text):
        report(match.start(), "contraction", f"Write {match.group()!r} in full.")
    for word, replacement in BANNED.items():
        for match in re.finditer(r"\b" + re.escape(word) + r"\b", text, re.I):
            if not any(start <= match.start() and match.end() <= end for start, end in allowed):
                report(match.start(), "word", f"Use {replacement!r} instead of {match.group()!r}.")
    offset = 0
    for sentence in re.split(r"(?<=[.!?])\s+", text):
        count = len(WORDS.findall(sentence))
        limit = 20 if is_instruction(sentence) else 25
        if count > limit:
            start = offset + len(sentence) - len(sentence.lstrip())
            report(start, "length", f"Use at most {limit} words. This sentence has {count}.")
        offset += len(sentence)
        while offset < len(text) and text[offset].isspace():
            offset += 1
    return issues


def check_markdown(text, allowed_terms=(), start_line=1):
    return [
        issue
        for block in markdown_blocks(text, start_line)
        for issue in check_block(block, allowed_terms)
    ]


def lean_docstrings(text):
    """Read documentation comments. Ignore source, strings, and other comments."""
    blocks = []
    index = 0
    while index < len(text):
        if text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif text[index] == "«":
            end = text.find("»", index + 1)
            index = len(text) if end < 0 else end + 1
        elif text[index] == "'" and (char := re.match(r"'(?:\\.|[^'\\\n])'", text[index:])):
            index += len(char.group())
        elif text[index] == '"':
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
        elif text.startswith("/-", index):
            documented = text[index : index + 3] in {"/--", "/-!"}
            start = index + (3 if documented else 2)
            index = start
            depth = 1
            content = []
            while index < len(text) and depth:
                if text.startswith("/-", index):
                    depth += 1
                    content.append("  ")
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    if depth:
                        content.append("  ")
                    index += 2
                else:
                    char = text[index]
                    content.append(char if depth == 1 or char == "\n" else " ")
                    index += 1
            if depth:
                raise ValueError("Close each block comment.")
            if documented:
                blocks.append(Block("".join(content), 1 + text[:start].count("\n")))
        else:
            index += 1
    return blocks


def check_lean(text, allowed_terms=()):
    return [
        issue
        for block in lean_docstrings(text)
        for issue in check_markdown(block.text, allowed_terms, block.line)
    ]


def check_manual(text, allowed_terms=()):
    marker = re.search(r"^#doc\b.*?=>[^\n]*\n", text, re.M)
    if marker is None:
        return [Issue(1, "source", "Add the Verso document entry.")]
    return check_markdown(text[marker.end() :], allowed_terms, 1 + text[: marker.end()].count("\n"))


class HTMLProse(HTMLParser):
    BLOCKS = {
        "article",
        "aside",
        "blockquote",
        "br",
        "dd",
        "div",
        "dl",
        "dt",
        "figcaption",
        "figure",
        "footer",
        "h1",
        "h2",
        "h3",
        "h4",
        "h5",
        "h6",
        "header",
        "li",
        "main",
        "nav",
        "ol",
        "p",
        "section",
        "table",
        "td",
        "th",
        "title",
        "tr",
        "ul",
    }
    VOID = {
        "area",
        "base",
        "br",
        "col",
        "embed",
        "hr",
        "img",
        "input",
        "link",
        "meta",
        "source",
        "wbr",
    }

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.blocks = []
        self.parts = []
        self.first_line = 1
        self.last_line = 1
        self.skipped = 0

    def flush(self):
        if self.parts:
            self.blocks.append(Block("".join(self.parts), self.first_line))
            self.parts.clear()

    def add(self, text, line):
        if not text.strip() and not self.parts:
            return
        if not self.parts:
            self.first_line = line
        elif line > self.last_line:
            self.parts.append("\n" * (line - self.last_line))
        else:
            self.parts.append(" ")
        self.parts.append(text)
        self.last_line = line + text.count("\n")

    def handle_starttag(self, tag, attrs):
        if self.skipped:
            if tag not in self.VOID:
                self.skipped += 1
            return
        fields = dict(attrs)
        if (
            tag in {"script", "style", "pre", "code"}
            or "hidden" in fields
            or fields.get("aria-hidden") == "true"
        ):
            if tag == "code":
                self.add("X", self.getpos()[0])
            else:
                self.flush()
            if tag not in self.VOID:
                self.skipped = 1
            return
        if tag in self.BLOCKS:
            self.flush()
        for name in ("alt", "aria-label", "title"):
            if fields.get(name):
                self.blocks.append(Block(fields[name], self.getpos()[0]))
        if tag == "meta" and fields.get("name") == "description" and fields.get("content"):
            self.blocks.append(Block(fields["content"], self.getpos()[0]))

    def handle_endtag(self, tag):
        if self.skipped:
            if tag not in self.VOID:
                self.skipped -= 1
        elif tag in self.BLOCKS:
            self.flush()

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in self.VOID:
            self.handle_endtag(tag)

    def handle_data(self, data):
        if not self.skipped:
            self.add(data, self.getpos()[0])


def check_html(text, allowed_terms=()):
    parser = HTMLProse()
    parser.feed(text)
    parser.close()
    parser.flush()
    return [issue for block in parser.blocks for issue in check_block(block, allowed_terms)]


def main():
    paths = [
        ROOT / "README.md",
        ROOT / "GLOSSARY.md",
        *ROOT.joinpath("docs").glob("*.md"),
        *ROOT.joinpath("Netlib").rglob("*.lean"),
        ROOT / "docbuild/Manual.lean",
        ROOT / "docs/assets/index.html",
    ]
    terms = glossary_terms(ROOT.joinpath("GLOSSARY.md").read_text())
    errors = []
    for path in sorted(paths):
        text = path.read_text()
        if path == ROOT / "docbuild/Manual.lean":
            checker = check_manual
        else:
            checker = {".lean": check_lean, ".html": check_html}.get(path.suffix, check_markdown)
        try:
            issues = checker(text, terms)
        except ValueError as error:
            issues = [Issue(1, "source", str(error))]
        errors.extend(f"{path.relative_to(ROOT)}:{issue.line}: {issue.message}" for issue in issues)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Prose checks passed for {len(paths)} files. Human review is still necessary.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
