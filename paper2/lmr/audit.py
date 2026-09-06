#!/usr/bin/env python3
"""Static release guard for theorem coverage and forbidden Lean tokens."""

from __future__ import annotations

import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent
THEOREM = re.compile(r"(?m)^theorem\s+([^\s(:{]+)")
AXIOM_PRINT = re.compile(r"(?m)^#print\s+axioms\s+([^\s]+)")
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom declaration": re.compile(r"(?m)^\s*axiom\b"),
    "noncomputable": re.compile(r"\bnoncomputable\b"),
    "Classical.choose": re.compile(r"\bClassical\.choose\b"),
}


def code_only(text: str) -> str:
    """Replace comments and strings with spaces while preserving newlines."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        pair = text[i : i + 2]
        char = text[i]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif in_string:
            if char == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif char == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        elif char == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(char)
            i += 1
    if block_depth or in_string:
        raise SystemExit("FAIL: unterminated comment or string")
    return "".join(out)


def duplicates(names: list[str]) -> list[str]:
    return sorted(name for name, count in Counter(names).items() if count > 1)


def main() -> None:
    sources = sorted(ROOT.glob("*.lean"))
    cleaned = {path: code_only(path.read_text(encoding="utf-8")) for path in sources}
    theorems = [
        name
        for path, text in cleaned.items()
        if path.name != "Check.lean"
        for name in THEOREM.findall(text)
    ]
    qualified_prints = AXIOM_PRINT.findall(cleaned[ROOT / "Check.lean"])
    prints = [name.removeprefix("Rule737.") for name in qualified_prints]

    failures: list[str] = []
    if any(not name.startswith("Rule737.") for name in qualified_prints):
        failures.append("Check.lean must qualify local names to avoid overloaded-name resolution")
    if duplicates(theorems):
        failures.append(f"duplicate theorem names: {duplicates(theorems)}")
    if duplicates(prints):
        failures.append(f"duplicate #print axioms names: {duplicates(prints)}")

    missing = sorted(set(theorems) - set(prints))
    extra = sorted(set(prints) - set(theorems))
    if missing:
        failures.append(f"theorems missing from Check.lean: {missing}")
    if extra:
        failures.append(f"unknown Check.lean entries: {extra}")

    for path, text in cleaned.items():
        for label, pattern in FORBIDDEN.items():
            if pattern.search(text):
                failures.append(f"{path.name}: forbidden token {label}")

    if failures:
        for failure in failures:
            print(f"FAIL: {failure}")
        raise SystemExit(1)

    print(f"PASS: {len(theorems)} theorem declarations")
    print(f"PASS: {len(prints)} matching #print axioms checks")
    print("PASS: no sorry, admit, axiom declaration, noncomputable, or Classical.choose")


if __name__ == "__main__":
    main()
