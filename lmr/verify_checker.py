#!/usr/bin/env python3
"""End-to-end checks for parsing and named conformance failures."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent
cases = [
    ("100 200;150;100 50", "OK"),
    (" 100  200 ; 150 ; 100  50 ", "OK"),
    (";0;", "OK"),
    ("100 bad 200;150;100 50", "PARSE"),
    ("100 200;150;100 bad 50", "PARSE"),
    ("-1 100;50;50", "PARSE"),
    ("100 200;1.5;100 50", "PARSE"),
    ("100 200;150;100 50;extra", "PARSE"),
    ("100 200;150;100", "LENGTH allocation=1 book=2"),
    ("100 200;150;101 49", "CAP at 0: fill 101 > size 100"),
    ("100 200;150;100 40", "CONSERVATION sum=140 expected=150"),
    ("100 200;150;90 60", "SERIAL at 0: partial fill 90/100 with 60 behind"),
]
run = subprocess.run(
    [str(root / ".lake/build/bin/allocation_record")],
    input="\n".join(line for line, _ in cases) + "\n",
    text=True, capture_output=True, check=True,
)
expected = [f"{i}: {verdict}" for i, (_, verdict) in enumerate(cases, 1)]
if run.stdout.splitlines() != expected:
    raise SystemExit(f"FAIL\nExpected: {expected!r}\nReceived: {run.stdout!r}\n{run.stderr}")
print(f"PASS: {len(cases)} executable parser/conformance cases")
