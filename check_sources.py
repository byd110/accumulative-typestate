#!/usr/bin/env python3
"""Reject proof holes and new global assumptions in the listed Rocq sources."""
from pathlib import Path
import re
import sys


def without_comments(text):
    depth = 0
    result = []
    i = 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            result.append("  ")
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            result.append("  ")
            i += 2
        else:
            result.append(text[i] if depth == 0 or text[i] == "\n" else " ")
            i += 1
    if depth:
        raise ValueError("unclosed Rocq comment")
    return "".join(result)


root = Path(__file__).resolve().parent
paths = [root / line.strip() for line in (root / "_CoqProject").read_text().splitlines()
         if line.strip().endswith(".v")]
errors = []
for path in paths:
    source = without_comments(path.read_text())
    for match in re.finditer(r"\b(?:Admitted|admit|Abort|Axiom|Axioms|Parameter|Parameters)\b", source):
        line = source.count("\n", 0, match.start()) + 1
        errors.append(f"{path.relative_to(root)}:{line}: {match.group()}")
    if path.parent == root:
        obsolete = r"\b(?:Branch|Do|instruction|paths|paths_spec|path_seq|typed_trace|check_trace|monitored_trace|retire)\b"
        for match in re.finditer(obsolete, source):
            line = source.count("\n", 0, match.start()) + 1
            errors.append(f"{path.relative_to(root)}:{line}: obsolete interface {match.group()}")
    if path.name == "semantics.v":
        for match in re.finditer(r"\b(?:protocols|typestate|soundness|copying_soundness|runtime_monitor)\b", source):
            line = source.count("\n", 0, match.start()) + 1
            errors.append(f"semantics.v:{line}: raw semantics depends on {match.group()}")
if errors:
    print("\n".join(errors), file=sys.stderr)
    sys.exit(1)
print(f"Checked {len(paths)} Rocq sources: no proof holes or new global assumptions.")
