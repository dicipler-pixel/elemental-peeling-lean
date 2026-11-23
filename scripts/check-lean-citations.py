#!/usr/bin/env python3
"""Check that every Lean name a results/*.md file cites exists in results/*.lean.

The prose cites lemmas as *(Lean: `name`)*.  A renamed or never-written lemma
silently turns a proof claim into a broken pointer, so:

  * collect every backticked token in a ``Lean:`` citation,
  * look it up among the `theorem`/`lemma`/`def` declarations of results/*.lean,
  * report citations that resolve to nothing, and the theorem counts per file,
  * report any `sorry`, `admit` or `axiom` found in those files.

Run from the project root:  python3 scripts/check-lean-citations.py
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = sorted((ROOT / "results").glob("*.lean"))
DOCS = sorted((ROOT / "results").glob("*.md"))

decl = re.compile(r"^(?:theorem|lemma|def|abbrev|instance|structure)\s+([A-Za-z_][A-Za-z0-9_'✝.]*)", re.M)
cite = re.compile(r"Lean:\s*([^*\n]*)")
token = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*)`")

# names cited in prose that are tactics or Mathlib lemmas, not local declarations
TACTICS = {"ring", "omega", "norm_num", "simp", "decide", "linarith", "nlinarith", "interval_cases",
           "rcases", "induction", "exact", "refine", "intro", "positivity", "field_simp", "ring_nf",
           "assumption", "trivial", "native_decide", "push_cast", "simp_all", "cases", "subst"}


def strip_comments(src: str) -> str:
    """Drop `/- ... -/` and `-- ...` so prose inside comments is not read as a tactic."""
    src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    return re.sub(r"--[^\n]*", " ", src)


names, counts, bad = set(), {}, []
for f in LEAN:
    src = f.read_text(encoding="utf-8")
    found = decl.findall(src)
    counts[f.name] = len(found)
    names.update(found)
    code = strip_comments(src)
    for word in ("sorry", "admit", "axiom"):
        if re.search(r"(?<![A-Za-z_.])" + word + r"(?![A-Za-z_])", code):
            bad.append(f"{f.name}: contains `{word}`")

missing = []
for d in DOCS:
    for m in cite.finditer(d.read_text(encoding="utf-8")):
        for n in token.findall(m.group(1)):
            if n in names or n in TACTICS or "." in n:
                continue
            missing.append(f"{d.name}: cites `{n}` — no such declaration")

print("declarations per Lean file")
for k, v in counts.items():
    print(f"  {k:34s} {v:3d} theorems/defs, {v} declared")
if bad:
    print("\nproof-status flags")
    for b in bad:
        print("  " + b)
if missing:
    print("\ncitations that resolve to nothing")
    for m in missing:
        print("  " + m)
    sys.exit(1)
print("\nall Lean citations resolve")
