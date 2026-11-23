#!/usr/bin/env python3
"""Check the paper against the files it talks about.

Two jobs:

  1. **names** — every Lean identifier cited in `results/light-bridge-paper.md` and
     `results/light-bridge-coverage.md` must be a declaration in `results/*.lean`. A renamed theorem
     would otherwise leave a citation pointing at nothing.
  2. **numbers** — every measured value the paper quotes in its tables is recomputed from the data
     files (`results/tableU_count_formulas.csv`, `results/tableW_specific_heat.csv`) or from the
     constants, and must agree at the quoted precision. A drifted dataset must not leave a paper
     claiming an old number.

Run from the project root: python3 scripts/check-paper.py
Exit status is non-zero if a name or a number fails.
"""
import csv, math, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = [ROOT / "results" / "light-bridge-paper.md", ROOT / "results" / "light-bridge-coverage.md",
        ROOT / "results" / "one-equation.md", ROOT / "results" / "digit-table.md",
        ROOT / "results" / "class-from-digits.md", ROOT / "results" / "light-chart.md",
        ROOT / "results" / "key-correlations.md", ROOT / "results" / "counterflow-test.md",
        ROOT / "results" / "light-bridge-explained.md", ROOT / "results" / "atom-or-nucleus.md",
        ROOT / "results" / "digit-ratio-equation.md", ROOT / "results" / "per-system-test.md",
        ROOT / "results" / "locked-digits.md", ROOT / "results" / "gap-digits.md",
        ROOT / "results" / "prime-scales.md"]
LEAN = sorted((ROOT / "results").glob("*.lean"))

decl = re.compile(r"^(?:theorem|lemma|def|abbrev|instance|structure)\s+([A-Za-z_][A-Za-z0-9_'✝.]*)", re.M)
ident = re.compile(r"^(?:[A-Z][A-Za-z0-9]*\.)?[a-z_][A-Za-z0-9_']*$")

known = set()
for f in LEAN:
    for name in decl.findall(f.read_text(encoding="utf-8")):
        known.add(name.split(".")[-1])
# names that are Lean/Mathlib identifiers used in prose but not declared here
EXEMPT = {"lean", "sorry", "axiom", "propext", "decide", "rfl", "simp", "omega", "ring", "norm_num",
          "linarith", "field_simp", "native_decide", "theorem", "lemma", "def", "namespace"}

fail = 0
cited, missing = 0, []
for doc in DOCS:
    text = doc.read_text(encoding="utf-8")
    for tok in re.findall(r"`([^`\n]+)`", text):
        tok = tok.strip()
        if not ident.match(tok):
            continue
        if tok.rsplit(".", 1)[-1] in {"md", "py", "csv", "lean", "sh", "tex", "pdf", "json", "toml"}:
            continue
        if tok in EXEMPT:
            continue
        cited += 1
        base = tok.split(".")[-1]
        if base not in known:
            missing.append((doc.name, tok))
print("  names: %d identifiers cited, %d unresolved" % (cited, len(missing)))
for m in missing:
    print("    MISSING: %s cites `%s`" % m)
if missing:
    fail = 1

# ---------------------------------------------------------------- numbers
def close(a, b, tol):
    return abs(a - b) <= tol * max(1.0, abs(b))

checks = []
def want(label, got, exp, tol):
    ok = close(got, exp, tol)
    checks.append((label, got, exp, ok))

rows = list(csv.DictReader(open(ROOT / "results" / "tableU_count_formulas.csv")))
last = rows[-1]
assert int(last["x"]) == 10 ** 9, last["x"]
want("pi(1e9)", int(last["pi"]), 50847534, 0)
want("B(1e9)", int(last["base_1mod6"]), 25422713, 0)
want("K(1e9)", int(last["twinkey_5mod6"]), 25424819, 0)
want("N(1e9)", int(last["twin_starts"]), 3424506, 0)
want("D(1e9)", int(last["double_twins"]), 234287, 0)

heat = list(csv.DictReader(open(ROOT / "results" / "tableW_specific_heat.csv")))
q = sorted(float(r["C_over_3R"]) for r in heat)
med = q[len(q) // 2] if len(q) % 2 else 0.5 * (q[len(q) // 2 - 1] + q[len(q) // 2])
want("median C/3R", med, 1.038, 5e-4)
want("n elements with C", len(heat), 78, 0)
want("quantum solids", sum(x < 0.95 for x in q), 7, 0)
want("classical", sum(abs(x - 1) <= 0.1 for x in q), 56, 0)
want("soft", sum(x > 1.15 for x in q), 10, 0)
want("within 10% (%)", 100 * sum(abs(x - 1) < 0.1 for x in q) / len(q), 72, 0.01)

C2 = 0.6601618158468696
R = 8.314462618
want("2C2", 2 * C2, 1.3203236, 1e-6)
want("1/(2C2)", 1 / (2 * C2), 0.757390, 1e-6)
want("kappa", (1 / (2 * C2)) / (3 * R), 0.030364, 1e-4)

# theorem counts quoted in Appendix A
per_file = {}
for f in LEAN:
    per_file[f.stem] = len(re.findall(r"^theorem ", f.read_text(encoding="utf-8"), re.M))
want("total theorems", sum(per_file.values()), 249, 0)
for stem, n in [("master-theorem", 45), ("light-bridge-theorems", 21), ("scale-theorems", 23),
                ("promotion-theorems", 27), ("merge-theorems", 12), ("generative-key", 12),
                ("fission-theorem", 30), ("count-formulas", 16), ("specific-heat", 19),
                ("one-equation", 14), ("digit-roles", 20), ("prime-scales", 10)]:
    want("theorems in %s" % stem, per_file.get(stem, -1), n, 0)

eq = list(csv.DictReader(open(ROOT / "results" / "tableX_one_equation.csv")))
lastq = eq[-1]
want("mean log^2 in the top decade", float(lastq["mean_log2"]), 398.10, 1e-4)
tot_n = sum(int(r_["handoffs"]) for r_ in eq)
want("mean log^2 over the whole chain",
     sum(int(r_["handoffs"]) * float(r_["mean_log2"]) for r_ in eq) / tot_n, 385.47, 2e-4)
want("span/pred at 1e9", float(lastq["span_over_pred"]), 1.000224, 1e-5)
want("handoffs in the top decade", int(lastq["handoffs"]), 2984194, 0)
want("c(decade) at 1e8-1e9", float(lastq["c_decade"]), 0.75755, 1e-4)
for r_ in eq:
    if int(r_["x"]) == 10 ** 7:
        want("c(decade) at 1e6-1e7", float(r_["c_decade"]), 0.75326, 1e-4)

for label, got, exp, ok in checks:
    print("  %-22s %-14s (paper: %-12s) %s"
          % (label, ("%.6g" % got) if isinstance(got, float) else got, exp, "ok" if ok else "MISMATCH"))
    if not ok:
        fail = 1

print("  PAPER CHECKS %s" % ("PASSED" if not fail else "FAILED"))
sys.exit(1 if fail else 0)
