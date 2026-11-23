#!/usr/bin/env python3
"""Cross-check: the *proved* Lean definitions versus the Python the record computes with.

Random Laws (scripts/random_laws.py) checks that the identities hold in one implementation. This
script closes the other half of the loop: it appends `#eval` lines to a copy of
`results/master-theorem.lean`, runs Lean, parses the printed values of `period`, `cnt`, `counted`
and `closed` on the same random inputs, and compares them with the reference implementation.

Run: python3 scripts/random_lean_cross.py [n] [seed]
"""
import random, subprocess, sys, pathlib, re

N = int(sys.argv[1]) if len(sys.argv) > 1 else 120
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 20261123
SRC = pathlib.Path("results/master-theorem.lean")
OUT = pathlib.Path(".scratch/verify/eval_master.lean")

# --- the reference implementation (identical to random_laws.py)
C = [0, 2, 10, 18, 36, 54, 86, 118]
def L(m): return 2 * ((((m + 1) + 1) // 2)) ** 2
def period(Z):
    for m in range(1, 8):
        if Z <= C[m]: return m
def cnt(Z): return C[period(Z)] - Z
def counted(Z): return Z - C[period(Z) - 1]
def block(Z):
    m, h = period(Z), cnt(Z)
    if h in (L(m) - 2, L(m) - 1): return "s"
    if h <= 5: return "p"
    if h <= 15: return "d"
    if h <= 29: return "f"
    return "?"
def closed(Z): return block(Z) in ("p", "s")

rng = random.Random(SEED)
Zs = sorted({rng.randint(1, 118) for _ in range(N)})

OUT.parent.mkdir(parents=True, exist_ok=True)
body = SRC.read_text()
lines = "\n".join(
    "#eval (Master.period %d, Master.cnt %d, Master.counted %d, decide (Master.closed %d))" % (z, z, z, z)
    for z in Zs)
OUT.write_text(body + "\n\n" + lines + "\n")
res = subprocess.run(["lean", str(OUT)], capture_output=True, text=True)
if res.returncode != 0:
    print("Lean failed:"); print(res.stdout[-2000:]); print(res.stderr[-2000:]); sys.exit(1)

tuples = re.findall(r"\((\d+), (\d+), (\d+), (true|false)\)", res.stdout)
if len(tuples) != len(Zs):
    print("expected %d evaluations, parsed %d" % (len(Zs), len(tuples)))
    print(res.stdout[-500:]); sys.exit(1)

bad = []
for z, (pm, cm, vm, cl) in zip(Zs, tuples):
    got = (int(pm), int(cm), int(vm), cl == "true")
    want = (period(z), cnt(z), counted(z), closed(z))
    if got != want: bad.append((z, got, want))

print("compared %d random cells: Lean vs the reference implementation" % len(Zs))
print("  fields: period, countdown h, counted part v, closed")
if bad:
    for z, got, want in bad[:10]:
        print("  MISMATCH Z=%d  Lean %s  python %s" % (z, got, want))
    sys.exit(1)
print("  all %d agree" % len(Zs))
# also report the attribute coverage
print("  cells covered: %d distinct Z, blocks hit: %s"
      % (len(Zs), sorted({block(z) for z in Zs})))
