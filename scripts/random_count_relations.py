#!/usr/bin/env python3
"""Random-input tests of the count relations R18-R28, and their stability.

Two different questions, both asked on random inputs:

  * **exactness** — the identities (R18-R23, R28) are arithmetic, so on random draws they must hold
    with zero failures.  A single failure is a bug, not noise.
  * **stability** — the laws (R24-R27) are measurements, so what has to be stable is the *constant*:
    estimated on random windows of equal width in log x, it must not drift and must not trend.

The exact group draws random bounds, random twin starts, random handoffs, random quadruplets and
random windows of the twin chain.  The stability group draws 400 random windows spanning a factor 2
in x and estimates, inside each, the twin density constant, the merge density constant, the air
constant and the merge rate; it prints the mean, the spread and the drift against log x.

Run: python3 scripts/random_count_relations.py [TRIALS] [LIM] [--no-lean] [--seed=N]
     (defaults 2000 trials, 1e8; --no-lean skips the Lean cross-check of the definitions)
"""
import sys, math, random, json, subprocess, pathlib
import numpy as np

args = [a for a in sys.argv[1:] if not a.startswith("--")]
TRIALS = int(float(args[0])) if len(args) > 0 else 2000
LIM = int(float(args[1])) if len(args) > 1 else 10 ** 8
DO_LEAN = "--no-lean" not in sys.argv
C2 = 0.6601618158468696
TC = 2 * C2
SEED = int(next((a.split("=")[1] for a in sys.argv if a.startswith("--seed=")), 20261124))
rng = random.Random(SEED)
nprng = np.random.default_rng(SEED)

results = []
def check(name, bad, total):
    ok = bad == 0
    results.append((name, ok, bad, total))
    print("  %-58s %5d/%d %s" % (name, total - bad, total, "ok" if ok else "FAILED"))
    return ok

# ---------------------------------------------------------------- the data
sv = np.ones(LIM + 8, dtype=bool)
sv[:2] = False
for i in range(2, int((LIM + 6) ** 0.5) + 1):
    if sv[i]:
        sv[i * i::i] = False
primes = np.nonzero(sv[:LIM + 1])[0].astype(np.int64)
npt = primes.size
primes2 = np.nonzero(sv[:LIM + 3])[0].astype(np.int64)     # so p+2 is always in range
ts = primes2[sv[primes2 + 2]]
ts = ts[ts <= LIM]
gi = np.searchsorted(primes, ts)                            # global prime index of each twin start
print("  data: %d primes, %d twin starts, %d handoffs to %d"
      % (npt, ts.size, ts.size - 1, LIM))
bpref = np.concatenate(([0], np.cumsum(primes % 6 == 1)))
kpref = np.concatenate(([0], np.cumsum(primes % 6 == 5)))
def B(x): return int(bpref[np.searchsorted(primes, x, "right")])
def K(x): return int(kpref[np.searchsorted(primes, x, "right")])
def P(x): return int(np.searchsorted(primes, x, "right"))
def N(x): return int(np.searchsorted(ts, x, "right"))
airs = np.diff(ts) - 2
merged = np.diff(gi) == 2
airpref = np.concatenate(([0], np.cumsum(airs)))
mpref = np.concatenate(([0], np.cumsum(merged)))
log2p = np.log(ts[1:].astype(float)) ** 2                  # squared log of the arriving start

print("\n== Exact relations, on random inputs")

# R18: P = B + K + 2
bad = 0
for _ in range(TRIALS):
    x = rng.randint(3, LIM)
    if P(x) != B(x) + K(x) + 2: bad += 1
check("R18  P(x) = B(x) + K(x) + 2", bad, TRIALS)

# R19: twin starts > 3 are 5 mod 6; and N <= K + 1
bad = 0
for _ in range(TRIALS):
    p = int(ts[rng.randrange(ts.size)])
    if p > 3 and p % 6 != 5: bad += 1
    x = rng.randint(3, LIM)
    if N(x) > K(x) + 1: bad += 1
check("R19  twin start > 3 is 5 mod 6;  N <= K+1", bad, 2 * TRIALS)

# R20: twin starts > 5 are 11, 17 or 29 mod 30
bad = 0
for _ in range(TRIALS):
    p = int(ts[rng.randrange(ts.size)])
    if p > 5 and p % 30 not in (11, 17, 29): bad += 1
check("R20  twin start > 5 is 11, 17 or 29 mod 30", bad, TRIALS)

# R21: air = 4 mod 6, total = 2 mod 6  (the handoff 3 -> 5 has air 0 and is the one exception)
bad = 0
for _ in range(TRIALS):
    i = rng.randrange(airs.size)
    a = int(airs[i])
    if i == 0 and a == 0: continue
    if a % 6 != 4 or (a + 4) % 6 != 2: bad += 1
check("R21  air = 4 mod 6,  total = air+4 = 2 mod 6", bad, TRIALS)

# R22: the minimal merge (air 4) starts at 11 mod 30 — the theorem's hypothesis is p > 5, and the
# single quadruplet at p = 5 (5,7,11,13) is the exception the hypothesis excludes.
quads = np.nonzero(airs == 4)[0]
big = [i for i in quads if ts[i] > 5]
small = [i for i in quads if ts[i] <= 5]
bad = 0
for _ in range(TRIALS):
    p = int(ts[big[rng.randrange(len(big))]])
    if p % 30 != 11: bad += 1
if [int(ts[i]) for i in small] not in ([], [5]):
    bad += 1
check("R22  air = 4 (quadruplet) starts at 11 mod 30 (p > 5)", bad, TRIALS)

# R23: the telescoping identity, on random windows of the chain
bad = 0
for _ in range(TRIALS):
    i = rng.randrange(ts.size - 1)
    j = min(ts.size - 1, i + rng.randint(1, 500))
    span = int(ts[j]) - int(ts[i])
    if int(airpref[j]) - int(airpref[i]) != span - 2 * (j - i): bad += 1
check("R23  sum of airs = span - 2*handoffs (random windows)", bad, TRIALS)

# R28: segments = handoffs - merges + 1, on random windows
bad = 0
for _ in range(TRIALS):
    i = rng.randrange(ts.size - 1)
    j = min(ts.size - 1, i + rng.randint(1, 200))
    if j - i < 1: continue
    runs = 1 + int(np.count_nonzero(~merged[i:j]))
    if runs != (j - i) - int(mpref[j] - mpref[i]) + 1: bad += 1
check("R28  segments = handoffs - merges + 1 (random windows)", bad, TRIALS)

# ---------------------------------------------------------------- stability
print("\n== Stability of the laws, on random windows (factor 2 in x)")
def li_k(x, k):
    u = np.linspace(math.log(2.0), math.log(float(x)), 20000)
    return float(np.trapezoid(np.exp(u) / u ** k, u))

edges = np.exp(np.linspace(math.log(1e4), math.log(LIM / 2), 401))
idxs = np.searchsorted(ts, edges, "right")
windows = [(float(edges[w]), float(edges[w + 1]), int(idxs[w]), int(idxs[w + 1]))
           for w in range(400) if idxs[w + 1] - idxs[w] >= 50]
nprng.shuffle(windows)
rows = []
for (x1, x2, i, j) in windows:
    dN = j - i                                  # twin starts in the window
    dH = max(1, dN - 1)                         # handoffs between them
    dD = float(mpref[j - 1] - mpref[i])         # merges among those handoffs
    dair = float(airpref[j - 1] - airpref[i])
    t2 = float(np.mean(log2p[i:j - 1])) if j - 1 > i else float(np.mean(log2p[i:j]))
    rows.append(dict(x=math.sqrt(x1 * x2),
                     twin_rate=(dN / (li_k(x2, 2) - li_k(x1, 2))) / TC,
                     merge_rate=(dD / dH) / (TC / math.log(math.sqrt(x1 * x2))),
                     merge_dens=(dD / (li_k(x2, 3) - li_k(x1, 3))) / TC ** 2,
                     gap=(dair / dH + 2.0) / (t2 / TC)))

def stats(key, label):
    v = np.array([r[key] for r in rows])
    lx = np.array([math.log(r["x"]) for r in rows])
    corr = float(np.corrcoef(lx, v)[0, 1]) if v.std() > 0 else 0.0
    within = float(np.mean(np.abs(v - 1) < 0.25))
    print("  %-26s mean %6.4f  sd %6.4f  min %6.3f  max %6.3f  drift %+5.2f  within 25%% %4.1f%%"
          % (label, v.mean(), v.std(), v.min(), v.max(), corr, 100 * within))
    return v, corr
v1, c1 = stats("twin_rate", "N / (2C2 Li2) in the window")
v2, c2 = stats("merge_rate", "D / N / (2C2/log x)")
v3, c3 = stats("merge_dens", "D / ((2C2)^2 Li3)")
v4, c4 = stats("gap", "mean gap / (t^2/(2C2))")
print("  %d windows; largest |drift| against log x: %.2f" % (len(rows), max(abs(c) for c in (c1, c2, c3, c4))))
print("  by log-quartile (mean of each ratio):")
q = np.array_split(np.argsort([r["x"] for r in rows]), 4)
for k, qi in enumerate(q):
    print("    x in [%8.0f, %9.0f]   N %6.3f   D %6.3f   D-dens %6.3f   gap %6.3f"
          % (min(rows[i]["x"] for i in qi), max(rows[i]["x"] for i in qi),
             np.mean([rows[i]["twin_rate"] for i in qi]),
             np.mean([rows[i]["merge_rate"] for i in qi]),
             np.mean([rows[i]["merge_dens"] for i in qi]),
             np.mean([rows[i]["gap"] for i in qi])))
ok_stab = (abs(v1.mean() - 1) < 0.05 and abs(v2.mean() - 1) < 0.10
           and abs(v3.mean() - 1) < 0.15 and abs(v4.mean() - 1) < 0.02
           and max(abs(c) for c in (c1, c2, c3, c4)) < 0.5)
check("stability: R25, R26, R27 and the gap law across random windows", 0 if ok_stab else 1, 1)

# ---------------------------------------------------------------- Lean cross-check
if DO_LEAN:
    print("\n== Lean definitions vs this sieve, on random bounds")
    srcl = pathlib.Path("results/count-formulas.lean")
    out = pathlib.Path(".scratch/verify/eval_counts.lean")
    out.parent.mkdir(parents=True, exist_ok=True)
    ns = sorted({rng.randint(3, 200) for _ in range(60)})
    evals = "\n".join(
        "#eval (Counts.baseCount %d, Counts.ladderCount %d, Counts.twinCount %d, "
        "(Counts.primesUpTo %d).card, Counts.handoffs %d)" % (n, n, n, n, n) for n in ns)
    out.write_text(srcl.read_text() + "\n\n" + evals + "\n")
    res = subprocess.run(["lean", str(out)], capture_output=True, text=True)
    if res.returncode != 0:
        print("  lean failed:"); print(res.stdout[-1500:]); print(res.stderr[-1500:])
        check("Lean counts agree with the sieve on random bounds", 1, 1)
    else:
        import re
        got = re.findall(r"\((\d+), (\d+), (\d+), (\d+), (\d+)\)", res.stdout)
        bad = 0
        if len(got) != len(ns):
            bad = 1
        else:
            for n, (b, k, t, p, h) in zip(ns, got):
                n = int(n)
                ref = (B(n), K(n), int(np.searchsorted(ts, n, "right")), P(n),
                       max(0, int(np.searchsorted(ts, n, "right")) - 1))
                if (int(b), int(k), int(t), int(p), int(h)) != ref:
                    bad += 1
        check("Lean counts agree with the sieve on random bounds", bad, len(ns))

fails = [r for r in results if not r[1]]
print("\n  RANDOM COUNT RELATIONS %s (%d groups, %d checks, %d failed)"
      % ("PASSED" if not fails else "FAILED", len(results),
         sum(r[3] for r in results), len(fails)))
sys.exit(1 if fails else 0)
