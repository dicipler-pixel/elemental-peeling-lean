#!/usr/bin/env python3
"""Reliability of the one equation, on random data and on regular data.

The equation is `span = sum log^2 p / (2C2)`, i.e. `air = log^2 p/(2C2) - 2` per handoff. The
cumulative statement is a tautology given the airs (it telescopes), so the reliability that has to be
tested is the *per-handoff* one, and the question is whether it holds wherever you cut the chain:

  regular data   — decade boundaries, half-decades, a regular grid of cut points;
  random data    — random windows, random halves, random subsamples;
  controls       — the air values permuted across positions (the law must get worse),
                   and synthetic chains built to obey the law (the estimator must recover it).

Reports, per group, the estimate of `c·2C2` (1 if the law holds), its standard error, and the
calibration of the z-scores. Writes results/tableY_reliability.csv.

Run: python3 scripts/reliability.py [LIM] [TRIALS]
"""
import sys, csv, math, random
import numpy as np

LIM = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 9
TRIALS = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
rng = np.random.default_rng(20261126)
py = random.Random(20261126)
C2 = 0.6601618158468696
TC = 2 * C2

sv = np.ones(LIM + 8, dtype=bool)
sv[:2] = False
for i in range(2, int((LIM + 6) ** 0.5) + 1):
    if sv[i]:
        sv[i * i::i] = False
pr = np.nonzero(sv[:LIM + 3])[0].astype(np.int64)
ts = pr[sv[pr + 2]]
ts = ts[ts <= LIM]
air = (np.diff(ts) - 2).astype(float)
t2 = np.log(ts[1:].astype(float)) ** 2
a = air + 2.0                      # the gap
res = a - t2 / TC                  # per-handoff residual of the law
n = a.size
print("to 1e%d: %d handoffs; per-handoff residual mean %.3f, s.d. %.1f"
      % (round(math.log10(LIM)), n, res.mean(), res.std()))

rows = []
def report(label, c, se, z=None, extra=""):
    rows.append((label, c, se, "" if z is None else z, extra))
    print("  %-42s c*2C2 = %.5f +- %.5f%s %s"
          % (label, c, se, ("" if z is None else "   (z = %+.2f)" % z), extra))

def est(i0, i1):
    """through-origin coefficient, its standard error, and the z of the law's own residual"""
    q, aa = t2[i0:i1], a[i0:i1]
    c = float((q * aa).sum() / (q * q).sum())
    r = aa - c * q
    se = float(np.sqrt((r * r).sum() / max(1, len(q) - 1) / (q * q).sum()))
    rl = res[i0:i1]                       # the law's residual: not the fitted one
    z = float(rl.mean() / (rl.std() / math.sqrt(len(q)))) if rl.std() > 0 else 0.0
    return c, se, z

print("\n== regular data: the cut points are fixed, not drawn")
report("all handoffs", *est(0, n))
for d in range(4, int(math.log10(LIM)) + 1):
    i0 = int(np.searchsorted(ts[1:], 10 ** d))
    i1 = int(np.searchsorted(ts[1:], 10 ** (d + 1)))
    if i1 - i0 < 100:
        continue
    report("decade 1e%d - 1e%d" % (d, d + 1), *est(i0, i1))
for k in range(1, 5):
    i0 = int(np.searchsorted(ts[1:], 10 ** 8 + (k - 1) * 10 ** 8 / 4))
    i1 = int(np.searchsorted(ts[1:], 10 ** 8 + k * 10 ** 8 / 4))
    report("quarter %d of 1e8-1e9" % k, *est(i0, i1))
mid = n // 2
report("first half (by handoff)", *est(0, mid))
report("second half (by handoff)", *est(mid, n))
cut = int(np.searchsorted(ts[1:], math.sqrt(ts[0] * ts[-1])))
report("below the geometric midpoint", *est(0, cut))
report("above the geometric midpoint", *est(cut, n))

print("\n== random data: windows drawn uniformly in handoff index")
cs, ses, zs = [], [], []
for _ in range(TRIALS):
    w = int(py.randint(200, 5000))
    i0 = int(rng.integers(0, max(1, n - w)))
    c, se, z = est(i0, i0 + w)
    cs.append(c); ses.append(se); zs.append(z)
cs, ses, zs = np.array(cs), np.array(ses), np.array(zs)
report("random windows: mean of the estimates", cs.mean(), ses.mean() / math.sqrt(len(cs)))
print("  %-42s sd(z) = %.3f, mean z = %+.3f, |z|<2 in %.1f%% of windows"
      % ("calibration of the per-window z-scores", np.std(zs), np.mean(zs),
         100 * np.mean(np.abs(zs) < 2)))
# regular cuts vs random draws, at equal window size: no selection bias if the scatters match
W = 400
reg = [est(i, i + W)[0] for i in range(0, n - W, W)]
rndw = []
for _ in range(len(reg)):
    i0 = int(rng.integers(0, n - W))
    rndw.append(est(i0, i0 + W)[0])
reg, rndw = np.array(reg), np.array(rndw)
print("  %-42s regular %.2e, random %.2e  (ratio %.2f)"
      % ("equal-size windows (400 handoffs): sd(c)",
         np.std(reg), np.std(rndw), np.std(rndw) / np.std(reg)))
frac = 100 * np.mean(np.abs(cs * TC - 1) < 0.05)
print("  %-42s %.1f%%  (median %.2e)" % ("windows within 5% of the law", frac, np.median(np.abs(cs * TC - 1))))

print("\n== controls")
# (1) permute the airs across positions: the law must get worse
sig_sd = np.std([ (a[i:i+500].mean() - t2[i:i+500].mean()/TC) for i in range(0, n - 500, max(1, (n - 500)//400)) ])
null_sd = []
for _ in range(100):
    perm = rng.permutation(n)
    ap = a[perm]
    ds = [ (ap[i:i+500].mean() - t2[i:i+500].mean()/TC) for i in range(0, n - 500, max(1, (n - 500)//100)) ]
    null_sd.append(np.std(ds))
print("  window residual s.d.: signal %.2f, permuted airs %.2f (ratio %.2f)"
      % (sig_sd, np.mean(null_sd), np.mean(null_sd) / sig_sd))
# (2) synthetic chains built to obey the law: the estimator must recover it
bias, sds = [], []
for _ in range(400):
    m = int(rng.integers(500, 5000))
    tt = np.log(np.exp(rng.uniform(math.log(1e4), math.log(LIM), m)))
    q = tt ** 2
    aa = q / TC + rng.normal(0, 1.0, m) * 0          # exact law
    aa = np.round(q / TC)                             # integer gaps, as primes have
    c = (q * aa).sum() / (q * q).sum()
    bias.append(c * TC - 1)
    aa2 = np.round(q / TC) + rng.normal(0, 280, m)    # with the real scatter
    c2 = (q * aa2).sum() / (q * q).sum()
    sds.append(c2 * TC - 1)
print("  synthetic, exact integer law:   mean c*2C2-1 = %+.2e  (sd %.2e)" % (np.mean(bias), np.std(bias)))
print("  synthetic, real scatter added:  mean c*2C2-1 = %+.2e  (sd %.2e)" % (np.mean(sds), np.std(sds)))

print("\n== bookkeeping conventions (the two classic slips)")
c_ok, se_ok, _ = est(0, n)
print("  m = handoffs          : c*2C2 = %.6f" % (c_ok * TC))
c_m1, _, _ = est(0, n - 1)
print("  m off by one          : c*2C2 = %.6f  (changes by %.1e)" % (c_m1 * TC, abs(c_m1 - c_ok) * TC))
print("  span including the last pair: %.6f relative difference" % (2.0 / (ts[-1] - ts[0])))

with open("results/tableY_reliability.csv", "w") as f:
    f.write("group,c_times_2C2,se,z,note\n")
    for row in rows:
        f.write("%s,%.6f,%.6f,%s,%s\n" % (row[0], row[1] * TC, row[2] * TC, row[3], row[4]))

h1 = est(0, mid); h2 = est(mid, n)
split_z = (h1[0] - h2[0]) / math.sqrt(h1[1] ** 2 + h2[1] ** 2)
print("  halves agree: (c1-c2)/se = %+.2f" % split_z)
ok = (abs(c_ok * TC - 1) < 0.005 and abs(np.mean(zs)) < 0.25 and 0.75 < np.std(zs) < 1.3
      and np.mean(null_sd) / sig_sd > 2.5 and abs(np.mean(sds)) < 0.01
      and abs(c_m1 * TC - 1) < 0.005 and abs(split_z) < 3
      and np.std(rndw) / np.std(reg) < 1.3)
print("\n  RELIABILITY %s  (overall c*2C2 = %.5f, z calibrated at sd %.2f, permuted/synthetic controls as above)"
      % ("PASSED" if ok else "FAILED", c_ok * TC, np.std(zs)))
sys.exit(0 if ok else 1)
