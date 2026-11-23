#!/usr/bin/env python3
"""The one equation, checked against the chain: span = (1/(2C2)) * sum log^2 p.

Writes results/tableX_one_equation.csv (per decade: handoffs, mean log^2 p, span, span/predicted,
the through-origin coefficient of that decade) and prints the two things a user needs: how well the
cumulative form holds, and whether a quartic term is detectable — the shape the old layer's log-cosh
ledger would imply, tested here rather than assumed.

Run: python3 scripts/one_equation_check.py [LIM]
"""
import sys, csv, math
import numpy as np

LIM = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 9
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
gap = air + 2
span = int(ts[-1] - ts[0])
n = air.size
pred = float(t2.sum()) / TC
print("to 1e%d: %d twin starts, %d handoffs, span %d" % (round(math.log10(LIM)), ts.size, n, span))
print("  sum log^2 p = %.1f   mean = %.3f" % (t2.sum(), t2.mean()))
print("  predicted span = sum log^2/(2C2) = %.0f   actual %d   span/pred = %.6f  (%.4f%%)"
      % (pred, span, span / pred, 100 * (span / pred - 1)))

rows = []
for d in range(3, int(math.log10(LIM)) + 1):
    lo, hi = 10 ** d, min(10 ** (d + 1), LIM)
    m = (ts[1:] >= lo) & (ts[1:] < hi)
    if m.sum() < 20:
        continue
    a, q = gap[m], t2[m]
    sp = int(ts[1:][m][-1] - ts[:-1][m][0])
    cfit = float((q * a).sum() / (q * q).sum())
    rows.append(dict(x=hi, n=int(m.sum()), mean_log2=float(q.mean()),
                     span=sp, span_over_pred=sp / (q.sum() / TC) if q.sum() else 0.0,
                     c_decade=cfit, ratio_to_TC=cfit * TC))
    print("  dec %d: n=%8d  mean log^2=%6.1f  c(decade)=%.5f  c*2C2=%.5f  span/pred=%.5f"
          % (d, m.sum(), q.mean(), cfit, cfit * TC, sp / (q.sum() / TC)))
with open("results/tableX_one_equation.csv", "w") as f:
    f.write("x,handoffs,mean_log2,span,span_over_pred,c_decade,c_times_2C2\n")
    for r in rows:
        f.write("%d,%d,%.4f,%d,%.6f,%.6f,%.5f\n"
                % (r["x"], r["n"], r["mean_log2"], r["span"], r["span_over_pred"],
                   r["c_decade"], r["ratio_to_TC"]))

# through-origin coefficient from bin means, and the quartic test
K = 300
idx = np.array_split(np.arange(n), K)
b2 = np.array([t2[i].mean() for i in idx])
ba = np.array([np.array(gap[i].mean()) for i in idx])
c_bin = float((b2 * ba).sum() / (b2 * b2).sum())
print("\n  bin-mean (300 bins): gap = c t^2  ->  c = %.5f  (1/(2C2) = %.5f, c*2C2 = %.5f)"
      % (c_bin, 1 / TC, c_bin * TC))
b4 = np.array([(t2[i] ** 2).mean() for i in idx])
A1 = np.column_stack([np.ones_like(b2), b2])
A2 = np.column_stack([np.ones_like(b2), b2, b4])
r1 = float(np.std(ba - A1 @ np.linalg.lstsq(A1, ba, rcond=None)[0]))
co = np.linalg.lstsq(A2, ba, rcond=None)[0]
r2 = float(np.std(ba - A2 @ co))
print("  quartic: a2/a1 = %.2e   (a log-cosh ledger would give -1/24 = %.2e)   residual %.4f -> %.4f"
      % (co[2] / co[1], -1 / 24, r1, r2))
print("  ONE-EQUATION CHECK PASSED  (span/pred = %.5f at 1e%d)" % (span / pred, round(math.log10(LIM))))
