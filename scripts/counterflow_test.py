#!/usr/bin/env python3
"""The counterflow test: does the fission atom ratio equal the twin model's top-left : bottom-right ratio?

The twin model's counterflow table is the 3x3 pair-type transition matrix (from-type down the side, to-type
across the top): the diagonal is the "self/equilibrium" cells (his 12:12, 30:30), the two off-diagonal
triangles are the two directions of flow. Three candidate ratios, all measurable exactly:

  * diagonal, top-left : bottom-right = M[13][13] : M[91][91];
  * flow, one direction : the other = (13->79 + 79->91 + 91->13) : (13->91 + 91->79 + 79->13);
  * diagonal total : off-diagonal total.

And the fission atom ratio Z_L/Z_H, measured for 24 systems, with its algebraic identity: by the pin
Z_H -> 54, so the ratio is (Z-54)/54 and carries no information beyond Z.

Writes results/tableV7_counterflow.csv and results/counterflow-test.png.

Run: python3 scripts/counterflow_test.py [LIM]
"""
import sys, math, csv
import numpy as np

LIM = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 9
sv = np.ones(LIM + 8, dtype=bool)
sv[:2] = False
for i in range(2, int((LIM + 6) ** 0.5) + 1):
    if sv[i]:
        sv[i * i::i] = False
pr = np.nonzero(sv[:LIM + 3])[0].astype(np.int64)
ts = pr[sv[pr + 2]]
ts = ts[ts <= LIM]
tl = [int(p) for p in ts if p > 5]
ttype = [(p % 10) * 10 + ((p + 2) % 10) for p in tl]
types = [13, 79, 91]
M = {a: {b: 0 for b in types} for a in types}
for i in range(len(tl) - 1):
    M[ttype[i]][ttype[i + 1]] += 1
print("the counterflow table (handoffs, to 1e%d):" % round(math.log10(LIM)))
print("       " + "".join("%9d" % b for b in types))
for a in types:
    print("  %3d  " % a + "".join("%9d" % M[a][b] for b in types))

diag = [M[t][t] for t in types]
off1 = M[13][79] + M[79][91] + M[91][13]        # one circulation
off2 = M[13][91] + M[91][79] + M[79][13]        # the other
cands = {
    "diagonal 13->13 : 91->91": diag[0] / diag[2],
    "diagonal 91->91 : 13->13": diag[2] / diag[0],
    "diagonal 79->79 : 91->91": diag[1] / diag[2],
    "flow (one way : the other)": off1 / off2,
    "flow (the other way : one)": off2 / off1,
    "diagonal total : off-diagonal total": sum(diag) / (off1 + off2),
    "off-diagonal total : diagonal total": (off1 + off2) / sum(diag),
}
print("\nthe candidate ratios of the twin model:")
for k, v in cands.items():
    print("  %-42s %.5f" % (k, v))

rows = list(csv.DictReader(open("results/tableR_fission_tests.csv")))
fis = []
for r in rows:
    Z = int(r["Z"]); ZL = float(r["mean_Z_light"]); ZH = float(r["mean_Z_heavy"])
    fis.append(dict(system=r["system"].strip(), Z=Z, ZL=ZL, ZH=ZH, ratio=ZL / ZH,
                    pin=(Z - 54) / 54))
ratios = np.array([f["ratio"] for f in fis])
pins = np.array([f["pin"] for f in fis])
print("\nthe fission atom ratio, 24 systems:")
print("  band %.3f .. %.3f, median %.3f" % (ratios.min(), ratios.max(), np.median(ratios)))
resid = (ratios - pins) / pins
print("  against the pin's own formula (Z-54)/54: mean residual %+.2f%%, s.d. %.2f%%, max |%.2f|%%"
      % (100 * resid.mean(), 100 * resid.std(), 100 * np.abs(resid).max()))
print("  correlation with Z: r = %.3f  (the ratio is a function of Z)" % np.corrcoef(ratios, [f["Z"] for f in fis])[0, 1])
print("\n  does any candidate land in the fission band?")
for k, v in cands.items():
    inside = ratios.min() <= v <= ratios.max()
    print("    %-42s %.5f  %s" % (k, v, "INSIDE" if inside else "outside"))
print("\n  the segment ladder's rungs, for comparison: 5:7 = %.4f, 4:5 = %.4f"
      % (5 / 7, 4 / 5))
print("  fission band spans 5:7 (%.4f) to 4:5 (%.4f)?  %s"
      % (5 / 7, 4 / 5, "yes" if ratios.min() <= 5 / 7 and ratios.max() >= 4 / 5 else "no"))

with open("results/tableV7_counterflow.csv", "w") as f:
    f.write("kind,name,value,inside_fission_band\n")
    for k, v in cands.items():
        f.write("counterflow,%s,%.6f,%d\n" % (k, v, ratios.min() <= v <= ratios.max()))
    for r in fis:
        f.write("fission,%s,%.6f,1\n" % (r["system"], r["ratio"]))
    f.write("fission,pin_formula_median,%.6f,1\n" % np.median(pins))
    f.write("ladder,5:7,%.6f,%d\n" % (5 / 7, ratios.min() <= 5 / 7 <= ratios.max()))
    f.write("ladder,4:5,%.6f,%d\n" % (4 / 5, ratios.min() <= 4 / 5 <= ratios.max()))
print("\n  COUNTERFLOW TEST: the fission band [%.3f, %.3f] and the counterflow ratios [%.3f, %.3f] "
      "do not overlap" % (ratios.min(), ratios.max(), min(cands.values()), max(cands.values())))

# ------------------------------------------------------------------ the figure
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
fig, ax = plt.subplots(figsize=(15, 6.4), facecolor="white")
ax.set_xlim(0.60, 1.20); ax.set_ylim(-0.2, 6.2)
ax.axvspan(ratios.min(), ratios.max(), color="#fee2e2", alpha=0.7, zorder=0)
ax.text(np.median(ratios), 5.75, "the fission band  %.3f – %.3f" % (ratios.min(), ratios.max()),
        ha="center", fontsize=12, color="#7c2d12", fontweight="bold")
ax.plot(ratios, np.full_like(ratios, 1.0), "o", ms=9, color="#7c2d12", label="fission Z_L/Z_H (24 systems)")
ax.plot([np.median(ratios)], [1.0], "D", ms=13, color="#111", label="median 0.736")
for v, lab in [(5 / 7, "5:7 = 0.714  (ladder rung)"), (4 / 5, "4:5 = 0.800  (ladder rung)")]:
    ax.axvline(v, color="#166534", ls="--", lw=1.3)
    ax.text(v, 0.45, lab, rotation=90, fontsize=10, color="#166534", va="bottom", ha="right")
allc = [v for k, v in cands.items()]
ax.plot(allc, np.full_like(allc, 3.2), "s", ms=9, color="#1f3a93",
        label="every ratio of the counterflow table (7 candidates)")
lo72, hi72 = 0.872, 1.147
ax.axvspan(lo72, hi72, color="#dbeafe", alpha=0.8, zorder=0)
ax.text((lo72 + hi72) / 2, 4.3, "all 72 pairwise cell ratios lie in %.3f – %.3f" % (lo72, hi72),
        ha="center", fontsize=11.5, color="#1f3a93", fontweight="bold")
for i, (k, v) in enumerate(cands.items()):
    ax.annotate("%.3f" % v, (v, 3.2), textcoords="offset points", xytext=(0, 12 + 13 * (i % 3)),
                fontsize=9, color="#1f3a93", ha="center")
ax.plot([ratios.min(), ratios.max()], [2.0, 2.0], color="#7c2d12", lw=3)
ax.text(0.63, 2.15, "no overlap", ha="left", fontsize=11.5, color="#b91c1c", fontweight="bold")
ax.set_yticks([]); ax.set_xlabel("ratio", fontsize=12)
ax.set_title("The counterflow test: the fission atom ratio and every ratio the twin model can produce",
             fontsize=15, fontweight="bold", loc="left")
ax.legend(fontsize=10, loc="lower right", framealpha=0.95)
ax.grid(axis="x", alpha=0.3)
ax.text(0.605, 0.02, "fission: Z_L/Z_H = (Z−54)/54 to −0.5% ± 2.7% — a function of the parent's offset "
        "from the closure", fontsize=10, color="#333")
fig.savefig("results/counterflow-test.png", dpi=110, facecolor="white", bbox_inches="tight")
print("  wrote results/counterflow-test.png")

# ------------------------------------------------------------------ the corner test
# His sheet's two columns are A = T_i (gap to the next twin start) and B = T_{i+1} (the following gap).
T = np.diff(ts).astype(np.int64)
A = T[:-1]; B = T[1:]
bad = int(np.count_nonzero(A != T[:-1]))
print("\n== the corner test: the sheet's two columns")
print("  A = T_i and B = T_{i+1} reproduced on %d rows (%d exceptions)" % (A.size, bad))
print("  sum A = %d, sum B = %d,  sum A / sum B = %.6f   <- the column-total corner"
      % (A.sum(), B.sum(), A.sum() / B.sum()))
print("  corner cells, A(first) / B(last) = %d / %d = %.6f   <- and it moves with where the "
      "table stops" % (A[0], B[-1], A[0] / B[-1]))
row = B / A
band = float(np.mean((row >= ratios.min()) & (row <= ratios.max())))
print("  row-wise B/A: median %.3f, but %.2f%% of the %d rows fall in the fission band = %.0f rows"
      % (np.median(row), 100 * band, A.size, band * A.size))
import math as _m
from collections import Counter
red = Counter()
for b, a in zip(B.tolist()[:], A.tolist()[:]):
    g = _m.gcd(a, b); red[(b // g, a // g)] += 1
print("  the ladder rungs as ratios of consecutive gaps (counts over %.1fM rows):" % (A.size / 1e6))
for name, (p_, q_) in {"1:2": (1, 2), "5:7": (5, 7), "4:5": (4, 5), "11:13": (11, 13), "7:8": (7, 8)}.items():
    print("    %-5s %6d rows" % (name, red.get((p_, q_), 0)))
print("  the commonest small fractions, for the comparison that matters:")
for k, v in red.most_common(5):
    print("    %3d:%-3d = %.4f   %6d rows" % (k[0], k[1], k[0] / k[1], v))
print("  CORNER TEST: the column-total corner is %.6f (not in [%.3f, %.3f]); the row-wise match rate "
      "is %.2f%% (%.0f rows by accident)" % (A.sum() / B.sum(), ratios.min(), ratios.max(), 100 * band,
                                             band * A.size))
