#!/usr/bin/env python3
"""The per-system test, run: can the digit ratio track the fission ratio?

The proposal: restrict the handoffs to the fragment range at each parent's charge and recompute
R_digits there; if those track 0.744, 0.748, 0.757, 0.767, 0.767 it is a mechanism, if they stay flat it
is a coincidence of levels.

What is tested here:

  1. R_digits in fixed windows (decades, halves, quarters): does it move at all?
  2. R_digits at the *positional analogue* of each parent: the table puts a parent at Z/118 of its own
     ladder, so its prime-side analogue is the handoff at the same fraction of the chain
     (log p / log LIM = Z/118). R_digits computed there, per parent.
  3. the correlation between those per-parent values and the measured Z_L/Z_H, with a shuffle control;
  4. the quantities that *do* vary with height (counterflow asymmetry, self-share, mean gap), and whether
     any of them has the 21% range the fission ratio needs.

Writes results/tableV9_per_system.csv.  Run: python3 scripts/per_system_digit_ratio.py [LIM]
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
ts = ts[(ts > 5) & (ts <= LIM)]
beg, end = ts % 10, (ts + 2) % 10
N = ts.size
print("to 1e%d: %d twin starts, %d handoffs" % (round(math.log10(LIM)), N, N - 1))

def R_digits(i0, i1):
    """sum of closing digits / sum of opening digits over the handoffs in [i0, i1)"""
    a, b = end[i0:i1 - 1], beg[i0 + 1:i1]
    return float(a.sum()) / float(b.sum()), int(a.size)

print("\n== 1. fixed windows (the digit ratio does not move)")
rows = []
for d in range(3, int(math.log10(LIM)) + 1):
    i0 = int(np.searchsorted(ts, 10 ** d)); i1 = int(np.searchsorted(ts, 10 ** (d + 1)))
    if i1 - i0 < 20:
        continue
    r, m = R_digits(i0, i1)
    rows.append(("decade 1e%d-1e%d" % (d, d + 1), i0, i1, r, m))
    print("  decade 1e%d-1e%d: R = %.6f  over %7d handoffs" % (d, d + 1, r, m))
for name, i0, i1 in [("first half", 0, N // 2), ("second half", N // 2, N)]:
    r, m = R_digits(i0, i1)
    rows.append((name, i0, i1, r, m))
    print("  %-16s R = %.6f  over %7d handoffs" % (name, r, m))
allR, _ = R_digits(0, N)
print("  all: R = %.6f" % allR)

# bootstrap noise on a 2000-handoff window, to know what 'flat' means
W = 2000
boot = []
rng = np.random.default_rng(7)
for _ in range(400):
    i0 = int(rng.integers(0, N - W))
    boot.append(R_digits(i0, i0 + W)[0])
boot = np.array(boot)
print("\n  random windows of %d handoffs: mean %.6f, sd %.6f  (so a move of <%.4f is noise)"
      % (W, boot.mean(), boot.std(), 3 * boot.std()))

print("\n== 2. the positional analogue of each parent (log p / log LIM = Z / 118)")
rows_fis = list(csv.DictReader(open("results/tableR_fission_tests.csv")))
per_Z = {}
for r in rows_fis:
    Z = int(r["Z"]); v = float(r["mean_Z_light"]) / float(r["mean_Z_heavy"])
    per_Z.setdefault(Z, []).append((v, r["system"].strip()))
print("   Z   frac=Z/118   window (handoffs)      R_digits    Z_L/Z_H (measured)")
per = []
for Z in sorted(per_Z):
    frac = Z / 118.0
    i0 = int(round(frac * (N - 1)))
    # a window centred on the analogue, 2e5 handoffs wide (or what fits)
    half = min(100000, i0, N - 1 - i0)
    i0a, i1a = i0 - half, i0 + half
    if i1a - i0a < 100:
        i0a, i1a = max(0, i0 - 1000), min(N, i0 + 1000)
    r, m = R_digits(i0a, i1a)
    ratio = float(np.mean([v for v, _ in per_Z[Z]]))
    per.append((Z, frac, i0a, i1a, r, m, ratio))
    print("  %3d   %.4f      %8d-%8d    %.6f    %.4f" % (Z, frac, i0a, i1a, r, ratio))

Rs = np.array([p[4] for p in per]); Ys = np.array([p[6] for p in per]); Zs = np.array([p[0] for p in per])
print("\n  spread of R_digits across the 11 parents: %.6f  (max-min %.6f)"
      % (Rs.std(), Rs.max() - Rs.min()))
print("  spread of Z_L/Z_H across the same parents:  %.4f  (max-min %.4f) — %.0fx wider"
      % (Ys.std(), Ys.max() - Ys.min(), (Ys.max() - Ys.min()) / max(1e-12, Rs.max() - Rs.min())))
print("  correlation R_digits vs Z_L/Z_H: r = %+.3f" % np.corrcoef(Rs, Ys)[0, 1])
rng2 = np.random.default_rng(11)
null = [abs(np.corrcoef(Rs, rng2.permutation(Ys))[0, 1]) for _ in range(5000)]
print("  shuffle null: |r| > observed in %.1f%% of permutations -> p = %.2f"
      % (100 * np.mean(np.array(null) >= abs(np.corrcoef(Rs, Ys)[0, 1])),
         float(np.mean(np.array(null) >= abs(np.corrcoef(Rs, Ys)[0, 1])))))

print("\n== 3. the quantities that do vary with height, and how far")
M = {}
for i in range(N - 1):
    k = (int(end[i]), int(beg[i + 1]))
    M[k] = M.get(k, 0) + 1
for d in range(4, int(math.log10(LIM)) + 1):
    i0 = int(np.searchsorted(ts, 10 ** d)); i1 = int(np.searchsorted(ts, 10 ** (d + 1)))
    if i1 - i0 < 100:
        continue
    Md = {}
    for i in range(i0, min(i1 - 1, N - 1)):
        k = (int(end[i]), int(beg[i + 1]))
        Md[k] = Md.get(k, 0) + 1
    fwd = Md.get((3, 7), 0) + Md.get((9, 1), 0) + Md.get((1, 9), 0)
    bwd = Md.get((3, 9), 0) + Md.get((9, 7), 0) + Md.get((1, 1), 0)
    self_ = Md.get((3, 1), 0) + Md.get((9, 9), 0) + Md.get((1, 7), 0)
    tot = fwd + bwd + self_
    print("  decade 1e%d: counterflow one-way/other = %.4f   self-share = %.4f"
          % (d, fwd / bwd, self_ / tot))

with open("results/tableV9_per_system.csv", "w") as f:
    f.write("Z,frac_of_ladder,window_start,window_end,R_digits,handoffs,measured_ZL_ZH\n")
    for p in per:
        f.write("%d,%.4f,%d,%d,%.6f,%d,%.4f\n" % p)
print("\n  PER-SYSTEM TEST: R_digits is flat (sd %.2e) where the fission ratio needs a %.2f spread"
      % (Rs.std(), Ys.max() - Ys.min()))
print("  -> the agreement is a LEVEL agreement, not a per-system mechanism.")
