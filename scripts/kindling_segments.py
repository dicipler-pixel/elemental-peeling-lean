#!/usr/bin/env python3
"""Kindling and firewood against the segments: which gaps are surface and which are volume.

The record's ratio is S/V = 4/air: the pair (4 units) is surface, the air is volume. Every handoff has
one air, so the ratio is per handoff — but handoffs come in two kinds, and they are not the same kind
of gap:

  * an **external** air — the gap that ends a segment. It is any gap between twin starts, so it follows
    the measured law, mean t²/(2C₂) − 2 (large: ~290 at 10⁹);
  * an **internal** air — the gap that joins two pairs into one segment. It is a *single prime gap* by
    definition (merged means no prime between partner and next start), so it is small, and it is the
    prime gap at that height (mean ~log p ≈ 20 at 10⁹).

So a segment of k pairs is kindling inside and firewood outside: its internal S/V is one order of
magnitude above its external S/V. This script measures that, per segment size k = 1..7, with the
external airs on both sides. Writes results/tableV3_kindling.csv.

Run: python3 scripts/kindling_segments.py [LIM]
"""
import sys, math
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
air = np.diff(ts) - 2
gi = np.searchsorted(pr, ts)
merged = np.diff(gi) == 2
# segment id per pair: a merge joins i and i+1
seg = np.zeros(ts.size, dtype=np.int64)
for i in range(1, ts.size):
    seg[i] = seg[i - 1] + (0 if merged[i - 1] else 1)
# segment boundaries
starts = {}
for i, s in enumerate(seg):
    if s not in starts:
        starts[s] = i
order = sorted(starts)
sizes, int_air, ext_air, spans = [], [], [], []
for k, s in enumerate(order):
    i0 = starts[s]
    i1 = starts[order[k + 1]] if k + 1 < len(order) else ts.size
    k_pairs = i1 - i0
    a_int = air[i0:i1 - 1]                        # internal airs (merged handoffs)
    a_before = air[i0 - 1] if i0 > 0 else None     # external air leading in
    a_after = air[i1 - 1] if i1 - 1 < air.size else None
    sizes.append(k_pairs)
    int_air.append(a_int)
    ext_air.append(np.array([x for x in (a_before, a_after) if x is not None]))
    spans.append(int(ts[i1 - 1] - ts[i0]) + 4)
sizes = np.array(sizes)
print("to 1e%d: %d twin starts, %d handoffs, %d segments" % (round(math.log10(LIM)), ts.size, air.size, len(sizes)))
print("  pairs per segment %.4f; share of pairs in k>=2 segments %.3f"
      % (air.size / len(sizes), np.sum(sizes[sizes >= 2]) / sizes.sum()))

print("\n  k   segments   internal airs   mean air_in   S/V_in    mean air_out   S/V_out   S/V ratio   S/V of the segment")
rows = []
for k in range(1, 8):
    m = sizes == k
    if not m.sum():
        continue
    ints = np.concatenate([int_air[i] for i in np.nonzero(m)[0]]) if k > 1 else np.array([])
    exts = np.concatenate([ext_air[i] for i in np.nonzero(m)[0]])
    mi = float(ints.mean()) if ints.size else float("nan")
    mo = float(exts.mean()) if exts.size else float("nan")
    sv_i = 4 / mi if ints.size else float("nan")
    sv_o = 4 / mo if exts.size else float("nan")
    # the segment's own ratio: surface 4 per pair, volume the internal airs
    sv_seg = (4 * k / (ints.sum() / m.sum())) if ints.size else float("nan")
    rows.append(dict(k=k, segs=int(m.sum()), n_int=int(ints.size), mean_in=mi, sv_in=sv_i,
                     mean_out=mo, sv_out=sv_o, ratio=sv_i / sv_o if ints.size else float("nan"),
                     sv_seg=sv_seg))
    print("  %d  %9d  %13d   %10.2f  %8.3f   %11.1f  %8.3f   %8.2f   %10.4f"
          % (k, m.sum(), ints.size, mi, sv_i, mo, sv_o,
             (sv_i / sv_o) if ints.size else float("nan"), sv_seg))

allsize = sizes
print("\n  internal airs are prime gaps: they must satisfy air == 4 mod 6 and be consecutive-prime gaps")
ints_all = np.concatenate([a for a in int_air if a.size])
print("  internal airs: n=%d  mean %.2f  median %d  max %d  mod 6 values %s"
      % (ints_all.size, ints_all.mean(), int(np.median(ints_all)), int(ints_all.max()),
         sorted(set((ints_all % 6).tolist()))))
ext_all = np.concatenate([a for a in ext_air if a.size])
print("  external airs: n=%d  mean %.2f  median %d" % (ext_all.size, ext_all.mean(), int(np.median(ext_all))))
print("  ratio of the two S/V readings: %.2f   (air ratio %.2f)"
      % (float(ints_all.mean() / ext_all.mean()) if False else ext_all.mean() / ints_all.mean(),
         ext_all.mean() / ints_all.mean()))
# the prime gap at the same height, for reference
gaps = np.diff(pr).astype(float)
print("  mean prime gap to 1e%d: %.2f   (internal air mean %.2f)" % (round(math.log10(LIM)), gaps.mean(), ints_all.mean()))

with open("results/tableV3_kindling.csv", "w") as f:
    f.write("k_pairs,segments,internal_airs,mean_air_internal,SV_internal,mean_air_external,"
            "SV_external,SV_ratio,SV_of_segment\n")
    for r in rows:
        f.write("%d,%d,%d,%.3f,%.4f,%.2f,%.4f,%.3f,%.5f\n"
                % (r["k"], r["segs"], r["n_int"], r["mean_in"], r["sv_in"], r["mean_out"],
                   r["sv_out"], r["ratio"], r["sv_seg"]))
ok = (set((ints_all % 6).tolist()) == {4} and ints_all.mean() < ext_all.mean())
print("\n  KIND-LING CHECK %s  (internal airs mean %.1f vs external %.1f)"
      % ("PASSED" if ok else "FAILED", ints_all.mean(), ext_all.mean()))
sys.exit(0 if ok else 1)
