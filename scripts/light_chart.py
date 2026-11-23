#!/usr/bin/env python3
"""The Light Chart: element types, the stable core, and the ratio a segment carries.

Four panels, three kinds of claim, each labelled:
  A  exact   — the segment ratio r = air/(air+4) on the five classes, and which textbook ratios it excludes;
  B  measured— the fission atom ratio Z_light/Z_heavy for the 24 evaluated systems, against the band;
  C  measured (fission) / descriptive (chemistry) — the block-by-block interaction matrix;
  D  proved+measured — the stable core along Z: the block, the closed cells (s and p only), the holes.

Writes results/light-chart.png and results/tableV6_ratios.csv.
Run: python3 scripts/light_chart.py
"""
import csv, math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

C2 = 0.6601618158468696
el = {int(r["Z"]): r for r in csv.DictReader(open("results/tableO_element_properties.csv"))}
fis = list(csv.DictReader(open("results/tableR_fission_tests.csv")))
def blk(Z):
    Z = int(round(Z))
    return el[Z]["block"] if Z in el else "?"

fig = plt.figure(figsize=(16.5, 11), facecolor="white")
gs = fig.add_gridspec(2, 2, left=0.06, right=0.975, top=0.885, bottom=0.075, wspace=0.24, hspace=0.32)
fig.suptitle("The Light Chart: element types, the stable core, and the ratio a segment carries",
             fontsize=20, fontweight="bold", y=0.965)
fig.text(0.5, 0.925, "exact (ratio ladder) · measured (fission ratios, block interactions, the core) · "
         "descriptive (standard chemistry) — each panel says which", ha="center", fontsize=11.5, color="#444")

# ---------- A: the ratio ladder
axA = fig.add_subplot(gs[0, 0])
air = np.linspace(2, 44, 500)
r = air / (air + 4)
axA.plot(air, r, color="#1f3a93", lw=2)
axA.axhspan(0.5, 1.0, color="#e8f0fb", zorder=0)
classes = [(4, "4"), (10, "10"), (16, "16"), (22, "22"), (28, "28")]
offs = {4: (-30, -16), 10: (-34, 10), 16: (-18, 14), 22: (8, 12), 28: (6, -16)}
for a, lab in classes:
    axA.plot([a], [a / (a + 4)], "o", ms=9, color="#166534", zorder=5)
    axA.annotate("%d → %s" % (a, {4: "1:2", 10: "5:7", 16: "4:5", 22: "11:13", 28: "7:8"}[a]),
                 (a, a / (a + 4)), textcoords="offset points", xytext=offs[a], fontsize=10,
                 color="#166534", fontweight="bold")
for val, lab in [(1/3, "1:3 — needs air = 2  ✗"), (2/3, "2:3 — needs air = 8  ✗"),
                 (3/4, "3:4 — needs air = 12  ✗")]:
    axA.axhline(val, color="#b91c1c", ls="--", lw=1.2)
    axA.text(30, val + 0.012, lab, fontsize=9.5, color="#b91c1c")
axA.axhline(1.0, color="#b91c1c", ls=":", lw=1.2)
axA.text(26, 1.005, "1:1, 2:1, 3:1 — above the ladder  ✗", fontsize=9.5, color="#b91c1c")
axA.set_xlabel("air (the gap inside the segment)", fontsize=11)
axA.set_ylabel("r = air / T  =  air / (air + 4)", fontsize=11)
axA.set_title("A. The ratio a segment carries — exact, five rungs, band [1/2, 1)", fontsize=12.5,
              fontweight="bold", loc="left")
axA.set_ylim(0.2, 1.09); axA.grid(alpha=0.25)
axA.text(2.5, 0.235, "air % 6 = 4  ⇒  air ∈ {4, 10, 16, 22, 28, …}\nrung n:  r → 1 as air → ∞",
         fontsize=9.5, color="#333")

# ---------- B: fission ratios
axB = fig.add_subplot(gs[0, 1])
zs = [int(x["Z"]) for x in fis]
ratios = [float(x["mean_Z_light"]) / float(x["mean_Z_heavy"]) for x in fis]
axB.axhspan(0.5, 1.0, color="#e8f0fb", zorder=0)
for v, lab in [(0.5, "1:2"), (5/7, "5:7"), (0.8, "4:5"), (11/13, "11:13"), (7/8, "7:8")]:
    axB.axhline(v, color="#166534", ls=":", lw=1)
    axB.text(99.3, v, lab, fontsize=9, color="#166534", va="center")
axB.plot(zs, ratios, "o", ms=8, color="#7c2d12", alpha=0.85)
axB.axhline(np.median(ratios), color="#7c2d12", ls="--", lw=1)
axB.text(97.6, 0.615, "median %.3f" % np.median(ratios), fontsize=9.5,
         color="#7c2d12", fontweight="bold")
axB.set_xlabel("parent Z", fontsize=11)
axB.set_ylabel("Z_light / Z_heavy", fontsize=11)
axB.set_title("B. Fission atom ratios, 24 systems — measured, inside the same band", fontsize=12.5,
              fontweight="bold", loc="left")
axB.set_ylim(0.45, 1.02); axB.grid(alpha=0.25)
axB.text(88.8, 0.955, "pin: Z_L + Z_H = Z,  Z_H → 54", fontsize=9.5, color="#333")

# ---------- C: block interactions
axC = fig.add_subplot(gs[1, 0]); axC.axis("off")
axC.set_title("C. Element-type interactions", fontsize=12.5, fontweight="bold", loc="left")
axC.text(0.0, 0.90, "fission fragment pairs (measured, 24 systems):", fontsize=11)
pairs = [("d", "p", 12), ("s", "p", 7), ("d", "s", 4), ("p", "p", 1)]
yy = 0.78
for a, b, n in pairs:
    axC.add_patch(FancyBboxPatch((0.02, yy - 0.055), 0.16, 0.1, boxstyle="round,pad=0.01",
                                 facecolor="#f3f4f6", edgecolor="#9ca3af"))
    axC.text(0.10, yy, "%s → %s" % (a, b), ha="center", fontsize=12, fontweight="bold")
    axC.text(0.24, yy, "%2d of 24" % n, fontsize=11.5, va="center")
    axC.text(0.36, yy, {"d": "light fragment in the d block (Y…Tc)",
                        "s": "light in the s block (Rb, Sr)", "p": "light in the p block (Kr)"}[a],
             fontsize=9.5, va="center", color="#444")
    yy -= 0.13
axC.text(0.0, 0.30, "standard chemistry (descriptive, not measured here):", fontsize=11)
chem = [("s–p", "ionic salts (NaCl, CaO)"), ("p–p", "covalent molecules (H₂O, CO₂, SO₂)"),
        ("d–p", "ligand complexes, oxides, halides (FeCl₃, TiO₂)"),
        ("f–d", "f-block oxides and halides (UO₂, UF₆)")]
yy = 0.245
for a, b in chem:
    axC.text(0.02, yy, a, fontsize=11, fontweight="bold")
    axC.text(0.12, yy, b, fontsize=9.5, color="#444")
    yy -= 0.055
axC.text(0.0, 0.03, "the measured pair set is small: d→p dominates, then s→p, then d→s; "
         "the light fragment's type moves p → s → d as Z rises", fontsize=9.5, color="#333")

# ---------- D: the stable core along Z
axD = fig.add_subplot(gs[1, 1])
Zs = sorted(el)
blocks = [el[z]["block"] for z in Zs]
hs = [int(el[z]["countdown_h"]) for z in Zs]
colmap = {"s": "#2563eb", "p": "#166534", "d": "#b45309", "f": "#7c3aed"}
for z, b, h in zip(Zs, blocks, hs):
    axD.plot([z], [h], "o", ms=3.4, color=colmap[b])
for b, lab in [("s", "s"), ("p", "p"), ("d", "d"), ("f", "f")]:
    axD.plot([], [], "o", color=colmap[b], label="block %s" % lab)
closed = [z for z, b, h in zip(Zs, blocks, hs) if b in ("s", "p")]
axD.plot(closed, [el[z]["countdown_h"] for z in closed], "o", ms=7, mfc="none", mec="#111", mew=0.8,
         label="closed cell (s, p): 50 of 118")
for c in [2, 10, 18, 36, 54, 86, 118]:
    axD.axvline(c, color="#9ca3af", ls=":", lw=0.8)
axD.set_xlabel("Z", fontsize=11)
axD.set_ylabel("holes h = L(m) − v", fontsize=11)
axD.set_title("D. The stable core is the s and p blocks — proved/measured", fontsize=12.5,
              fontweight="bold", loc="left")
axD.set_yticks([0, 5, 15, 29])
axD.set_ylim(-1.5, 34)
axD.legend(fontsize=8.5, loc="lower center", ncol=2, framealpha=0.92)
axD.grid(alpha=0.25)

fig.savefig("results/light-chart.png", dpi=105, facecolor="white")

# ---------- the table
with open("results/tableV6_ratios.csv", "w") as f:
    f.write("kind,object,ratio_numerator,ratio_denominator,ratio,note\n")
    for a, lab in classes:
        f.write("segment_class,air=%d,%d,%d,%.6f,on the ladder\n" % (a, a, a + 4, a / (a + 4)))
    for name, p, q in [("1:3", 1, 3), ("2:3", 2, 3), ("3:4", 3, 4), ("1:1", 1, 1), ("2:1", 2, 1),
                       ("3:1", 3, 1)]:
        f.write("textbook,%s,%d,%d,%.6f,excluded (air = 4r/(1-r) is not 4 mod 6, or negative)\n"
                % (name, p, q, p / q))
    for x, rr in zip(fis, ratios):
        f.write("fission,%s,%s,%s,%.6f,measured Z_light/Z_heavy\n"
                % (x["system"].strip(), x["mean_Z_light"], x["mean_Z_heavy"], rr))
print("wrote results/light-chart.png and results/tableV6_ratios.csv")
print("  ratio band: [%.4f, 1)   fission ratios: %.3f .. %.3f, median %.3f"
      % (min(a / (a + 4) for a, _ in classes), min(ratios), max(ratios), float(np.median(ratios))))
print("  block pairs: %s" % pairs)
