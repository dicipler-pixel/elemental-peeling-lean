#!/usr/bin/env python3
"""Draw Figure 1: the step ratios, the wall, and the band the archive cannot resolve.

    python3 scripts/band_figure.py

Reads the shipped baseline archive, writes `paper/fig-band.pdf` (vector, for LaTeX) and
`paper/fig-band.png` (preview).  Every number drawn is recomputed here; nothing is typed in.
"""
import json
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "atlas/data/ptable_data.json")
WALL = 3 + 2 * 2 ** 0.5

plt.rcParams.update({
    "font.family": "serif", "font.size": 8, "axes.linewidth": 0.6,
    "xtick.major.width": 0.6, "ytick.major.width": 0.6, "axes.edgecolor": "#333333",
})

d = json.load(open(DATA))
steps = [(e["sym"], s["z"]) for e in d["elements"] for s in e["steps"]]
rungs = [(e["sym"], e["anion"]["z0"]) for e in d["elements"] if e["anion"]]
z = np.array([v for _, v in steps])
zr = np.array([v for _, v in rungs])
outside = [(s, v) for s, v in steps if v > WALL]
inside_max = max((v, s) for s, v in steps if v <= WALL)
rung_in = max((v, s) for s, v in rungs if v <= WALL)
rung_out = min((v, s) for s, v in rungs if v > WALL)
band = (rung_in[0], rung_out[0])

fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(6.3, 3.5), height_ratios=[1.15, 1],
                               gridspec_kw={"hspace": 0.55})

# ---- panel (a): where the 3,570 steps live ---------------------------------
bins = np.logspace(np.log10(z.min() * 0.95), np.log10(z.max() * 1.05), 60)
ax1.hist(z, bins=bins, color="#9fb3c8", edgecolor="none", label=f"removal steps (n = {len(z)})")
ax1.hist(zr, bins=bins, color="#c9b6ff", edgecolor="none", alpha=0.85,
         label=f"anion rungs (n = {len(zr)})")
ax1.set_xscale("log")
ax1.axvline(WALL, color="#b8860b", lw=1.0, ls="--")
ax1.annotate(r"wall $3+2\sqrt{2}$", xy=(WALL, ax1.get_ylim()[1] * 0.72),
             xytext=(WALL * 1.12, ax1.get_ylim()[1] * 0.72), fontsize=7, color="#7a5a00")
ax1.set_xlabel("step ratio  $z = I_{k+1}/I_k$  (log scale)")
ax1.set_yticks([])
ax1.legend(frameon=False, fontsize=7, loc="upper center", bbox_to_anchor=(0.32, 1.0))
for s in ("top", "right"):
    ax1.spines[s].set_visible(False)
ax1.set_title("(a)  3,570 steps and 65 rungs; eight steps lie outside the wall", fontsize=8,
              loc="left")

# ---- panel (b): the band ---------------------------------------------------
ax2.set_xlim(5.55, 6.02)
ax2.set_ylim(-1.95, 2.30)
ax2.axvspan(band[0], band[1], color="#f2c14e", alpha=0.28, lw=0)
ax2.axvline(WALL, color="#b8860b", lw=1.0, ls="--")
ax2.scatter(z[z <= 6.05], np.zeros_like(z[z <= 6.05]), s=6, color="#41576b", zorder=3,
            label="steps")
ax2.scatter(zr[zr <= 6.05], np.ones_like(zr[zr <= 6.05]), s=10, marker="|", color="#6b4fbb",
            zorder=3, label="rungs")
ir = min((v, s0) for s0, v in rungs if 5.70 < v < 5.80)
cs = min((v, s0) for s0, v in outside)
leader = dict(arrowstyle="-", lw=0.5, color="#888888",
              shrinkA=2, shrinkB=2)
labels = [
    (inside_max[0], 0, (5.60, -0.55), "left",  f"{inside_max[1]} {inside_max[0]:.6f}"),
    (cs[0], 0, (5.985, -0.62), "right",        f"{cs[1]} {cs[0]:.6f}"),
    (ir[0], 1, (5.585, 1.62), "left",          f"{ir[1]} {ir[0]:.6f}"),
    (band[0], 1, (5.815, 2.12), "center",      f"{rung_in[1]} {band[0]:.6f}"),
    (band[1], 1, (5.945, 0.62), "right",       f"{rung_out[1]} {band[1]:.6f}"),
]
for v, y, xytext, ha, text in labels:
    ax2.annotate(text, xy=(v, y), xytext=xytext, fontsize=6.5, ha=ha, va="center",
                 color="#222222", arrowprops=leader)
ax2.annotate("", xy=(band[0], -1.00), xytext=(band[1], -1.00),
             arrowprops=dict(arrowstyle="<->", lw=0.7, color="#7a5a00"))
ax2.text((band[0] + band[1]) / 2, -1.38, "same sorting throughout",
         fontsize=6.5, ha="center", va="top", color="#7a5a00")
ax2.set_yticks([])
ax2.set_xlabel("step ratio  $z$  (linear, zoom on the band)")
ax2.legend(frameon=False, fontsize=7, loc="upper right", ncol=2, bbox_to_anchor=(1.0, 1.03))
for s in ("top", "right", "left"):
    ax2.spines[s].set_visible(False)
ax2.set_title(f"(b)  the band [{band[0]:.6f}, {band[1]:.6f}) contains the wall", fontsize=8,
              loc="left")

fig.savefig(os.path.join(ROOT, "paper/fig-band.pdf"), bbox_inches="tight")
fig.savefig(os.path.join(ROOT, "paper/fig-band.png"), dpi=200, bbox_inches="tight")
print(f"steps {len(z)}, rungs {len(zr)}, outside {len(outside)}, wall {WALL:.6f}")
print(f"band [{band[0]:.6f}, {band[1]:.6f}); inside max {inside_max}")
print("wrote paper/fig-band.pdf and paper/fig-band.png")
