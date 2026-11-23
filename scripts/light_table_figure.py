#!/usr/bin/env python3
"""Draw the Light Table: the four digits, the two ladders, the roles, and where the heat sits."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

CLASSES = {1: (1, 11), 3: (13, 23), 7: (7, 17), 9: (19, 29)}
PRIMES = {1: 6355189, 7: 6356475, 11: 6356197, 13: 6356062,
          17: 6355839, 19: 6354987, 23: 6356436, 29: 6356346}
TWINS = {11: 1141217, 17: 1142128, 29: 1141159, 23: 0}
OPENS = {1: 1141217, 3: 1, 7: 1142128, 9: 1141159}
CLOSES = {1: 1141159, 3: 1141217, 7: 1, 9: 1142128}
HEAT = {(13, 13): (0.7978, "self"), (79, 79): (0.7994, "self"), (91, 91): (0.8011, "self"),
        (13, 91): (0.7743, "back"), (79, 13): (0.7535, "back"), (91, 79): (0.7759, "back"),
        (13, 79): (0.7363, "fwd"), (79, 91): (0.7202, "fwd"), (91, 13): (0.7205, "fwd")}

fig = plt.figure(figsize=(16, 9.6), facecolor="white")
gs = fig.add_gridspec(2, 2, width_ratios=[1.45, 1], height_ratios=[1, 1],
                      left=0.035, right=0.975, top=0.88, bottom=0.06, wspace=0.10, hspace=0.20)
axA = fig.add_subplot(gs[:, 0]); axB = fig.add_subplot(gs[0, 1]); axC = fig.add_subplot(gs[1, 1])
for ax in (axA, axB, axC):
    ax.set_xlim(0, 1); ax.set_ylim(0, 1); ax.axis("off")

fig.suptitle("The Light Table: four digits, two ladders, and what clusters on 1 · 3 · 7 · 9",
             fontsize=20, fontweight="bold", y=0.965)
fig.text(0.5, 0.915, "primes and twin starts to 10⁹ — each digit is the mod-10 shadow of two classes "
         "mod 30, one per ladder", ha="center", fontsize=12.5, color="#444")

# ---- panel A: the 8 cells
digits = [1, 3, 7, 9]
for j, d in enumerate(digits):
    x = 0.02 + j * 0.245
    axA.text(x + 0.105, 0.965, "digit %d" % d, ha="center", fontsize=15, fontweight="bold")
    for i, (ladder, idx) in enumerate([("base  1 mod 6", 0), ("twin  5 mod 6", 1)]):
        c = CLASSES[d][idx]
        y = 0.52 - i * 0.40
        dead = c == 23
        face = "#ececec" if dead else ("#e8f0fb" if idx == 0 else "#effaf0")
        axA.add_patch(FancyBboxPatch((x, y), 0.21, 0.35, boxstyle="round,pad=0.012,rounding_size=0.02",
                                     linewidth=1.6, edgecolor="#8a8a8a" if dead else "#3b5b8c", facecolor=face))
        axA.text(x + 0.105, y + 0.275, "%d" % c, ha="center", fontsize=26,
                 fontweight="bold", color="#777" if dead else "#1d1d1d")
        axA.text(x + 0.105, y + 0.196, ladder, ha="center", fontsize=9.5, color="#444")
        axA.text(x + 0.105, y + 0.120, "%s primes" % format(PRIMES[c], ","), ha="center", fontsize=10.5)
        axA.text(x + 0.105, y + 0.066, "12.50% of π(10⁹)", ha="center", fontsize=9, color="#666")
        if idx == 1:
            if dead:
                axA.text(x + 0.105, y + 0.012, "dead: p+2 = 0 mod 5", ha="center", fontsize=9.5,
                         color="#a33", style="italic")
            else:
                axA.text(x + 0.105, y + 0.012, "%s twin starts" % format(TWINS[c], ","), ha="center",
                         fontsize=10.5, color="#166534", fontweight="bold")
        else:
            axA.text(x + 0.105, y + 0.012, "≡ %d (mod 30)" % c, ha="center", fontsize=9, color="#666")
axA.text(0.5, 0.462, "", ha="center")
fig.text(0.035, 0.022,
         "Each digit carries one base class and one twin class (they differ by 10).  The twin ladder has four classes and three are live:",
         fontsize=10.5, color="#333")
fig.text(0.035, 0.002,
         "class 23 is structurally dead (p+2 = 25 is a multiple of 5), which is why only 11, 17, 29 can open a pair.",
         fontsize=10.5, color="#333")

# ---- panel B: roles
axB.text(0.0, 0.97, "the two roles in a pair", fontsize=14, fontweight="bold")
axB.text(0.0, 0.885, "opener = the start's digit      closer = the partner's digit",
         fontsize=10, color="#444")
hdrs = ["digit", "opens", "closes"]
xs = [0.02, 0.16, 0.52]
for x, h in zip(xs, hdrs):
    axB.text(x, 0.80, h, fontsize=10.5, fontweight="bold", color="#333")
for k, d in enumerate(digits):
    y = 0.68 - k * 0.135
    axB.text(xs[0], y, "%d" % d, fontsize=15, fontweight="bold")
    o, c = OPENS[d], CLOSES[d]
    axB.text(xs[1], y, ("%s" % format(o, ",")) if o > 2 else "1   (p = 3 — the only one)",
             fontsize=10.5, color="#1d1d1d" if o > 2 else "#a33")
    axB.text(xs[2], y, ("%s" % format(c, ",")) if c > 2 else "1   (p = 5 — the only one)",
             fontsize=10.5, color="#1d1d1d" if c > 2 else "#a33")
axB.text(0.0, 0.10,
         "3 closes but never opens; 7 opens but never closes.\n"
         "Digits 1 and 9 do both — 1 is 11→13's opener and 29→31's closer.",
         fontsize=10, color="#333")
axB.plot([0.0, 1.0], [0.175, 0.175], color="#ddd", lw=1)

# ---- panel C: the heat sits on the transition
axC.text(0.0, 0.97, "where the heat sits: on the transition, not the digit", fontsize=14, fontweight="bold")
axC.text(0.0, 0.89, "ΣT / Σt² per pair-type cell, 3.4M handoffs below 10⁹", fontsize=10, color="#444")
grid = {13: 0, 79: 1, 91: 2}
col = {"self": "#dbeafe", "back": "#e5e7eb", "fwd": "#fee2e2"}
for (a, b), (v, kind) in HEAT.items():
    x = 0.26 + grid[b] * 0.245
    y = 0.60 - grid[a] * 0.195
    axC.add_patch(FancyBboxPatch((x, y), 0.225, 0.165, boxstyle="round,pad=0.008,rounding_size=0.02",
                                 linewidth=1.2, edgecolor="#9ca3af", facecolor=col[kind]))
    axC.text(x + 0.112, y + 0.112, "%d→%d" % (a, b), ha="center", fontsize=10, color="#444")
    axC.text(x + 0.112, y + 0.040, "%.3f" % v, ha="center", fontsize=13, fontweight="bold")
for k, b in enumerate([13, 79, 91]):
    axC.text(0.26 + k * 0.245 + 0.112, 0.795, "to %d" % b, ha="center", fontsize=10.5, fontweight="bold")
for k, a in enumerate([13, 79, 91]):
    axC.text(0.02, 0.60 - k * 0.195 + 0.082, "from %d" % a, fontsize=10, fontweight="bold", va="center")
axC.text(0.02, 0.075, "self 0.798   ·   back 0.768   ·   forward 0.726", fontsize=10.5, color="#333")
axC.text(0.02, 0.02, "the digit pair sets the kind of step; the kind sets the heat.",
         fontsize=10.5, color="#333")

fig.savefig("results/light-table.png", dpi=110, facecolor="white")
print("wrote results/light-table.png")
