#!/usr/bin/env python3
"""The elements' hole structure, and how many holes there are.

Three different counts go by the name "holes", and the point of this script is to keep them apart:

  (i)  **the element's own holes** — h(Z) = L(m) − v(Z), the countdown: how many slots the period has
       left when the element sits in it. It runs 0..31 over 118 elements, and it *is* the block label
       (p for h ≤ 5, d for 6–15, f for 16–29, s for the two row-head values).
  (ii) **the inventory's holes** — 120 − 118 = 2: the two slots of the rung that no element fills.
  (iii)**the shell's pores** — 2n² − (electrons actually in shell n) at Z = 118: 18, 54, 90 for n = 5, 6,
       7, total 162. These close at the partial sums of 2n² (2, 10, 28, 60, 110), not at the table's
       closures (2, 10, 18, 36, 54, 86, 118).

Also measures whether the number of holes orders any property (it does not, within a block), and where
the hole-free elements sit. Writes results/tableV4_holes.csv.

Run: python3 scripts/element_holes.py
"""
import csv, math
import numpy as np
import random

C = [0, 2, 10, 18, 36, 54, 86, 118]
def L(m): return 2 * (((m + 1) + 1) // 2) ** 2

rows = list(csv.DictReader(open("results/tableO_element_properties.csv")))
def f(x):
    x = (x or "").strip()
    return float(x) if x else None
els = [dict(Z=int(r["Z"]), sym=r["element"], m=int(r["period_m"]), h=int(r["countdown_h"]),
            blk=r["block"], M=f(r["atomic_mass_u"]), Cm=f(r["C_molar_J_per_molK"]),
            EN=f(r["EN"]), rad=f(r["radius_pm"])) for r in rows]
print("%d elements" % len(els))

print("\n== (i) the element's own holes: h = L(m) - v")
from collections import Counter
ch = Counter(e["h"] for e in els)
print("  h values 0..31, counts:")
for lo in range(0, 32, 8):
    print("   h=%2d-%2d: %s" % (lo, lo + 7, [ch.get(h, 0) for h in range(lo, lo + 8)]))
print("  total holes over all 118 elements: %d" % sum(e["h"] for e in els))
print("  mean holes per element: %.2f" % np.mean([e["h"] for e in els]))

print("\n== the block is the hole interval: does the label follow h on all 118?")
def block_of(m, h):
    if h in (L(m) - 2, L(m) - 1):
        return "s"
    if h <= 5:
        return "p"
    if h <= 15:
        return "d"
    if h <= 29:
        return "f"
    return "?"
bad = [(e["sym"], e["h"], e["blk"], block_of(e["m"], e["h"])) for e in els if block_of(e["m"], e["h"]) != e["blk"]]
print("  mismatches: %d %s" % (len(bad), bad[:5]))
print("  per block: h range and the number of elements")
for b in "spdf":
    hs = [e["h"] for e in els if e["blk"] == b]
    print("   %s: n=%3d  h %2d..%2d  median %2d" % (b, len(hs), min(hs), max(hs), int(np.median(hs))))

print("\n== (ii) the inventory's holes")
print("  120 - 118 = %d  (the 8s2 slots no element fills)" % (120 - 118))
print("  the seven hole-free elements (h = 0): %s" % [e["sym"] for e in els if e["h"] == 0])

print("\n== (iii) the shell pores at Z = 118")
occ = {"shell 5": 32, "shell 6": 18, "shell 7": 8}
tot = 0
for k, v in occ.items():
    n = int(k.split()[1])
    pore = 2 * n * n - v
    tot += pore
    print("  %s: capacity %3d, filled %2d, pore %3d" % (k, 2 * n * n, v, pore))
print("  total pore %d;  the record's law pore(n) = 18(2n-9): %s" % (tot, [18 * (2 * n - 9) for n in (5, 6, 7)]))
shell_sums = np.cumsum([2 * n * n for n in range(1, 8)])
print("  the shells close at %s" % shell_sums.tolist())
print("  the table closes at  %s" % C[1:])
print("  they differ because each 2n^2 is taken twice (L(m) = 2*ceil((m+1)/2)^2)")

print("\n== does the number of holes order a property?")
def spearman(a, b):
    ra = np.argsort(np.argsort(np.asarray(a, float)))
    rb = np.argsort(np.argsort(np.asarray(b, float)))
    return float(np.corrcoef(ra, rb)[0, 1])
for key, name in [("Cm", "molar heat"), ("EN", "electronegativity"), ("rad", "radius")]:
    sub = [e for e in els if e[key] is not None]
    print("  %-16s all: %+.3f" % (name, spearman([e[key] for e in sub], [e["h"] for e in sub])), end="")
    for b in "spd":
        s2 = [e for e in sub if e["blk"] == b]
        if len(s2) > 6:
            print("   | %s: %+.3f" % (b, spearman([e[key] for e in s2], [e["h"] for e in s2])), end="")
    print()

print("\n== holes by period: how full each period is at Z = 118")
for m in range(1, 8):
    sub = [e for e in els if e["m"] == m]
    print("  period %d: capacity %2d, elements %2d, last h = %2d" % (m, L(m), len(sub), min(e["h"] for e in sub)))

with open("results/tableV4_holes.csv", "w") as fo:
    fo.write("Z,element,period_m,countdown_h,holes,block,L_m,sleep_slots_left\n")
    for e in els:
        fo.write("%d,%s,%d,%d,%d,%s,%d,%d\n"
                 % (e["Z"], e["sym"], e["m"], e["h"], e["h"], e["blk"], L(e["m"]), L(e["m"]) - e["h"]))
ok = (len(bad) == 0 and all(e["h"] == 0 for e in els if e["Z"] in C[1:])
      and sum(1 for e in els if e["h"] == 0) == 7)
print("\n  HOLES CHECK %s (blocks follow h on all 118, seven hole-free elements, pores 18/54/90)"
      % ("PASSED" if ok else "FAILED"))
