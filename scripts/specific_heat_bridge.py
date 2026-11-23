#!/usr/bin/env python3
"""The heat capacity in the three readings the density triangle gives it, and its table labels.

Part 1 (exact, random): the triangle commutes.  Random masses, densities, volumes, heat capacities
are drawn and every reading is checked against the other two — the density triangle, its heat twin,
Dulong–Petit in the per-gram / per-mole / per-volume forms, and the forced exchange rate.  A single
failure is a bug.

Part 2 (measured): the element table's own heat column, against the Light Bridge's labels — block,
period, countdown h.  This is where the record's `C/3R` gets its labels: which blocks are classical,
which are stiff, and whether the countdown h really orders the heat or only appears to.

Run: python3 scripts/specific_heat_bridge.py [trials]
Writes results/tableW_specific_heat.csv.
"""
import sys, csv, math, random
import numpy as np

TRIALS = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
rng = random.Random(20261125)
R = 8.314462618
TC = 1 / (2 * 0.6601618158468696)     # 1/(2 C2) = 0.75739, the record's c

print("== 1. The triangle commutes (random inputs, exact to 1e-12)")
bad = 0
for _ in range(TRIALS):
    M = rng.uniform(1, 300)          # molar mass
    D = rng.uniform(0.1, 25)         # density
    c = rng.uniform(0.05, 30)        # specific heat per gram
    V = M / D                        # molar volume
    C = c * M                        # molar heat
    if abs(D - M / V) > 1e-9 * max(1, D): bad += 1
    if abs(V - M / D) > 1e-9 * max(1, V): bad += 1
    if abs(C - c * D * V) > 1e-9 * max(1, C): bad += 1
    if abs(D * c - C / V) > 1e-9 * max(1, D * c): bad += 1
print("  triangle, heat twin, volumetric reading: %d/%d ok" % (TRIALS - bad, TRIALS))

bad2 = 0
for _ in range(TRIALS):
    M = rng.uniform(1, 300)
    Rr = R
    c = 3 * Rr / M
    D = rng.uniform(0.1, 25)
    V = M / D
    if abs(M * c - 3 * Rr) > 1e-9 * 3 * Rr: bad2 += 1
    if abs(D * c - 3 * Rr / V) > 1e-9 * 3 * Rr / V: bad2 += 1
    # two solids, same molar volume, same volumetric heat
    c2 = 3 * Rr / ((D * 2) * V)                  # a heavier solid, same molar volume
    if abs(D * c - (D * 2) * c2) > 1e-9 * 3 * Rr / V: bad2 += 1
print("  Dulong-Petit per gram / per mole / per volume: %d/%d ok" % (TRIALS - bad2, TRIALS))

bad3 = 0
for _ in range(TRIALS):
    a, b, t = TC, 3 * R, rng.uniform(1, 40)
    T = a * t ** 2 / b
    if abs(T - (a / b) * t ** 2) > 1e-12: bad3 += 1
print("  the exchange rate is a/b, nothing else: %d/%d ok" % (TRIALS - bad3, TRIALS))
print("  kappa = %.6f K per unit t^2   (0.75739 / 24.943)" % (TC / (3 * R)))

print("\n== 2. The element table, by the Light Bridge's own labels")
rows = list(csv.DictReader(open("results/tableO_element_properties.csv")))
def f(x):
    x = (x or "").strip()
    return float(x) if x else None
els = [dict(Z=int(r["Z"]), sym=r["element"], m=int(r["period_m"]), h=int(r["countdown_h"]),
            blk=r["block"], M=f(r["atomic_mass_u"]), C=f(r["C_molar_J_per_molK"]),
            c=f(r["c_gram_J_per_gK"]), EN=f(r["EN"]), IE=f(r["IE1_kJ"]), rad=f(r["radius_pm"]))
       for r in rows]
have = [e for e in els if e["C"] and e["M"]]
for e in have:
    e["q"] = e["C"] / (3 * R)
print("  %d elements carry a molar heat capacity" % len(have))
q = np.array([e["q"] for e in have])
print("  C/3R: median %.3f  mean %.3f  sd %.3f  min %.2f (%s)  max %.2f (%s)"
      % (np.median(q), q.mean(), q.std(), q.min(), have[int(np.argmin(q))]["sym"],
         q.max(), have[int(np.argmax(q))]["sym"]))
print("  within +-10%% of 3R: %.0f%%" % (100 * np.mean(np.abs(q - 1) < 0.1)))
print("  labels: quantum solid (C/3R < 0.95) %d, classical (|C/3R-1| <= 0.1) %d, "
      "soft (> 1.15) %d, weakly off %d"
      % (sum(q < 0.95), sum(abs(q - 1) <= 0.1), sum(q > 1.15),
         len(q) - sum(q < 0.95) - sum(abs(q - 1) <= 0.1) - sum(q > 1.15)))

def spearman(a, b):
    ra = np.argsort(np.argsort(np.asarray(a, float)))
    rb = np.argsort(np.argsort(np.asarray(b, float)))
    return float(np.corrcoef(ra, rb)[0, 1])

with open("results/tableW_specific_heat.csv", "w") as fo:
    fo.write("Z,element,period_m,countdown_h,block,molar_mass_u,C_molar,C_over_3R,label\n")
    for e in have:
        lab = ("quantum solid" if e["q"] < 0.95 else
               "classical" if abs(e["q"] - 1) <= 0.1 else
               "soft (anomalous)" if e["q"] > 1.15 else "weakly off")
        fo.write("%d,%s,%d,%d,%s,%.4f,%.3f,%.4f,%s\n"
                 % (e["Z"], e["sym"], e["m"], e["h"], e["blk"], e["M"], e["C"], e["q"], lab))

print("\n  by block (the Light Bridge block label):")
for blk in "spdf":
    v = np.array([e["q"] for e in have if e["blk"] == blk])
    if v.size:
        print("    %s: n=%2d  median %.3f  mean %.3f  spread %.2f-%.2f"
              % (blk, v.size, np.median(v), v.mean(), v.min(), v.max()))
print("  by period m:")
for m in range(1, 8):
    v = np.array([e["q"] for e in have if e["m"] == m])
    if v.size:
        print("    m=%d: n=%2d  median %.3f" % (m, v.size, np.median(v)))
print("\n  does the countdown h order the heat?")
print("    all elements:      Spearman(C/3R, h) = %+.3f  (n=%d)" % (spearman(q, [e["h"] for e in have]), len(have)))
for blk in "spd":
    sub = [e for e in have if e["blk"] == blk]
    if len(sub) > 5:
        print("    within block %s:   Spearman(C/3R, h) = %+.3f  (n=%2d)"
              % (blk, spearman([e["q"] for e in sub], [e["h"] for e in sub]), len(sub)))
print("    against Z:         Spearman(C/3R, Z) = %+.3f" % spearman(q, [e["Z"] for e in have]))
print("    against mass M:    Spearman(C/3R, M) = %+.3f" % spearman(q, [e["M"] for e in have]))
print("    against radius:    Spearman(C/3R, r) = %+.3f"
      % spearman([e["q"] for e in have if e["rad"]], [e["rad"] for e in have if e["rad"]]))

stiff = sorted([e for e in have if e["q"] < 0.95], key=lambda e: e["q"])
soft = sorted([e for e in have if e["q"] > 1.15], key=lambda e: -e["q"])
print("\n  labelled quantum solids (C/3R < 0.95): %d" % len(stiff))
for e in stiff:
    print("    %-3s Z=%3d m=%d h=%2d %s  C/3R=%.3f" % (e["sym"], e["Z"], e["m"], e["h"], e["blk"], e["q"]))
print("  labelled soft/anomalous (C/3R > 1.15): %d" % len(soft))
for e in soft:
    print("    %-3s Z=%3d m=%d h=%2d %s  C/3R=%.3f" % (e["sym"], e["Z"], e["m"], e["h"], e["blk"], e["q"]))

cg = [(e["c"], 3 * R / e["M"]) for e in have if e["c"]]
rr = float(np.corrcoef([a for a, _ in cg], [b for _, b in cg])[0, 1])
print("\n  per gram: c_measured vs 3R/M   r = %.4f, median ratio %.3f (n=%d)"
      % (rr, np.median([a / b for a, b in cg]), len(cg)))

# the volumetric reading needs a density column the table does not carry: say so with numbers
print("\n  the radius column is NOT a molar volume (implied rho from (4/3)pi r^3 N_A):")
NA = 6.02214076e23
for sym in ("Fe", "Cu", "Au", "Al", "C"):
    for e in have:
        if e["sym"] == sym and e["rad"]:
            Vm = 4 / 3 * math.pi * (e["rad"] * 1e-10) ** 3 * NA
            print("    %-3s r=%3.0f pm -> V_m=%5.1f cm3/mol -> rho=%5.2f g/cm3, 3R/V_m=%6.2f J/cm3/K"
                  % (sym, e["rad"], Vm, e["M"] / Vm, 3 * R / Vm))
            break

ok = (bad == 0 and bad2 == 0 and bad3 == 0 and rr > 0.99)
print("\n  SPECIFIC HEAT BRIDGE %s" % ("PASSED" if ok else "FAILED"))
sys.exit(0 if ok else 1)
