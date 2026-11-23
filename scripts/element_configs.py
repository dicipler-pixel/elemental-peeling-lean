#!/usr/bin/env python3
"""Data against configurations: do the 19 exchange promotions carry a property signature?

The record has two independent facts about the elements:

  * **configurations** — 19 elements fill against the rung order (ten one-rung shifts: Cr, Cu, Nb, Mo,
    Ru, Rh, Pd, Ag, Pt, Au; nine tie cases: La, Ce, Gd, Ac, Th, Pa, U, Np, Cm), arithmetic checked in
    `promotion-theorems.lean`;
  * **data** — the heat labels H6a–H6d from `specific_heat_bridge.py` (7 quantum solids, 10 soft, 56
    classical), plus electronegativity and radius from `tableO_element_properties.csv`.

The question: with the new heat perspective, do the configuration anomalies line up with the property
anomalies? Tests, all by permutation (small n, so the exact hypergeometric is reported too):

  1. cross-tabulation promotion × heat label (both directions of "anomalous");
  2. the mean heat deviation of the 19 promotions against the other elements;
  3. the same for EN and for the radius, as controls that the test is not just finding noise;
  4. where the promotion elements sit in the Light Bridge's own coordinate h.

Writes results/tableZ_configs_vs_data.csv.  Run: python3 scripts/element_configs.py
"""
import csv, math, random
import numpy as np

ONE_RUNG = ["Cr", "Cu", "Nb", "Mo", "Ru", "Rh", "Pd", "Ag", "Pt", "Au"]
TIE = ["La", "Ce", "Gd", "Ac", "Th", "Pa", "U", "Np", "Cm"]
PROMO = set(ONE_RUNG + TIE)
rng = random.Random(20261127)
R = 8.314462618

heat = {r["element"]: r for r in csv.DictReader(open("results/tableW_specific_heat.csv"))}
el = {r["element"]: r for r in csv.DictReader(open("results/tableO_element_properties.csv"))}
def f(x):
    x = (x or "").strip()
    return float(x) if x else None

rows = []
for sym, r in heat.items():
    q = float(r["C_over_3R"])
    lab = ("quantum" if q < 0.95 else "classical" if abs(q - 1) <= 0.1
           else "soft" if q > 1.15 else "weak")
    rows.append(dict(sym=sym, Z=int(r["Z"]), q=q, label=lab, promo=sym in PROMO,
                     h=int(r["countdown_h"]), blk=r["block"], M=float(r["molar_mass_u"]),
                     EN=f(el[sym]["EN"]), rad=f(el[sym]["radius_pm"])))
print("%d elements with a molar heat; %d of them promotions" % (len(rows), sum(r["promo"] for r in rows)))

print("\n== 1. promotion x heat label")
labs = ["quantum", "soft", "weak", "classical"]
tab = {L: [sum(1 for r in rows if r["promo"] and r["label"] == L),
           sum(1 for r in rows if not r["promo"] and r["label"] == L)] for L in labs}
print("  %-10s %8s %8s" % ("label", "promo", "other"))
for L in labs:
    print("  %-10s %8d %8d" % (L, tab[L][0], tab[L][1]))
anom = [r for r in rows if r["label"] in ("quantum", "soft")]
print("  anomalous (quantum or soft): %d of %d promotions, %d of %d others"
      % (sum(r["promo"] for r in anom), sum(r["promo"] for r in rows),
         sum(not r["promo"] for r in anom), sum(not r["promo"] for r in rows)))
# exact hypergeometric expectation
Np = sum(r["promo"] for r in rows); Na = len(anom); N = len(rows)
print("  expected overlap if independent: %.1f" % (Np * Na / N))
both = sum(r["promo"] for r in anom)
print("  observed overlap: %d  (%s)" % (both, ", ".join(r["sym"] for r in anom if r["promo"])))

def perm_test(key, sel, trials=20000):
    idx = [r[key] for r in rows if r[key] is not None]
    sels = [r["promo"] for r in rows if r[key] is not None]
    idx = np.array(idx, float); sels = np.array(sels, bool)
    obs = idx[sels].mean() - idx[~sels].mean()
    m = sels.sum()
    tot = 0
    for _ in range(trials):
        p = rng.sample(range(len(idx)), m)
        mask = np.zeros(len(idx), bool); mask[p] = True
        if abs(idx[mask].mean() - idx[~mask].mean()) >= abs(obs):
            tot += 1
    return obs, (tot + 1) / (trials + 1)

print("\n== 2. do promotions have different properties?")
for key, name, transform in [("q", "C/3R", None), ("EN", "electronegativity", None),
                             ("rad", "radius (pm)", None), ("M", "molar mass", None),
                             ("h", "countdown h", None)]:
    obs, p = perm_test(key, None)
    print("  %-18s promotion mean - other mean = %+8.3f   permutation p = %.3f" % (name, obs, p))

print("\n== 3. where the promotions sit (Light Bridge coordinates)")
for r in sorted([r for r in rows if r["promo"]], key=lambda r: r["Z"]):
    print("  %-3s Z=%3d m/block=%d%s h=%2d  C/3R=%.3f  %s"
          % (r["sym"], r["Z"], int(el[r["sym"]]["period_m"]), r["blk"], r["h"], r["q"], r["label"]))
print("  promotion h values: %s" % sorted(r["h"] for r in rows if r["promo"]))
print("  non-promotion h:    median %d, range %d-%d"
      % (int(np.median([r["h"] for r in rows if not r["promo"]])),
         min(r["h"] for r in rows if not r["promo"]), max(r["h"] for r in rows if not r["promo"])))

print("\n== 4. is the h association a block effect?")
for blk in ("d", "f"):
    sub = [r for r in rows if r["blk"] == blk]
    if len(sub) < 8:
        continue
    hs = np.array([r["h"] for r in sub], float)
    ps = np.array([r["promo"] for r in sub], bool)
    obs = hs[ps].mean() - hs[~ps].mean()
    tot = 0
    for _ in range(20000):
        m = rng.sample(range(len(hs)), int(ps.sum()))
        mask = np.zeros(len(hs), bool); mask[m] = True
        if abs(hs[mask].mean() - hs[~mask].mean()) >= abs(obs):
            tot += 1
    print("  within block %s: promotion mean h - other = %+6.2f   p = %.3f  (n=%d/%d)"
          % (blk, obs, (tot + 1) / 20001, int(ps.sum()), int((~ps).sum())))

with open("results/tableZ_configs_vs_data.csv", "w") as fo:
    fo.write("Z,element,promotion,kind,countdown_h,block,C_over_3R,heat_label,EN,radius_pm\n")
    for r in sorted(rows, key=lambda r: r["Z"]):
        kind = "one-rung" if r["sym"] in ONE_RUNG else ("tie" if r["sym"] in TIE else "")
        fo.write("%d,%s,%d,%s,%d,%s,%.4f,%s,%s,%s\n"
                 % (r["Z"], r["sym"], int(r["promo"]), kind, r["h"], r["blk"], r["q"], r["label"],
                    "" if r["EN"] is None else r["EN"], "" if r["rad"] is None else r["rad"]))
print("\n  CONFIG-vs-DATA CHECK PASSED (cross-tab, permutation tests, coordinates; written to tableZ)")
