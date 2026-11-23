#!/usr/bin/env python3
"""Verify the measured parts of the fission theorem.

Two layers:

1. If the raw ENDF/B-VIII.0 yield tables are present (`.scratch/fission/fy/*-454.txt`,
   see `fission-tests.md` §0 for provenance and format), rebuild the derived tables
   `results/tableR_fission_tests.csv` and `results/tableS_fission_parity.csv`.
2. Check every number quoted in `fission-theorem.md` against those tables, and exit
   non-zero if any of them has moved.

Run from the project root:  python3 scripts/fission_verify.py
"""
import csv, glob, os, re, sys, math, collections, statistics, pathlib

RAW = pathlib.Path(".scratch/fission/fy")
CSV_R = pathlib.Path("results/tableR_fission_tests.csv")
CSV_S = pathlib.Path("results/tableS_fission_parity.csv")
SYM = ("H He Li Be B C N O F Ne Na Mg Al Si P S Cl Ar K Ca Sc Ti V Cr Mn Fe Co Ni Cu Zn "
       "Ga Ge As Se Br Kr Rb Sr Y Zr Nb Mo Tc Ru Rh Pd Ag Cd In Sn Sb Te I Xe Cs Ba La Ce Pr "
       "Nd Pm Sm Eu Gd Tb Dy Ho Er Tm Yb Lu Hf Ta W Re Os Ir Pt Au Hg Tl Pb Bi Po At Rn Fr Ra "
       "Ac Th Pa U Np Pu Am Cm Bk Cf Es Fm Md No Lr").split()
ZOF = {s: i + 1 for i, s in enumerate(SYM)}
CLOS = {0: 0, 1: 2, 2: 10, 3: 18, 4: 36, 5: 54, 6: 86, 7: 118}


def period(z):
    for m in range(1, 8):
        if z <= CLOS[m]:
            return m


def llen(m):
    return 2 * ((((m + 1) + 1) // 2)) ** 2


def cnt(z):
    return CLOS[period(z)] - z


def blk(z):
    m, h = period(z), cnt(z)
    if h in (llen(m) - 2, llen(m) - 1):
        return "s"
    if h <= 5:
        return "p"
    if h <= 15:
        return "d"
    return "f"


def closed(z):
    return blk(z) in ("p", "s")


def load(path):
    out = []
    for line in open(path):
        if line.startswith("#") or not line.strip():
            continue
        f = line.split()
        if len(f) < 4:
            continue
        try:
            out.append((int(f[0]), int(f[1]), float(f[3])))   # columns are (Z, A, ISO, Y)
        except ValueError:
            pass
    return out


def stats(path):
    base = os.path.basename(path)[:-8]
    parts = base.split("-")
    idx, nuc, lib = parts[0], parts[1], parts[2]
    en = "SF" if len(parts) > 3 and parts[3] == "SF" else (parts[3] if len(parts) > 3 else "")
    el = re.match(r"([A-Z][a-z]?)", nuc).group(1)
    Zp, Ap = ZOF[el], int(nuc[len(el):])
    rec = load(path)
    mass = collections.defaultdict(float)
    zA = collections.defaultdict(lambda: collections.defaultdict(float))
    for z, a, y in rec:
        mass[a] += y
        zA[a][z] += y
    As = sorted(a for a in mass if mass[a] > 0)
    mid = Ap / 2.0
    light = [a for a in As if a < mid]
    heavy = [a for a in As if a >= mid]
    Al = max(light, key=lambda a: mass[a])
    Ah = max(heavy, key=lambda a: mass[a])
    inner = [a for a in As if Al + 8 <= a <= Ah - 8]
    Av = min(inner, key=lambda a: mass[a])
    peak = max(mass[Al], mass[Ah])

    def zp(a):
        d = zA.get(a)
        return max(d, key=lambda z: d[z]) if d else None

    def meanZ(lo, hi):
        s = sy = 0.0
        for a in As:
            if lo <= a <= hi:
                for z, y in zA[a].items():
                    s += z * y
                    sy += y
        return s / sy

    Atot = Ap + 1 if idx == "n" else Ap
    tot = sum(mass.values())
    wclosed = 0.0
    for a in light:
        z1 = zp(a)
        a2 = min(heavy, key=lambda x: abs(x - (Atot - a))) if heavy else None
        z2 = zp(a2) if a2 is not None else None
        if z1 is None or z2 is None:
            continue
        if closed(z1) and closed(z2):
            wclosed += mass[a]
    ze = sum(y for z, a, y in rec if z % 2 == 0)
    zo = sum(y for z, a, y in rec if z % 2)
    Ne = sum(y for z, a, y in rec if (a - z) % 2 == 0)
    No = sum(y for z, a, y in rec if (a - z) % 2)
    oddL = sum(y for z, a, y in rec if z % 2 and a < mid) / sum(y for z, a, y in rec if a < mid)
    label = nuc + ("(SF)" if idx == "0" else "") + " " + en + " " + lib
    return dict(system=label, Z=Zp, A=Ap,
                A_light=Al, A_heavy=Ah, A_valley=Av, valley_over_peak=mass[Av] / peak,
                mean_Z_light=meanZ(min(As), mid - 1), mean_Z_heavy=meanZ(mid, max(As)),
                closed_pair_share=wclosed / tot, even_over_odd_Z=ze / zo,
                even_over_odd_N=Ne / No, odd_Z_share_light=oddL,
                delta=54 - Zp / 2 - 5, library=lib, energy=en)


def rebuild():
    if not RAW.exists() or not list(RAW.glob("*-454.txt")):
        print("raw ENDF tables absent — checking the committed CSVs only")
        return
    rows = sorted((stats(p) for p in RAW.glob("*-454.txt")), key=lambda r: (r["Z"], r["system"]))
    with open(CSV_R, "w", newline="") as f:
        w = csv.writer(f)
        cols = ["system", "Z", "A", "energy", "A_light", "A_heavy", "A_valley",
                "valley_over_peak", "mean_Z_light", "mean_Z_heavy", "closed_pair_share", "delta"]
        w.writerow(cols)
        for r in rows:
            w.writerow([r["system"], r["Z"], r["A"], r["energy"], r["A_light"], r["A_heavy"],
                        r["A_valley"], "%.5f" % r["valley_over_peak"], "%.2f" % r["mean_Z_light"],
                        "%.2f" % r["mean_Z_heavy"], "%.3f" % r["closed_pair_share"], "%.1f" % r["delta"]])
    with open(CSV_S, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["system", "Z", "A", "energy", "even_over_odd_Z", "even_over_odd_N", "odd_Z_share_light"])
        for r in rows:
            w.writerow([r["system"], r["Z"], r["A"], r["energy"], "%.3f" % r["even_over_odd_Z"],
                        "%.3f" % r["even_over_odd_N"], "%.3f" % r["odd_Z_share_light"]])
    print("rebuilt", CSV_R.name, "and", CSV_S.name, "from", len(rows), "systems")


def readcsv(path):
    with open(path) as f:
        return list(csv.DictReader(f))


CHECKS = []


def check(name, got, want, tol):
    ok = abs(got - want) <= tol
    CHECKS.append((name, got, want, tol, ok))


def main():
    rebuild()
    R = readcsv(CSV_R)
    for r in R:
        for k in ("Z", "A", "A_light", "A_heavy"):
            r[k] = int(r[k])
        for k in ("valley_over_peak", "mean_Z_light", "mean_Z_heavy", "closed_pair_share", "delta"):
            r[k] = float(r[k])

    low = [r for r in R if r["Z"] <= 96]
    pin = statistics.mean(r["mean_Z_heavy"] for r in low)
    sem = statistics.stdev(r["mean_Z_heavy"] for r in low) / math.sqrt(len(low))
    check("heavy charge, mean over Z<=96", pin, 53.956, 0.05)
    check("heavy charge, s.e.m.", sem, 0.094, 0.03)
    check("number of systems with Z<=96", len(low), 21, 0)

    # the light piece against Z-54: every system except U-238 (whose fission is thresholded) is
    # inside 0.21 protons; U-238 at 500 keV sits at 0.46 and at 14 MeV at 0.92.
    devs = {}
    for r in R:
        if r["Z"] <= 94 and "0014.000" not in r["energy"] and not r["system"].startswith("U238"):
            devs[r["system"]] = r["mean_Z_light"] - (r["Z"] - 54)
    check("max |light-(Z-54)|, Z<=94, not U-238, not 14 MeV", max(abs(v) for v in devs.values()), 0.21, 0.01)
    u8 = [r for r in R if r["system"].startswith("U238") and "0000.500" in r["system"]][0]
    check("U-238 500 keV: light minus (Z-54)", u8["mean_Z_light"] - 38, 0.46, 0.01)

    # Cm-244 has drifted: the light piece is 1.5 below Z-54 at Cf
    cf = [r for r in R if r["Z"] == 98]
    check("Cf: light minus (Z-54)", cf[0]["mean_Z_light"] - (98 - 54), -1.49, 0.05)

    # closed-pair shares
    def pick(tag, energy="2.53E", lib="endfb8.0"):
        return [r for r in R if r["system"].startswith(tag) and energy in r["system"]
                and lib in r["system"]][0]

    def pick_any(tag):
        return [r for r in R if r["system"].startswith(tag)][0]

    check("closed share, Th-232 500 keV", pick_any("Th232")["closed_pair_share"], 0.357, 0.02)
    check("closed share, U-235 thermal", pick("U235")["closed_pair_share"], 0.158, 0.02)
    check("closed share, U-233 thermal", pick("U233")["closed_pair_share"], 0.200, 0.02)
    check("closed share, Np-237 thermal", pick("Np237")["closed_pair_share"], 0.083, 0.02)
    for tag in ("Pu239", "Am241", "Cm244", "Cf252"):
        check("closed share, " + tag + " (must be 0)", pick_any(tag)["closed_pair_share"], 0.0, 0.001)

    # valley/peak, SF series
    for tag, want in (("Cm244", 0.00014), ("Cm248", 0.00025), ("Cf250", 0.00257),
                      ("Cf252", 0.00267), ("Fm256", 0.0673)):
        check("valley/peak, " + tag, pick_any(tag)["valley_over_peak"], want, 0.0002 + 0.02 * want)

    # the decisive same-Z pair: thermal vs spontaneous at Z = 96
    th = pick_any("Cm245")["valley_over_peak"]
    sf = pick_any("Cm244")["valley_over_peak"]
    check("Cm thermal / Cm SF ratio", th / sf, 31.0, 2.0)

    S = readcsv(CSV_S)
    for r in S:
        for k in ("even_over_odd_Z", "even_over_odd_N", "odd_Z_share_light"):
            r[k] = float(r[k])
    def picks(tag, energy="2.53E", lib="endfb8.0"):
        return [r for r in S if r["system"].startswith(tag) and energy in r["system"]
                and lib in r["system"]][0]

    check("even/odd Z, U-235 thermal", picks("U235")["even_over_odd_Z"], 1.635, 0.02)
    check("even/odd Z, U-235 thermal (JEFF-3.3, independent check)",
          picks("U235", lib="jeff3.3")["even_over_odd_Z"], 1.781, 0.02)
    check("even/odd Z, Cf-252 SF", [r for r in S if r["system"].startswith("Cf252")][0]["even_over_odd_Z"], 1.096, 0.02)
    check("odd-Z share, U-235 thermal light", picks("U235")["odd_Z_share_light"], 0.380, 0.01)

    bad = [c for c in CHECKS if not c[4]]
    print("\n%-46s %10s %10s %8s  %s" % ("check", "measured", "in theorem", "tol", ""))
    for name, got, want, tol, ok in CHECKS:
        print("%-46s %10.5f %10.5f %8.5f  %s" % (name, got, want, tol, "ok" if ok else "**MISMATCH**"))
    print("\n%d checks, %d mismatches" % (len(CHECKS), len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
