#!/usr/bin/env python3
"""The four sequence readings of a fission yield table, per system.

For a fixed parent Z (and a fixed incident energy) the products form a set of occupied
charge cells.  Read that set four ways, as asked:

  1. end digit sequence            digits of the occupied cells, in increasing Z
  2. gap end digit sequence        digits of the gaps between consecutive occupied cells
  3. subset gap number order       the gap values in order of first appearance
  4. subset end digit order        the end digits in order of first appearance

Plus the two structures that survive every energy: the valley (the single hole, at the
symmetry point) and the period-2 alternation (even-Z cells favoured).

Usage: python3 scripts/sequence_readings.py [threshold-fraction]   (default 0.01)
"""
import collections, glob, os, re, sys

FRAC = float(sys.argv[1]) if len(sys.argv) > 1 else 0.01
RAW = ".scratch/fission/fy"

def load(p):
    out = []
    for line in open(p):
        if line.startswith("#") or not line.strip():
            continue
        f = line.split()
        if len(f) < 4:
            continue
        try:
            out.append((int(f[0]), int(f[1]), float(f[3])))
        except ValueError:
            pass
    return out

def readings(path):
    d = collections.defaultdict(float)
    for z, a, y in load(path):
        d[z] += y
    mx = max(d.values())
    occ = sorted(z for z, y in d.items() if y > FRAC * mx)
    digits = [z % 10 for z in occ]
    gaps = [occ[i + 1] - occ[i] for i in range(len(occ) - 1)]
    gapdigits = [g % 10 for g in gaps]
    first_gap = []
    for g in gaps:
        if g not in first_gap:
            first_gap.append(g)
    first_dig = []
    for x in digits:
        if x not in first_dig:
            first_dig.append(x)
    # runs of consecutive cells, and the holes between them
    runs, start = [], occ[0]
    for i in range(len(occ) - 1):
        if occ[i + 1] != occ[i] + 1:
            runs.append((start, occ[i]))
            start = occ[i + 1]
    runs.append((start, occ[-1]))
    holes = [(runs[i][1] + 1, runs[i + 1][0] - 1) for i in range(len(runs) - 1)]
    # even/odd yield ratio
    ze = sum(y for z, a, y in load(path) if z % 2 == 0)
    zo = sum(y for z, a, y in load(path) if z % 2)
    return dict(occ=occ, digits=digits, gaps=gaps, gapdigits=gapdigits,
                first_gap=first_gap, first_dig=first_dig, runs=runs, holes=holes, even_odd=ze / zo)

def label(p):
    parts = os.path.basename(p)[:-8].split("-")
    return parts[1] + ("(SF)" if parts[0] == "0" else "") + " " + (parts[3] if len(parts) > 3 else "")

print("threshold: %.3f of the peak cell\n" % FRAC)
print("%-16s %4s %-16s %-28s %-22s %-10s %-16s %6s" % (
    "system", "n", "runs", "1 end digits", "2 gap digits", "3 gap order", "4 digit order", "even/odd"))
for p in sorted(glob.glob(RAW + "/*-454.txt")):
    r = readings(p)
    print("%-16s %4d %-16s %-28s %-22s %-10s %-16s %6.2f" % (
        label(p), len(r["occ"]), str(r["runs"]),
        "".join(map(str, r["digits"])) if len(r["digits"]) <= 27 else "(%d cells)" % len(r["digits"]),
        "".join(map(str, r["gapdigits"])) if len(r["gapdigits"]) <= 21 else "(%d gaps)" % len(r["gapdigits"]),
        str(r["first_gap"]), str(r["first_dig"]), r["even_odd"]))
    if r["holes"]:
        print("%-16s      holes %s" % ("", [("Z %d-%d" % h) for h in r["holes"]]))
