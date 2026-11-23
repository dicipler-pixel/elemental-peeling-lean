#!/usr/bin/env python3
"""The air / gap / total law, decade by decade, with three models scored.

The measurements come from `.scratch/work/c1e*.json` (segmented sieve, see
`.scratch/work/centroid_ext.py`).  Each decade k carries, for pairs whose start
lies in [10^k, 10^(k+1)):  n, sum(air), sum(air^2), sum(t^2), sum(t).

Identity used everywhere: air = gap - 2, T = air + 4 = gap + 2, where gap is the
start-to-start (= centre-to-centre) distance.  So a law on the gap becomes a law
on the air with an offset of -2, and on the total with an offset of +2.

Models scored (mean air predicted):
  A  flat   0.75 * <t^2>                    (3/4, no offset)
  B  total  0.757390 * <t^2> - 4            (H-L with no offset on T)
  C  gap    0.757390 * <t^2> - 2            (H-L with no offset on the gap)
"""
import json, math, pathlib, sys

HL = 1.0 / 1.32032363169374          # 1/(2*C_2), Hardy-Littlewood twin constant

def load():
    # d1e*.json is the fixed accumulator (exact pair counts), c1e*.json the earlier one;
    # prefer the fixed file when both cover a decade.
    dec = {}
    files = sorted(pathlib.Path(".scratch/work").glob("c1e*.json")) + \
        sorted(pathlib.Path(".scratch/work").glob("d1e*.json"))
    for f in files:
        for k, v in json.loads(f.read_text())["decades"].items():
            dec[int(k)] = v
    return dec

def rows(dec):
    out = []
    for k in sorted(dec):
        v = dec[k]
        n = v["n"]
        air = v["sum_air"] / n
        t2 = v["sum_t2"] / n
        var = max(0.0, v["sum_air2"] / n - air * air)
        se = math.sqrt(var / n)          # standard error of the mean air
        out.append(dict(k=k, n=n, air=air, t2=t2, se=se, gap=air + 2))
    return out

def main():
    R = rows(load())
    print("dec  n            <air>      +-      <gap>     <t^2>    gap/t^2   +-")
    for r in R:
        print("%2d %10d %9.3f %8.3f %9.3f %8.2f %9.6f %8.5f"
              % (r["k"], r["n"], r["air"], r["se"], r["gap"], r["t2"],
                 r["gap"] / r["t2"], r["se"] / r["t2"]))
    print()
    print("residuals in units of air (sigma in brackets)")
    print("dec   flat 3/4        total-4        gap-2")
    tot = {k: [] for k in "ABC"}
    for r in R:
        A = 0.75 * r["t2"]
        B = HL * r["t2"] - 4
        C = HL * r["t2"] - 2
        for key, m in zip("ABC", (A, B, C)):
            tot[key].append((r["air"] - m) / r["se"])
        print("%2d  %+7.3f (%5.1f) %+7.3f (%5.1f) %+7.3f (%5.1f)"
              % (r["k"], r["air"] - A, (r["air"] - A) / r["se"],
                 r["air"] - B, (r["air"] - B) / r["se"],
                 r["air"] - C, (r["air"] - C) / r["se"]))
    print()
    print("pooled chi^2 over decades 7 and up:")
    for key, name in (("A", "flat 3/4"), ("B", "total -4"), ("C", "gap -2")):
        vals = [z for z, r in zip(tot[key], R) if r["k"] >= 7]
        print("  %-10s %8.1f over %d decades" % (name, sum(z * z for z in vals), len(vals)))

if __name__ == "__main__":
    main()
