#!/usr/bin/env python3
"""The Light Table: what clusters on the end digits 1, 3, 7, 9 — measured to 1e9.

The four digits are not four equivalent classes. Every prime > 5 ends in 1, 3, 7 or 9, and each of
those digits is the mod-10 shadow of **two** classes mod 30 — one on each ladder:

    digit 1: 1 (base, 1 mod 6)   and 11 (twin, 5 mod 6)
    digit 3: 13 (base)           and 23 (twin)
    digit 7: 7  (base)           and 17 (twin)
    digit 9: 19 (base)           and 29 (twin)

and the digits play two different roles in a twin pair: the **opener** (the twin start's digit) and the
**closer** (the partner's). Openers are {1,7,9} (the three twin classes 11, 17, 29); closers are
{1,3,9}. So digit 3 closes and never opens, digit 7 opens and never closes, digits 1 and 9 do both.
Each of the two "impossible" roles happens exactly once — at 3 and at 5, the two smallest pairs.

Measures, per class and per digit: primes, twin starts, the mean gap that follows, the mean air of the
handoff leaving a twin start in that class, and the 3x3 pair-type transition table with its heat
(sum T / sum t^2). Writes results/tableV2_digit_table.csv and prints the table.

Run: python3 scripts/digit_table.py [LIM]
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
pr = pr[pr <= LIM]
ts = pr[sv[pr + 2]]

print("to 1e%d: %d primes, %d twin starts" % (round(math.log10(LIM)), pr.size, ts.size))

CLASSES = [1, 7, 11, 13, 17, 19, 23, 29]
DIGIT_CLASSES = {1: (1, 11), 3: (13, 23), 7: (7, 17), 9: (19, 29)}
rows = []
print("\n== per class mod 30")
print("  class  ladder   primes      share   twin starts   mean gap after   mean air after")
for c in CLASSES:
    m = pr % 30 == c
    cnt = int(m.sum())
    pm = pr[m]
    gaps = np.diff(pm).astype(float)
    tw = ts % 30 == c
    tcnt = int(tw.sum())
    tsc = ts[tw]
    # mean air of the handoff leaving a twin start in this class
    idx = np.searchsorted(ts, tsc)
    ok = idx + 1 < ts.size
    airs = (ts[np.minimum(idx + 1, ts.size - 1)] - tsc - 2)[ok]
    rows.append(dict(cls=c, digit=c % 10, ladder="base" if c % 6 == 1 else "twin",
                     primes=cnt, share=cnt / pr.size, twins=tcnt,
                     meangap=float(gaps.mean()), meanair=float(airs.mean()) if airs.size else float("nan")))
    print("  %5d  %-6s %9d  %7.4f %10d   %12.2f  %14.1f"
          % (c, "base" if c % 6 == 1 else "twin", cnt, cnt / pr.size, tcnt,
             gaps.mean(), airs.mean() if airs.size else float("nan")))

print("\n== per digit")
print("  digit  primes      share   opens   closes   mean air (twin starts here)")
for d in (1, 3, 7, 9):
    m = pr % 10 == d
    opens = int((ts % 10 == d).sum())
    closes = int(((ts + 2) % 10 == d).sum())
    tsc = ts[ts % 10 == d]
    idx = np.searchsorted(ts, tsc)
    ok = idx + 1 < ts.size
    airs = (ts[np.minimum(idx + 1, ts.size - 1)] - tsc - 2)[ok]
    print("  %5d  %9d  %7.4f %7d %8d   %10.1f"
          % (d, int(m.sum()), m.sum() / pr.size, opens, closes, airs.mean() if airs.size else float("nan")))

print("\n== the 3x3 pair-type transition table, with its heat (sum T / sum t^2)")
types = [13, 79, 91]
tsl = ts.tolist()
# the type label is (opener digit, closer digit): 11 -> 13, 17 -> 79, 29 -> 91
ttype = [(p % 10) * 10 + ((p + 2) % 10) for p in tsl]
print("  %6s %6s %10s %10s %10s" % ("from", "to", "pairs", "mean T", "heat c"))
cells = {}
for i in range(len(tsl) - 1):
    a, b = ttype[i], ttype[i + 1]
    T = tsl[i + 1] + 2 - tsl[i]
    q = math.log(tsl[i]) ** 2
    key = (a, b)
    sT, sq, n = cells.get(key, (0, 0.0, 0))
    cells[key] = (sT + T, sq + q, n + 1)
for a in types:
    for b in types:
        sT, sq, n = cells.get((a, b), (0, 0.0, 0))
        if n:
            print("  %6d %6d %10d %10.1f %10.4f" % (a, b, n, sT / n, sT / sq))

with open("results/tableV2_digit_table.csv", "w") as f:
    f.write("class,digit,ladder,primes,prime_share,twin_starts,mean_gap_after,mean_air_after\n")
    for r in rows:
        f.write("%d,%d,%s,%d,%.5f,%d,%.3f,%.2f\n"
                % (r["cls"], r["digit"], r["ladder"], r["primes"], r["share"], r["twins"],
                   r["meangap"], r["meanair"]))
print("\n== the air class by departing type (the record's 28/10/16/4/22)")
for a in types:
    sub = [i for i in range(len(tsl) - 1) if ttype[i] == a]
    if not sub:
        continue
    airs = np.array([tsl[i + 1] - tsl[i] - 2 for i in sub])
    cls = airs % 30
    tot = len(airs)
    print("  type %d: n=%7d  air classes 28:%.3f 10:%.3f 16:%.3f 4:%.3f 22:%.3f"
          % (a, tot, *[np.mean(cls == c) for c in (28, 10, 16, 4, 22)]))
print("  DIGIT TABLE BUILD PASSED")
