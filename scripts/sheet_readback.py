#!/usr/bin/env python3
"""Read the sheet back: the T-column, the overlap excess, and the end-digit correlation.

1. For the twin starts between 340 and 900, compute the totals T = (q+2) - p and compare
   with the numbers written on the sheet.
2. Check the two excess identities:
      sum T = (last start - first start) + 2 * (number of segments)     [two per segment]
      primes per row summed over R rows sharing boundaries over-counts by R-1
3. Measure the end-digit transition matrix of consecutive primes (the "correlate to the
   prime just before"), and its decay with lag.
"""
import collections, sympy

print("== 1. the T column, twin starts 340..900")
P = list(sympy.primerange(340, 900))
tw = [p for p in P if sympy.isprime(p + 2)]
T = [(tw[i + 1] + 2) - tw[i] for i in range(len(tw) - 1)]
sheet = [74, 14, 32, 62, 50, 32, 20, 26, 20, 152, 14, 8, 32]
print("   twin starts:", tw)
print("   computed T  :", T)
print("   on the sheet:", sheet)
print("   first %d agree exactly: %s" % (len(sheet), T[:len(sheet)] == sheet))

print("\n== 2. the two excesses")
print("   sum T = %d ; (last-start - first-start) + 2*segments = %d + %d = %d"
      % (sum(T[:len(sheet)]), tw[len(sheet)] - tw[0], 2 * len(sheet),
         tw[len(sheet)] - tw[0] + 2 * len(sheet)))
print("   sheet rows share their boundary primes 419, 461, 521, 599, 659, 809:"
      " 6 = R-1 for R = 7 rows")

print("\n== 3. end-digit correlation of consecutive primes")
LIM = 2_000_000
ps = [p for p in sympy.primerange(5, LIM)]
D = [p % 10 for p in ps]
digs = [1, 3, 7, 9]
M = collections.Counter((D[i], D[i + 1]) for i in range(len(D) - 1))
row = {d: sum(M[(d, e)] for e in digs) for d in digs}
print("   P(next digit | this digit), n = %d   (null 0.2500, SE %.4f)"
      % (sum(row.values()), 0.25 / row[1] ** 0.5))
print("        " + "".join("%8d" % e for e in digs))
for d in digs:
    print("   %4d" % d + "".join("%8.4f" % (M[(d, e)] / row[d]) for e in digs))
for lag in range(1, 5):
    c = collections.Counter((D[i], D[i + lag]) for i in range(len(D) - lag))
    r = {d: sum(c[(d, e)] for e in digs) for d in digs}
    dev = max(abs(c[(d, e)] / r[d] - 0.25) for d in digs for e in digs)
    print("   lag %d: max |P - 0.25| = %.4f" % (lag, dev))
print("\n   gap step histogram (the base key's ordering):")
steps = collections.Counter(b - a for a, b in zip(ps, ps[1:]) if b - a <= 20)
for s in (2, 4, 6, 8, 10):
    print("     step %2d: %7d" % (s, steps[s]))
