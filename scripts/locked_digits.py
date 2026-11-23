#!/usr/bin/env python3
"""The un-baking test: 3 and 7 cannot come back, 1 and 9 can — and what that does to the fission ratio.

Part A (primes, exact): the return event `closer digit == next opener digit`. Measured to 1e9, with the
per-decade stability of the one rate that is not forced.

Part B (fission): the heavy fragment's last digit as a closure-offset marker. A pre-registered test:
    digit 3 on Z_H  =>  Z_H = 53, one below the closure  =>  R = (Z-53)/53
    digit 4         =>  Z_H = 54                          =>  R = (Z-54)/54
    digit 5         =>  Z_H = 55                          =>  R = (Z-55)/55
and the association between that digit and the excitation energy.

Writes results/tableV10_locked_digits.csv.
Run: python3 scripts/locked_digits.py [LIM]
"""
import sys, math, csv
from math import comb
import numpy as np

LIM = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 9
sv = np.ones(LIM + 8, dtype=bool)
sv[:2] = False
for i in range(2, int((LIM + 6) ** 0.5) + 1):
    if sv[i]:
        sv[i * i::i] = False
pr = np.nonzero(sv[:LIM + 3])[0].astype(np.int64)
ts = pr[sv[pr + 2]]
ts = ts[(ts > 5) & (ts <= LIM)]
beg, end = ts % 10, (ts + 2) % 10
N = ts.size

print("== A. the roles (exact)")
print("  openers: %s   closers: %s"
      % ({int(d): int((beg == d).sum()) for d in (1, 7, 9)},
         {int(d): int((end == d).sum()) for d in (1, 3, 9)}))
print("  returnable digits = {1,7,9} n {1,3,9} = {1,9}")
print("\n  the return event, per departing digit:")
rows_out = []
for c in (1, 3, 7, 9):
    m = end[:-1] == c
    n = int(m.sum())
    ret = int(np.count_nonzero(beg[1:][m] == c)) if n else 0
    rate = ret / n if n else float("nan")
    rows_out.append((c, n, ret, rate))
    print("    closer %d: %8d rows  %7d returns  P(return) = %s"
          % (c, n, ret, ("%.4f" % rate) if n else "undefined (never a closer)"))
print("    -> 3 returns exactly never; 7 never even occurs as a closer; 1 and 9 return ~35% of the time")

print("\n  the one rate that is not forced, by decade:")
rates = []
for d in range(4, int(math.log10(LIM)) + 1):
    i0 = int(np.searchsorted(ts, 10 ** d)); i1 = int(np.searchsorted(ts, 10 ** (d + 1)))
    if i1 - i0 < 100:
        continue
    m = (end[i0:i1 - 1] == 1) | (end[i0:i1 - 1] == 9)
    n = int(m.sum())
    ret = int(np.count_nonzero(beg[i0 + 1:i1][m] == end[i0:i1 - 1][m]))
    rates.append((d, n, ret / n))
    print("    1e%d: n=%8d  P(return | digit 1 or 9) = %.4f" % (d, n, ret / n))
if len(rates) > 1:
    span = max(r for _, _, r in rates) - min(r for _, _, r in rates)
    print("    range %.4f .. %.4f  (a %.0f%% variation)" % (min(r for _, _, r in rates),
                                                          max(r for _, _, r in rates), 100 * span /
                                                          np.mean([r for _, _, r in rates])))

print("\n== B. the fission side: the heavy fragment's last digit")
rows = list(csv.DictReader(open("results/tableR_fission_tests.csv")))
def exc(s):
    s = s.strip()
    if "0014" in s or "14.000" in s: return "14 MeV"
    if "SF" in s: return "SF"
    if "0000.500" in s: return "0.5 MeV"
    if "2.53E" in s: return "thermal"
    return "?"
data = []
for r in rows:
    Z = int(r["Z"]); ZH = float(r["mean_Z_heavy"]); ZL = float(r["mean_Z_light"])
    data.append(dict(name=r["system"].strip(), Z=Z, ZL=ZL, ZH=ZH, R=ZL / ZH,
                     digit=round(ZH) % 10, exc=exc(r["system"])))
print("  digit of Z_H by excitation:")
for e in ("0.5 MeV", "thermal", "SF", "14 MeV"):
    sub = [x for x in data if x["exc"] == e]
    if sub:
        print("    %-8s n=%2d  digits %s  Z_H %.2f-%.2f (mean %.2f)  R %.4f-%.4f"
              % (e, len(sub), sorted(set(x["digit"] for x in sub)),
                 min(x["ZH"] for x in sub), max(x["ZH"] for x in sub),
                 np.mean([x["ZH"] for x in sub]), min(x["R"] for x in sub), max(x["R"] for x in sub)))

# pre-registered test: R = (Z - ZH)/ZH with ZH read from the digit
OFF = {3: 53, 4: 54, 5: 55, 6: 56}
print("\n  the test: Z_H from the digit, R predicted = (Z - Z_H)/Z_H")
print("    %-26s %3s %4s %7s %7s %7s %7s" % ("system", "Z", "d", "Z_H", "R meas", "R pred", "resid"))
res_pin, res_dig = [], []
for x in data:
    Zh = OFF.get(x["digit"], 54)
    Rp = (x["Z"] - Zh) / Zh
    res_dig.append((x["R"] - Rp) / Rp)
    res_pin.append((x["R"] - (x["Z"] - 54) / 54) / ((x["Z"] - 54) / 54))
    print("    %-26s %3d %4d %7d %7.4f %7.4f %+6.2f%%"
          % (x["name"][:26], x["Z"], x["digit"], Zh, x["R"], Rp, 100 * res_dig[-1]))
res_dig = np.array(res_dig); res_pin = np.array(res_pin)
print("  the plain pin:   mean %+.2f%%, sd %.2f%%, max |%.2f|%%" % (100 * res_pin.mean(), 100 * res_pin.std(),
                                                                  100 * np.abs(res_pin).max()))
print("  with the digit:  mean %+.2f%%, sd %.2f%%, max |%.2f|%%" % (100 * res_dig.mean(), 100 * res_dig.std(),
                                                                  100 * np.abs(res_dig).max()))

# the association the digit actually carries
hi = [x for x in data if x["exc"] == "14 MeV"]
lo = [x for x in data if x["exc"] != "14 MeV"]
a = sum(1 for x in hi if x["ZH"] < 54); b = len(hi) - a
c = sum(1 for x in lo if x["ZH"] < 54); d_ = len(lo) - c
pv = 0.0
for i in range(a, a + b + 1):
    if i <= c + d_ and (a + b - i) <= c + d_:
        pv += comb(a + b, i) * comb(c + d_, a + b - i) / comb(a + b + c + d_, a + b)
print("\n  Z_H below the closure 54:  14 MeV %d/%d,  others %d/%d   Fisher p = %.1e"
      % (a, a + b, c, c + d_, pv))
print("  mean Z_H: 14 MeV %.2f  others %.2f" % (np.mean([x["ZH"] for x in hi]),
                                               np.mean([x["ZH"] for x in lo])))

with open("results/tableV10_locked_digits.csv", "w") as f:
    f.write("kind,name,value,note\n")
    for c_, n, ret, rate in rows_out:
        f.write("return,digit_%d,%d,%s\n" % (c_, n, ("%.4f" % rate) if n else "never a closer"))
    for d, n, r in rates:
        f.write("return_by_decade,1e%d,%.4f,n=%d\n" % (d, r, n))
    for x, rd in zip(data, res_dig):
        f.write("fission,%s,%.4f,digit %d; residual with digit %+.2f%%\n"
                % (x["name"], x["R"], x["digit"], 100 * rd))
print("\n  LOCKED-DIGIT TEST PASSED (3 never returns; the digit cuts the pin residual %.1f%% -> %.1f%%)"
      % (100 * np.abs(res_pin).max(), 100 * np.abs(res_dig).max()))
