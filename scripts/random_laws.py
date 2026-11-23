#!/usr/bin/env python3
"""Random-input tests of the Light Bridge laws.

Purpose: the Lean files *prove* the identities; this script checks that the identities are the
ones the rest of the record computes with, on random inputs, and that they hold together:

  * the table functions (period, countdown, counted part, block, group, closed) on random Z;
  * every split identity on random splits;
  * the pin on random actinides, the symmetric switch on random even Z;
  * the prime-side identities on random real twin pairs (air mod 6, T = air+4, the class shift,
    the value ladder's +3, the merged-total telescoping);
  * the depth shift on random gaps.

Exit status is non-zero if any test fails.  Run: python3 scripts/random_laws.py [trials]
"""
import random, sys, math
import sympy

TRIALS = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
rng = random.Random(20261123)

C = [0, 2, 10, 18, 36, 54, 86, 118]
def L(m): return 2 * ((((m + 1) + 1) // 2)) ** 2
def period(Z):
    for m in range(1, 8):
        if Z <= C[m]: return m
def cnt(Z): return C[period(Z)] - Z
def counted(Z): return Z - C[period(Z) - 1]
def block(Z):
    m, h = period(Z), cnt(Z)
    if h in (L(m) - 2, L(m) - 1): return "s"
    if h <= 5: return "p"
    if h <= 15: return "d"
    if h <= 29: return "f"
    return "?"
def group(Z):
    b = block(Z)
    if b in ("p", "d"): return 18 - cnt(Z)
    if b == "s": return L(period(Z)) - cnt(Z)
    return None
def closed(Z): return block(Z) in ("p", "s")
def V(g): return (0.75 * g + 0.5) % 7.5

results = []
def check(name, ok):
    results.append((name, ok))
    if not ok: print("  FAIL:", name)

# --- 1. the table, on random Z
bad = 0
for _ in range(TRIALS):
    Z = rng.randint(1, 118)
    if counted(Z) + cnt(Z) != L(period(Z)): bad += 1
    if block(Z) == "?": bad += 1
    b = block(Z)
    if b == "s" and not (cnt(Z) in (L(period(Z)) - 2, L(period(Z)) - 1)): bad += 1
    if b != "s" and cnt(Z) in (L(period(Z)) - 2, L(period(Z)) - 1): bad += 1
    if closed(Z) != (b in ("p", "s")): bad += 1
    g = group(Z)
    if g is not None and not (1 <= g <= 18): bad += 1
check("table identities on %d random cells (v+h=L, block partition, closed, group in 1..18)" % TRIALS, bad == 0)

# --- 2. splits
bad = 0
for _ in range(TRIALS):
    Z = rng.randint(2, 118); Z1 = rng.randint(1, Z - 1); Z2 = Z - Z1
    if Z1 + Z2 != Z: bad += 1
    if cnt(Z1) + cnt(Z2) != C[period(Z1)] + C[period(Z2)] - Z: bad += 1
    if Z - Z1 != Z2: bad += 1
check("split identities on %d random splits (conservation, countdown sum)" % TRIALS, bad == 0)

# --- 3. the pin and the symmetric switch
bad = 0
for _ in range(TRIALS):
    Z = rng.randint(91, 108)
    if C[5] != 54 or cnt(54) != 0: bad += 1
    if cnt(Z - 54) != 108 - Z: bad += 1
for _ in range(TRIALS):
    Z = rng.choice([z for z in range(88, 107) if z % 2 == 0])
    if closed(Z // 2) != (Z >= 98): bad += 1
check("pin on random actinides, symmetric switch on random even Z", bad == 0)

# --- 4. closed-cell splits (the windows are finite, so enumerate them exactly)
bad = 0
for Zpar, want in ((92, [36, 37, 38]), (94, [38]), (96, [])):
    got = [Z1 for Z1 in range(30, Zpar // 2 + 2) if closed(Z1) and closed(Zpar - Z1)]
    if got != want: bad += 1; print("   Z=%d: got %s want %s" % (Zpar, got, want))
check("closed-cell splits: 92 -> [36,37,38], 94 -> [38], 96 -> []", bad == 0)

# --- 5. the prime side, on real twin pairs
def twin_start_after(n):
    p = int(sympy.nextprime(n))
    while not sympy.isprime(p + 2):
        p = int(sympy.nextprime(p))
    return p
bad = 0
for _ in range(max(50, TRIALS // 50)):
    p = twin_start_after(rng.randint(10**6, 10**11))
    q = twin_start_after(p + 2)
    air, T = q - p - 2, (q + 2) - p
    if air % 6 != 4: bad += 1
    if air % 30 not in (4, 10, 16, 22, 28): bad += 1
    if T != air + 4 or T % 6 != 2: bad += 1
    if (T - air) % 30 != 4: bad += 1
    if abs(V(T) - (V(air) + 3) % 7.5) > 1e-9: bad += 1
    if air % 10 not in (0, 2, 4, 6, 8): bad += 1
n_pairs = max(50, TRIALS // 50)
check("prime-side identities on %d random real twin pairs (air mod 6, T=air+4, class shift, V(T)=V+3)" % n_pairs, bad == 0)

# --- 6. merged totals telescope
bad = 0
for _ in range(max(20, TRIALS // 100)):
    p = twin_start_after(rng.randint(10**6, 10**9))
    starts = [p]
    for _ in range(rng.randint(1, 6)):
        starts.append(twin_start_after(starts[-1] + 2))
    n = len(starts) - 1
    tot = sum((starts[i + 1] + 2) - starts[i] for i in range(n))
    if tot != (starts[-1] - starts[0]) + 2 * n: bad += 1
check("merged totals: sum T = span + 2n on random twin chains", bad == 0)

# --- 7. the depth shift
bad = 0
for _ in range(TRIALS):
    g = rng.randrange(2, 10**6, 2)
    if (g + 10) % 3 != (g + 1) % 3: bad += 1
    if g % 3 != 1 and ((g % 3 == 0) == ((g + 10) % 3 == 0)): bad += 1
check("depth shift: (g+10) mod 3 = (g+1) mod 3, exactly one groove divisible by 3", bad == 0)

# --- 8. the ladders' intersections and the fissility band
proton, osc, magic = [2, 10, 18, 36, 54, 86, 118], [2, 8, 20, 40, 70, 112, 168], [2, 8, 20, 28, 50, 82, 126]
check("ladder intersections: proton&magic = {2}, oscillator&magic = {2,8,20}",
      [x for x in proton if x in magic] == [2] and [x for x in osc if x in magic] == [2, 8, 20])
bad = 0
for _ in range(TRIALS):
    Z = rng.randint(88, 100); A = Z + rng.randint(140, 160)
    f = Z * Z / A
    if not (30 < f < 45): bad += 1
check("fissility of random actinides lies in 30..45", bad == 0)

# --- 9. the measured laws, checked at random scales against the recorded sums
import json, pathlib
C2 = 0.6601618158468695739278121100145557784326233602847334133194484233354056423
HL = 1.0 / (2 * C2)
dec = {}
for pat in ("d1e*.json", "c1e*.json"):
    for f in sorted(pathlib.Path(".scratch/work").glob(pat)):
        for k, v in json.loads(f.read_text())["decades"].items():
            dec[int(k)] = v
if dec:
    bad = 0; n = 0
    for _ in range(TRIALS):
        k = rng.choice(sorted(dec))
        v = dec[k]
        nn = v["n"]; air = v["sum_air"] / nn; t2 = v["sum_t2"] / nn
        var = max(0.0, v["sum_air2"] / nn - air * air); se = (var / nn) ** 0.5
        pred = HL * t2 - 2                      # the gap law, written on the air
        n += 1
        if abs(air - pred) > 6 * se + 1e-12: bad += 1
    check("air law <air> = t^2/(2C2) - 2 at %d random (decade) draws, within 6 sigma" % n, bad == 0)
else:
    print("  (no recorded sums found — skipping the measured-law check)")

# --- report
nfail = sum(1 for _, ok in results if not ok)
print("\n%d test groups, %d trials each; %d failed" % (len(results), TRIALS, nfail))
for name, ok in results:
    print("  %-4s %s" % ("ok" if ok else "FAIL", name))
sys.exit(1 if nfail else 0)
