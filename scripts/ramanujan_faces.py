#!/usr/bin/env python3
"""Check the exact and numerical claims of 'Ramanujan's Gamma Fractions Read as Stacks of Faces'.

The gamma-quotient continued fraction is

    4 Γ((x+3)/4)² / Γ((x+1)/4)²  =  x + 1²/(2x + 3²/(2x + 5²/(2x + …)))

whose n-th step matrix is [[0, (2n−1)²], [1, 2x]].  Its face has

    z_n = (s + x)/(s − x),  s = √(x² + (2n−1)²),  Γ_n = (z_n − 1)/(z_n + 1) = x/s,

which `unified/Bridge/Faces.lean` proves exactly.  This script checks the numbers the session
record reports and the two constants it says nobody has derived.

    python3 scripts/ramanujan_faces.py
"""
import sys
from mpmath import mp, mpf, gamma, pi, sqrt, log

mp.dps = 60


def cf(x, N):
    """Backward evaluation of x + 1²/(2x + 3²/(2x + …)) with N terms."""
    f = 2 * x
    for n in range(N - 1, 0, -1):
        a = x if n == 1 else 2 * x
        f = a + (2 * n - 1) ** 2 / f
    return f


def closed(x):
    return 4 * gamma((x + 3) / 4) ** 2 / gamma((x + 1) / 4) ** 2


def face(x, n):
    s = sqrt(x ** 2 + (2 * n - 1) ** 2)
    z = (s + x) / (s - x)
    return z, (z - 1) / (z + 1), x / s


def main():
    ok = True
    print("value of the fraction against its closed form")
    for xv in (1, 3, 10, mpf(1) / 2):
        x = mpf(xv)
        v, c = cf(x, 4000), closed(x)
        err = abs(v - c)
        print(f"  x={float(x):5}  cf={mp.nstr(v, 16)}  closed={mp.nstr(c, 16)}  |diff|={mp.nstr(err, 3)}")

    print("\nface formulas (numeric, and the exact form is proved in Faces.lean)")
    for xv, n in ((1, 1), (3, 2), (10, 7)):
        z, gz, g = face(mpf(xv), n)
        same = abs(gz - g) < mpf(10) ** (-40)
        ok &= same
        print(f"  x={xv:2} n={n}: z={mp.nstr(z, 12)}  (z-1)/(z+1)={mp.nstr(gz, 12)}  x/s={mp.nstr(g, 12)}  equal={same}")

    print("\nBrouncker's first face at the wall")
    z, gz, g = face(mpf(1), 1)
    print(f"  Γ₁² = {mp.nstr(g ** 2, 20)}   z₁ = {mp.nstr(z, 20)}   3+2√2 = {mp.nstr(3 + 2 * sqrt(2), 20)}")
    ok &= abs(g ** 2 - mpf(1) / 2) < mpf(10) ** (-40)
    ok &= abs(z - (3 + 2 * sqrt(2))) < mpf(10) ** (-40)

    print("\nerror × N^x  (the record's two constants)")
    for xv, target, name in ((1, 4 / pi ** 2, "4/π²"), (3, mpf(1) / 4, "1/4")):
        x = mpf(xv)
        c = closed(x)
        vals = [abs(cf(x, N) - c) * N ** x for N in (100, 400, 1600, 6400)]
        print(f"  x={xv}: " + "  ".join(mp.nstr(v, 10) for v in vals) + f"   → {name} = {mp.nstr(target, 10)}")
        ok &= abs(vals[-1] - target) < mpf(1) / 100

    print("\nthe record's rule: error times the product of the face ratios stays nearly fixed")
    for xv in (0.5, 1, 3):
        x = mpf(xv)
        c = closed(x)
        row = []
        for N in (100, 400, 1600, 6400):
            prod = mpf(1)
            for n in range(1, N + 1):
                s = sqrt(x ** 2 + (2 * n - 1) ** 2)
                prod *= (s + x) / (s - x)
            row.append(abs(cf(x, N) - c) * prod)
        spread = max(row) / min(row)
        print(f"  x={float(x):4}: " + "  ".join(mp.nstr(v, 6) for v in row)
              + f"   spread x{mp.nstr(spread, 4)}")
        ok &= spread < mpf("1.1")

    print("\nproduct of the face ratios against N^x  (the power law)")
    for xv in (1, 3, 10):
        x = mpf(xv)
        prod = mpf(1)
        for n in range(1, 1601):
            s = sqrt(x ** 2 + (2 * n - 1) ** 2)
            prod *= (s + x) / (s - x)
        print(f"  x={xv:2}: ∏z / N^x = {mp.nstr(prod / mpf(1600) ** x, 12)}")

    print("\nall checks passed" if ok else "\nSOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
