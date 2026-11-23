#!/usr/bin/env python3
"""The ladder fits reported in the note, computed from data/H_to_At_thresholds.csv.

Two rival one-parameter laws for the peel reflection of an element,
Gamma_k = (z_k - 1)/(z_k + 1) with z_k = IE(k+1)/IE(k):

  * the framework's clock with a linear phase, Gamma_k = tanh((p + q k)/2) -- which is the same
    model as a geometric ladder, because artanh(Gamma) = (1/2) log z, so the least-squares fit is
    taken in that coordinate and the score is computed on Gamma;
  * Gamma_k = A / k, fitted through the origin and scored on Gamma.

Both are scored on the same response, which is the only way the medians are comparable.  The
script also reports the log-scale score of the same geometric fit (not comparable with the other
two, and reported separately for that reason), the pooled constant of z_k = 1 + c/k, and the
exponent of a direct log-log fit of IE against k, which is a different summary.

Run: python3 scripts/ladder_fit.py
"""
import csv, math, pathlib, statistics

ROOT = pathlib.Path(__file__).resolve().parents[1]


def ladders():
    out = {}
    for row in csv.DictReader((ROOT / "data" / "H_to_At_thresholds.csv").open()):
        if row["kind"] == "IE":
            out.setdefault(row["symbol"], []).append((int(row["k"]), float(row["energy_eV"])))
    for v in out.values():
        v.sort()
    return out


def ols(xs, ys):
    n = len(ys); mx = sum(xs) / n; my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    b = sxy / sxx
    return my - b * mx, b


def r2(xs, ys, f):
    my = sum(ys) / len(ys)
    ss = sum((y - my) ** 2 for y in ys)
    res = sum((y - f(x)) ** 2 for x, y in zip(xs, ys))
    return 1 - res / ss if ss > 0 else float("nan")


def main():
    lad = ladders()
    for rule in (2, 4, 6):
        clock, hyper, logz = [], [], []
        for sym, v in lad.items():
            steps = [(k, e2 / e1) for (k, e1), (_, e2) in zip(v, v[1:])]
            if len(steps) < rule:
                continue
            ks = [k for k, _ in steps]
            gam = [(z - 1) / (z + 1) for _, z in steps]
            logs = [math.log(z) for _, z in steps]
            p, q = ols(ks, [l / 2 for l in logs])
            clock.append(r2(ks, gam, lambda k: math.tanh(p + q * k)))
            logz.append(r2(ks, logs, lambda k: 2 * (p + q * k)))
            a = sum((1 / k) * g for k, g in zip(ks, gam)) / sum((1 / k) ** 2 for k in ks)
            hyper.append(r2(ks, gam, lambda k: a / k))
        print(f"ladders with >= {rule} steps: n = {len(clock)}")
        print(f"  clock tanh((p+qk)/2), scored on Gamma : median R^2 = {statistics.median(clock):.4f}")
        print(f"  hyperbola A/k, scored on Gamma        : median R^2 = {statistics.median(hyper):.4f}")
        print(f"  same clock scored on log z (not comparable): {statistics.median(logz):.4f}")

    cs, exps = [], []
    for sym, v in lad.items():
        steps = [(k, e2 / e1) for (k, e1), (_, e2) in zip(v, v[1:])]
        cs += [(k, (z - 1) * k) for k, z in steps if k >= 2]
        if len(v) >= 6:
            a, b = ols([math.log(k) for k, _ in v], [math.log(e) for _, e in v])
            exps.append(b)
    print(f"pooled (z_k - 1) k over k >= 2: n = {len(cs)}, median {statistics.median([c for _, c in cs]):.2f}")
    print(f"direct log-log fit log IE = a + b log k: median exponent {statistics.median(exps):.2f}")


if __name__ == "__main__":
    main()
