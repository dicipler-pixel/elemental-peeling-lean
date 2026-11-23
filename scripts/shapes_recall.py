#!/usr/bin/env python3
"""Reproduce the shape/column nearest-neighbour scores of Section 5.4.

    python3 scripts/shapes_recall.py

Reads `atlas/data/atlas_data.json` (byte-identical to the archive embedded in the periodic
table, verified against it) and applies the four distances exactly as the table's JavaScript
defines them.  The distance definitions are transliterated from the table's own code; the
algorithmic reading was established in the referee round; its summary is in
`atlas/README.md`.

Score: for each element, take its first eight adjacent IE ratios, build the shape's
features, find the nearest *other* element by that shape's distance, and count a hit when
the two share a column.  Leave-one-out, first minimum wins, over the 77 elements with at
least nine ionisation energies (F to At).

Exit status is non-zero if a published score fails.
"""
import json
import math
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "atlas/data/atlas_data.json")
K = 8


def nearest_scores(elements, features, distance):
    hits = 0
    for i, e in enumerate(elements):
        best, best_j = 1e99, -1
        for j in range(len(elements)):
            if j == i:
                continue
            d = distance(i, j, features)
            if d < best:
                best, best_j = d, j
        hits += elements[best_j]["col"] == e["col"]
    return hits


def main():
    archive = json.load(open(DATA))
    elements = [e for e in archive["elements"]
                if not e.get("heavy") and len(e["ie"]) >= K + 1 and e.get("col")]
    n = len(elements)
    print(f"archive elements {len(archive['elements'])}; eligible {n}")
    if n != 77:
        print(f"FAIL eligible sample is {n}, published 77")
        return 1

    z = [[e["ie"][j + 1] / e["ie"][j] for j in range(K)] for e in elements]
    g = [[(v - 1) / (v + 1) for v in row] for row in z]
    L = [[0.5 * math.log(v) for v in row] for row in z]
    LL = [[math.log(math.log(v)) for v in row] for row in z]

    def circle(i, j, _):
        x = [v / math.sqrt(K) * 0.999 for v in g[i]]
        y = [v / math.sqrt(K) * 0.999 for v in g[j]]
        d2 = sum((a - b) ** 2 for a, b in zip(x, y))
        nx, ny = 1 - sum(a * a for a in x), 1 - sum(b * b for b in y)
        return math.acosh(1 + 2 * d2 / (nx * ny))

    def diamond(i, j, _):
        return sum(abs(a - b) for a, b in zip(L[i], L[j]))

    def cube(i, j, _):
        hi, lo = -1e9, 1e9
        for q in range(K):
            for s in (1, -1):
                r = math.log(1 - s * g[j][q]) - math.log(1 - s * g[i][q])
                hi, lo = max(hi, r), min(lo, r)
        return 0.5 * (hi - lo)

    def simplex(i, j, _):
        d = [LL[j][q] - LL[i][q] for q in range(K)]
        return max(d) - min(d)

    want = {"circle": 53, "diamond": 52, "cube": 48, "simplex": 60}
    fail = []
    got = {}
    for name, dist in (("circle", circle), ("diamond", diamond), ("cube", cube), ("simplex", simplex)):
        h = nearest_scores(elements, z, dist)
        got[name] = h
        ok = h == want[name]
        print(f"{'ok  ' if ok else 'FAIL'} {name}: {h}/{n}  (published {want[name]}/{n})")
        if not ok:
            fail.append(name)

    raw = [e["ie"][:K] for e in elements]
    l2 = nearest_scores(elements, raw, lambda i, j, x: math.dist(x[i], x[j]))
    l1 = nearest_scores(elements, raw, lambda i, j, x: sum(abs(a - b) for a, b in zip(x[i], x[j])))
    print(f"ok   raw energies, L2: {l2}/{n}   L1: {l1}/{n}  (published 4/{n})")
    if l2 != 4 or l1 != 4:
        fail.append("raw")

    chance = sum(sum(e["col"] == f["col"] for f in elements if f is not e) for e in elements)
    chance /= n * (n - 1)
    print(f"ok   uniform chance over the other {n-1}: {chance:.12f}  (published 0.044429254956)")
    print(f"ok   simplex - circle: {got['simplex'] - got['circle']}/{n}")

    if fail:
        print(f"\n{len(fail)} score(s) failed: {', '.join(fail)}")
        return 1
    print("\nall shape scores reproduced")
    return 0


if __name__ == "__main__":
    sys.exit(main())
