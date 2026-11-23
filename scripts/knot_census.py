#!/usr/bin/env python3
"""Reproduce the knot census of Section 6 from versioned inputs.

    python3 scripts/knot_census.py

Inputs, both shipped:

  knots/data/knotinfo_amphichiral_2026.11.2.csv   the 78 amphicheiral prime knots through 13
      crossings, read from KnotInfo release 2026.11.2 (symmetry_type containing "amphicheiral"),
      with the symmetry type of each.  Regenerate with `make_snapshot()` if the release moves.

  knots/data/census_through_13.csv   the VOTKP census: one row per prime knot, with the
      `theta_is_zero` and `amphichiral` flags.

Exit status is non-zero if any published claim fails.  Nothing is sent anywhere: the
comparison is local.
"""
import csv
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SNAP = os.path.join(ROOT, "knots/data/knotinfo_amphichiral_2026.11.2.csv")
CENSUS = os.path.join(ROOT, "knots/data/census_through_13.csv")

FAIL = []


def check(label, got, want):
    ok = got == want
    print(f"{'ok  ' if ok else 'FAIL'} {label}: {got}  (published {want})")
    if not ok:
        FAIL.append(label)


def truth(v):
    return str(v).strip().lower() in ("true", "1", "yes", "t")


def main():
    snap = list(csv.DictReader(open(SNAP)))
    census = list(csv.DictReader(open(CENSUS)))

    check("prime knots through 13 crossings", len(census), 12965)
    check("amphicheiral knots (KnotInfo snapshot)", len(snap), 78)
    types = {t: sum(1 for r in snap if r["symmetry_type"] == t) for t in
             ("negativeamphicheiral", "fullyamphicheiral", "positiveamphicheiral")}
    check("  ... negative", types["negativeamphicheiral"], 47)
    check("  ... fully", types["fullyamphicheiral"], 30)
    check("  ... positive", types["positiveamphicheiral"], 1)
    check("  ... at 11 crossings", sum(1 for r in snap if r["crossings"] == "11"), 0)
    check("  ... at 13 crossings", sum(1 for r in snap if r["crossings"] == "13"), 0)

    ki = {r["knot"] for r in snap}
    amph = {r["knot"] for r in census if truth(r["amphichiral"])}
    thz = {r["knot"] for r in census if truth(r["theta_is_zero"])}
    check("census amphichiral flag", len(amph), 78)
    check("census theta-zero set", len(thz), 78)
    check("KnotInfo names == census theta-zero names", ki == thz, True)
    check("census amphichiral == census theta-zero", amph == thz, True)

    if FAIL:
        print(f"\n{len(FAIL)} claim(s) failed: {', '.join(FAIL)}")
        return 1
    print("\nall knot census claims reproduced")
    return 0


def make_snapshot():
    """Refresh the snapshot from the KnotInfo skill (network, and a 17 MB download)."""
    import re
    import subprocess
    rows = []
    for n in range(3, 14):
        out = subprocess.run(
            ["python3", os.path.join(ROOT, ".skill/knotinfo-query/scripts/knotinfo.py"), "find",
             "symmetry_type~amphicheiral", f"crossing_number={n}", "--all",
             "--columns", "symmetry_type"],
            capture_output=True, text=True, check=True).stdout
        for line in out.splitlines():
            m = re.match(r"^(\S+)\s+symmetry_type=(\S+)", line)
            if m:
                rows.append({"knot": m.group(1), "crossings": n, "symmetry_type": m.group(2)})
    rows.sort(key=lambda r: (r["crossings"], r["knot"]))
    with open(SNAP, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["knot", "crossings", "symmetry_type"])
        w.writeheader()
        w.writerows(rows)
    print(f"wrote {len(rows)} rows to {SNAP}")


if __name__ == "__main__":
    if "--refresh" in sys.argv:
        make_snapshot()
    else:
        sys.exit(main())
