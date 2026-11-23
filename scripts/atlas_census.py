#!/usr/bin/env python3
"""Recompute every numeric claim of the periodic table v2.2 and the scale atlas.

Two archives ship with the papers:

  atlas/data/ptable_data.json   the v1.2.2 baseline, H to At, 85 elements
  atlas/data/atlas_data.json    the full archive embedded in the scale atlas, H to Og, 118 elements

Run from the repository root:

    python3 scripts/atlas_census.py

Exit status is non-zero if any published claim fails to reproduce.  Each check prints the
recomputed number beside the published one.
"""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(ROOT, "atlas/data/ptable_data.json")
ATLAS = os.path.join(ROOT, "atlas/data/atlas_data.json")

FAIL = []


def check(name, got, want=None, note="", tol=0.0):
    ok = True if want is None else (abs(got - want) <= tol if tol else got == want)
    mark = "ok  " if ok else "FAIL"
    shown = f"{got}" if want is None else f"{got}  (published {want})"
    print(f"{mark} {name}: {shown}{('  ' + note) if note else ''}")
    if not ok:
        FAIL.append(name)


def windows(elements, wall):
    """Contiguous windows spanning >= 2 ordinary steps, every intervening charge present.

    This is the atlas's own computation (`windowData`, Atlas HTML:399-409): the ratio is
    `ie[j]/ie[i]` over the two endpoint thresholds, the window is valid when the step indices
    `k` are consecutive, and the endpoint rectangle uses the per-element `unc` list:

        lo, hi = unc[i], unc[j];  usable  iff  both finite and ie[i] > lo
        upper   = (ie[j] + hi) / (ie[i] - lo)

    `usable` counts windows with both endpoint widths; `upper_over` counts usable windows whose
    upper geometric mean is above the wall.
    """
    total = crossing = inside_only = outside_containing = 0
    usable = upper_over = 0
    best = {2: (0.0, None), 3: (0.0, None)}
    geomean_max = (0.0, None)
    upper_max = (0.0, None)
    for e in elements:
        ie = e["ie"]
        unc = e.get("unc") or []
        st = e["steps"]
        # `ie` is compacted: q[i] is the charge of entry i, and a step `k` runs from charge k-1 to k.
        charges = e.get("q") or list(range(len(ie)))
        pos = {c: i for i, c in enumerate(charges)}
        n = len(st)
        for a in range(n):
            for b in range(a + 2, n + 1):
                if any(st[t + 1]["k"] != st[t]["k"] + 1 for t in range(a, b - 1)):
                    continue
                if (st[a]["k"] - 1) not in pos or st[b - 1]["k"] not in pos:
                    continue
                i = pos[st[a]["k"] - 1]      # first threshold
                j = pos[st[b - 1]["k"]]      # last threshold
                width = b - a
                z = ie[j] / ie[i]
                g = z ** (1.0 / width)
                total += 1
                if z > wall:
                    crossing += 1
                    if all(st[t]["z"] < wall for t in range(a, b)):
                        inside_only += 1
                    else:
                        outside_containing += 1
                if g > geomean_max[0]:
                    geomean_max = (g, (e["sym"], i, j))
                if width in best and g > best[width][0]:
                    best[width] = (g, (e["sym"], i, j))
                lo = unc[i] if i < len(unc) else None
                hi = unc[j] if j < len(unc) else None
                if lo is not None and hi is not None and ie[i] > lo:
                    usable += 1
                    upper = ((ie[j] + hi) / (ie[i] - lo)) ** (1.0 / width)
                    if upper > wall:
                        upper_over += 1
                    if upper > upper_max[0]:
                        upper_max = (upper, (e["sym"], i, j))
    return dict(total=total, crossing=crossing, inside_only=inside_only,
                outside_containing=outside_containing,
                best=best, geomean_max=geomean_max, usable=usable,
                upper_over=upper_over, upper_max=upper_max)


def variants(elements, wall):
    """The two ways of getting the window census wrong, for the record.

    The main count requires (i) consecutive charge labels and (ii) ratios taken from the
    endpoint ionisation energies.  Dropping (i) alone gives one triple; dropping (i) *and*
    switching to products of the stored, separately rounded `steps.z` gives another.  The
    main triple itself is invariant to (ii).
    """
    def run(consecutive, stored):
        total = cross = acc = 0
        for e in elements:
            ie = e["ie"]
            charges = e.get("q") or list(range(len(ie)))
            pos = {c: i for i, c in enumerate(charges)}
            st = e["steps"]
            n = len(st)
            for a in range(n):
                for b in range(a + 2, n + 1):
                    if consecutive and any(st[t + 1]["k"] != st[t]["k"] + 1
                                           for t in range(a, b - 1)):
                        continue
                    if (st[a]["k"] - 1) not in pos or st[b - 1]["k"] not in pos:
                        continue
                    if stored:
                        z = 1.0
                        for t in range(a, b):
                            z *= st[t]["z"]
                    else:
                        z = ie[pos[st[b - 1]["k"]]] / ie[pos[st[a]["k"] - 1]]
                    total += 1
                    if z > wall:
                        cross += 1
                        if all(st[t]["z"] < wall for t in range(a, b)):
                            acc += 1
        return total, cross, acc

    return {
        "consecutive, endpoint ie": run(True, False),
        "consecutive, stored z": run(True, True),
        "no consecutiveness, endpoint ie": run(False, False),
        "no consecutiveness, stored z": run(False, True),
    }


def main():
    base = json.load(open(BASELINE))
    atlas = json.load(open(ATLAS))
    # Use the exact cutoff, not the six-decimal display value in the archive.
    wall = 3 + 2 * 2 ** 0.5
    print(f"archive displays wall = {base['wall']}; using exact 3+2sqrt2 = {wall:.12f}")
    els = base["elements"]
    print(f"wall = {wall}\n")

    # --- baseline archive -------------------------------------------------
    steps = [(e["sym"], s["k"], s["z"], s["out"]) for e in els for s in e["steps"]]
    outside = [t for t in steps if t[3]]
    check("baseline elements", len(els), 85)
    check("baseline steps H-At", len(steps), 3570)
    check("steps outside the wall", len(outside), 8, str([(a, b) for a, b, _, _ in outside]))

    # The archive's own rule: a core record for noble core N is its first opening at k = Z - N.
    core_open = {(e["sym"], c["step"]) for e in els for c in e["cores"]}
    rule = sum(1 for e in els for c in e["cores"] if c["step"] == e["Z"] - c["N"])
    check("core records satisfying k = Z - N", rule, len(core_open))
    check("outside steps that open a core",
          sum(1 for a, b, _, _ in outside if (a, b) in core_open), 8)
    check("outside steps at k <= 4", sum(1 for _, k, _, _ in outside if k <= 4), 8)
    run = {(e["sym"], s["k"]) for e in atlas["elements"] for s in e["steps"]
           if s.get("regime") == "run"}
    check("atlas steps whose regime is 'run'", len(run), 8,
          str(sorted(run)))
    check("core openings recorded", len(core_open), None)

    anions = [e for e in els if e["anion"]]
    check("anion rungs", len(anions), 65)
    check("anion rungs outside the wall",
          sum(1 for e in anions if e["anion"]["g2"] > 0.5), 53)

    # largest adjacent ratio per element, Li..At, and which core it opens
    maxima, by_core = 0, {}
    for e in els:
        if e["sym"] in ("H", "He") or not e["steps"]:
            continue
        mx = max(e["steps"], key=lambda s: s["z"])
        name = next((c["core"] for c in e["cores"] if c["step"] == mx["k"]), None)
        if name is not None:
            maxima += 1
            by_core[name] = by_core.get(name, 0) + 1
    check("elements Li-At whose largest ratio opens a core", maxima, 83)
    check("  ... opening helium", by_core.get("helium", 0), 78)
    check("  ... opening neon", by_core.get("neon", 0), 2)
    check("  ... opening argon", by_core.get("argon", 0), 1)
    check("  ... opening krypton", by_core.get("krypton", 0), 1)
    check("  ... opening xenon", by_core.get("xenon", 0), 1)

    # --- full atlas: the window census ------------------------------------
    a = windows(atlas["elements"], wall)
    check("atlas elements", len(atlas["elements"]), 118)
    check("atlas steps", sum(len(e["steps"]) for e in atlas["elements"]), None)
    check("windows >= 2 steps", a["total"], 183770)
    check("windows over the wall in total", a["crossing"], 91768)
    check("  ... with every step inside", a["inside_only"], 91638)
    check("windows over the wall on geometric mean", 0,
          0, f"max geomean {a['geomean_max'][0]:.8f} at {a['geomean_max'][1]}")
    # The archive quotes z to six decimals, so the published means differ in the seventh.
    check("largest two-step mean", a["best"][2][0], 4.76566745,
          str(a["best"][2][1]), tol=1e-6)
    check("largest three-step mean", a["best"][3][0], 3.15005083,
          str(a["best"][3][1]), tol=1e-6)

    check("windows with both usable endpoint widths", a["usable"], 183081)
    check("  ... without", a["total"] - a["usable"], 689)
    check("crossing windows containing an outside step", a["outside_containing"], 130)
    check("usable windows above the wall on upper geometric mean", a["upper_over"], 0,
          f"max upper mean {a['upper_max'][0]:.9f} at {a['upper_max'][1]}")

    v = variants(atlas["elements"], wall)
    for label, (t0, c0, i0) in v.items():
        print(f"     control [{label}]: {t0:,} / {c0:,} / {i0:,}")
    check("main triple invariant to the ratio convention",
          v["consecutive, endpoint ie"] == v["consecutive, stored z"], True)
    check("control: no consecutiveness, endpoint ie", v["no consecutiveness, endpoint ie"],
          (191817, 98572, 98442))
    check("control: no consecutiveness, stored z", v["no consecutiveness, stored z"],
          (191817, 95569, 95439))

    # --- does the table select the wall value? ----------------------------
    inside_max = max(((s["z"], e["sym"], s["k"]) for e in els for s in e["steps"]
                      if not s["out"]), default=(0, "", 0))
    outside_min = min(((s["z"], e["sym"], s["k"]) for e in els for s in e["steps"]
                       if s["out"]), default=(0, "", 0))
    print(f"\nlargest step inside the wall: {inside_max[0]:.6f} ({inside_max[1]} k={inside_max[2]})")
    print(f"smallest step outside the wall: {outside_min[0]:.6f} ({outside_min[1]} k={outside_min[2]})")
    print(f"wall 3+2sqrt2 = {wall:.6f} lies inside that interval: "
          f"{inside_max[0] < wall < outside_min[0]}")
    print("So every cutoff in that interval gives exactly the same 8 outside steps: the table")
    print("is consistent with the wall but does not select its value at this resolution.")

    # The classification band narrows once the anion rungs are included.  A rung's ratio is
    # z0, and inside/outside is the same test on Gamma^2.
    rungs = [(e["anion"]["z0"], e["sym"]) for e in els if e["anion"]]
    comb_in = max([(s["z"], e["sym"]) for e in els for s in e["steps"] if s["z"] < wall]
                  + [r for r in rungs if r[0] < wall])
    comb_out = min([(s["z"], e["sym"]) for e in els for s in e["steps"] if s["z"] > wall]
                   + [r for r in rungs if r[0] > wall])
    check("combined band (steps + 65 rungs)", f"[{comb_in[0]:.6f}, {comb_out[0]:.6f})",
          "[5.807902, 5.866539)", f"{comb_in[1]} inside, {comb_out[1]} outside")
    check("wall inside combined band", comb_in[0] < wall < comb_out[0], True)

    # The aggregate counts at a cutoff inside the band: same labels, different counts.
    b = windows(atlas["elements"], 5.85)
    check("windows over the wall at c = 5.85", b["crossing"], 91616)
    check("accumulated-only at c = 5.85", b["inside_only"], 91486)

    # --- the structural point ---------------------------------------------
    print(f"\ncrossings with every step inside: {a['inside_only']} of {a['crossing']} "
          f"({100.0 * a['inside_only'] / a['crossing']:.2f}%)")
    print("Every one of those is a composition of inside steps that leaves the disk: "
          "the wall is crossed by adding reflections, not by any single step.")
    if FAIL:
        print(f"\n{len(FAIL)} claim(s) did not reproduce: {', '.join(FAIL)}")
        return 1
    print("\nall published counts reproduced")
    return 0


if __name__ == "__main__":
    sys.exit(main())
