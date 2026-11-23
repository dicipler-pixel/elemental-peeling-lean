#!/usr/bin/env python3
"""Keep the paper's numbers honest: every figure quoted in ONE_BODY.txt must still be the
figure the code produces.

    python3 scripts/check_paper_numbers.py

It recomputes the archive census and the Ramanujan checks, formats the values the paper
quotes, and looks for each one in the text.  A missing string means the prose has drifted
from the computation -- either the data changed or the sentence is wrong -- and the script
says which.  Exit status is non-zero if any quoted figure is not found.
"""
import importlib.util
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAPERS = [os.path.join(ROOT, "paper/ONE_BODY.txt"),
          os.path.join(ROOT, "paper/ONE_BODY_SUBMISSION.txt"),
          os.path.join(ROOT, "paper/one-body.tex")]


def normalise(text):
    r"""Accept the LaTeX spellings of the same figure: 3{,}570 and 3\,570 both mean 3,570."""
    return text.replace("{,}", ",").replace("\\,", "").replace("$", "")


def load_census():
    spec = importlib.util.spec_from_file_location("ac", os.path.join(ROOT, "scripts/atlas_census.py"))
    ac = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ac)
    return ac


def main():
    papers = {p: normalise(open(p, encoding="utf-8").read())
              for p in PAPERS if os.path.exists(p)}
    ac = load_census()
    atlas = json.load(open(os.path.join(ROOT, "atlas/data/atlas_data.json")))
    base = json.load(open(os.path.join(ROOT, "atlas/data/ptable_data.json")))
    wall = 3 + 2 * 2 ** 0.5

    a = ac.windows(atlas["elements"], wall)
    els = base["elements"]
    steps = [s for e in els for s in e["steps"]]
    outside = [s for s in steps if s["z"] > wall]
    anions = [e["anion"] for e in els if e["anion"]]

    want = {
        "baseline steps": f"{len(steps):,}",
        "steps outside": f"{len(outside):,}",
        "anion rungs": f"{len(anions)}",
        "rungs outside": f"{sum(1 for a0 in anions if a0['g2'] > 0.5)}",
        "full-archive steps": f"{sum(len(e['steps']) for e in atlas['elements']):,}",
        "windows": f"{a['total']:,}",
        "windows over the wall": f"{a['crossing']:,}",
        "windows with every step inside": f"{a['inside_only']:,}",
        "usable windows": f"{a['usable']:,}",
        "missing-width windows": f"{a['total'] - a['usable']:,}",
        "largest two-step mean": f"{a['best'][2][0]:.8f}",
        "largest three-step mean": f"{a['best'][3][0]:.8f}",
        "largest step inside": f"{max(s['z'] for s in steps if s['z'] <= wall):.6f}",
        "smallest step outside": f"{min(s['z'] for s in outside):.6f}",
        "windows at c = 5.85 (accumulated)": f"{ac.windows(atlas['elements'], 5.85)['inside_only']:,}",
    }

    missing = []
    for label, value in want.items():
        absent = [os.path.basename(p) for p, t in papers.items() if value not in t]
        if absent:
            missing.append((label, value, absent))
        print(f"{'ok  ' if not absent else 'MISS'} {label}: {value}"
              + (f"   (absent from {', '.join(absent)})" if absent else ""))

    if missing:
        print("\nthe paper does not quote the current figures:")
        for label, value, absent in missing:
            print(f"  {label}: expected {value} in {', '.join(absent)}")
        return 1
    print("\nevery figure quoted in the papers matches the computation")
    return 0


if __name__ == "__main__":
    sys.exit(main())
