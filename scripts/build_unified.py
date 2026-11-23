#!/usr/bin/env python3
"""Build the unified development: LoopWall (root repo) + DiracTime + VOTKP + Bridge.

Compiles in dependency order with `lean -o`, because `lean` alone writes no object file.
A module is skipped when its `.olean` is newer than its source and than every dependency's.

    python3 scripts/build_unified.py [--force]

Exit status is non-zero if any module fails to elaborate.
"""
import os
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMP = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.M)

# module prefix -> directory holding its sources
TREES = {
    "LoopWall": "LoopWall",
    "DiracTime": "unified/DiracTime",
    "VOTKP": "unified/VOTKP",
    "Bridge": "unified/Bridge",
    "Found": "unified/Found",
    "PrimeGap": "unified/PrimeGap",
    "Unified": "unified",
    "Showcase": "unified",
}

# modules that are deliberately outside the unified root
EXCLUDE = {
    "DiracTime.UnitaryEntropy",  # needs Physlib, not on this VM
    "VOTKP",  # no such module; VOTKP is a namespace
}

LEAN_PATH = ".:unified:" + os.environ.get("LEAN_PATH", "")


def source_of(mod):
    head = mod.split(".")[0]
    d = TREES.get(head)
    if d is None:
        return None
    return os.path.join(ROOT, d, mod[len(head) + 1:].replace(".", "/") + ".lean") \
        if "." in mod else os.path.join(ROOT, d + ".lean")


def collect():
    mods = {}
    for d in ("LoopWall", "unified/DiracTime", "unified/VOTKP", "unified/Bridge", "unified/Found",
              "unified/PrimeGap"):
        full = os.path.join(ROOT, d)
        if not os.path.isdir(full):
            continue
        for name in sorted(os.listdir(full)):
            if not name.endswith(".lean"):
                continue
            path = os.path.join(full, name)
            head = "LoopWall" if d == "LoopWall" else os.path.basename(d)
            mod = f"{head}.{name[:-5]}"
            mods[mod] = path
    return mods


SYNC = {
    "unified/PrimeGap/CountFormulas.lean": "results/count-formulas.lean",
    "unified/PrimeGap/DigitRoles.lean": "results/digit-roles.lean",
}


def check_sync():
    """The prime-gap leg is a build copy; fail if it drifts from the working file."""
    bad = []
    for copy, original in SYNC.items():
        a, b = os.path.join(ROOT, copy), os.path.join(ROOT, original)
        if os.path.exists(b) and open(a, "rb").read() != open(b, "rb").read():
            bad.append(f"{copy} != {original}")
    if bad:
        raise SystemExit("prime-gap copy out of sync: " + "; ".join(bad))


# A declaration line, not a docstring line that happens to begin with "lemma".  The name must
# be followed by a binder, a type ascription, or the end of the line.
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(theorem|lemma)\s+([^\s:({[]+)\s*(?:[:({[]|$)", re.M)


def census():
    """Print the theorem/lemma count of each tree, and the total."""
    trees = {"LoopWall": "LoopWall", "DiracTime": "unified/DiracTime", "VOTKP": "unified/VOTKP",
             "PrimeGap": "unified/PrimeGap", "Bridge": "unified/Bridge", "Found": "unified/Found"}
    total = 0
    for name, d in trees.items():
        n = 0
        for f in sorted(os.listdir(os.path.join(ROOT, d))):
            if f.endswith(".lean"):
                with open(os.path.join(ROOT, d, f), encoding="utf-8") as fh:
                    n += len(DECL.findall(fh.read()))
        print(f"{name:10s} {n:5d}")
        total += n
    print(f"{'total':10s} {total:5d}")
    return total


def main():
    if "--count" in sys.argv:
        census()
        return 0
    check_sync()
    force = "--force" in sys.argv
    mods = collect()
    for extra in ("unified/Unified.lean",):
        p = os.path.join(ROOT, extra)
        if os.path.exists(p):
            mods["Unified"] = p
    deps = {}
    for mod, path in mods.items():
        with open(path, encoding="utf-8") as fh:
            deps[mod] = [m for m in IMP.findall(fh.read()) if m in mods]
    # topological order
    order, state = [], {}

    def visit(m, stack=()):
        if state.get(m) == 2:
            return
        if state.get(m) == 1:
            raise SystemExit(f"import cycle: {' -> '.join(stack + (m,))}")
        state[m] = 1
        for d in deps[m]:
            visit(d, stack + (m,))
        state[m] = 2
        order.append(m)

    for m in sorted(mods):
        visit(m)

    env = dict(os.environ, LEAN_PATH=LEAN_PATH)
    failed, built, skipped = [], 0, 0
    t0 = time.time()
    for mod in order:
        if mod in EXCLUDE:
            continue
        path = mods[mod]
        olean = path[:-5] + ".olean"
        dep_oleans = [mods[d][:-5] + ".olean" for d in deps[mod] if d not in EXCLUDE]
        fresh = os.path.exists(olean) and os.path.getmtime(olean) >= os.path.getmtime(path) \
            and all(os.path.exists(o) and os.path.getmtime(olean) >= os.path.getmtime(o)
                    for o in dep_oleans)
        if fresh and not force:
            skipped += 1
            continue
        r = subprocess.run(["lean", "-o", olean, path], cwd=ROOT, env=env,
                           capture_output=True, text=True)
        if r.returncode != 0:
            failed.append((mod, r.stdout + r.stderr))
            print(f"FAIL {mod}")
            print("\n".join((r.stdout + r.stderr).splitlines()[:12]))
        else:
            built += 1
            print(f"ok   {mod}")
    dt = time.time() - t0
    print(f"\n{built} built, {skipped} up to date, {len(failed)} failed, {dt:.1f}s")
    if failed:
        print("failed:", ", ".join(m for m, _ in failed))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
