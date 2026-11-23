#!/usr/bin/env python3
"""Isolating a segment's class from its digit sequences.

Two sequences live inside a segment:

  * the **gap end digits** — `2` for each pair, and the air's digit `4,0,6,2,8` for each merge;
  * the **prime end digits** — `1,3,7,9` down the primes of the segment.

The claim to test: the class of the segment (its total mod 30) is recoverable from the gap end digits
alone. It should be, and for an exact reason: 30 = lcm(6,10), so a gap that is 4 mod 6 is *fixed* mod 30
by its last digit (`air_class_of_digit` in results/digit-roles.lean). The class is then

    class(T) = (2k + sum of the interior gaps' classes) mod 30,

with 2 per pair (the span of k pairs is 2k + the internal airs). The prime end digits are weaker: a prime's digit carries two classes (one per ladder),
except inside the twin starts where the three live digits carry one class each.

Checks: 0 exceptions on every internal air, every segment, and every distinct digit sequence. Writes
results/tableV5_class_from_digits.csv.

Run: python3 scripts/class_from_digits.py [LIM]
"""
import sys, math
import numpy as np
from collections import Counter, defaultdict

LIM = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 9
CLASS_OF_DIGIT = {4: 4, 0: 10, 6: 16, 2: 22, 8: 28}

sv = np.ones(LIM + 8, dtype=bool)
sv[:2] = False
for i in range(2, int((LIM + 6) ** 0.5) + 1):
    if sv[i]:
        sv[i * i::i] = False
pr = np.nonzero(sv[:LIM + 3])[0].astype(np.int64)
ts = pr[sv[pr + 2]]
ts = ts[ts <= LIM]
air = np.diff(ts) - 2
gi = np.searchsorted(pr, ts)
merged = np.diff(gi) == 2

# --- 1. every internal air: its digit fixes its class
internal = air[merged]
dig = internal % 10
cls = np.array([CLASS_OF_DIGIT[int(d)] for d in dig])
print("to 1e%d: %d internal airs" % (round(math.log10(LIM)), internal.size))
bad1 = int(np.count_nonzero((internal % 30) != cls))
print("  air %% 30 == class(digit):  %d exceptions" % bad1)
print("  digit shares: %s" % {int(d): int((dig == d).sum()) for d in sorted(set(dig.tolist()))})

# --- 2. every segment: class from the digit sequence vs class from the endpoints
seg = np.zeros(ts.size, dtype=np.int64)
seg[1:] = np.cumsum(~merged)
bounds = np.searchsorted(seg, np.arange(seg[-1] + 2))
# class by digits: for each segment, 4k + sum of the internal classes
# build the per-handoff class contribution (0 for external handoffs)
contrib = np.zeros(air.size, dtype=np.int64)
contrib[merged] = [CLASS_OF_DIGIT[int(a % 10)] for a in internal]
cpref = np.concatenate(([0], np.cumsum(contrib)))
bad2 = 0
checked = 0
seqs = defaultdict(Counter)
for s in range(seg[-1] + 1):
    i0, i1 = int(bounds[s]), int(bounds[s + 1])
    k = i1 - i0
    if k < 2:
        continue
    T = int(ts[i1 - 1]) + 2 - int(ts[i0])
    from_digits = (2 * k + int(cpref[i1 - 1] - cpref[i0])) % 30
    checked += 1
    if from_digits != T % 30:
        bad2 += 1
    if k <= 7:                     # tabulate every sequence that occurs
        seqs[k][tuple(int(a % 10) for a in air[i0:i1 - 1])] += 1
print("\n  segments checked: %d   class-from-digits vs class-from-endpoints: %d exceptions"
      % (checked, bad2))

print("\n  the short sequences (gap end digits inside the segment):")
for k in sorted(seqs):
    print("  k=%d: %d distinct sequences (of %d over the 5 digits)" % (k, len(seqs[k]), 5 ** (k - 1)))
    for sq, n in seqs[k].most_common(5):
        c = (2 * k + sum(CLASS_OF_DIGIT[d] for d in sq)) % 30
        print("      %-16s %8d   -> class %2d" % (str(sq), n, c))

# --- 3. the prime end digits: only the digit, unless we are on the twin ladder
pd = ts[1:] % 10
print("\n  prime end digits of the arriving starts: %s"
      % {int(d): int((pd == d).sum()) for d in sorted(set(pd.tolist()))})
pair_classes = Counter((int(ts[i] % 30), int(ts[i] % 10)) for i in range(ts.size) if ts[i] > 5)
print("  (class, digit) pairs among twin starts above 5: %s"
      % sorted(set((d, c) for c, d in pair_classes)))
print("  -> each live digit carries exactly one class here; each digit carries two in general")

with open("results/tableV5_class_from_digits.csv", "w") as f:
    f.write("k_pairs,sequence,n,class_of_segment\n")
    for k in sorted(seqs):
        for sq, n in seqs[k].most_common():
            f.write("%d,%s,%d,%d\n" % (k, "".join(str(d) for d in sq), n,
                                       (2 * k + sum(CLASS_OF_DIGIT[d] for d in sq)) % 30))
ok = (bad1 == 0 and bad2 == 0)
print("\n  CLASS-FROM-DIGITS %s (airs %d exceptions, segments %d exceptions)"
      % ("PASSED" if ok else "FAILED", bad1, bad2))
sys.exit(0 if ok else 1)
