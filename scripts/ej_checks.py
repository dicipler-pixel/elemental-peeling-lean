#!/usr/bin/env python3
"""Checks on E. Johnson, *EJ's Alternate Base Prime Number Pattern and the Twin Prime Counterflow Model*
(Zenodo 23484151): the two theorems, the counterexample to Conjecture 4.3, and the mod-9 split."""
import collections
import sympy

print("== Theorem 3.1: gap = d2 - d1 (mod 10) on consecutive primes > 5")
ps = [p for p in sympy.primerange(7, 10**6)]
bad = sum(1 for a, b in zip(ps, ps[1:]) if (b - a - (b % 10 - a % 10)) % 10 != 0)
print("   violations in %d pairs: %d" % (len(ps) - 1, bad))

print("\n== Theorem 10.2: twin residues mod 9")
tw = [p for p in sympy.primerange(7, 10**6) if sympy.isprime(p + 2)]
res = collections.Counter((p % 9, (p + 2) % 9) for p in tw)
print("   %d twins; transitions %s" % (len(tw), dict(res)))
print("   only the three allowed pairs: %s" % (set(res) <= {(2, 4), (5, 7), (8, 1)}))

print("\n== Conjecture 4.3: normalized subscripts determine the gaps?")
def subs(seg): return [p // 10 for p in seg]
def norm(seg):
    s = subs(seg); return tuple(x - s[0] for x in s)
def gaps(seg): return tuple(b - a for a, b in zip(seg, seg[1:]))
A = [127, 131, 137, 139]
B = [211, 223, 227, 229]
for name, seg in (("paper's row", A), ("counterexample", B)):
    print("   %-11s %s  primes=%s  subs=%s  normalized=%s  gaps=%s"
          % (name, seg, all(sympy.isprime(p) for p in seg), subs(seg), norm(seg), gaps(seg)))
same = norm(A) == norm(B)
print("   same normalized sequence: %s ; same gaps: %s" % (same, gaps(A) == gaps(B)))
if same and gaps(A) != gaps(B):
    print("   => Conjecture 4.3 is FALSE (a counterexample exists)")

print("\n== Conjecture 6.4: with bg_{i+1} = ep_i and ep_{i-1} = bg_i both sides equal the total gap")
rungs = [(11, 19), (29, 31), (41, 43), (59, 61), (71, 73), (101, 109), (137, 139)]
print("   %-6s %-22s %s" % ("rung", "bg_i-1, bg_i, ep_i, ep_{i+1}", "consecutive?"))
for i in range(1, len(rungs) - 1):
    bg_prev, ep_prev = rungs[i - 1]
    bg, ep = rungs[i]
    consecutive = (bg == ep_prev)
    print("   %-6d bg %3d ep %3d ; previous ep %3d ; shares boundary: %s"
          % (i, bg, ep, ep_prev, consecutive))
