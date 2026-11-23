#!/usr/bin/env python3
"""The three scaled formulas on the prime side, measured, with their error and their units.

    energy        Ê = gap / t² = 1/(2C₂) = 0.757390 ± 0.000018     (per handoff)
    acceleration  a = 1/C₂ = 1.514780                               (per handoff, in span per log²p)
    mass          m̂ = T / t² = 1/(2C₂) + 2/t²                       (per handoff; T = gap + 2)

and the two conversions, stated with their constants:

    kelvin      T_K = κ t²,  κ = (1/(2C₂))/3R = 0.030364 K per unit t²
    joule/mol   E   = 3R κ t² = (1/(2C₂)) t² = 0.75739 t² J per mol   (because 3R·κ = 1/(2C₂))

Each is checked per decade and against its own error bar. Nothing here converts mass to grams: on the
prime side mass is a count of pairs or a span of integers.

Run: python3 scripts/prime_scales.py [LIM]
"""
import sys, math, csv
import numpy as np

LIM = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 9
C2 = 0.6601618158468696
TC = 2 * C2
R = 8.314462618
KAPPA = (1 / TC) / (3 * R)

sv = np.ones(LIM + 8, dtype=bool)
sv[:2] = False
for i in range(2, int((LIM + 6) ** 0.5) + 1):
    if sv[i]:
        sv[i * i::i] = False
pr = np.nonzero(sv[:LIM + 3])[0].astype(np.int64)
ts = pr[sv[pr + 2]]
ts = ts[(ts > 5) & (ts <= LIM)]
gap = np.diff(ts).astype(float)
T = gap + 2.0                       # the total gap = the "rest mass" of a handoff
t2 = np.log(ts[1:].astype(float)) ** 2

print("to 1e%d: %d handoffs" % (round(math.log10(LIM)), gap.size))
print("\nthe constants")
print("  1/(2C₂)      = %.6f   (the energy coefficient, = a/2)" % (1 / TC))
print("  a = 1/C₂     = %.6f" % (1 / C2))
print("  κ            = %.6f K per unit t²  (=(1/(2C₂))/3R)" % KAPPA)
print("  3R·κ         = %.6f  = 1/(2C₂)  -> the J/mol reading has the same coefficient" % (3 * R * KAPPA))

print("\nper decade, the scaled trio")
print("  decade        n      Ê = gap/t²   a = 2Ê     m̂ = T/t²    ρ = pairs/span   2C₂/t²")
rows = []
for d in range(4, int(math.log10(LIM)) + 1):
    m = (ts[1:] >= 10 ** d) & (ts[1:] < 10 ** (d + 1))
    if m.sum() < 100:
        continue
    g, tt, q = gap[m], T[m], t2[m]
    E = float((q * g).sum() / (q * q).sum())          # through origin: gap = E t²
    M = float((q * tt).sum() / (q * q).sum())         # through origin: T = M t²
    span = int(ts[1:][m][-1] - ts[:-1][m][0])
    rho = m.sum() / span
    rows.append((10 ** (d + 1), int(m.sum()), E, 2 * E, M, rho, TC / float(q.mean())))
    print("  1e%d-1e%d %8d   %9.6f   %9.6f   %9.6f   %9.3e      %9.3e"
          % (d, d + 1, m.sum(), E, 2 * E, M, rho, TC / float(q.mean())))

Eall = float((t2 * gap).sum() / (t2 * t2).sum())
res = gap - Eall * t2
se = float(math.sqrt((res * res).sum() / (gap.size - 1) / (t2 * t2).sum()))
print("\n  all handoffs: Ê = %.6f ± %.6f   (1/(2C₂) = %.6f, ratio %.5f)"
      % (Eall, se, 1 / TC, Eall * TC))
print("  acceleration a = 2Ê = %.5f ± %.5f   (1/C₂ = %.5f)" % (2 * Eall, 2 * se, 1 / C2))
Tall = float((t2 * T).sum() / (t2 * t2).sum())
print("  mass m̂ = %.5f   and 1/(2C₂) + 2/⟨t²⟩ = %.5f   (the pair's correction)"
      % (Tall, 1 / TC + 2 / float(t2.mean())))
rho_all = gap.size / int(ts[-1] - ts[0])
print("  density ρ = %.4e pairs/span;  2C₂/⟨t²⟩ = %.4e" % (rho_all, TC / float(t2.mean())))
print("  E·ρ with E the mean gap: %.4f   (identically 1: E = span/m and rho = m/span)"
      % (float(gap.mean()) * rho_all))
print("  with E the coefficient Ê it is %.2e instead — different objects, which is the point"
      % (Eall * rho_all))

print("\nthe two converted readings of the same formula (conversions, not discoveries)")
print("  kelvin:     T = κ t²  ->  at t² = ⟨t²⟩ = %.1f, T = %.2f K" % (float(t2.mean()), KAPPA * float(t2.mean())))
print("  joule/mol:  E = 3R κ t² = %.5f t²  ->  at ⟨t²⟩, E = %.1f J/mol"
      % (3 * R * KAPPA, 3 * R * KAPPA * float(t2.mean())))
print("  the same at t = log 10^12: %.1f K, %.0f J/mol"
      % (KAPPA * math.log(1e12) ** 2, 3 * R * KAPPA * math.log(1e12) ** 2))

print("\nmass: what is and is not defined here")
print("  prime side: mass = pairs (a count) or span (integers). No gram exists on this side.")
print("  element side (measured): M(Z) = 2.619 Z - 9.36 u, R² = 0.9985")
print("  the two are NOT connected by a mass identification; the only bridge is κ, a conversion.")

with open("results/tableV12_prime_scales.csv", "w") as f:
    f.write("x,handoffs,E_hat,a,m_hat,rho,2C2_over_mean_t2\n")
    for r in rows:
        f.write("%d,%d,%.6f,%.6f,%.6f,%.4e,%.4e\n" % r)
ok = abs(Eall * TC - 1) < 0.005 and abs(3 * R * KAPPA - 1 / TC) < 1e-12
print("\n  PRIME SCALES %s (Ê·2C₂ = %.5f, 3R·κ = 1/(2C₂) exactly, mass = count on this side)"
      % ("PASSED" if ok else "FAILED", Eall * TC))
