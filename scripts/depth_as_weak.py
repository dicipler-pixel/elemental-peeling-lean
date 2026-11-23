#!/usr/bin/env python3
"""The depth-versus-weak-force comparison, with every number in depth-as-weak-force.md."""
import math

# --- the weak force
alpha_em = 1 / 137.036
sin2_theta_W = 0.23122
alpha_W = alpha_em / sin2_theta_W
G_F = 1.1663787e-5          # GeV^-2
m_p = 0.938272              # GeV
r_nucleon = 0.84e-15        # m
r_weak = 1e-18              # m

# --- the depth (measured; see depth-correlates.md §3)
H_depth = 1.5678            # bits, three-way depth entropy
I_depth = 0.0448            # bits, mutual information with the crossing
mean_gap = 18.9             # steps, mean gap between consecutive primes > 5 below 2.2e8

print("weak force")
print("  alpha_W = g^2/4pi            = %.4f   (1/%.1f)" % (alpha_W, 1 / alpha_W))
print("  low-energy suppression G_F m_p^2 = %.1e" % (G_F * m_p ** 2))
print("  range / nucleon radius       = %.1e" % (r_weak / r_nucleon))
print("depth")
print("  coupling to the digit I/H    = %.4f   (1/%.1f)" % (I_depth / H_depth, H_depth / I_depth))
print("  range / mean gap             = %.3f   (1/%.1f)" % (1 / mean_gap, mean_gap))
print("comparison")
print("  relative ranges differ by    = %.0fx" % ((1 / mean_gap) / (r_weak / r_nucleon)))
print("  couplings differ by          = %.1fx" % (alpha_W / (I_depth / H_depth)))
print("  global suppression: weak %.1e, depth %.3f -> %.0fx apart"
      % (G_F * m_p ** 2, I_depth / H_depth, (I_depth / H_depth) / (G_F * m_p ** 2)))
print("memory along the ladder: P(shallow|shallow) 0.567, P(shallow|deep) 0.592"
      " -> %.1f points at lag 1, 0.7 at lag 2" % (100 * (0.592 - 0.567)))
