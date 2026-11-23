#!/usr/bin/env python3
"""Read the Riemann zeros off the primes.

Von Mangoldt's explicit formula is exact:

    psi(x) = x - sum_rho x^rho/rho - zeta'(0)/zeta(0) - (1/2) log(1 - x^-2),

so with rho = 1/2 + i*gamma,

    (psi(x) - x) / sqrt(x)  =  - sum_gamma 2*[ (1/2) cos(gamma L) + gamma sin(gamma L) ] / (1/4+gamma^2),
    L = log x,

a sum of oscillations at the zeros' frequencies with amplitude 2/|rho| = 2/gamma (to leading order).
Sample that function on a grid of equal log-steps, Fourier transform in L, and the zeros appear as peaks.

Usage: python3 scripts/zeros_in_the_primes.py [LIM] [XMIN] [NBINS]
Prints the peaks, matches them to the known zeros, runs a shuffle null, and checks the 2/gamma law.
"""
import sys, math
import numpy as np

LIM = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**7
XMIN = float(sys.argv[2]) if len(sys.argv) > 2 else 1e3
NB = int(sys.argv[3]) if len(sys.argv) > 3 else 6000
SEG = 1 << 26

KNOWN = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178,
                  40.918719, 43.327073, 48.005151, 49.773832, 52.970321, 56.446248,
                  59.347044, 60.831779, 65.112544, 67.079811, 69.546402, 72.067158,
                  75.704691, 77.144840])


def primes_to(lim):
    root = int((lim + 4096) ** 0.5) + 1
    sv = np.ones(root // 2 + 2, dtype=bool)
    sv[0] = False
    for i in range(1, int(root ** 0.5 / 2) + 1):
        if sv[i]:
            sv[(2 * i + 1) ** 2 // 2::(2 * i + 1)] = False
    BP = (2 * np.nonzero(sv)[0] + 1)
    BP = BP[BP >= 3]
    out = []
    lo = 3
    while lo < lim:
        hi = min(lo + SEG, lim)
        n = (hi - lo) // 2
        arr = np.ones(n, dtype=bool)
        for p in BP:
            if p * p >= hi:
                break
            st = max(p * p, ((lo + p - 1) // p) * p)
            if st % 2 == 0:
                st += p
            if st < hi:
                arr[(st - lo) // 2::p] = False
        out.append(lo + 2 * np.nonzero(arr)[0])
        lo = hi
    return np.concatenate(out).astype(np.int64)


def main():
    L0 = math.log(XMIN)
    dL = (math.log(LIM) - L0) / NB
    ps = primes_to(LIM)
    ps = ps[ps >= XMIN]
    lg = np.log(ps.astype(np.float64))
    k = np.clip(((lg - L0) / dL).astype(np.int64), 0, NB - 1)
    psi = np.cumsum(np.bincount(k, weights=lg, minlength=NB))
    x = np.exp(L0 + np.arange(1, NB + 1) * dL)
    g = (psi - x) / np.sqrt(x)
    win = np.hanning(NB)

    def spec(sig):
        F = np.fft.rfft((sig - sig.mean()) * win)
        return np.abs(F), np.fft.rfftfreq(len(sig), d=dL) * 2 * math.pi

    p, f = spec(g)
    sel = (f > 5) & (f < 60)
    fs = f[sel]
    pn = p[sel] / p[sel].max()
    res = fs[1] - fs[0]
    tol = 0.35
    peaks = [i for i in range(2, len(fs) - 2) if pn[i] > 0.08 and pn[i] == max(pn[i - 2:i + 3])]
    print("primes used: %d   frequency resolution %.3f   peaks above 8%% of max: %d"
          % (ps.size, res, len(peaks)))
    print("\n  peak     nearest zero   offset    power   2/gamma law")
    hits, ratios = 0, []
    for i in peaks:
        j = int(np.argmin(np.abs(KNOWN - fs[i])))
        d = KNOWN[j] - fs[i]
        cal = pn[peaks[0]]
        flag = "match" if abs(d) < tol else "-"
        hits += abs(d) < tol
        if abs(d) < tol:
            ratios.append(pn[i] / (cal * KNOWN[0] / KNOWN[j]))
        print("  %7.3f   %9.3f   %+7.3f  %7.3f   %7.3f  %s"
              % (fs[i], KNOWN[j], d, pn[i], cal * KNOWN[0] / KNOWN[j], flag))
    print("\n  %d of %d peaks match a known zero within %.2f" % (hits, len(peaks), tol))
    recovered = sum(1 for z in KNOWN if 5 < z < 60 and min(np.abs(fs - z)) < tol)
    print("  %d of %d known zeros in [5,60] recovered"
          % (recovered, sum(1 for z in KNOWN if 5 < z < 60)))
    if ratios:
        print("  amplitude law: measured/predicted = %.3f mean, spread %.3f-%.3f"
              % (np.mean(ratios), min(ratios), max(ratios)))
    rng = np.random.default_rng(1)
    tot, trials = 0, 200
    for _ in range(trials):
        q, _ = spec(rng.permutation(g))
        qn = q[sel] / q[sel].max()
        pk = [i for i in range(2, len(fs) - 2) if qn[i] > 0.08 and qn[i] == max(qn[i - 2:i + 3])]
        tot += sum(1 for i in pk if min(np.abs(KNOWN - fs[i])) < tol)
    print("  null (shuffle, %d trials): %.2f matches per realisation" % (trials, tot / trials))


if __name__ == "__main__":
    main()
