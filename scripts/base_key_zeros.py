#!/usr/bin/env python3
"""The base count's explicit formula: the zeros of L(s, chi) found in the two ladders.

The base count B(x) = # {p <= x : p = 1 mod 6} and the twin-ladder count K(x) = # {p = 5 mod 6}
have an exact explicit formula, because 1 mod 6 and 5 mod 6 are the two values of the real
character chi = chi_{-3} mod 3 on the primes.  For that character

    psi(x; chi) = sum_{p^k <= x} chi(p)^k log p = - sum_rho x^rho / rho + (trivial zeros) + const,

rho over the zeros of L(s, chi), and on the critical line

    (psi(x; chi) - const) / sqrt(x) = - sum_gamma 2[(1/2)cos(gamma L) + gamma sin(gamma L)]
                                        / (1/4 + gamma^2),        L = log x,

the same shape as von Mangoldt's formula for zeta, with a different set of frequencies.  And
B(x) - K(x) is exactly this sum, so the split of the primes into the two ladders oscillates at
the zeros of L(s, chi_{-3}).

This script (i) computes the first zeros of L(s, chi_{-3}) from its Hurwitz-zeta form
L(s, chi) = 3^{-s} (zeta(s, 1/3) - zeta(s, 2/3)), high precision, then (ii) bins the prime data
in log x, transforms, and reports which of those zeros it recovers, with the 2/gamma amplitudes
and a shuffled control.

    python3 scripts/base_key_zeros.py [LIM] [XMIN] [NBINS]      # default 1e8 1e3 6000
"""
import sys, math
import numpy as np
import mpmath as mp

SEG = 1 << 26


def lchi_zeros(tmax=70.0, step=0.02):
    """Zeros of L(s, chi_{-3}) on the critical line, up to imaginary part tmax.

    Lambda(s) = (3/pi)^((s+1)/2) Gamma((s+1)/2) L(s, chi) satisfies Lambda(s) = Lambda(1-s)
    (the root number is 1 for this character), so on the critical line it is real; its sign
    changes are the zeros."""
    mp.mp.dps = 30

    def Lam(t):
        s = mp.mpf(1) / 2 + 1j * mp.mpf(t)
        v = (mp.mpf(3) / mp.pi) ** ((s + 1) / 2) * mp.gamma((s + 1) / 2) \
            * mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))
        return mp.re(v)

    out, t, prev = [], 0.5, Lam(0.5)
    while t < tmax:
        t2 = t + step
        v = Lam(t2)
        if prev == 0 or (prev < 0) != (v < 0):
            a, b = t, t2
            for _ in range(90):
                m = (a + b) / 2
                if (Lam(a) < 0) != (Lam(m) < 0):
                    b = m
                else:
                    a = m
            out.append(float((a + b) / 2))
        t, prev = t2, v
    return out


def primes_in(lo, hi, BP):
    if hi <= lo:
        return np.zeros(0, dtype=np.int64)
    n = (hi - lo + 1) // 2
    arr = np.ones(n, dtype=bool)
    for p in BP:
        if p * p >= hi:
            break
        st = max(p * p, ((lo + p - 1) // p) * p)
        if st % 2 == 0:
            st += p
        if st < hi:
            arr[(st - lo) // 2::p] = False
    out = lo + 2 * np.nonzero(arr)[0]
    return out[(out < hi) & (out > 1)]


def base_primes(root):
    sv = np.ones(root // 2 + 2, dtype=bool)
    sv[0] = False
    for i in range(1, int(root ** 0.5 / 2) + 1):
        if sv[i]:
            sv[(2 * i + 1) ** 2 // 2::(2 * i + 1)] = False
    b = 2 * np.nonzero(sv)[0] + 1
    return b[b >= 3]


def chi3(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


def main():
    LIM = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 8
    XMIN = float(sys.argv[2]) if len(sys.argv) > 2 else 1e3
    NB = int(sys.argv[3]) if len(sys.argv) > 3 else 6000
    print("zeros of L(s, chi_{-3}) on the critical line:")
    Z = lchi_zeros(max(70.0, 2 * math.pi * 10))
    print("  " + ", ".join("%.6f" % z for z in Z))
    print("  %d zeros below %.0f" % (len(Z), Z[-1] if Z else 0))
    with open("results/tableV_L_zero_chi3.csv", "w") as f:
        f.write("n,gamma\n")
        for i, z in enumerate(Z, 1):
            f.write("%d,%.6f\n" % (i, z))

    BP = base_primes(int(math.sqrt(LIM)) + 1000)
    L0, dL = math.log(XMIN), (math.log(LIM) - math.log(XMIN)) / NB
    w = np.zeros(NB)
    lo = 3
    while lo < LIM:
        hi = min(lo + SEG, LIM)
        ps = primes_in(lo, hi, BP)
        for p in ps.tolist():
            c = chi3(p)
            pk, sgn = p, c
            while pk <= LIM:
                lg = math.log(p)
                k = int((math.log(pk) - L0) / dL)
                if 0 <= k < NB:
                    w[k] += sgn * lg
                pk *= p
                sgn *= c
        lo = hi
    psi = np.cumsum(w)
    x = np.exp(L0 + np.arange(1, NB + 1) * dL)
    g = psi / np.sqrt(x)
    win = np.hanning(NB)

    def spec(sig):
        F = np.fft.rfft((sig - sig.mean()) * win)
        return np.abs(F), np.fft.rfftfreq(len(sig), d=dL) * 2 * math.pi

    P, f = spec(g)
    sel = (f > 4) & (f < 65)
    fs = f[sel]
    Pn = P[sel] / P[sel].max()
    res = fs[1] - fs[0]
    tol = max(0.4, 1.2 * res)
    peaks = [i for i in range(2, len(fs) - 2) if Pn[i] > 0.08 and Pn[i] == max(Pn[i - 2:i + 3])]
    print("\n  frequency resolution %.3f, %d peaks above 8%% of the max\n" % (res, len(peaks)))
    print("   peak     nearest L-zero   offset    power   2/gamma law")
    hits, ratios = 0, []
    for i in peaks:
        j = int(np.argmin(np.abs(np.array(Z) - fs[i])))
        d = Z[j] - fs[i]
        hit = abs(d) < tol
        hits += hit
        pred = Pn[peaks[0]] * Z[0] / Z[j]
        if hit:
            ratios.append(Pn[i] / pred)
        print("  %7.3f   %12.3f   %+7.3f  %7.3f   %7.3f  %s"
              % (fs[i], Z[j], d, Pn[i], pred, "match" if hit else "-"))
    print("\n  %d of %d peaks match a zero of L(s, chi_{-3}) within %.2f" % (hits, len(peaks), tol))
    inside = [z for z in Z if fs[0] < z < fs[-1]]
    got = sum(1 for z in inside if min(np.abs(fs - z)) < tol)
    print("  %d of %d zeros inside the window recovered" % (got, len(inside)))
    if ratios:
        print("  amplitude law: measured/predicted = %.3f mean, spread %.3f-%.3f"
              % (np.mean(ratios), min(ratios), max(ratios)))
    rng = np.random.default_rng(7)
    tot, trials = 0, 200
    for _ in range(trials):
        Q, _ = spec(rng.permutation(g))
        Qn = Q[sel] / Q[sel].max()
        pk = [i for i in range(2, len(fs) - 2) if Qn[i] > 0.08 and Qn[i] == max(Qn[i - 2:i + 3])]
        tot += sum(1 for i in pk if min(np.abs(np.array(Z) - fs[i])) < tol)
    print("  null (shuffle, %d trials): %.2f matches per realisation" % (trials, tot / trials))

    # a sharper statistic than counting peaks: the share of the window's spectral power that
    # sits within tol of a zero.  The signal puts it there; a shuffle scatters it.
    ZA = np.array(Z)

    def captured(sig):
        Q, _ = spec(sig)
        Qs = Q[sel] ** 2
        near = np.zeros_like(fs, dtype=bool)
        for z in ZA:
            near |= np.abs(fs - z) < tol
        return Qs[near].sum() / Qs.sum(), Qs[near].sum(), Qs.nonzero()[0].size

    cs = captured(g)[0]
    null_c = [captured(rng.permutation(g))[0] for _ in range(30)]
    print("  power within %.2f of a zero: signal %.3f, shuffle %.3f +- %.3f"
          % (tol, cs, np.mean(null_c), np.std(null_c)))
    ok = hits == len(peaks) and got == len(inside) and cs > np.mean(null_c) + 3 * np.std(null_c)
    print("  BASE-KEY ZEROS %s (%d/%d peaks, %d/%d zeros, power %.3f vs %.3f)"
          % ("PASSED" if ok else "FAILED", hits, len(peaks), got, len(inside), cs, np.mean(null_c)))


if __name__ == "__main__":
    main()
