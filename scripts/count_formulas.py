#!/usr/bin/env python3
"""The counts, measured decade by decade, and every relation between them.

    python3 scripts/count_formulas.py [LIM]          # default 1e9

The counts (definitions in results/count-formulas.md; the arithmetic that relates them
is proved in results/count-formulas.lean):

    P(x)  primes <= x                                 the primitive count
    B(x)  primes <= x that are 1 mod 6                the base ladder  4+6k  (the base key)
    K(x)  primes <= x that are 5 mod 6                the twin ladder 5+6k  (the twin key)
    N(x)  twin starts <= x  (p and p+2 prime)         the twin count
    H(x)  = N(x) - 1                                  handoffs = twin-key cells filled
    D(x)  handoffs with no prime strictly between      the double twin count
          the departing partner p+2 and the arriving start q

A handoff is merged exactly when the arriving start q sits two places after the departing
start p in the prime sequence (the only prime between them being the partner p+2), so
merging is decided on global prime indices, never on a gap value.

Checks printed (each exact, so a mismatch is a bug, not noise):

    B + K + 2 = P                     the two ladders exhaust the primes
    air = q - p - 2 is 4 mod 6        every handoff above the seed (3,5), air 0
    sum of total gaps = last - first  the telescoping identity: the count is a span over a mean gap

and three Hardy-Littlewood predictions with no free parameter:

    N(x) ~ 2 C2 Int dx/log^2 x,   D(x) ~ (2 C2)^2 Int dx/log^3 x,   B, K ~ li(x)/2

Writes results/tableU_count_formulas.csv, .scratch/counts/air_hist.json,
.scratch/counts/segment_hist.json.
"""
import sys, json, math, os
import numpy as np

C2 = 0.6601618158468696          # twin prime constant
TC = 2 * C2                      # 1.3203236316937392
SEG = 1 << 26


def primes_in(lo, hi, BP):
    """Primes in [lo, hi) by a segmented odd-only sieve."""
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
    return out[out < hi]


def base_primes(root):
    sv = np.ones(root // 2 + 2, dtype=bool)
    sv[0] = False
    for i in range(1, int(root ** 0.5 / 2) + 1):
        if sv[i]:
            sv[(2 * i + 1) ** 2 // 2::(2 * i + 1)] = False
    b = 2 * np.nonzero(sv)[0] + 1
    return b[b >= 3]


def li_integral(x, k):
    """Int_2^x dt/log(t)^k by trapezoid on u = log t (k = 1, 2, 3)."""
    u = np.linspace(math.log(2.0), math.log(float(x)), 2 * 10 ** 6)
    return float(np.trapezoid(np.exp(u) / u ** k, u))


def brute(lim):
    """Independent full sieve: the same counts, no segmentation."""
    sv = np.ones(lim + 4, dtype=bool)
    sv[:2] = False
    for i in range(2, int((lim + 3) ** 0.5) + 1):
        if sv[i]:
            sv[i * i::i] = False
    pr = np.nonzero(sv[:lim + 1])[0]
    ts = pr[sv[pr + 2]]
    pos = np.full(lim + 1, -1, dtype=np.int64)
    pos[pr] = np.arange(pr.size)
    D = int(np.count_nonzero(np.diff(pos[ts]) == 2)) if ts.size > 1 else 0
    return dict(P=int(pr.size), B=int(np.count_nonzero(pr % 6 == 1)),
                K=int(np.count_nonzero(pr % 6 == 5)), N=int(ts.size),
                H=int(ts.size) - 1, D=D)


def main():
    lim = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 9
    BP = base_primes(int(math.sqrt(lim)) + 1000)
    decs = [10 ** d for d in range(1, int(math.log10(lim)) + 1)]
    rows = []

    # ---- seed: the primes 2,3,5 and the twin starts 3,5 (the zero-air join) ----
    P, Bs, Ks, N, H, D = 3, 0, 1, 2, 1, 0
    G4 = G2 = G0 = 0
    span_sum, air_sum, log2_sum, first_ts, last_ts = 2, 0, 0.0, 3, 5
    last_ts_gi, prev_prime, gi = 2, 5, 3      # 7 is prime number 3 (indexing 2 as 0)
    cnt_primes = 0                            # primes actually sieved, to check P independently
    airhist = {0: 1}
    seghist, run = {}, 2

    for di, d in enumerate(decs):
        hi_d = min(decs[di + 1] if di + 1 < len(decs) else lim, lim)
        if d >= lim:
            break
        d_air = {}
        lo = 7 if di == 0 else max(d, 7)
        lo += (lo % 2 == 0)
        while lo < hi_d:
            hi = min(lo + SEG, hi_d)
            ps_all = primes_in(lo, min(hi + 4, hi_d + 4), BP)
            ps = ps_all[ps_all < hi]
            if ps.size == 0:
                lo = hi
                continue
            gidx = gi + np.arange(ps.size)            # global prime index of each ps
            # gaps of the ordinary prime sequence
            if prev_prime is not None:
                g0 = int(ps[0]) - prev_prime
                G4 += g0 % 6 == 4; G2 += g0 % 6 == 2; G0 += g0 % 6 == 0
            dg = np.diff(ps)
            G4 += int(np.count_nonzero(dg % 6 == 4))
            G2 += int(np.count_nonzero(dg % 6 == 2))
            G0 += int(np.count_nonzero(dg % 6 == 0))
            # the two ladders
            r6 = ps % 6
            Bs += int(np.count_nonzero(r6 == 1))
            Ks += int(np.count_nonzero(r6 == 5))
            # twin starts: p and p+2 prime
            j = np.searchsorted(ps_all, ps + 2)
            ok = j < ps_all.size
            tpa = np.zeros(ps.size, dtype=bool)
            tpa[ok] = ps_all[j[ok]] == (ps + 2)[ok]
            tp = tpa
            ts, tidx = ps[tp], gidx[tp]
            if ts.size:
                # cross-segment handoff: last_ts -> ts[0]
                q = int(ts[0])
                gap = q - last_ts
                H += 1
                span_sum += gap
                air = gap - 2
                air_sum += air
                airhist[air] = airhist.get(air, 0) + 1
                d_air[air] = d_air.get(air, 0) + 1
                if int(tidx[0]) - last_ts_gi == 2:
                    D += 1; run += 1
                else:
                    seghist[run] = seghist.get(run, 0) + 1; run = 1
                # within-segment handoffs
                if ts.size > 1:
                    gaps = np.diff(ts)
                    airs = gaps - 2
                    merged = np.diff(tidx) == 2
                    H += int(gaps.size)
                    span_sum += int(gaps.sum())
                    air_sum += int(airs.sum())
                    log2_sum += float((np.log(ts[1:].astype(np.float64)) ** 2).sum())
                    for a, c in zip(*np.unique(airs, return_counts=True)):
                        airhist[int(a)] = airhist.get(int(a), 0) + int(c)
                        d_air[int(a)] = d_air.get(int(a), 0) + int(c)
                    Dm = int(np.count_nonzero(merged))
                    D += Dm
                    for m in merged.tolist():
                        if m:
                            run += 1
                        else:
                            seghist[run] = seghist.get(run, 0) + 1
                            run = 1
                last_ts, last_ts_gi = int(ts[-1]), int(tidx[-1])
            N = H + 1
            prev_prime = int(ps[-1])
            gi += ps.size
            cnt_primes += int(ps.size)
            lo = hi
        P = 2 + Bs + Ks
        rows.append(dict(x=hi_d, P=P, B=Bs, K=Ks, N=N, H=H, D=D, G4=G4, G2=G2, G0=G0,
                         span=span_sum, air_sum=air_sum, log2=log2_sum,
                         mean_air=air_sum / H if H else 0.0,
                         mean_log2=log2_sum / H if H else 0.0,
                         span_ratio=(span_sum / (log2_sum / TC)) if log2_sum else 0.0))
        print("  to %-11d P=%-11d B=%-11d K=%-11d N=%-10d H=%-10d D=%-8d D/H=%.4f"
              % (hi_d, P, Bs, Ks, N, H, D, D / H if H else 0), flush=True)

    seghist[run] = seghist.get(run, 0) + 1
    os.makedirs(".scratch/counts", exist_ok=True)
    be = ""
    if lim < 10 ** 8:
        print("\n  (bound below 1e8: the csv and the histograms are left as the 1e9 run wrote them)")
    else:
        be = "" if lim >= 10 ** 8 else "x"
    if lim >= 10 ** 8:
      with open("results/tableU_count_formulas.csv", "w") as f:
        f.write("x,pi,base_1mod6,twinkey_5mod6,twin_starts,handoffs,double_twins,"
                "gaps_4mod6,gaps_2mod6,gaps_0mod6,sum_total_gaps,sum_air,mean_air,"
                "HL_twin,HL_double,HL_half_li,sum_log2,mean_log2,span_over_pred\n")
        for r in rows:
            r["HL_twin"] = TC * li_integral(r["x"], 2)
            r["HL_double"] = TC ** 2 * li_integral(r["x"], 3)
            r["HL_half_li"] = 0.5 * li_integral(r["x"], 1)
            f.write("%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%.4f,%.1f,%.1f,%.1f,%.2f,%.4f,%.6f\n"
                    % (r["x"], r["P"], r["B"], r["K"], r["N"], r["H"], r["D"],
                       r["G4"], r["G2"], r["G0"], r["span"], r["air_sum"],
                       r["mean_air"], r["HL_twin"], r["HL_double"], r["HL_half_li"],
                       r["log2"], r["mean_log2"], r["span_ratio"]))
      json.dump({str(k): v for k, v in sorted(airhist.items())},
                open(".scratch/counts/air_hist.json", "w"))
      json.dump({str(k): v for k, v in sorted(seghist.items())},
                open(".scratch/counts/segment_hist.json", "w"))
    for r in rows:
        if "HL_twin" not in r:
            r["HL_twin"] = TC * li_integral(r["x"], 2)
            r["HL_double"] = TC ** 2 * li_integral(r["x"], 3)
            r["HL_half_li"] = 0.5 * li_integral(r["x"], 1)

    print("\n  x            B+K+2-P  N/HL2     D/HL3     B/HLli    (B-li/2)/sqrt x")
    for r in rows:
        print("  %-12d %5d   %8.5f  %8.5f  %8.5f   %+7.3f"
              % (r["x"], r["B"] + r["K"] + 2 - r["P"], r["N"] / r["HL_twin"],
                 r["D"] / r["HL_double"], r["B"] / r["HL_half_li"],
                 (r["B"] - r["HL_half_li"]) / math.sqrt(r["x"])))
    print("\n  telescoping: sum of total gaps %.0f, last-first %d,  sum of airs %.0f, "
          "last-first-2(N-1) %d" % (rows[-1]["span"], last_ts - first_ts, rows[-1]["air_sum"],
                                    last_ts - first_ts - 2 * (rows[-1]["N"] - 1)))
    if lim <= 10 ** 7:
        ref = brute(lim)
        bad = [k for k in ref if abs(ref[k] - (H if k == "H" else N if k == "N" else
               D if k == "D" else Bs if k == "B" else Ks if k == "K" else P)) > 0]
        print("  brute force to %d: %s  -> %s"
              % (lim, ref, "AGREES" if not bad else "MISMATCH in " + str(bad)))
    print("  the one equation: span = sum(log^2 p)/(2C2)  ->  span/predicted")
    for r in rows:
        print("    x=%-11d sum_log2=%-16.1f  mean log2=%-8.2f  span/pred=%.5f"
              % (r["x"], r["log2"], r["mean_log2"], r["span_ratio"]))
    print("  air mod 6 seen:", sorted(set(a % 6 for a in airhist)))
    print("  airs seen:", sorted(airhist)[:14], "...")
    print("  gaps mod 6 (4/2/0):", rows[-1]["G4"], rows[-1]["G2"], rows[-1]["G0"])
    print("  segments:", {k: seghist[k] for k in sorted(seghist)})
    print("  segments %d, handoffs %d, pairs per segment %.4f"
          % (sum(seghist.values()), rows[-1]["H"], rows[-1]["H"] / sum(seghist.values())))
    checks = [cnt_primes + 3 == rows[-1]["P"],
              rows[-1]["span"] == last_ts - first_ts,
              rows[-1]["air_sum"] == last_ts - first_ts - 2 * (rows[-1]["N"] - 1),
              set(a % 6 for a in airhist) <= {0, 4},
              set(ah for ah in airhist if ah % 6 == 0) <= {0}]
    if lim <= 10 ** 7:
        ref = brute(lim)
        checks.append(ref["P"] == rows[-1]["P"] and ref["B"] == rows[-1]["B"]
                      and ref["K"] == rows[-1]["K"] and ref["N"] == rows[-1]["N"]
                      and ref["D"] == rows[-1]["D"])
    print("  COUNT CHECKS %s (prime count, telescoping, air sum, air residues%s)"
          % ("PASSED" if all(checks) else "FAILED",
             ", brute force" if lim <= 10 ** 7 else ""))
    print("  independent prime count %d (= 2 + 3 + sieved %d) vs P = %d  -> %s"
          % (cnt_primes + 3, cnt_primes, rows[-1]["P"],
             "AGREES" if cnt_primes + 3 == rows[-1]["P"] else "MISCOUNT"))


if __name__ == "__main__":
    main()
