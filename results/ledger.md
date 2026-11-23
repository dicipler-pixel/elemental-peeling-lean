# The ledger: assets, liabilities, equity — with the exclusions in equity

Two books, because there are two kinds of difference. A **structural** difference never moves and is
booked to equity. A **temporal** difference is a balance that is still settling, and is booked to
liabilities where it amortises to zero.

---

## Book 1 — the structural ledger (capacity = realised + excluded)

Every row is a double entry: the claim (capacity) against the kernel (what the arithmetic and the data
actually use). The difference is always a count of *forbidden moves*, so it is never a rounding.

| account | claim (capacity) | realised (kernel) | excluded | why excluded |
|---|---|---|---|---|
| wheel classes | 30 residues | **8** | 22 | not coprime to $2\cdot3\cdot5$ |
| base key cells | $4\times5=20$ | **16** | 4 | the four pairs that land on 5 |
| twin key cells | $3\times5=15$ | **9** | 6 | the three landing on 3, the three on 5 |
| primes per 30-row | 8 slots | **7** | 1 | one of the eight is always a multiple of 7 |
| twins per 30-block | values 0–4 | **0,1,2,3** | 4 | no fourth twin residue ($3=8-5$) |
| element cells | 120 | **118** | 2 | $8s^2$ is never reached |

$$8+22=30,\quad 16+4=20,\quad 9+6=15,\quad 7+1=8,\quad 4+1=5,\quad 118+2=120 .$$

**Every row closes.** This is the trial balance of the whole structure, and the credit side is saturated:
16 of 16 cells, 9 of 9 pairs, 3 of 3 twins attained (637 blocks), 7 of 8 primes attained.

**Equity is the excluded column** — 22, 4, 6, 1, 1, 2 — and it has a single character throughout: it is
what the residues forbid. That is the "big one": in every row the balance item is not an estimate, it is
a count of moves that cannot happen.

---

## Book 2 — the flow ledger (the type walk, and the decaying excess)

The walk on $\{11,17,29\}$ is circulant at every scale (the three edge ratios agree to five parts in ten
thousand), so write it as three shares: stay $s$, forward $f$, reverse $r$.

| | stay $s$ | forward $f$ | reverse $r$ | $f/r-1$ |
|---|---|---|---|---|
| **par** (the limit) | 0.3333 | 0.3333 | 0.3333 | 0 |
| **book** below $10^9$ | 0.3118 | 0.3554 | 0.3328 | +6.8% |
| deviation | $-0.0215$ | $+0.0221$ | $-0.0005$ | |

Two readings, both exact:

* the deviation is **not** spread over the cycle — reverse sits at par (0.2% off), and the whole
  imbalance is a transfer out of *stay* ($-6.5\%$ relative) into *forward* ($+6.6\%$ relative), which is
  what makes $f/r-1=+6.8\%$;
* the transfer **amortises**. $f/r-1$ by window: 1.19, 1.16, 1.20, 1.13, 1.08, **1.065** for
  $10^3$–$10^4$ … $10^8$–$10^9$, and above $10^7$ it follows $1.35/\log x$ to within 6%.

So the excess is booked as a **prepayment, not as retained earnings**: it is an asset being written down,
and it must not be capitalised. What survives the limit is par — $s=f=r=1/3$ — and that is the only
part that belongs in equity.

| item | book value at $10^9$ | limit | class |
|---|---|---|---|
| stay share | 0.3118 | 0.3333 | amortising |
| forward/reverse excess | $+6.5\%$ | 0 | amortising |
| self-share vs par | $-6.5\%$ | 0 | amortising |
| circulant structure (edges equal) | exact | exact | **equity** |
| $9$ cells, all occupied | exact | exact | **equity** |

---

## The open items (liabilities not yet settled)

| item | amount | status |
|---|---|---|
| rule failures in the element table | 19 of 118 = 16.1% | named, not explained individually |
| unfilled capacity (pores) | 18, 54, 90 = $18(2n-9)$ | capacity exists, no elements |
| $P(\text{gap}=1)$ deficit | 0.1797 vs 0.1907 = 6% | unexplained |
| $f/d$ ordering | 3 parameters per series | no closed form |
| air law intercept | ~~$0.7503$ vs $\tfrac{1}{2C_2}=0.75739$, i.e. $-0.9\%$~~ — **resolved**: the offset is $-2$, not $0$ | the $-0.9\%$ was $2/\langle t^2\rangle$; `air-law-offset.md` |

None of these is small enough to ignore and none has an exact kernel yet. They are the liabilities: the
part of the book that is still open.

---

## The correspondence to $c=E/(m\,\Delta T)$

Your page's line and the balance sheet are the same identity read from different ends. In both, **the
ratio is exact and the scale is free**:

| | thermodynamics | this ledger |
|---|---|---|
| ratio identified exactly | $c=E/(m\Delta T)$ | 8 of 30, 16 of 20, 9 of 15, 7 of 8 |
| scale that must be supplied | $m$ or $E$ | which capacity you count (30, 20, 15, 8) |
| residual | the measurement error | the excluded column |

And the "pushed in / shaved in place" from your sketch is the equity line doing its job: the excluded
count absorbs whatever the claim and the kernel disagree by, which is why no row can fail to balance and
why the balance item is the only place pressure shows.
