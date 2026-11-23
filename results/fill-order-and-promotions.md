# The fill order is not an input, and the nineteen are not exceptions

## 1. The fill order is the rung order — the table's own axis

The fill sequence is

$$1s,\ 2s,\ 2p,\ 3s,\ 3p,\ 4s,\ 3d,\ 4p,\ 5s,\ 4d,\ 5p,\ 6s,\ 4f,\ 5d,\ 6p,\ 7s,\ 5f,\ 6d,\ 7p .$$

That is not a list to be memorised. It is the **diagonal enumeration of the triangle** $l<n$: order the
pairs $(n,l)$ by $n+l$, tie by $n$. Equivalently: rung by rung, and inside a rung by row. But the rung *is*
the table's axis — a cell is $(m,q)$ with $q=n+l$ — and the row is the other axis. So

> **the fill order is the order of the table's own coordinates.** Nothing is added by stating it.

The one thing that is *not* arithmetic is the claim that energy increases with the rung. That is the single
physical input behind Madelung, and it is one inequality, not a sequence:

$$\text{input: } E \text{ increases with } q=n+l \quad\text{(screening, approximately)}.$$

(The measured configurations then *shift* at four occupancies, where the exchange term beats the rung — §3.)

## 2. The digit hypothesis, tested

Your proposal: the order of fill is a subsequence of the gap end digits or of the prime end digit sequence.
Stated precisely, the block sequence is

$$l = 0,0,1,0,1,0,2,1,0,2,1,0,3,2,1,0,3,2,1,$$

and each block is labelled by its width's digit, $4l+2 \bmod 10$:

$$2,2,6,2,6,2,0,6,2,0,6,2,4,0,6,2,4,0,6 .$$

Tested against 78,494 gap end digits and 78,495 prime end digits:

| test | gap end digits | prime end digits |
|---|---|---|
| the full 19-digit pattern as a **contiguous** run | **no** | **no** |
| as a **subsequence** | yes (trivially — four symbols, a long sequence) | **no** |
| every 3-, 4-, 5- and 6-digit window as a contiguous run | yes | no |

So the *order* is not in either digit sequence: the only positive is that short windows of the block
digits occur somewhere among the gaps, which they must, since the gaps take four symbols too.

**What is real, and is what you are pointing at**, is the alphabet: blocks are labelled by even digits
(2, 6, 0, 4) and gaps end in even digits (0, 2, 4, 6, 8) — the same alphabet, and the block index is a
bijection of its digit:

$$l \;\longleftrightarrow\; 4l+2 \bmod 10 \;=\; 0\to2,\ 1\to6,\ 2\to0,\ 3\to4 .$$

So the block you are in is readable from the digit, exactly; the *order* the blocks are visited in is not.

## 3. The nineteen are exchange promotions, not exceptions

They are predicted, not unexplained. The criterion is one line:

$$\text{promote } ns \to (n-1)d \iff G(k)\,K > \text{rung},$$

with $G(k)=\Phi(k+1)-\Phi(k)$ the Hund exchange increment. Applied to the three $d$ series it reproduces
every measured configuration decision (30/30, with two fitted numbers per series — a rung and a
contraction — and one unit $K$ shared by all three), and the two families are:

* **ten one-rung promotions** (gap 1 in the index): Cr, Cu, Nb, Mo, Ru, Rh, Pd, Ag, Pt, Au;
* **nine tie promotions** (gap 0, where $4f/5d$ or $5f/6d$ share $n+l$): La, Ce, Gd, Ac, Th, Pa, U, Np, Cm.

The mechanism in both families is the same: at $d^4\to d^5$, $d^9\to d^{10}$, $f^6\to f^7$ and
$f^{13}\to f^{14}$ the exchange increment is at its maximum ($+4$, $+4$, $+6$, $+6$ quanta) and beats the
rung. Where it does not beat the rung, nothing happens — which is why the list has 19 members and not 118.

**So the word is wrong, and it is now changed throughout the record**: these are the **exchange
promotions**. The arithmetic behind the list is machine-checked in
[`promotion-theorems.lean`](promotion-theorems.lean) (27 theorems, 0 `sorry`):

* $G$ has the closed form $G(k)=k$ up to the half-fill and $G(k)=k+1-\text{cap}$ after it, its peak is
  at the half-filled shell ($+4$ for $d$, $+6$ for $f$) and its range is $\text{cap}-2$ — 8 and 12
  quanta against a rung of 1 (`G_d`, `G_f`, `G_d_peak`, `G_f_spread`, `rank_cannot_follow`);
* **no promotion crosses two rungs**: all nineteen rung gaps are 0 or 1, and the shape is then forced
  from $(n+l)$ alone — gap $+1$ ⟹ $s\to d$, gap $0$ ⟹ $f\to d$ (`promos_gap_le_one`,
  `gap_one_is_s_to_d`, `gap_zero_is_f_to_d`);
* the split is **ten and nine**, with their exact shapes (`promos_split`, `promos_gap_one_shape`,
  `promos_gap_zero_shape`).

What remains genuinely open is narrower and should be named as such: the two numbers per $d$ series in
the criterion — a rung and a contraction — are **fitted**, and the file proves them *as a fit*
(`fit_3d`, `fit_4d`, `fit_5d` exhibit rational values that reproduce the measured flip sets exactly).
For the $f$ series no such fit exists: a straddle two electrons apart forces a contraction above 12,
six times the largest $d$ value (`f_straddle_forces_B`). That is why the $f/d$ ordering is an
oscillation about the tie and not a rung.

## 4. The revised input list

| input | kind |
|---|---|
| spin-½ | one number, physical |
| the $1/r$ potential (Coulomb degeneracy $n^2$) | one potential, physical |
| energy increases with the rung $q=n+l$ | **one inequality**, not a sequence |
| the scales $R$, $c$, $G$ | measurements |

Everything else is arithmetic: the cells, the counts, the widths, the capacities, the bridges, the
closures — and now the fill order itself, which is the rung order.
