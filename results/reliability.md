# Reliability of the one equation: random cuts, regular cuts, and two controls

The equation of [`one-equation.md`](one-equation.md) is

$$p_N-p_1=\frac{1}{2C_2}\sum_{i=1}^{N-1}\log^{2}p_i,\qquad \frac{1}{2C_2}=0.757390\pm0.000018 .$$

**What can and cannot be tested.** The cumulative form is a tautology *given the airs*: it telescopes, so
permuting the gaps, cutting the chain anywhere, or resampling it leaves the sum unchanged. The content is
one level down — the per-handoff law $\text{air}_i=\log^{2}p_i/(2C_2)-2$ — and that is what has to be
reliable wherever you cut. Every test below therefore estimates the rate $c$ **per handoff** (through the
origin, $\sum q a/\sum q^{2}$ with $q=\log^{2}p$, $a=\text{air}+2$) and reports $c\cdot2C_2$, which is
$1$ if the law holds, with its standard error. `scripts/reliability.py`, run to $10^{9}$; it prints
`RELIABILITY PASSED` and writes [`tableY_reliability.csv`](tableY_reliability.csv).

## 1. Regular data — the cut points fixed in advance, not drawn

| group | $c\cdot2C_2$ | s.e. | $z$ of the law's residual |
|---|---|---|---|
| all handoffs | 0.75755 | 0.00039 | $+0.43$ |
| decade $10^{4}$–$10^{5}$ | 0.76657 | 0.02047 | $+0.51$ |
| $10^{5}$–$10^{6}$ | 0.76342 | 0.00826 | $+0.72$ |
| $10^{6}$–$10^{7}$ | 0.75326 | 0.00306 | $-1.41$ |
| $10^{7}$–$10^{8}$ | 0.75788 | 0.00116 | $+0.45$ |
| $10^{8}$–$10^{9}$ | 0.75755 | 0.00042 | $+0.41$ |
| four quarters of $10^{8}$–$10^{9}$ | 0.7579, 0.7570, 0.7608, 0.7568 | 0.0023 each | $+0.22,-0.19,+1.45,-0.24$ |
| first half / second half (by handoff) | 0.75762 / 0.75750 | 0.00055 | $+0.42 / +0.21$ |
| below / above the geometric midpoint | 0.77167 / 0.75755 | 0.023 / 0.0004 | $+0.60 / +0.43$ |

No cut is more than $1.5\sigma$ from the law, including the four quarters — the $1.45$ on quarter 3 is one
look in twenty and is not a feature. The two smallest groups carry the largest errors, as they must: the
error scales as $1/\sqrt{m}$, and the low decades have 20 and 80 times fewer handoffs than the top one.
The half-split agrees at $(c_1-c_2)/\mathrm{se}=+0.15$: **no drift between the halves of the range.**

## 2. Random data — 1000 windows of 200 to 5000 handoffs, drawn uniformly

| quantity | value |
|---|---|
| mean of the estimates | $c\cdot2C_2=0.75696\pm0.00053$ (i.e. $1.000\ 0\pm0.000\ 7$ after the global rate) |
| calibration of the per-window $z$ | s.d. $0.876$, mean $-0.054$, $\lvert z\rvert<2$ in $97.7\%$ of windows |
| windows within 5% of the law | $96.6\%$ (median $\lvert c\cdot2C_2-1\rvert=1.1\times10^{-2}$) |

The $z$-calibration is the part worth reading: if the law and its quoted standard error were right, the
per-window $z$ would be standard normal, and it is — s.d. $0.88$, mean $-0.05$, $97.7\%$ inside two sigma.
So the error bar is honest, not decorative: a single window's estimate scatters by exactly the amount the
residual s.d. predicts.

**Regular against random, at the same window size** (400 handoffs): s.d. of the estimate is $3.26\times10^{-2}$
on the fixed grid and $3.30\times10^{-2}$ on random draws — ratio $1.01$. There is no selection bias in
where the window starts; the only thing that sets the precision is how many handoffs it contains.

## 3. Two controls, one of which must fail

| control | result |
|---|---|
| **airs permuted across positions** (the law must get worse) | window-residual s.d. $39.46$ against $11.19$ for the real pairing — **3.5× worse**. The law is localised: the gap belongs to *its* $\log^{2}p$, not to the average |
| **synthetic chains obeying the law**, integer gaps at the true positions | recovers $c\cdot2C_2-1=+1.4\times10^{-6}$ (s.d. $3.6\times10^{-5}$): the estimator is unbiased |
| **synthetic chains with the real scatter added** ($\sigma=280$) | $c\cdot2C_2-1=-1.3\times10^{-4}$ (s.d. $3.2\times10^{-2}$): no bias introduced by the noise |

The permutation control is the one that matters, and it is the reason the cumulative identity cannot be
mistaken for evidence: it shows the law is a statement about the *pairing* of gaps to positions, and that
the pairing is doing the work.

## 4. The two bookkeeping slips, priced

| slip | effect on $c\cdot2C_2$ |
|---|---|
| $m$ off by one (handoffs vs starts) | $1.0\times10^{-7}$ — irrelevant at any $m>10^{4}$ |
| span taken to include the last pair ($p_N+2-p_1$) | $2/(p_N-p_1)$ — $2\times10^{-9}$ at $10^{9}$ |

So the two errors that change a *count* by one change the *rate* by nothing. The rates that do move are the
ones with real physics in them: the decade coefficients in §1 differ by up to $1.4\%$ from each other, and
that is sample size, not a convention.

## 5. What this does not establish

* **The value of $1/(2C_2)$ is an input**, measured in [`air-law-offset.md`](air-law-offset.md) to $10^{12}$;
  these tests establish that the equation is *reliable* — same answer from any cut, calibrated error bars,
  no drift, sensitive controls — not that the constant has the value it has.
* **Nothing beyond $10^{9}$** is tested here; the air law itself is flat to $10^{12}$ in the record, but
  this script stops where its prime data stop.
* **The cumulative claim is not independently tested**, because it cannot be: it is exact given the airs
  (`Law.span_from_logs`). What is tested is the law that feeds it.
