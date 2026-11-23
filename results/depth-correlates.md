# Depth correlates — and the correlator is 3

Your sundial claim, measured on the sieve. Short version: **the two grooves of a crossing split the wrong
way for the digit to explain, and the thing that decides them is the factor 3.** The split is $58/42$ one
way and $30/70$ the other, and the table reproduces almost exactly.

## 1. The claim, stated as a measurement

Every crossing $d_1\to d_2$ has two grooves ten apart, $g$ and $g+10$, which the digit cannot separate.
Measured at $2.2\times10^8$ — 12,122,533 steps, both primes $>5$ — the shallow share is:

| crossing | $g$ | shallow | deep $g{+}10$ | further |
|---|---|---|---|---|
| 1→3 | 2 | **32.2%** | 39.1% | 28.7% |
| 1→7 | 6 | **57.7%** | 17.2% | 25.1% |
| 1→9 | 8 | 30.7% | **40.3%** | 29.0% |
| 3→1 | 8 | 33.6% | **38.2%** | 28.1% |
| 3→7 | 4 | 34.1% | 26.9% | 38.9% |
| 3→9 | 6 | **57.7%** | 17.2% | 25.1% |
| 7→3 | 6 | **58.5%** | 15.7% | 25.8% |
| 9→1 | 2 | 29.7% | **39.8%** | 30.5% |

Five of your six figures reproduce to $0.2\%$: 1→7 (57.9/17.2), 1→9 (30.8/40.4), 3→1 (33.8/38.3),
3→7 (34.3/27.0), 3→9 (57.9/17.2). The sixth, **1→3, does not**: you have 49.0/29.5, I measure 32.2/39.1.
At $10^6$ I get 43.4/40.2 for that cell, so the 1→3 row looks like a run from a much smaller range left
in the figure — the twin cell is the one whose shallow share moves fastest with scale.

So yes: **depth correlates**, and strongly — within one crossing the odds swing from $58:42$ to $30:70$.

## 2. Why: the shift of ten is a shift of one modulo 3

The two grooves differ by 10, and $10\equiv1\pmod 3$. So the pair $(g,g+10)$ has residues $(r,r+1)$:
exactly one of them is divisible by 3 unless $r=1$, in which case neither is (Lean: `depth_shift_mod3`,
`depth_dichotomy`). And that is exactly how the measurement sorts:

| the shallow $g$ | residues $(g,\ g{+}10)$ | shallow share | what wins |
|---|---|---|---|
| 6 | $(0,\,1)$ | **57.7–58.5%** | the shallow — it is the multiple of 3 |
| 2, 8 | $(2,\,0)$ | **29.7–33.6%** | the deep — *it* is the multiple of 3 |
| 4 | $(1,\,2)$ | **34.1–38.1%** | neither; the deep wins weakly |
| 10 | $(1,\,2)$ | **38.3–44.6%** | neither; the split is near even |

So the depth is not a free second coordinate and not a fixed one: it is decided by whether the groove is a
multiple of 3 — the same 3 that kills four of the eight base slots and makes the twin alphabet three.

## 3. How much information the depth carries

Two honest numbers, which answer different questions:

* **Locally, the swing is large**: a factor of 2 in the odds, $58:42$ against $30:70$.
* **Globally, it is small**: with the depth split three ways (shallow, deep, further), its entropy is
  $1.568$ bits, and conditioning on the crossing leaves $1.523$ — a mutual information of
  **0.045 bits, 2.9% of the uncertainty**. The reason is the third bucket: $32\%$ of the weight sits at
  $g\ge$ shallow$+20$ and the crossing predicts nothing about it.

So "depth correlates" is right in the sense that matters for a *reading* — it changes the odds enough to
identify the groove — and wrong in the sense of *explaining*: 97% of the depth's uncertainty is not about
the crossing at all, it is about how far out in the gap distribution the prime pair happens to sit.

## 4. What does not reproduce: the station means

Panel (C) gives 16.95, 15.82, 18.82, 16.39 for the four stations. I cannot reproduce those numbers under
any grouping:

| grouping | 1 | 3 | 7 | 9 |
|---|---|---|---|---|
| mean gap **departing** from the digit | 17.90 | 18.90 | 17.27 | 18.53 |
| mean gap **arriving** at the digit | 18.51 | 17.27 | 18.92 | 17.89 |
| your panel (C) | 16.95 | 15.82 | 18.82 | 16.39 |

The *ordering* of your four matches the arriving side exactly — $3<9<1<7$ — but all four sit 1.5–2 below
my values, and station 7 is out of line with the rest of the pattern ($1.11\times$ the station-1 value
where mine is $1.02\times$). That looks like a different range or a different count basis (for instance
steps restricted to a sub-block), not a different definition. Worth a re-run before it goes in the record;
the depth table above is solid, this panel is not yet.

## 5. The stove knob

Your two photographs make the same point physically, and the data supports the reading: the dial position
is the digit, the shaft is the depth, and **the dial cannot separate the grooves** — inside a cell the
split is never $100/0$, it is $30/70$ at best. So a single dial reading is genuinely ambiguous, and the
second setting is what resolves it. That is the sundial's design claim, and it is confirmed: one number
(the digit) leaves a 2:1 ambiguity that only the depth resolves.

## 6. What this does to the record

* The base key's 16 cells are the right unit: the crossing *predicts* the depth, so the depth is not an
  independent axis.
* The depth is *not* determined by the crossing either (3:2 odds at best), so each cell carries a
  distribution over classes rather than a class. That is a refinement of the record's line "the class
  carries the information, the label adds under a percent" — true for the **twin** key, false for the
  **base** key, where the label predicts the depth at $58:42$.
* And the predictor is the same small prime as everywhere else in this system: 3.

*(Reproduce: `.scratch/work/depth.py` for the 16-cell table; the identities are `depth_shift_mod3` and
`depth_dichotomy` in [`merge-theorems.lean`](merge-theorems.lean).)*
