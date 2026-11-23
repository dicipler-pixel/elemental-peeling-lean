# The intuitive table: what the picture is, and what it is not

`intuitive-periodic-table.png` draws the periodic table with its layout decided by the two equations
rather than by convention.

## What is measured, and reproduced here

* **Block widths.** $2(2l+1)$ = 2, 6, 10, 14 — the odd numbers doubled.
* **Depths.** $\#\{n : l+1 \le n \le 8-l\}$ = 8, 6, 4, 2; the $s$ column is cut to 7 because $8s$ is
  never reached. So the four rectangles tile the 118 real elements exactly:
  $2\cdot7 + 6\cdot6 + 10\cdot4 + 14\cdot2 = 14+36+40+28 = 118$.
* **The rule.** Fill by $(n+l, n)$, two per orbital. Checked against the measured configuration of all
  118 elements: **99 exact, 19 exchange promotions** — Cr, Cu, Nb, Mo, Ru, Rh, Pd, Ag, La, Ce, Gd, Pt, Au, Ac,
  Th, Pa, U, Np, Cm. Every one is a half-filled or closed $d$/$f$ shell. The 19 are ringed in the
  figure; they are named, not averaged away. (Lr was in the register until its configuration was
  settled as $5f^{14}7s^26d^1$, which the rule already gives.)
* **The continuation.** The arithmetic does not stop at 7. Under the same rule $8s^2$ would make 120
  (the table is two cells short), and $5g$ — 18 wide, $2(2l+1)$ with $l=4$ — opens at $Z = 121$. The
  table stops at 118 because that is where the measured sequence ends, not because the rule ends.

## The prime strip, and the one number that differs

Eight columns, $\varphi(30) = 8$ — the residues 1, 7, 11, 13, 17, 19, 23, 29 mod 30 — with the row
index the subset number. A row never fills: **at least one of the eight is a multiple of 7** (the
eight residues cover all of $\mathbb{Z}/7$), so the capacity is 7, and 6 in the blocks where two of
the eight are divisible by 7 (91 and 119, for instance). Width − capacity = 0 for the elements, 1 for
the primes.

That "8 = 2 + 6" — $\varphi(30)$ against the $s$+$p$ widths — is a **match of widths, not a mapping**.
Measured, a last-digit key carries $-0.142$ bits about the block: less than chance. Drawn side by side
the two tables are the same equation with a different capacity; that is the only claim the picture
makes.

## The rule past $n = 7$ — the modified table

Nothing in $2(2l+1)$ or $2n^2$ knows about $Z=118$. Continue the same two equations and the table keeps
going, one row per shell:

| $n$ | widths $2(2l+1)$, $l<n$ | capacity $2n^2$ | blocks reached by $Z\le118$ | electrons placed | missing |
|---|---|---|---|---|---|
| 1 | 2 | 2 | $s$ | 2 | — closes |
| 2 | 2, 6 | 8 | $s,p$ | 8 | — closes |
| 3 | 2, 6, 10 | 18 | $s,p,d$ | 18 | — closes |
| 4 | 2, 6, 10, 14 | 32 | $s,p,d,f$ | 32 | — closes |
| 5 | 2, …, 18 | 50 | $s,p,d,f$ | 32 | $g$ |
| 6 | 2, …, 22 | 72 | $s,p,d$ | 18 | $f,g,h$ |
| 7 | 2, …, 26 | 98 | $s,p$ | 8 | $d,f,g,h,i$ |
| 8 | 2, …, 30 | 128 | none yet | 0 | all ($8s$ is the next cell, $Z=119,120$) |
| 9 | 2, …, 34 | 162 | — | 0 | — |
| 10 | 2, …, 38 | 200 | — | 0 | — |

Two things this makes visible. **Only shells 1–4 close.** From $n=5$ the filling runs ahead into the
next shell before the current one is full — that is exactly why the periods have lengths
$2,8,8,18,18,32,32$ and not $2,8,18,32$: a period is not a shell, it is a *diagonal* through the
shells. And **the capacity never comes back**: $50,72,98,128,162,200$ is what the arithmetic has
written, of which 32, 18, 8 and 0 have been filled — the sums run 2, 8, 18, 32, 32, 18, 8 = 118.

The column that changes name each row is the block ladder: $2(2l+1)$ for $l=0,1,2,\dots$ gives cells
$2,6,10,14,18,22,26,30$ — that is $2\times$ the odd numbers $2l+1 = 1,3,5,7,9,11,13,15$, and it is the
**second** of the three pair ladders:

* the base key's floors: $1k+1 \to 1,2,3,4,5$ (step 1),
* the blocks: $2l+1 \to 1,3,5,7$ (step 2 pairs; widths $2,6,10,14$ cells),
* the twin key's classes: $3c+2 \to 2,5,8,11,14$ (step 3).

Each is an arithmetic progression in the *pair* count, and $\sum_{l<n}2(2l+1)=2n^2$ is the statement
that the cell counts close while the pair counts close at $n^2$. The table stops at 7 for nuclear
reasons — the measured sequence ends there — not because the arithmetic does; the arithmetic has
already written rows 8, 9 and 10, and the first two cells of row 8 are $8s^2$.

The full block ledger to $n=10$ is in [`tableF_scales.csv`](tableF_scales.csv).
