# Why nineteen: the index charges one rung, the step costs up to eight

The Madelung rule orders subshells by $(n+l,n)$ and then fills them. It is a **rank**: every subshell
step costs the same one rung, whoever takes it. The measured configurations say the cost of a step is
not constant — and the 19 exchange promotions are exactly where the real step cost differs from the rung.

(Count corrected: lawrencium is $[\mathrm{Rn}]\,5f^{14}7s^2 6d^1$, not $7p^1$. With $6d^1$ it agrees
with the rule and leaves the register: **99 exact, 19 exchange promotions**.)

## 1. What actually moves, all nineteen

Every exception is a transfer of one electron (two for Pd and Th) between two subshells, and the two
subshells are always **adjacent in the index**:

| Z | element | moves | index gap | exchange before → after | verdict |
|---|---|---|---|---|---|
| 24 | Cr | $4s\to3d$ | 1 | 6 → 10 | half-fill, +4 |
| 29 | Cu | $4s\to3d$ | 1 | 0 → 0 | closed shell, no exchange |
| 41 | Nb | $5s\to4d$ | 1 | 3 → 6 | +3 |
| 42 | Mo | $5s\to4d$ | 1 | 6 → 10 | half-fill, +4 |
| 44 | Ru | $5s\to4d$ | 1 | 6 → 3 | **loses** 3 |
| 45 | Rh | $5s\to4d$ | 1 | 3 → 1 | **loses** 2 |
| 46 | Pd | $5s\to4d$ (×2) | 1 | 1 → 0 | closed shell |
| 47 | Ag | $5s\to4d$ | 1 | 0 → 0 | closed shell |
| 57 | La | $4f\to5d$ | 0 | 0 → 0 | tie, d wins |
| 58 | Ce | $4f\to5d$ | 0 | 1 → 0 | tie, d wins |
| 64 | Gd | $4f\to5d$ | 0 | 15 → 21 | half-fill, +6 |
| 78 | Pt | $6s\to5d$ | 1 | 1 → 0 | **loses** 1 |
| 79 | Au | $6s\to5d$ | 1 | 0 → 0 | closed shell |
| 89 | Ac | $5f\to6d$ | 0 | 0 → 0 | tie, d wins |
| 90 | Th | $5f\to6d$ (×2) | 0 | 1 → 1 | tie, d wins |
| 91 | Pa | $5f\to6d$ | 0 | 3 → 1 | **loses** 2 |
| 92 | U | $5f\to6d$ | 0 | 6 → 3 | **loses** 3 |
| 93 | Np | $5f\to6d$ | 0 | 10 → 6 | **loses** 4 |
| 96 | Cm | $5f\to6d$ | 0 | 15 → 21 | half-fill, +6 |

Two facts hold with no exception and are worth stating as the frame:

* **the index gap is 0 or 1 in all nineteen** — ten of one, nine of the other. No exception crosses
  two rungs.
* **the exchange (Hund, $\sum\binom{u}{2}$ over subshells) falls in eight of them** — Ru, Rh, Pd, Pt,
  Ce, Pa, U, Np — rises in five (Cr, Nb, Mo, Gd, Cm) and is unchanged in six. The textbook sentence
  "half-filled and closed shells are stabilised" is true of four of the nineteen and false of the rest;
  §5 says why.

## 2. The step cost, exactly

For a subshell of capacity $2(2l+1)$ holding $k$ electrons, the exchange gain of adding one more is
$$G(k)=\Phi(k+1)-\Phi(k),\qquad \Phi(k)=\binom{u}{2},\quad u=\min(k,\ \text{cap}-k).$$
For a $d$ shell that is $G=0,1,2,3,4,-4,-3,-2,-1,0$ for $k=0,\dots,9$; for an $f$ shell
$0,1,2,3,4,5,6,-6,-5,-4,-3,-2,-1,0$. Closed form: $G(k)=k$ up to the half-fill, then
$G(k)=k-(\text{cap}-1)$.

The spread is 8 quanta for $d$ and 12 for $f$, against a rung of 1. **That is the fault**: a rank that
charges 1 per step cannot follow a quantity that swings from $+4$ to $-4$ inside one subshell.

*(Lean: the closed form, the two peaks, the two ranges and the range-beats-rank inequality are
`G_d`, `G_f`, `G_d_peak`, `G_f_peak`, `G_d_spread`, `G_f_spread`, `rank_cannot_follow` in
[`promotion-theorems.lean`](promotion-theorems.lean).)*

## 3. Family A — the ten that cross one rung ($ns \to (n-1)d$)

The rule is the obvious one: move the electron when the exchange increment beats the rung,
$$G(k)\,K > \Delta_{\text{series}} .$$
With a **linear** rung $\Delta(k)=A-Bk$ (in units of $K$), each $d$ series is fit exactly — the
predicted flip set equals the measured one, with two numbers per series:

| series | $A$ (rung at $k=0$) | $B$ (contraction per electron) | crossing $k^\*=A/B$ | flips predicted = measured |
|---|---|---|---|---|
| 3d | 6.74 | 0.88 | 7.7 | $\{4,9\}$ = Cr, Cu |
| 4d | 7.51 | 1.88 | 4.0 | $\{3,4,6,7,8,9\}$ = Nb, Mo, Ru, Rh, Pd, Ag |
| 5d | 11.52 | 1.77 | 6.5 | $\{8,9\}$ = Pt, Au |

($A$ and $B$ are not separately pinned — they trade off along a ridge — but the flip set is the same for
every admissible pair, and the crossing is the stable output: $k^\*\in[6.8,9.0]$ for $3d$, $[3.0,4.5]$
for $4d$, $[6.0,7.5]$ for $5d$.)

Read the table as the answer to "what cancelled". The $d$ level crosses the $s$ level **inside** each
series — at $k\approx4$ for $4d$, at $k\approx7$ for $3d$ and $5d$ — and once it is below, every
subsequent element promotes, which is why the exceptions come in a *block* rather than scattering.
The two ends of each series are decided by exchange: at $k=4$ the increment is $+4$ and it beats the
rung even when the rung is still positive ($3d$: Cr at $k=4$ with the level still above the $s$ level,
$k^\*=7.7$).

Note what this does *not* say: the "closed shell" cases (Cu, Ag, Au, Pd) are fit only because $\Delta$
has already gone negative there. At $k=9$ the exchange increment is **0** — $d^9$ and $d^{10}$ have the
same $\Phi$ — so nothing about those four is exchange-stabilised. They are the tail of the crossing.

## 4. Family B — the ten that sit on a tie (f/d, d/p)

$(n+l)$ for $4f$ is 7 and for $5d$ is 7. For $5f$ and $6d$ it is 8. For $6d$ and $7p$ it is 8. In these
places **the index does not order anything** — the outcome is decided by the tie-break "$n$", which is
a convention with no energy behind it. That is the fault of the other half: not a step that costs too
much, but a step with no rung at all.

The measured pattern in the ties is not monotone, and that is the finding:

| series | $f$-occupation at which the $d$ level wins | count |
|---|---|---|
| $4f$ (La–Yb) | $k_f=0,1$ (La, Ce) and $k_f=7$ (Gd) | 3 |
| $5f$ (Ac–No) | $k_f=0,1,2,3,4$ (Ac, Th, Pa, U, Np) and $k_f=7$ (Cm) | 6 |
| $5f^{\,14}$ (Lr) | none — $6d^1$ is what the rule says, so Lr is not an exception | 0 |

The last row is here to be explicit: with $6d^1$, lawrencium's measured configuration is exactly the
predicted one, so it is *not* a nineteenth-plus-one. It also removes the only $d/p$ case, which is why
there is no "largest $n$ wins" statement left in the tie list at all.

So the $5f$ level lies below $6d$ for the first five electrons and the $4f$ level only for the first
two; the half-shell $f^7$ pulls one electron back out in both series (+6 quanta, the largest single
increment in the table); and at $f^{14}$ the electron skips $6d$ altogether. No linear rung fits this set. The
conflict is exact and worth stating: keeping $f^6$ (Sm, Pu — no promotion) needs the rung above $+6$,
while promoting out of $f^7$ (Gd, Cm) needs it below $-6$, two electrons apart; a grid over
$A\in[-20,20]$, $B\in[-6,6]$ returns **no** admissible pair. Adding a pairing term does not rescue it
either: the same two constraints then force $B-P>12$. So the $f/d$ ordering is not a rung at all — it
oscillates around the exact tie by more than 12 exchange quanta, which is the size of the half-shell
gain itself.

## 5. What faulted, in one paragraph

The rule is a **sum of two integers**, and a sum of integers is a rank: it can say *which* subshell
comes next, and it charges the same 1 for every step. Reality charges the exchange term instead, which
is quadratic in the number of unpaired spins and therefore has no idea about ranks: its increment runs
$+4$ down to $-4$ for a $d$ shell. Two failures follow, and they account for the nineteen exactly:

* **where the rank is tight but not tied** ($s$ vs $d$, gap 1) the swing of the increment crosses it —
  ten elements, and the crossing point moves with $Z$ because the $d$ level falls through the $s$
  level inside each series;
* **where the rank is tied** ($f$ vs $d$, $d$ vs $p$, gap 0) there is nothing to cross, and the
  tie-break decides — nine elements, decided by where the true levels happen to sit, which oscillates.

And the closing sentence of the textbook — "half-filled and closed shells are specially stable" — is
two different mechanisms glued together. Half-filled is exchange (Cr, Mo, Gd, Cm: $+4,+4,+6,+6$).
Closed is not: at $d^9\to d^{10}$ the exchange is unchanged at 0, and the pairing cost *rises* by one
pair. Whatever stabilises $d^{10}$ is the one-electron potential of the filled shell, not spin.

## 6. The comparison you asked for

$10,2,4,6,8 \mapsto 8,2,3.5,5,6.5$ is one linear map, $y=2+\tfrac34(x-2)$: a contraction of ratio $3/4$
about the fixed point 2. It is uniform — the same rule for every element of the sequence, and the
sequence survives as an arithmetic progression with step $2\to1.5$.

The periodic table's exceptions are the same shape with the roles swapped: the **ladder** is uniform
(rungs of 1 in the index) and the **cost** is not ($G$ swings over 8 quanta; the rung itself contracts
as $A-Bk$ with $B\approx0.9$–$1.9$ per electron). Where your map applies one ratio to a ladder, this one
applies a ladder to a swinging cost — and the exceptional elements are exactly the places where the
swing crosses the rung. The fixed point is the crossing $k^\*=A/B$: the filling at which the $d$ level
meets the $s$ level. $4d$: $k^\*\approx4$, $3d$: $k^\*\approx7.7$, $5d$: $k^\*\approx6.5$ — three
numbers instead of nineteen names.
