# If the table were not indexed by $Z$: what a second coordinate would and would not show

The blind spot is exactly one thing. A $Z$-indexed table quotients out the neutrons, so it cannot tell
"nothing happened" from "a neutron went in". Give it a neutron coordinate and the channels separate —
but what the new coordinate reveals is not what one would hope, and one thing stays invisible however
many counts you add.

## 1. The move table

| event | in $Z$ alone | in $(Z,N)$ |
|---|---|---|
| elastic scatter | identity | identity |
| **capture** $(n,\gamma)$ | **identity** (invisible) | $(0,\ +1)$ |
| $\beta^-$ | $+1$ | $(+1,\ -1)$ |
| $\beta^+$ / EC | $-1$ | $(-1,\ +1)$ |
| $\alpha$ | $-2$ | $(-2,\ -2)$ |
| fission | one cell → two | one cell → two, plus $\nu$ |

So at the level of bookkeeping the answer is **yes, exactly**: a second coordinate identifies the
channels, because capture becomes a unit step while a bounce stays the identity. (Lean:
`capture_moves_N`.) That is arithmetic, not measurement.

## 2. What it buys immediately: the multiplicity becomes readable

In a $(Z,N)$ table the neutrons are the *gap*:

$$\nu = N_{\text{parent}} - \bigl(N_1 + N_2\bigr) = A_{\text{parent}} - \bigl(A_1 + A_2\bigr).$$

Read out of the ENDF/B-VIII.0 yield tables by mass balance (no neutron counters involved):

| system | $\nu$ from the yields | textbook |
|---|---|---|
| U-235 thermal | 2.40 (ENDF) / 2.59 (JEFF) | 2.43 |
| U-233 thermal | 2.45 | 2.49 |
| Pu-239 thermal | 2.89 / 3.10 | 2.88 |
| Cf-252 SF | 3.93 | 3.77 |
| U-238, 14 MeV | 4.07 | rises with energy |

So a second coordinate does see them, and the numbers are right to a few per cent. Table:
[`tableT_fission_neutrons.csv`](tableT_fission_neutrons.csv).

## 3. What it costs: the split stops being one-parameter

In $Z$ alone, $Z_1+Z_2=Z$ pins the partner: one number fixes the pair, which is why the whole
distribution collapses onto a single variable and the "pin" is a statement about one number. With $N$
as well, $N_1+N_2+\nu=N$ has *two* free numbers — the light charge and the multiplicity — and

$$N-N_1 = N_2+\nu .$$

So the second coordinate buys the neutrons and pays for them in determinacy. (Lean: `neutron_unpinned`.)
That trade is the honest content of the question: the $Z$-table's rigidity is not a defect, it is what
you get for ignoring $\nu$.

## 4. What it reveals — and this is the surprise

Measured over the same 24 systems, both coordinates scored against their own closure ladders:

| coordinate | mean $\pm$ s.e. | s.d. | distance from its closure |
|---|---|---|---|
| $Z_{\rm heavy}$ | $54.14\pm0.13$ | 0.64 | **0.14 from $C(5)=54$** |
| $N_{\rm heavy}$ | $84.48\pm0.21$ | 1.05 | **2.48 from the magic 82** |

The heavy fragment sits **on** the proton closure and **past** the neutron one — 2.5 neutrons beyond
$N=82$, which is $2.4$ standard deviations. So adding the coordinate does not sharpen the picture; it
shows that the sharp closure here is the proton one, and that the neutron shell is one the fragments
have just left. The same, in one system: U-235 thermal gives light $(Z,N)=(38.03,\ 56.89)$ and heavy
$(54.03,\ 84.65)$ — the light piece 6.9 neutrons past the magic 50, the heavy 2.7 past 82, while both
proton numbers are within $0.05$ of a cell edge on the closure ladder.

## 5. And the ladder itself changes — so the theorem does not transfer

The proton closures are the partial sums of $2\lceil(m+1)/2\rceil^2$:

$$C=(2,\ 10,\ 18,\ 36,\ 54,\ 86,\ 118).$$

The neutron closures are the magic numbers

$$M=(2,\ 8,\ 20,\ 28,\ 50,\ 82,\ 126).$$

**They share exactly one term, 2** (Lean: `ladders_share_one`), and the discrepancy is structural: the
proton ladder is the hydrogenic $2n^2$ degeneracy (Coulomb $1/r$, no spin-orbit), while the neutron
ladder comes from the nuclear potential with its strong spin-orbit coupling, so it is not $2n^2$ at all
— $20$ is not twice a square where the proton value at that index is $18$ (Lean:
`twenty_not_twice_square`), and $28$ likewise where the proton value is $32$
(`twentyeight_not_twice_square`).

So an $N$-indexed table is a **different table with a different theorem**, not a translated version of
this one. Anything proved on the $Z$-axis — the countdown $v+h=L(m)$, the capacities $8,18,32$, the
"closed cell" predicate — has to be re-derived on the $N$-axis, and the derivation fails at $2n^2$ by
the third term. That is why the record's single-axis table is the proton one: it is the axis with a
closed-form closure law.

## 6. What no number of counts can show

Excitation energy. Both coordinates are counts, and the effect that dominates the fission landscape at
fixed $Z$ is not a count: Cm-245 thermal and Cm-244 spontaneous differ by a factor **31** in
valley/peak at the same $Z$, and U-235 moves by 127× between thermal and 14 MeV. A discrete table of
any width cannot hold that; you would need a continuous coordinate, and then it is no longer a table of
counts.

The same applies to the charge distribution's *width* (s.d. 2.3 around the pinned mean) and to the
barrier itself: whether a nucleus splits at all is a question about energy, not about where its cells
are.

## 7. Verdict

* **Identify the channels** — yes, exactly, by making capture a step in $N$ while the bounce stays the
  identity.
* **See the neutrons** — yes, and the multiplicity falls out of the mass balance to a few per cent.
* **Keep the structure** — no. The neutron ladder shares one term with the proton ladder, so the Light
  Bridge theorem does not survive the re-indexing; it would have to be rebuilt on a ladder that is not
  $2n^2$.
* **See the physics that decides** — no. Energy is not a count, and the largest effects in the fission
  data are energy effects.
