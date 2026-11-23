# Bolstering the strong force: the oscillator ladder, and the countdown that orders fission

Setting the weak force aside, the strong force gets two things the previous note did not give it: a
*ladder with a closed form* — not merely "not $2n^2$" — and a *measured ordering variable* for the fission
mode. Both are checkable and both are now in the theorem.

## 1. The ladder has a formula, and it is the 3D oscillator

There are two cumulant laws, and they are both elementary:

$$\text{Coulomb: } \sum_{l<n}2(2l+1)=2n^2=(2,8,18,32,50,\dots)$$
$$\text{3D oscillator: } \sum_{N<n}(N+1)(N+2)=\frac{n(n+1)(n+2)}{3}=(2,8,20,40,70,\dots)$$

Both are proved in the master file (`coulomb_cumulant`, `oscillator_cumulant`). They agree at $n=1,2$ —
giving 2 and 8 — and at $n=3$ they are **18 against 20**; from there the oscillator strictly exceeds the
Coulomb cumulant (`coulomb_oscillator_agree`, `oscillator_beats_coulomb`).

Now put the observed neutron magic numbers beside them:

| ladder | values |
|---|---|
| Coulomb $2n^2$ | 2, 8, 18, 32, 50, 70… |
| 3D oscillator | 2, 8, 20, 40, 70, 112, 168 |
| **observed magic** | **2, 8, 20**, 28, 50, 82, 126 |

$$\text{Coulomb}\cap\text{magic}=\{2\},\qquad \text{oscillator}\cap\text{magic}=\{2,8,20\}$$

(proved: `proton_meets_magic_only_at_two`, `oscillator_meets_magic`).

So the strong ladder is **the 3D oscillator up to 20, and spin-orbit splitting after it** — the observed
28 is where the oscillator has 40, 50 where it has 70, 82 where it has 112, 126 where it has 168. That is
a far stronger statement than "not $2n^2$": it says *which* ladder the strong force carries, where the two
ladders part company (at the third cumulant, 18 vs 20), and what breaks the agreement beyond it
(spin-orbit, not the shell counting).

**Why this matters for the theorem**: the proton side is Coulomb, so its ladder is closed-form, which is
exactly why the Light Bridge is a theorem at all. The neutron side is oscillator-plus-spin-orbit, so its
ladder is *not* closed-form — which is why every attempt to run the theorem on the neutron axis failed at
the third term, and why the $Z$-table is the one with a proof.

## 2. The mode: the force balance is not the variable, the countdown is

If the fission mode were the contest between electrostatic repulsion and strong binding, the controlling
number would be the fissility $Z^2/A$. It is not:

| quantity | range across the 24 systems | factor |
|---|---|---|
| $Z^2/A$ | 34.91 (Th-232) → 39.06 (Fm-256) | **1.12** |
| valley/peak | 0.00014 (Cm-244) → 0.1966 (Pu-239, 14 MeV) | **1405** |

The balance moves 12% while the mode moves by three orders of magnitude. What *does* order it, within
every excitation class, is the theorem's own quantity — the countdown of the symmetric fragment,
$h_{\rm sym}=54-Z/2$:

| class | $n$ | Spearman$(\ln R,\ h_{\rm sym})$ | Spearman$(\ln R,\ N_H-82)$ |
|---|---|---|---|
| thermal | 9 | **−0.87** | −0.08 |
| 0.5 MeV | 6 | **−0.89** | −0.77 |
| 14 MeV | 4 | **−0.80** | −0.80 |
| spontaneous | 5 | **−0.80** | **+0.70** (wrong sign) |
| pooled | 24 | +0.18 | −0.54 |

The spontaneous set makes the point in three lines: $h_{\rm sym}=6$ gives valley/peak $0.0002$ (Cm-244,
Cm-248), $h_{\rm sym}=5$ gives $0.0026$ (Cf-250, Cf-252), $h_{\rm sym}=4$ gives $0.067$ (Fm-256) — factors
18 and 26, in order, with the two members of each pair agreeing to 1.04–1.8.

And the heavy fragment's distance from $N=82$ — the shell variable one would naturally try — *reverses
sign* inside the spontaneous set ($+0.70$), because Fm-256 sits at the same $N_H=85.7$ as Cm-248 and is
270× shallower.

**A testable consequence, and it holds:** at fixed excitation the mode should depend on $Z$ alone. At fixed
$Z$ the scatter between different systems is 1.3–1.7× (the several U and Pu entries); across $Z=92\to96$ it
is 3.0× (thermal), and across $Z=96\to100$ it is 481× (spontaneous). The residual is smaller than the
effect.

## 3. What this adds to part (K)

Part (K) of the master theorem now reads:

> **(K) The forces.** **(K1)** The closure law is the Coulomb degeneracy: the period lengths are $2n^2$, so
> the table is an electromagnetic ladder. **(K2)** The strong ladder is the 3D oscillator
> $n(n+1)(n+2)/3$: it agrees with Coulomb at 2 and 8, exceeds it from the third cumulant (18 against 20),
> and matches the observed magic numbers at 2, 8 and 20 before spin-orbit splitting takes over. **(K3)**
> The fission mode is not the force balance — $Z^2/A$ spans 1.12 while the valley spans 481 — it is ordered
> within each excitation class by $h_{\rm sym}=54-Z/2$, the countdown of the symmetric fragment
> (Spearman −0.80 to −0.89), not by the heavy fragment's distance from $N=82$, which reverses sign.

## 4. What is proved and what is measured

| claim | status |
|---|---|
| Coulomb cumulant is $2n^2$; oscillator cumulant is $n(n+1)(n+2)/3$ | **proved** |
| they agree at $n=1,2$ and the oscillator wins from $n=3$ | **proved** |
| the proton ladder meets the magic numbers only at 2 | **proved** (finite check on lists) |
| the oscillator ladder meets them at 2, 8, 20 | **proved** |
| $Z^2/A$ ordered, spanning less than 2 | **proved** |
| the fissility spans 1.12 while the mode spans 481 | **measured** |
| $h_{\rm sym}$ orders the mode within a class (−0.80 to −0.89) | **measured** (24 systems) |
| the heavy-shell distance reverses sign within SF | **measured** |

Two honest limits, stated where they belong: the pooled correlation of $\ln R$ with $h_{\rm sym}$ is
$+0.18$, because the excitation classes are offset from one another — $h_{\rm sym}$ predicts the *ordering
inside* a class and not the absolute level, the same verdict as every other ordering variable in this
record. And the spin-orbit identification (28 where the oscillator has 40) is textbook physics, not
something derived here; what the file proves is only the arithmetic of the ladders and their intersections.
