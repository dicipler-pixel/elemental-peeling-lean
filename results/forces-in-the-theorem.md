# The three forces in the theorem

The weak-force reading of the depth was productive, so here is the rest of the assignment. Each force
gets the coordinate whose *measured* behaviour matches it on the same four axes — coupling, range,
exclusivity, and what it carries — and each assignment comes with a number rather than an analogy.

## 0. The assignment

| force | in the theorem | coupling | range | the evidence |
|---|---|---|---|---|
| **electromagnetic** | the closure ladder itself, $C(m)=\sum 2n^2$ | exact | infinite | the period lengths **are** $2n^2$: $L(2),L(4),L(6)=2\cdot2^2,2\cdot3^2,2\cdot4^2$ (proved) |
| **strong** | the neutron ladder, and the binding (mass excess) | O(1) | $10^{-15}$ m, saturating | the magic numbers are **not** $2n^2$: 20 and 28 are not twice a square (proved) |
| **weak** | the depth inside a crossing | $1/35$ | one step | $I/H=0.0448/1.568$; memory 2.5 points at lag 1, 0.7 at lag 2 |

The first line is the one that turns the analogy into an identification: **the table's closure law is the
Coulomb degeneracy.** $C$ is the partial sum of $2\lceil(m+1)/2\rceil^2$, which is $2n^2$ — the hydrogenic
count, i.e. the electromagnetic ladder of a $1/r$ potential with no spin-orbit. That is not a metaphor;
it is what "no $1/r$" means in the theorem. The record's `physics.md` already says the widths and
capacities are derived from $2l+1$ states times two spins and the Coulomb degeneracy $\sum(2l+1)=n^2$.
Put in the language of forces: **the Light Bridge is an electromagnetic object.**

## 1. Why the strong force is *not* that ladder — and where it is

The strong force is the one that would have to give a *different* ladder, and the record already has the
proof that it does. The neutron closures are the magic numbers

$$2,\ 8,\ 20,\ 28,\ 50,\ 82,\ 126,$$

and **20 and 28 are not twice a square** (proved: `strong_ladder_differs`), where the proton values at
the same indices are 18 and 32. A $2n^2$ ladder is Coulomb; the nuclear potential with its strong
spin-orbit is not, so the neutron axis has a ladder the Light Bridge theorem cannot span. That is exactly
what the second-coordinate note found empirically — the two ladders share only the term 2 — and this is
the reason.

The strong force's second appearance is the one part (J) already isolates: **the binding is the mass
excess**, the depth of the well, which the table cannot price. A mass law linear in $Z$ misses it by 44×
and identically for every split. So:

> the strong force is the neutron ladder plus the binding — the two things the proton-count table is
> structurally unable to hold.

## 2. The force balance does not set the mode — the shells do

If fission were a contest between the electrostatic repulsion ($\propto Z^2$) and the strong binding
($\propto A$), the controlling number would be the fissility $Z^2/A$. Measured over the whole set of
systems used in this record:

| quantity | range across the fissioning set | factor |
|---|---|---|
| fissility $Z^2/A$ | 34.91 (Th-232) → 39.06 (Fm-256) | **1.12** |
| valley/peak, spontaneous | 0.00014 (Cm-244) → 0.0673 (Fm-256) | **481** |
| valley/peak, thermal | 0.00145 (U-235) → 0.00491 (Pu-239) | 3.4 |

Inside the spontaneous set the force balance moves by 5% while the mode moves by a factor 481. **So the
mode of fission is not the force balance: it is the shell structure** — the strong force's ladder acting
through $N=82$ and the closure $C(5)=54$. (Proved: `fissility_band`, `fissility_narrow` — the ordering of
$Z^2/A$ and the fact that it spans less than a factor 2.)

This is worth stating plainly because it corrects a natural expectation: $Z^2/A$ is what decides
*whether* a nucleus fissions, and it does not decide *how*.

## 3. The full assignment, with what each force can and cannot be asked

| force | coordinate | what it can be asked | what it cannot |
|---|---|---|---|
| EM | $Z$, the closure ladder $2n^2$, the capacities | where the cells are, how many, the closure | anything about neutrons |
| strong | $N$ (magic numbers), the mass excess | the binding, the well's depth, the fission mode | any closed form on the $Z$ axis — its ladder is not $2n^2$ |
| weak | the depth (the multiple of 10), and $\beta$ as the unit step in $Z$ | the groove, the flavour-changing step | anything global: $1/35$ |

And the two structural facts that make the assignment non-arbitrary:

* **the couplings are separated by design**: exact (EM, the digit fixes the gap mod 10), $O(1)$ but
  ladder-changing (strong), $1/35$ (weak);
* **the ranges are separated by design**: infinite (EM occupies the whole ladder), saturating at the
  nuclear radius (strong), one step (weak).

So the theorem now says what each coordinate is *for*, in the only language that can be tested: which
quantity it carries and how strongly it couples to the others.

## 4. What this adds, and what it does not

**Adds:** a third and fourth way to reach the same conclusion the record has reached from the coordinate
side — that the proton ladder is $2n^2$ and the neutron ladder is not; that the depth is nearly decoupled;
that energy is not in the table. The force language makes the *reason* visible: each coordinate is owned
by a different force, with a different coupling and range, and the theorem is the statement that the
proton-side one has a closed form.

**Does not add:** any new prediction. Nothing here is a law; every number in §2 is measured, every
identity in §1 is proved, and the assignments are identifications — the weakest kind of claim in this
record — offered because they organise what is already there. In particular the $1/31.7$ against $1/35$
coincidence of the previous note should not be promoted: it is a numerical echo, not a derivation.
