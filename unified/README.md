# One body — elemental peeling, Dirac time, VOTKP

Three Lean 4 developments that were kept in three repositories are built here as **one library**,
with the theorems they had in common reduced to one statement each and the interfaces between them
proved rather than asserted.

| leg | what it is | source | modules | declarations |
| :--- | :--- | :--- | :-: | :-: |
| **LoopWall** | elemental peeling: peel ratio `z`, reflection `Γ = (z−1)/(z+1)`, the wall `Γ² = ½`, the ledger | this repository, `LoopWall/` | 48 | 1136 |
| **DiracTime** | *The Dirac Time of the Gigantefermion*: predictive quotient, path ledger, common clock, phase silence, chiral pairing | `dirac-time-lean` | 18 | 100 |
| **VOTKP** | *VOTKP: The Vector of Traits Kept under Peeling*: Smith coordinate, peel steps as velocities, film echo, predictive quotient, the knot lemma | `votkp-lean` | 15 | 186 |
| **Bridge** | the interfaces — new in this merge | `unified/Bridge/` | 6 | 39 |
| **PrimeGap** | the twin/base key: ladder partition, twin types mod 30, air residue, merged quadruplets | `results/count-formulas.lean`, `results/digit-roles.lean` | 2 | 32 |
| **Found** | the six-direction round that audited the interfaces — new in this merge | `unified/Found/` | 6 | 125 |

Declarations are a parser count of `theorem`/`lemma` in those trees. The three repositories count
their own headline results differently (badges read 1209, 86 + 3 and 140), so the columns are not
comparable with those badges; they are comparable with each other.

## Build it

```bash
python3 scripts/build_unified.py          # dependency-ordered, writes .olean next to each source
LEAN_PATH=.:unified:$LEAN_PATH lean unified/Bridge/Audit.lean   # axiom audit of every new theorem
```

`unified/Unified.lean` is the single root. It imports all 48 LoopWall modules, 17 of the 18
DiracTime modules, all 15 VOTKP modules, the six `Found` files and the three bridges.
`DiracTime/UnitaryEntropy.lean` is copied but **not** in the root: it needs Physlib, which is not
installed on this VM. That is the one module of the three legs that this build does not check.

Every declaration added here passes `-DwarningAsError=true` and depends on `propext`,
`Classical.choice` and `Quot.sound` only — `unified/Bridge/Audit.lean` prints the audit for all of
them. The imported legs carry linter warnings from their own repositories; they compile, and this
merge does not rewrite other people's proofs.

## What the merge found

The full statement-by-statement map is [`MAP.md`](MAP.md). The short version:

**1. Two theorems were proved twice, and now once.** The predictive quotient is Section 2 of
*Dirac Time* and Theorem 3.1 of *VOTKP*; the Smith identity `(z−1)/(z+1) = tanh(½ log z)` is
`LoopWall/Ledger.lean:34` and `VOTKP/Smith.lean:42`. `Bridge.Quotient.unseen_eq_unobservable`
proves the two quotients are the same subspace (Cayley–Hamilton closes the gap between the finite
observability map and the infinite intersection), and `Bridge.Reflection.two_smith_identities`
puts the two proofs of the identity side by side. The ledger descent is proved twice as well —
`LoopWall/LedgerDescent.lean:144` for step lists, `DiracTime/PathLedger.lean:21` for an abstract
path type — and `Found.Ledger.peel_descent_iff` is the common specialisation.

**2. The wall is a quantised ledger value.** With `ℓ = log z` the ledger and `Γ = tanh(ℓ/2)`,
the wall `Γ² = ½` is exactly `|ℓ| = 2 log(1 + √2)` — the two signs being the two reciprocal wall
ratios (`Bridge.Reflection.wall_ledger_value`).

**3. The rate is the clock, and the wall time follows from it.** `Found.CommonClock` shows the
loop-wall flow `Γ' = (ω/2)(1−Γ²)` is the common-clock gap read as a peel: `ω = τ̇(Eⱼ − Eₖ)`. This is
the closest join in the merge — the `ω` of the peel papers is the `τ̇` of *Dirac Time*. The wall is
then crossed exactly once forward, at `|δ|·τ_wall = 2 artanh(1/√2) = log(3 + 2√2)`
(`forward_wall_time_mul_abs_gap`, `existsUnique_forward_wall_iff`), and a zero gap never reaches it.

**4. One involution lemma covers three developments.** `Bridge.Chirality.odd_involution_vanishes`
is the shared skeleton of `ChiralPairing` (`S T S⁻¹ = −T` kills odd moments), of θ (`θ(mirror K) =
−θ K`, so amphichiral knots have `θ = 0`), and of the reflection (`Γ(1/z) = −Γ z`). Its complement
is the blindness statement: every readout through `Γ²` is mirror-invariant, the wall is *not*
mirror-fixed, and `Found.Chirality` carries the even/odd decomposition that makes this exact.

**5. The double angle is the diagonal of the velocity law.** `LoopWall/Clock.lean:25` and
`VOTKP/Smith.lean:72` are the same identity at `a = b` (`Bridge.Reflection.tanh_double_eq_oplus`).

**6. Most wall crossings have no wall-crossing step.** The periodic table's scale atlas counts
91,768 windows of removal steps that exceed `3+2√2` in total, and **91,638 of them do so with every
constituent step inside the wall** — while none exceeds it on geometric mean. That is the
composition law, not a coincidence of the archive: `Bridge.Composition.composite_two_eq_oplus` shows
a window composes by VOTKP's velocity law `⊕`, `crosses_iff_ledger_sum` gives the exact criterion
(total ledger past `log(3+2√2)`), `two_halves_cross` is a minimal witness (two steps at `z = 5/2`
are each inside, the product `25/4` is outside), and `geomean_lt_wall` proves the mean can never
cross. The data layer and its census are in [`atlas/`](../atlas/README.md).

**7. The Ramanujan faces are the same peel steps.**  Each term of a gamma-quotient continued
fraction is a face with `Γ_n = x/√(x² + (2n−1)²)` and `z_n = (s+x)/(s−x)`;
`Bridge.Faces.faceRatio_eq_gam` proves it, `faceGamma_sq_eq_half_iff_odd` gives the wall as
`2n − 1 = x`, and `brouncker_first_face` is the exact `3 + 2√2`.  So **every odd `x` has a face
exactly on the wall**, not only Brouncker's.  The fraction's power law (`error ~ N^{−x}`) is the
ledger sum `Σ 2 artanh Γ_n ≈ x log N`, measured not proved.  See
[`ramanujan/`](../ramanujan/README.md).

**8. The negative result, and its limit.** In the scalar present-reading model `L = z·`, `R = id`,
the peel ratio is a *complete* predictive state: the quotient is one-dimensional for every `z`,
zero included (`Bridge.Quotient.peel_predictive_dim`), so the wall changes no predictive dimension
there (`wall_is_not_a_memory_transition`). **This is model-dependent, not intrinsic.**
`Found.PredictivePeel` shows two other linearisations of the same ladder that do separate the wall
— one by a wall-coded readout, one by a fixed surjective readout with an auxiliary wall-coded rate —
and a homogenised log ledger that jumps at `z = 1` instead. The honest statement is that the
elemental sources fix no `(L, R)`, so "the predictive dimension of the peel" is under-specified
until one is declared.

## What is not claimed

* **θ is not formalised.** No knot type, no Alexander polynomial, no Laurent polynomial invariant.
  What is formalised is the algebraic step from `θ(mirror K) = −θ K` to `θ K = 0`
  (`Bridge.Chirality.theta_vanishes_on_amphichiral`). The converse — VOTKP Conjecture 21 — is not
  a consequence, and `odd_does_not_imply_converse` exhibits an odd function that vanishes away from
  its fixed locus. The 78-of-78 census is evidence for the conjecture, not a proof of it.
* **The knot census is confirmed, not assumed.** Live KnotInfo release 2026.11.2 gives exactly
  78 amphicheiral prime knots through 13 crossings (47 negative + 30 fully + 1 positive), zero at
  11 and at 13 crossings, and the name set is identical to the 78 with `θ ≡ 0` in the VOTKP census.
  That settles the *data* side of the 78/78 agreement; the *converse* remains open.
* **One shapes claim is not reproducible.** The table's "every shape groups columns better than raw
  energies (0.05)" holds: circle 53/77, diamond 52/77, cube 48/77, simplex 60/77, raw energies
  4/77.  The same sentence's "no shape beats the circle by more than its bootstrap spread" does not:
  no bootstrap procedure or spread ships, and the observed simplex − circle gap is 7/77.
* **The table does not select the wall value.** Every step ratio in the archive leaves a band
  `(5.639665, 5.947101)` between the largest step inside the wall and the smallest outside; any
  cutoff in that band sorts the 3,570 steps identically, and `3+2√2` lies inside it. The table is
  consistent with the wall and cannot distinguish it from any value in a 5.2% band
  (`scripts/atlas_census.py` prints the interval).  The aggregate window counts do not narrow it:
  they are computed *from* the cutoff, so 91,638 at the wall against 91,486 at `c = 5.85` is a
  consequence of the value, not a measurement of it.
* **The physics bridge is out of scope**, exactly as `LIMITATIONS.md` says for the LoopWall leg and
  as the two companion repositories say for theirs. Nothing here derives a Hamiltonian, a force or
  an empirical number, and `Found.CommonClock` is an identification of rates, not a derivation of
  either one from a physical model.
* **Perfect reflection is a limit only.** `det p = 0` corresponds to `|Γ| = 1`, but for a positive
  peel ratio `|Γ| < 1` strictly, so the block determinant never vanishes
  (`Found.WallReadout.det_ne_zero_of_pos`).
* **`blockDet` is not `1 − Γ²`.** The bridge `1 − Γ² = 4 det p` is a statement about one two-channel
  block (`normalizedDet`); `blockDet` is the product over blocks and equals `(1−Γ²)ⁿ`. The first
  draft of this merge stated it for `blockDet`; `Found.WallReadout` refuted that and the map keeps
  the correction.

## Provenance

[`PROVENANCE.md`](PROVENANCE.md): the exact commits the two outside legs were copied from, what was
copied verbatim, and what was written here.
