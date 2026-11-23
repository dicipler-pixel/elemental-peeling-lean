# The map

Every statement below is a declaration in this tree. Line numbers are as of the merge commit.
Declarations are counted by a parser over `theorem`/`lemma` and are quoted only to show the shape
of the merge, not as a quality measure.

## 1. What each leg is for

| leg | the object it owns | the question it answers |
| :--- | :--- | :--- |
| **LoopWall** | `z = IE_{k+1}/IE_k`, `Γ = (z−1)/(z+1)`, the wall `Γ² = ½`, the determinant ledger | which side of the wall a removal ladder falls on, and what a ledger readout can be |
| **DiracTime** | `N∞ = ⋂ ker(R Lⁿ)`, the predictive quotient, path ledgers, common clock, phase silence | what a state must remember to predict every future reading |
| **VOTKP** | Smith coordinate, velocity addition `⊕`, film echo, predictive quotient, knot lemma | the peel shape as a reflection coordinate, and peel steps as velocities |
| **PrimeGap** | primes on the two ladders `1 mod 6` / `5 mod 6`, twin starts, handoff air, merged quadruplets | which twin/base-key statements are arithmetic and which are measured (`results/count-formulas.md`) |

## 2. Statements proved more than once

| statement | proof A | proof B | joined by |
| :--- | :--- | :--- | :--- |
| predictive quotient: `N` = what no future reading sees, `dim V/N = rank 𝒪` | `unified/DiracTime/PredictiveQuotient.lean:31` (`unobservable`, infinite intersection) | `unified/VOTKP/Observer.lean:66` (`unseen`, kernel of the finite observability map) | `Bridge.Quotient.unseen_eq_unobservable` — Cayley–Hamilton (`VOTKP.Observer.horizon`) is exactly the bridge |
| Smith identity `(z−1)/(z+1) = tanh(½ log z)` | `LoopWall/Ledger.lean:34` (`gam_eq_tanh_half_log`) | `unified/VOTKP/Smith.lean:42` (`smith_identity`) | `Bridge.Reflection.two_smith_identities` |
| `tanh` addition | `LoopWall/Clock.lean:30` (`tanh_double`, the `a = b` case) | `unified/VOTKP/Smith.lean:72` (`tanh_add'`, the full `⊕` law) | `Bridge.Reflection.tanh_double_eq_oplus` |
| ledger descent: endpoint potential ⇔ every loop silent | `LoopWall/LedgerDescent.lean:144` (step lists on a symmetric relation) | `unified/DiracTime/PathLedger.lean:21` (abstract path type) | `Found.Ledger.peel_descent_iff` — the common specialisation on positive peel readings, and `Bridge.Reflection.tanh_ledger_descent` for the Γ form |

These are not cosmetic overlaps. The predictive quotient is the same theorem with two different
proofs of the finite-horizon step; the Smith identity is the definition both developments start
from; the descent theorem is the same cocycle argument in two encodings.

## 3. New bridges — `unified/Bridge/` (39 theorems, 2 definitions)

### `Reflection.lean`

| declaration | what it says |
| :--- | :--- |
| `log_wall_ratio` | `log(3 + 2√2) = 2 log(1 + √2)` |
| `wall_ledger_value` | the wall `Γ² = ½` is exactly `ℓ = ±2 log(1 + √2)` in the ledger `ℓ = log z` |
| `tanh_ledger_descent` | Dirac Time's `descent_iff` read through `Γ = tanh(ℓ/2)`: Γ is an endpoint function iff every loop is silent |
| `one_sub_gam_sq_eq_four_det` | `1 − Γ² = 4 det p` for a normalised two-channel block |
| `wall_iff_share_det` | wall `Γ² = ½` ⇔ `det p = 1/8` |
| `gam_sq_eq_one_iff_det_zero` | `|Γ| = 1` ⇔ `det p = 0` (a limit only — see §5) |
| `two_smith_identities` | the two independent proofs of the Smith identity, side by side |
| `tanh_double_eq_oplus` | the double-angle identity is the diagonal of `⊕` |

### `Chirality.lean`

| declaration | what it says |
| :--- | :--- |
| `odd_involution_vanishes` | the shared lemma: odd under an involution + fixed point ⇒ zero |
| `theta_vanishes_on_amphichiral` | the θ schema as an instance — one direction only |
| `odd_does_not_imply_converse` | `x ↦ x³ − x` is odd and vanishes at `1 ≠ −1`: oddness never gives the converse |
| `gam_mirror`, `even_readout_blind`, `wall_indicator_blind` | Γ is odd under `z ↦ 1/z`; everything read through `Γ²` is mirror-blind |
| `wall_is_chiral` | the wall ratio is not mirror-fixed and `Γ ≠ 0` there |
| `mirror_fixed_iff_gam_eq_zero` | the only mirror-fixed peel ratio is `z = 1`, where `Γ = 0` |

### `Quotient.lean`

| declaration | what it says |
| :--- | :--- |
| `unseen_eq_unobservable` | the two predictive quotients are one subspace |
| `same_future_iff_votkp` | identical futures ⇔ the difference is unobservable, in both notations |
| `peelL`, `peelR`, `peelL_apply`, `peelR_apply` | the peel ladder as a linear readout system |
| `peel_unobservable_eq_bot` | for `z ≠ 0` nothing is forgotten |
| `peel_predictive_dim` | in the scalar present-reading model the predictive quotient is one-dimensional, for every `z` |
| `wall_is_not_a_memory_transition` | in that model the wall and the neutral ratio have the same predictive dimension |
| `peel_closes` | the present peel ratio closes on its own at every `z` |

### `Composition.lean`

| declaration | what it says |
| :--- | :--- |
| `wall_pos` | `3 + 2√2 > 0` |
| `log_prod_eq_sum` | a window's ledger is the sum of its steps' logarithms |
| `composite_reflection_eq` | a window's reflection is `tanh((Σ log zᵢ)/2)` |
| `composite_two_eq_oplus` | two steps compose by the velocity law: `Γ(z₁z₂) = Γ(z₁) ⊕ Γ(z₂)` |
| `crosses_iff_ledger_sum` | a window crosses the wall exactly when its total ledger exceeds `log(3+2√2)` |
| `window_at_wall_ledger` | at the wall, the window ledger is `±2 log(1+√2)` |
| `two_halves_cross` | two steps at `z = 5/2` are each inside the wall; the product `25/4` is outside |
| `geomean_lt_wall` | the geometric mean of inside steps is inside |
| `composition_crosses_mean_does_not` | the atlas's two headline facts — 91,638 crossings, 0 on the mean — as one theorem |

The data this describes, and the census that reproduces the atlas's counts, are in
[`atlas/`](../atlas/README.md) and `scripts/atlas_census.py`.

### `Faces.lean`

| declaration | what it says |
| :--- | :--- |
| `faceRatio_pos` | a face's ratio `z_n` is positive |
| `faceRatio_eq_gam` | `(z_n − 1)/(z_n + 1) = x/√(x² + (2n−1)²)` |
| `faceGamma_sq_eq_half_iff` | `Γ_n² = ½ ⇔ (2n−1)² = x²` |
| `faceGamma_sq_eq_half_iff_odd` | for positive `x`, `Γ_n² = ½ ⇔ 2n − 1 = x`: every odd `x` has a wall face, at most one |
| `faceGamma_lt_one` | no face reaches perfect reflection |
| `brouncker_first_face` | at `x = 1` the first face is at the wall with `z₁ = 3 + 2√2` |

## 4. The six-direction round — `unified/Found/` (125 theorems)

| file | n | the strongest statements |
| :--- | :-: | :--- |
| `Ledger.lean` | 22 | `peel_descent_iff` (literal instance of `descent_iff`); `peelLedger_eq_log_sub` (the ledger telescopes with potential `log`); `peelReflection_eq_endpoint_gam`; controls `chiral_ledger_has_unsilent_loop`, `scalar_composition_ledger_not_reversal_odd` |
| `Chirality.lean` | 16 | `laurent_odd_vanishes_on_fixed` (the θ value type, `LaurentPolynomial (LaurentPolynomial ℚ)`); `evenPart`, `evenPart_of_odd`; `mirror_involutive`; `wall_mirror_blind`; `odd_zero_need_not_be_fixed` |
| `Phase.lean` | 3 | `silent_sector_iff_mod_one` (the paper's integer criterion is vanishing in `AddCircle 1`); `cyclic_descent_iff_silent_sector`; control `real_offset_zero_not_necessary` |
| `CommonClock.lean` | 24 | `hasDerivAt_gapPeel` (`Γ' = (δ/2)(1−Γ²)` with `δ = μⱼ − μₖ`); `gam_gapRatio`; `gapPeel_eq_wall_iff`; `artanh_wall`; `existsUnique_forward_wall_iff`; `forward_wall_time_mul_abs_gap` (`|δ|·τ_wall = 2 artanh(1/√2)`) |
| `PredictivePeel.lean` | 40 | `predictiveDimension_peel` (dimension 1 for every real `z`, including `0`) and `predictiveDimension_peel_at_upper_wall`; `wallGated_counterexample` (dimension 0 exactly at `Γ² = ½`); `wallPair_counterexample` (fixed surjective readout plus an auxiliary wall-coded rate: 1 at the wall, 2 at `z = 1`); `predictiveDimension_logLedger` (the homogenised ledger jumps at `z = 1`, not the wall) |
| `WallReadout.lean` | 20 | `four_det_eq_one_sub_gam_sq` (with its true hypotheses); `det_eighth_iff_gam_wall`; `blockDet_eq_pow_of_constant_balance`; `det_ne_zero_of_pos`; `wall_ratios_iff_abs_log`; `lower_wall_refutes_upper_only_without_branch` |

## 5. Refutations and corrections kept in the body

These are part of the merge, not footnotes. Each is a checked statement.

1. **`blockDet` is not `1 − Γ²`.** `Found.WallReadout.two_wall_blocks_refute_single_block_identity`
   exhibits two wall blocks with `blockDet = 1/4 ≠ 1/2`. The bridge `1 − Γ² = 4 det p` is about one
   block (`normalizedDet`); over `n` blocks `blockDet = (1−Γ²)ⁿ`
   (`blockDet_eq_pow_of_constant_balance`). The first draft of this merge overstated it.
2. **Perfect reflection is unattained.** `|Γ| = 1 ⇔ det p = 0`, but for `z > 0`, `|Γ| < 1`
   (`Found.WallReadout.abs_gam_lt_one_of_pos`), so `det p ≠ 0` (`det_ne_zero_of_pos`).
3. **Oddness does not give the converse.** `Bridge.Chirality.odd_does_not_imply_converse`. This is
   the guard in front of VOTKP Conjecture 21: the 78-of-78 agreement is evidence.
4. **The wall has two branches.** `Found.WallReadout.lower_wall_refutes_upper_only_without_branch`
   and `gam_wall_iff_upper_root_of_one_le`: on `0 < z < 1` the lower root is the wall, and a
   statement quoting only `3 + 2√2` needs the branch hypothesis.
5. **A zero gap never reaches the wall.** `Found.CommonClock.existsUnique_forward_wall_iff` is an
   iff: one forward crossing for every `δ ≠ 0`, none at `δ = 0`.
6. **The predictive dimension is not intrinsic.** `Found.PredictivePeel` constructs linearisations
   of the same ladder whose quotient dimension does change at the wall, and one whose dimension
   changes at `z = 1` instead. So `Bridge.Quotient.wall_is_not_a_memory_transition` is a statement
   about the scalar present-reading model only; the sources fix no `(L, R)`.
7. **The real offset need not vanish.** `Found.Phase.real_offset_zero_not_necessary`: the silence
   criterion is integrality, not vanishing of the real offset.

### The prime-gap leg

`unified/PrimeGap/` holds the two Lean files of the twin/base-key work, copied byte-identically from
`results/` (the build driver fails if they diverge). They prove the arithmetic core: every prime
above 3 is on exactly one ladder (`P = B + K + 2`), every twin start above 3 is on the 5-ladder,
every twin start above 5 is `11`, `17` or `29 mod 30`, every handoff air is `4 mod 6`, and a
four-prime merge can only start at `11 mod 30`. The counts themselves — 50,847,534 primes,
27,412,679 twins to `10^10`, 3,424,503 handoffs — are measurements, not theorems, and
`results/count-formulas.md` says which is which.

## 5b. External checks

| claim | tool | result |
| :--- | :--- | :--- |
| 12,965 prime knots through 13 crossings, 78 amphicheiral, none at 11 or 13 | KnotInfo 2026.11.2 | reproduced; name set identical to the 78 with `θ ≡ 0` in the VOTKP census (47 negative + 30 fully + 1 positive amphicheiral) |
| every shape groups columns better than raw energies (0.05) | shapes data embedded in the v2.2 table | reproduced: circle 53/77, diamond 52/77, cube 48/77, simplex 60/77, raw 4/77 |
| no shape beats the circle by more than its bootstrap spread | — | **not reproducible**: no spread ships; observed simplex − circle = 7/77 |
| Ramanujan face angles and power-law exponents | the session's own `checker/chk1.py` | reproduced (19.05°→18.52, 15.28°→15.27, 8.06°→8.05, 2.80°→2.79; exponents 0.49 / 1.00 / 3.00 / 9.9995) |
| `error × N^x → 4/π²` at `x=1`, `→ 1/4` at `x=3` | `scripts/ramanujan_faces.py` | reproduced to six digits; neither is derived |

## 6. The paper's Lean appendix against the tree

*What the Peel Keeps* v1.2.2, Appendix A, names four Lean files and 49 theorems. Every file count
and every named declaration resolves in this tree:

| appendix | file here | appendix says | found |
| :--- | :--- | :-: | :-: |
| `LoopWall.lean` | `LoopWall/Elements.lean` | 140 theorems, core only | 140 declarations, and the file has no imports |
| `OpeningMap.lean` | `LoopWall/OpeningMap.lean` | 117 theorems | 117 |
| `lean/TwoFaceForms.lean` | `LoopWall/TwoFace.lean` | 3 theorems | 3 |
| `russell/.../BoundaryAgreement.lean` | `LoopWall/BoundaryAgreement.lean` | 11 theorems | 11 |
| the 49 theorems named in the appendix's table | — | — | 49 of 49 found as declarations |

So the paper and this library are the same work, statement for statement. Two packaging
mismatches, neither mathematical:

1. The appendix calls `LoopWall/Elements.lean` "`LoopWall.lean`". The repository's `LoopWall.lean`
   is the import hub, not the 140-theorem file.
2. The Zenodo package does **not** contain the `lean/` directory or the `run_checks.sh` that
   Appendix A tells the reader to run. The files exist in `votkp-lean` under
   `research/2026-11-20-element-paper-loop-wall/lean/` — the `lean` field of `ptable_data.json`
   points there — but the package does not stand alone.

## 7. Where the merge stops

| not in this tree | why |
| :--- | :--- |
| θ as a knot invariant: knot type, diagram, Alexander polynomial, the two-variable Laurent polynomial | only the algebraic schema is formalised (`Bridge.Chirality.theta_vanishes_on_amphichiral`). The 78-knot census is a computation in the VOTKP repository, not a theorem here |
| VOTKP Conjecture 21 (`θ = 0 ⇒ amphichiral`) | open; the merge says only that oddness cannot prove it |
| the physics bridge of any leg | `LIMITATIONS.md` (LoopWall), `dirac-time-lean/LIMITATIONS.md`, `votkp-lean/LIMITATIONS.md` |
| `DiracTime/UnitaryEntropy.lean` | needs Physlib, not installed here; copied but outside the root |
| the rest of the 55-repository corpus | out of scope; the corpus map in `p-1a2a89…/harness/CORPUS_MAP.md` is the index to it |

## 7. Build and audit

```bash
python3 scripts/build_unified.py
LEAN_PATH=.:unified:$LEAN_PATH lean unified/Bridge/Audit.lean
```

`Bridge/Audit.lean` prints 24 lines, every one `[propext, Classical.choice, Quot.sound]`. The
`Found` files were accepted after the same check by the referee round: each compiles with
`-DwarningAsError=true` and contains no `axiom`, `sorry`, `admit` or `native_decide`.
