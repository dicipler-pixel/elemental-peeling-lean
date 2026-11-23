# Repairs before any formalization note

From four referee reports (swarm `smwsg6vno`, all accepted) plus checks run locally at `36322fb`.
Ordered by how much a referee would care. Nothing here touches a proof's validity; every item is
either a coverage hole in the audit, a prose claim the artifact does not carry, or a build gate the
repo does not pass.

## 1. The axiom audit does not cover `lemma`

`scripts/verify.py:51-52` matches `theorem` and not Lean's synonym `lemma`. So 23 named declarations
— all in `LoopWall/PeelDynamics.lean:60-293` — never appear in the audit that `README.md` describes as
covering "every named theorem". They are sound (re-audited separately: same three axioms), but the
coverage claim is broader than the regex.

Fix: `(?:theorem|lemma)` in `THEOREM_RE`; then `scripts/config.json` `expected_theorems` 1209 → **1232**,
and the count in four places: README badge, README Total row, `PROVENANCE.md`, verifier inventory.

## 2. `-DwarningAsError=true` fails on 17 of 67 files

Full sweep, `LEAN_PATH=.:$LEAN_PATH lean <file>` per source, counting warning lines:

| file | lines |
| :-- | :-: |
| `LoopWall/QuantumGeometricTensor.lean` | 20 |
| `LoopWall/TwoFieldAction.lean` | 14 |
| `LoopWall/TwoLevel.lean` | 10 |
| `LoopWall/BridgeUnderdetermination.lean` | 10 |
| `Hypersurface/ScopeControls.lean` | 9 |
| `LoopWall/FisherMatrix.lean` | 7 |
| `LoopWall/Rung.lean` | 6 |
| `LoopWall/Oscillator.lean` | 6 |
| `LoopWall/Schrodinger.lean` | 5 |
| `LoopWall/ColourWheel.lean` | 4 |
| `LoopWall/Archive.lean` | 4 |
| `LoopWall/A2.lean` | 4 |
| `Hypersurface/Boundary.lean` | 4 |
| `PauliMemory.lean` | 2 |
| `LoopWall/SpacingLaw.lean` | 2 |
| `LoopWall/Elements.lean` | 2 |
| `LoopWall/Quaternions.lean` | 1 |

110 warning lines; the sequencing linter reports twice, so roughly 60–70 distinct sites. Fifty of the
67 sources are clean. Five linter classes:

| linter | what it means | where |
| :-- | :-- | :-- |
| `unnecessarySeqFocus` | `<;>` where `;` would do | BridgeUnderdetermination:45(×2),71,73,97; QuantumGeometricTensor; TwoFieldAction; TwoLevel; PauliMemory:182 |
| `unusedVariables` | hypothesis never referenced — **substantive** | Archive:1852-1853; TwoFieldAction; QuantumGeometricTensor |
| `unusedSimpArgs` | a `simp` argument does nothing | QuantumGeometricTensor; TwoLevel |
| `unreachableTactics` | a tactic never executes — the goal was already closed | ScopeControls:15,38 |
| `unusedSectionVars` | auto-included section variable unused | FisherMatrix; Boundary:25,29,33,41 |

The last three are worth reading rather than silencing: `unusedVariables` at `Archive:1852-1853`
(`hc2`, `hn2`) shows `twoFace_margin_C_N` needs only the *lower* endpoints of both boxes — the theorem
is stronger than its statement, so disclose the strengthening instead of prefixing underscores.
`unreachableTactics` means a step the author expected to do work was doing none.

Fix: `;` for `<;>`, drop or `_`-prefix the unused binders, delete the dead `simp` arguments; a
`set_option linter.X false` is acceptable only where the warning is a false positive, and none of
these are.

## 3. `LIMITATIONS.md` claims a theorem that does not exist

`LIMITATIONS.md:35-40`: "and that every central ratio lies in its own interval". `ratioBoxes`
(`Archive.lean:901`) stores endpoint pairs only; `boxOK` evaluates the quadratic at those endpoints;
`ratioBoxes_no_crossing` (`:1819-1826`) never mentions a central value. There is no such theorem among
the 31 theorems and 5 defs in the file — the only `central` theorem is `twoFace_margin_C_N_central`,
which is the carbon/nitrogen margin.

The claim is true of the current CSV: an exact `Fraction` check of all 3,614 cases found zero
violations, and the generator reads the stored 12-decimal `z`, not the energies
(`gen_archive_lean.py`, `load()`). So reword to "checked by the generator, not theoremized".

## 4. The variational module has no first variation

`LoopWall/UniformLogRatio.lean:211` defines `variationalAction`; it is used nowhere else in the
repository. `eulerLagrangeResidual` is defined separately at `:214-217`, and
`motion_eulerLagrange_eq_zero_iff` (`:320-325`) is `rw […]; exact sub_eq_zero` — residual = 0 rewritten
into the ODE — under the docstring "Stationarity of the corrected motion action is exactly the stated
ledger ODE". The equivalence is the standard calculus of variations, but it is not proved here.
Either state and prove the first-variation lemma, or reword the docstring to "the residual vanishes".

## 5. `Observer.lean` header contradicts its theorem

`LoopWall/Observer.lean:6-7` says the criterion is "`R` vanishes on `ker R`". The theorem at `:38-41`
is that `ker R` is invariant under `L`. Everything vanishes on its own kernel; the content is the
invariance. One-line header fix.

## 6. A 117-theorem file cannot be regenerated

`LoopWall/OpeningMap.lean` names `gen_opening_map_lean.py` as its generator, and that script is not in
this repository (`PROVENANCE.md:25` says it belongs to an upstream package). 4,297 lines and 117
theorems that a reader cannot rebuild from what is checked in. Either check the script in or mark the
file as not reproducible here.

## 7. `LIMITATIONS.md` is stale in the safe direction

`LIMITATIONS.md:99-100` says the step "an additive, normalised, channel-composing readout must be a
multiple of a logarithm … is not formalized as a functional-equation uniqueness theorem". The fifth
round closed it: `CompositionBridge.eq_const_mul_log_of_append_additive` (`:524`) and
`COVERAGE.md:169` cites it. Move the sentence; do not weaken the theorem to restore agreement.

## What the note should carry that the repo does not have

1. **Prior art, stated first.** `Gamma' = (omega/2)(1-Gamma^2)` for a reflection coefficient is
   Walker & Wax, *J. Appl. Phys.* **17** (1946) 1043-1045, DOI 10.1063/1.1707673, whose abstract is
   exactly that first-order equation. `artanh x = (1/2)log((1+x)/(1-x))` is DLMF 4.37.24; `tanh' = sech^2`
   is DLMF 4.34.3; the log Cauchy equation is Kuczma Ch. 13; `r_4(1)=8`, `r_4(5)=48` is Jacobi.
2. **The stronger non-discrimination theorem.** Under the supplied uncertainty boxes, *every* cutoff
   in `[5.808010272529, 5.866514230542)` preserves all 3,637 classifications (binding rows Ag0 upper,
   Si0 lower). `3+2sqrt2 = 5.828427` lies inside. The repo's two rational windows are weaker because
   they ignore the error bars; this one does not.
3. **The window theorem is stronger than a count.** `ordinary_cutoff_window` (`Archive.lean:824-825`)
   is filter-*list* equality, so the same elements in archive order are selected, not merely the same
   number.
4. **The generated archive is byte-reproducible.** Regenerating from `data/H_to_At_thresholds.csv`
   gives SHA-256 `5d1270991e24e76f8efeba2d1b5c156f7ca891e375c82900306f5ceee2447bb4`, 232,253 bytes,
   identical to the checked-in file.
5. **The ladder is not the flow.** Along a real ladder the peel ratio is `z_k = 1 + c/k` with
   `c = 1.44` (pooled median over 84 elements, `k >= 2`), i.e. `Gamma_k ≈ 0.7/k`, which is the
   `Gamma' = -mu*Gamma^2` Riccati, not `Gamma' = (omega/2)(1-Gamma^2)`; fitting the tanh clock in the
   removal index gives median `R^2 = 0.035`. Eight of 3,570 steps exceed `3+2sqrt2`, all core openings
   at `k <= 4`, and that is the whole empirical content. See `results/peel-ladder-check.md`.
