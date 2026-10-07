<div align="center">

# Elemental Peeling and What the Boundary Retains — Lean proofs

**Machine-checked finite algebra behind the Elemental Peeling paper: what a specified removal takes away, what later records can recover, force recovery from readings, and the exclusion certificates of the combined peel.**

[![Lean proof check](https://github.com/dicipler-pixel/elemental-peeling-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/elemental-peeling-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-88-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley

</div>

---

## Start here

| If you want to… | Open |
| :--- | :--- |
| Know exactly what is **not** proved | [`LIMITATIONS.md`](LIMITATIONS.md) |
| Check where every file came from | [`PROVENANCE.md`](PROVENANCE.md) |
| See the statements that must be rejected | [`FalseControls/`](FalseControls/) |

## What the library contains

| Subject | File | Theorems |
| :--- | :--- | :-: |
| **Elemental foundations**: the original PR #17 layer (the Peirce cross term and its commutation criterion, the two-site transmission and its distinct later values, the first-order remainders, no conductance-only predictor) plus the V4 additions: joint records, the exact later gap and robustness margins, the impossibility of a common-record predictor between the two declared models, and the scalar boundary ledger (the inverse chord identity and penalty, and one worked instance, energies `10` and `14` against their mean `12`, where averaging before inverting underestimates) | [`ElementalFoundations`](ElementalFoundations.lean) | 30 |
| **Force recovery**: exact three-force recovery, unknown-offset four-reading recovery, deterministic error-combination bounds | [`ElementalForceRecovery`](ElementalForceRecovery.lean) | 14 |
| **Boundary ledger**: resolved versus common-floor comparisons for any finite family, and their quadratic-form version | [`ElementalBoundaryLedger`](ElementalBoundaryLedger.lean) | 5 |
| **Exclusion and a common retained coordinate**: the two-orbital Gram determinant is the squared antisymmetric amplitude; same-spin coincidence is forbidden while distinct samples are not; one retained coordinate drives two readouts; equal first-observer records do not fix the next filter record; the zero-time force-memory coefficient | [`PauliMemory`](PauliMemory.lean) | 17 |
| **The hypersurface layer**: two-sided boundary reduction with rectangular blocks and frame covariance; a declared quasistatic Hall model whose power is `σ(x² + y²)`, its incremental form diagonalized, with the exact negative witness when `2σ < c`; scalar boundary numerators and scope controls (the source headers of these files still read `uncompiled candidate`; they are checked here, see [`PROVENANCE.md`](PROVENANCE.md)) | [`Hypersurface/`](Hypersurface/) (`Boundary`, `Hall`, `ScopeControls`) | 22 |
| | **Total** | **88** |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: five control files, holding six deliberately false statements, must fail
   to compile, for a mathematical reason: a false later-transmission equality and an unsafe
   mean-before-inversion inequality (together in `FalseControl.lean`, so its rejection shows
   that at least one of the two is rejected), equal futures from equal instantaneous readouts, a
   positive same-spin pair density at coincidence, a response equality that drops the exterior
   self-energy term, and nonnegativity of the Hall incremental form at `σ = 1`, `c = 3`, where
   `2σ < c`.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The paper

*Elemental Peeling and What the Boundary Retains*, Jeromie Beasley. The Zenodo DOI will be added
here once the paper is deposited.

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released under the [MIT License](LICENSE) and the written text under [CC BY 4.0](LICENSE-CC-BY-4.0.md); see [`LICENSING.md`](LICENSING.md). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
