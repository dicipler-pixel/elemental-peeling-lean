# Provenance of the merged tree

## The three legs

| tree | source | commit | how it got here |
| :--- | :--- | :--- | :--- |
| `LoopWall/` | this repository, branch `open-math/repair-3-to-6-claims` | `b1f8add2f5dd3e506860225457afd3d42b733871` | already present; not copied |
| `unified/DiracTime/` | local `dirac-time-lean` checkout, project `p-472749bb…` | `69f29a228a105986133f8e05d313d059b496b6ff` | copied verbatim, 18 modules |
| `unified/VOTKP/` | `github.com/dicipler-pixel/votkp-lean` | `fa9f8ea93a1f3c9c9b6428a41bce378e7a9484df` | shallow clone, copied verbatim, 15 modules |

`DiracTime/UnitaryEntropy.lean` is copied but kept out of `unified/Unified.lean`: it imports
Physlib, which is not installed on this VM. That is the only module under `unified/` that the
build does not elaborate.

`votkp-lean`'s `Showcase.lean`, `Showcase_WithProofs.lean`, `peel-atlas/` and `two-trees/` are not
copied. The first two state the same results as `VOTKP/` in a second form and are not part of this
build; the last two are separate documents in that repository. Leaving them out keeps one root,
all of it checked.

## What was written here

| tree | authored | status |
| :--- | :--- | :--- |
| `unified/Bridge/` | this merge | new, 24 theorems + 2 definitions, all audited |
| `unified/PrimeGap/` | `results/count-formulas.lean`, `results/digit-roles.lean` (working copies in this repository) | copied verbatim; the build driver fails if the copies diverge |
| `unified/Found/` | the six-direction round `smwt0zi0i` (members m1–m6) | 6 files, accepted after recompilation; copied with namespaces intact |
| `scripts/build_unified.py` | this merge | dependency-ordered build driver |
| `unified/README.md`, `MAP.md`, this file | this merge | prose |

The `Found` files keep their own namespaces (`LedgerInterface`, `ChiralityInterface`, `Interface`,
`CommonClockPeel`, `ElementalPeeling.LoopWall.WallReadoutInterface`). Renaming them would break the
`file:line` citations in the round's reports; they are imported by `Unified.lean` as they are.

## What was modified

Nothing in the three legs. No proof in `LoopWall/`, `unified/DiracTime/` or `unified/VOTKP/` was
edited, and their linter warnings are left as their repositories have them. The strict gate
(`-DwarningAsError=true`) is applied to the files written here, not to imported code.

## Not done

* No commit, no push, no pull request. The tree is on disk in this project only.
* No independent-kernel replay (`leanchecker`) of the merged root; the axiom audit in
  `Bridge/Audit.lean` is the check that was run.
* No Physlib, so `UnitaryEntropy` is unverified here.
