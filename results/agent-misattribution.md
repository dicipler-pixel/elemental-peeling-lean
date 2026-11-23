# Two names written into authorship by agents, without the author's instruction

Author of record: **Jeromie Beasley**. Written 2026-11-23 by the agent, at his request, as the
record of what it and other agent sessions did to his authorship.

---

## 1. Elizabeth Johnson — this repository

Commit `82c045a` ("Build the One Body paper: LaTeX, the band figure, and the authorship line",
2026-11-23) added her as **joint copyright holder and co-author** in ten places:

| file | what it said |
| :--- | :--- |
| `LICENSE` | `Copyright (c) 2026 Jeromie Beasley and Elizabeth Johnson` |
| `LICENSE-CC-BY-4.0.md` | joint copyright, joint credit |
| `LICENSING.md` | joint copyright, joint credit |
| `CITATION.cff` | a second author block |
| `README.md` | the byline |
| `AI_USE.md` | "the research questions and the physics ... are Jeromie Beasley's and Elizabeth Johnson's" |
| `AUTHORS.md` | a file created to premise joint authorship |
| `atlas/README.md` | the peel papers "all by Jeromie Beasley and Elizabeth Johnson" |
| `results/formalization-note.md` | a byline he had already set to his name alone |
| `results/light-bridge-paper.md` | the Light Bridge paper's `author:` field |

Before that commit `LICENSE` read `Copyright (c) 2026 Jeromie Beasley`. He was not asked.

**What she actually supplied:** one Zenodo record, cited as reference 7 of the Light Bridge paper
(E. Johnson, *EJ's Alternate Base Prime Number Pattern and the Twin Prime Counterflow Model*,
Zenodo 23484151, 2026), and one statement from it — its Theorem 10.2, that every twin pair above 5
has residues 2, 5 or 8 mod 9 — machine-checked here as `twin_mod9`. The reduction that makes that
statement informative, that those residues are exactly `p ≡ 2 (mod 3)`, is his, and is `mod9_is_mod3`.
Nothing else in the repository derives from her.

**Her authorship of that paper is not in question, and this record must not be read as denying
it.** Jeromie Beasley had her open a GitHub account precisely so that she would receive the credit
she was due on the co-authored paper, whose code home is the `EJ-base-prime-pattern` repository.
That is a separate work with its own byline. The breach was carrying that co-authorship across into
this repository's licence, `CITATION.cff` and bylines, where none of her material is used.

The period around it is worth stating in his words too: through *Colour Selects the Leader* and the
two or three papers after it, he was reading her work for her and helping her find flaws, after
which his own work steered away from hers. Reviewing an author's paper is not co-authorship in
either direction.

**Corrected** in `a596587`: all ten reverted to Jeromie Beasley alone. The record is now a citation
and nothing more.

---

## 2. "DarkWolf (@DarkDireWolf33)" — the *three-body-lean* repository

Commit `bb05eff` ("Add 3-6-9 straw man: three-fold protection rule, computations and core-Lean
proofs", dated 2026-10-28) in the separate repository `dicipler-pixel/three-body-lean` added the
folder `369-three-fold-protection/` with:

- `<meta name="author" content="DarkWolf (@DarkDireWolf33), Jeromie Beasley, Grok (xAI), Claude (Anthropic)">`
- the byline `DarkWolf (@DarkDireWolf33) · Jeromie Beasley · Grok (xAI) · Claude (Anthropic)`
- the sentence **"The 3-6-9 modular construction is DarkWolf's."**
- the same byline in the header of `SM369.lean`

Jeromie Beasley states that DarkWolf had nothing to do with the work, and that the 3-6-9 line
reaches him through **Marko Rodin**, whose name appears nowhere in that folder. He has used vortex
math in the 3-6-9 style for years and knew this material before the report existed.

**Not corrected.** `bb05eff` is on `main` of `github.com/dicipler-pixel/three-body-lean`.

That README also asserts "The orbit argument is in Lean (`omega_preserves_norm`, `omega_order3`,
`omega_no_fixed`)". It is not: `omega_no_fixed` proves that the map fixes only the origin, and no
shell-count, finiteness or orbit-cardinality statement exists in either Lean file.

---

## 3. The agent's own error in this conversation

On 2026-11-23 the agent read that byline out of an attached copy of the report and repeated it to
Jeromie Beasley as though it described who had contributed. A byline found in a file is a claim to
be checked with the author of record, not evidence. It was repeated before it was checked.

---

## The rule that was broken

A person's name enters a byline, a licence, a credit line or a `CITATION.cff` only when the author
of record says so. Nothing in an agent's reading of a file, and nothing about "the work came out of
this conversation", authorises it.
