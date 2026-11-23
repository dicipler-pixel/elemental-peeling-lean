# The table as data

The loop wall in `LoopWall/` is the algebra of one removal step: `z`, `Γ = (z−1)/(z+1)`, the wall
`Γ² = ½`. **This directory is the data it is applied to** — every ionisation threshold of 118
elements, and the census the scale atlas draws from it.

| file | what it is | source |
| :--- | :--- | :--- |
| `data/ptable_data.json` | the v1.2.2 baseline, H (Z=1) to At (Z=85), 85 elements, 3,570 steps, 65 anion rungs | shipped in `What_the_Peel_Keeps_v1_2_2_Zenodo_package.zip`, `ptable/ptable_data.json` |
| `data/atlas_data.json` | the full archive behind the scale atlas, H to Og (Z=118), 118 elements, 5,714 steps | extracted from the JSON embedded in `Elemental_Peels_Scale_Atlas (2).html` |

Each step records `k` (which removal), `z = IE_{k+1}/IE_k`, `g2 = Γ²`, the two energies, and
`out = (Γ² > ½)`. Each element also carries `cores`: for every noble-gas core, the step at which
that core is first opened. The `regime` field of the full archive is `turn` except for eight steps
marked `run` — the same eight that lie outside the wall.

## The census

`python3 scripts/atlas_census.py` recomputes every numeric claim in the two documents. It passes
on the shipped data:

| claim | published | recomputed |
| :--- | :-: | :-: |
| elements, H–At | 85 | 85 |
| removal steps, H–At | 3,570 | 3,570 |
| steps outside the wall | 8 | 8 — Li k1, Be k2, B k3, C k4, Na k1, K k1, Rb k1, Cs k1 |
| … every one the first opening of a core | 8 | 8 |
| … every one at k ≤ 4 | 8 | 8 |
| anion rungs | 65 | 65 |
| anion rungs outside the wall | 53 | 53 |
| elements Li–At whose largest step opens a core | 83 | 83 |
| … opening helium / neon / argon / krypton / xenon | 78 / 2 / 1 / 1 / 1 | 78 / 2 / 1 / 1 / 1 |
| windows of ≥ 2 steps, full archive | 183,770 | 183,770 |
| windows over the wall in total | 91,768 | 91,768 |
| … with every constituent step inside | 91,638 | 91,638 |
| windows over the wall on geometric mean | 0 | 0 |
| largest two-step mean | 4.76566745 (Li) | 4.76566745 (Li) |
| largest three-step mean | 3.15005083 (B) | 3.15005083 (B) |
| windows with both usable endpoint widths | 183,081 | 183,081 |
| … without (`missing widths`) | 689 | 689 |
| usable windows above the wall on the upper mean | 0 | 0 (max 4.765667457) |

All of these are exact under the atlas's own computation, which is `z = ie[j]/ie[i]` over the two
endpoint **thresholds**, with the per-element `unc` list giving the endpoint rectangle:
`usable ⇔ unc[i], unc[j]` finite and `ie[i] > unc[i]`, upper ratio `(ie[j]+hi)/(ie[i]−lo)`. The
`ie` arrays are compacted, so the charge label `q[i]` is what makes a window's endpoints line up;
step `k` runs from charge `k−1` to charge `k`.

An earlier version of this file said the 183,081 split was uncheckable and that the printed means
differed in the seventh decimal. Both were wrong: the widths ship in `unc`, and the printed means
are exact under the `ie` convention. The error was multiplying the rounded stored `steps.z` instead
of dividing the endpoint `ie` values.

The rule that makes the window count exact is the atlas's own, stated in its prose and easy to miss:
**every intervening charge must be present**. The archive has gaps in `k` (seven elements), so a
window is a run of *consecutive* `k`, not a slice of the step list. Without that rule the counts are
191,817 / 95,569 / 95,439 — a 4% error that no rounding explains.

## What the numbers mean

**99.86% of the wall crossings have no wall-crossing step.** 91,638 of the 91,768 windows that
exceed `3+2√2` do so with every constituent step inside. That is not a coincidence of this archive:
it is the composition law. A window's ratio is the product of its steps, `Γ = tanh(½ log ·)` turns
products into VOTKP's velocity law `⊕`, so reflections add. `unified/Bridge/Composition.lean`
proves it (`composite_two_eq_oplus`, `crosses_iff_ledger_sum`), exhibits a minimal witness
(`two_halves_cross`: two steps at `z = 5/2` are each inside, the product `25/4` is outside), and
proves the other half of the atlas's finding — the geometric mean of inside steps is always inside
(`geomean_lt_wall`), which is why that count is exactly zero.

**The table does not select the wall value.** The largest step inside the wall is
`5.639665` (N, k=5) and the smallest outside is `5.947101` (Cs, k=1). Every cutoff in between gives
exactly the same eight outside steps, and `3+2√2 = 5.828427` lies inside that interval. Adding the
65 anion rungs narrows the band to `[5.807902, 5.866539)`, which still contains the wall. So the
table is *consistent with* the wall and cannot distinguish it from any other value in that band at
this resolution. The census prints the interval every run.

**And the aggregate counts are not evidence for the value.** The atlas's 91,768 / 91,638 are
computed *from* the cutoff: at `c = 5.85`, inside the band, the per-step classification is unchanged
(8 outside, all core openings) but the accumulated-only window count is 91,486 rather than 91,638.
So the window census tests the distribution, and presupposes the constant. What the table supports
is the distribution, not the number.

## Provenance

The attachments are `Periodic Table of Elemental Peels v2.2`, `Elemental_Peels_Scale_Atlas` and
`What_the_Peel_Keeps_v1_2_2_Zenodo_package.zip`, all by Jeromie Beasley and Elizabeth Johnson. The two JSON files are
copied or extracted verbatim; nothing in them was edited. The extraction of the atlas archive is a
brace-matched read of the `const d={...}` literal in the page's second `<script>` block; the
embedded object also carries `decay`, `window` and `faces` sections that this directory does not use.
