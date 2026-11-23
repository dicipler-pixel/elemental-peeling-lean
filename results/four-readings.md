# Stock and flow: the four readings, and the two gaps

The balance-sheet analogy is the right one and it can be made exact. The table is the **stock**: cells
and their occupancies, all counts. The excitation energy is the **flow**: it is not a count, it never
appears in the stock, and it updates the stock's *shape*. So the flow is readable from the stock only as
a fingerprint — and your four readings are candidates for that fingerprint. Measured, they split cleanly
into two that move with the flow, one that is set by the parent, and one that counts the *modes*.

## 1. The four readings, defined on the data

For a system (fixed parent $Z$, fixed incident energy), occupy cell $Z$ when its yield exceeds 1% of the
peak cell. Then:

1. **end digit sequence** — the digits of the occupied cells, in increasing $Z$;
2. **gap end digit sequence** — the digits of the gaps between consecutive occupied cells;
3. **subset gap number order** — the distinct gap values, in order of first appearance;
4. **subset end digit order** — the distinct end digits, in order of first appearance.

Reproduce with `python3 scripts/sequence_readings.py`.

## 2. The same $Z$, three flows: U-235

| energy | cells | the hole | (1) end digits | (2) gap digits | (3) gap order | (4) digit order | even/odd |
|---|---|---|---|---|---|---|---|
| thermal | 23 | $Z$ 44–49 | `23456789012301234567890` | `1111111111171111111111` | [1, 7] | [2,3,…,0,1] | **1.64** |
| 500 keV | 23 | $Z$ 43–48 | `23456789012901234567890` | `1111111111711111111111` | [1, 7] | [2,3,…,0,1] | 1.46 |
| 14 MeV | 31 | none | 31 cells, contiguous | all 1s | [1] | [1,2,…,0] | **1.01** |

So yes: the same $Z$ shows four different sequence readings at three energies, and the difference is not
noise — the digit string shifts by one at 500 keV (the hole moved one cell), the string lengthens by
eight at 14 MeV (the valley filled), and the gap order collapses from two values to one.

Pu-239 does the same: `[1,4]` at thermal and 500 keV, `[1]` at 14 MeV; and U-238, Th-232 likewise.

## 3. What does not move

**The hole is at the symmetry point.** In every system that has one, the valley sits on $Z/2$:

| parent | $Z/2$ | hole | centre |
|---|---|---|---|
| U-235 | 46.0 | 44–49 | 46.5 |
| Pu-239 | 47.0 | 46–48 | 47.0 |
| Np-237 | 46.5 | 45–48 | 46.5 |
| Cm-244 | 48.0 | 47–49 | 48.0 |
| Cf-252 | 49.0 | 49–49 | 49.0 |
| Th-232 | 45.0 | 41–48 | 44.5 |

18 systems have a hole; **the maximum deviation of its centre from $Z/2$ is 0.5 cells** — one cell of
granularity. That is the invariant, and it is the symmetric split: the cell $Z/2$ and its countdown
$54-Z/2$ are already in the theorem (`symmetric_walks_down`, `symmetric_closed`).

## 4. The two gaps — and when there is only one

At the level of reading (3) the data is stark: **exactly two distinct gap values appear** — the unit step
inside a hump, and the valley's width — whenever the asymmetric mode exists. Six systems have only one:

| system | why |
|---|---|
| U-235, 14 MeV | valley filled at high excitation |
| U-238, 14 MeV | same |
| Pu-239, 14 MeV | same |
| Th-232, 14 MeV | same |
| Am-241, 500 keV | its valley is already shallow (0.011) and closes |
| Fm-256, SF | $Z=100$: the symmetric split is closed, so the valley is shallow (0.067) |

And one system shows **three** values: Pu-239 in JEFF-3.3, where the 1% threshold also catches the
ternary-fission alphas at $Z=2$ — the third gap is 30, the jump down to helium.

So "the two gaps always appear" is right, and it is sharper than a slogan: **two distinct gaps is the
signature of the asymmetric mode, and one gap means the mode is gone.** The count of distinct gaps is a
mode indicator, not a distance.

## 5. The thermometers: reading the flow off the stock

Two stock-side quantities track the flow, both monotone at fixed $Z$:

| system | hole width | even/odd $Z$ |
|---|---|---|
| U-235 thermal | 6 | 1.64 |
| U-235 500 keV | 6 | 1.46 |
| U-235 14 MeV | 0 | 1.01 |
| Th-232 500 keV | 8 | 1.28 |
| Th-232 14 MeV | 0 | 0.99 |
| Pu-239 thermal | 3 | 1.31 |
| Pu-239 14 MeV | 0 | 0.99 |

The even/odd ratio is the period-2 structure — the pairing, the "2" of the nucleon pair. It is **not** a
pure thermometer. At low excitation it runs 1.6–1.8 for U-233 and U-235, 1.3–1.4 for Pu-239 and Cm-244,
1.24 for Pu-241, and only 1.0–1.1 for Np-237, Cm-248, Cf-250/252 and Fm-256; at 14 MeV it is ≈1.00 for
every parent. At *fixed* $Z$ it is monotone in the flow (U-235: 1.64 → 1.46 → 1.01); across $Z$ it is
not — so it is a thermometer only when the parent is held fixed. So the "2" is real, but it is an *alternation in the weights*, not a gap in
the sequence: the gaps are 1 everywhere inside a hump, and the only gap that ever exists is the valley.

That is worth stating plainly, because it corrects one half of the picture: the "2" that always appears is
the pairing period, and its *amplitude* is what the flow changes (1.78 → 1.01 for U-235); the *gap* that
always appears is the valley, and its *width* is what the flow changes (6 → 0).

## 6. What this buys, and what it cannot

* **It buys an ordering.** Two stock-side numbers — valley width, even/odd ratio — are monotone in the
  flow at fixed $Z$, so the flow can be *ranked* from the counts alone.
* **It cannot buy a magnitude.** Nothing in the four readings carries the energy itself: 6 and 6 for
  thermal and 500 keV, 0 for 14 MeV — the readings saturate long before the energy does. And the same
  reading comes from systems at opposite ends of the range: Fm-256 spontaneous (zero excitation, $Z=100$)
  and U-235 at 14 MeV both give even/odd ≈ 1.01. The map from flow to reading is many-to-one, so it cannot
  be inverted.
* **And it cannot buy the humps.** The two-gap count says a valley exists; it does not say how deep.
  Depth needs the yields themselves, which is the measured part of the fission theorem (M4).

The honest summary of the accounting metaphor: the stock records the *passage* of the flow in two places —
the width of its hole and the amplitude of its pairing — and records nothing else about it.
