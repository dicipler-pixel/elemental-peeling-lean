# Isolating a segment's class from its digit sequences

Your instruction, made precise and tested: inside a segment there are two digit sequences —

* the **gap end digits**: `2` for each pair and the air's digit `4, 0, 6, 2, 8` for each merge;
* the **prime end digits**: `1, 3, 7, 9` down the primes of the segment —

and the class of the segment is recoverable from **the gap end digits alone**, with an exact reason:
$30=\mathrm{lcm}(6,10)$, so a gap that is $4 \pmod 6$ is *fixed* mod 30 by its last digit. The mapping is

$$4\mapsto4,\qquad 0\mapsto10,\qquad 6\mapsto16,\qquad 2\mapsto22,\qquad 8\mapsto28,$$

and a segment of $k$ pairs whose internal airs are $a_1,\dots,a_{k-1}$ has

$$\boxed{\ \operatorname{class}(T)\;=\;\Bigl(2k+\sum_{i=1}^{k-1}\operatorname{cls}(a_i \bmod 10)\Bigr)\bmod 30\ }$$

because its span is $2k+\sum a_i$ (`2` per pair, one air per merge). Proved in
[`digit-roles.lean`](digit-roles.lean) §5 (`air_class_of_digit`, `sum_class_mod`,
`total_class_from_digits`), and tested on every segment below $10^{9}$:
`scripts/class_from_digits.py`, [`tableV5_class_from_digits.csv`](tableV5_class_from_digits.csv) —
**234,287 internal airs, 0 exceptions; 218,241 segments of $k\ge2$, 0 exceptions.**

## 1. The sequences, and what they give

| $k$ | distinct sequences found | of the $5^{k-1}$ possible | example → class |
|---|---|---|---|
| 2 | **5** | 5 | `(0) → 14`, `(8) → 2`, `(6) → 20`, `(4) → 8`, `(2) → 26` |
| 3 | **20** | 25 | `(6,0) → 2`, `(0,0) → 26`, `(0,6) → 2`, `(0,8) → 14`, `(8,0) → 14` |
| 4 | **65** | 125 | `(0,6,0) → 14`, `(6,0,0) → 14`, `(4,0,0) → 2` |
| 5 | 39 | 625 | — |
| 6 | 2 | 3,125 | — |
| 7 | 1 | 15,625 | — |

and the frequencies are not uniform: the digit `0` carries **36.5%** of the internal airs (85,402 of
234,287), so the two-pair segment with digit 0 — class **14** — is the commonest kindling there is
(74,136 of 203,254 two-pair segments, 36.5%). Digit `2` is the rarest at 9.3%.

Two distinct sequences always give two distinct classes here, which is the empirical form of the map
being a *function*: for a given interior digit sequence the class is unique, 0 exceptions.

## 2. What the prime end digits can and cannot do

* In general a prime's last digit carries **two** classes, one per ladder
  (`two_classes_per_digit`): `1 ↔ {1, 11}`, `3 ↔ {13, 23}`, `7 ↔ {7, 17}`, `9 ↔ {19, 29}`. So the prime
  end digits alone give the total *mod 10* only.
* Inside the twin starts the ambiguity collapses, because only three of the four digits are live:
  `1 → 11`, `7 → 17`, `9 → 29` (`twin_start_class_of_digit`). Measured: the (class, digit) pairs among
  twin starts above 5 are exactly `(11,1)`, `(17,7)`, `(29,9)` — three pairs, no fourth.
* And the two sequences are linked by the **digit path** (`digit_path`): each gap advances the end digit
  by the gap's own digit, so the prime end digits are the cumulative sum of the gap end digits from the
  segment's first start. That is why reading the *prime* digits and reading the *gap* digits are the same
  walk, and why the gap digits are the ones that carry the class: they carry the mod-3 information the
  prime digits lose.

## 3. How to read a segment

1. Write the segment's gaps: `2, a₁, 2, a₂, …, 2`.
2. Take the digits of the airs: each is one of `4, 0, 6, 2, 8`.
3. Replace each by its class: `4, 10, 16, 22, 28` — this is exactly where the five classes come from.
4. Add $2k$ (two per pair) and reduce mod 30. **That is the segment's class.**

Worked: the merge `(11,13) → (17,19)` has $k=2$ and one internal air $=4$, whose digit `4` has class 4;
$2k=4$, so the class is $4+4=8$. The span is $2\cdot2+4=8$, and $(17+2)-11=8$ ✓ — which is the record's
`T = air + 4` seen as the $k=2$ case of the formula.

## 4. Why this matters for the table

The Light Table gives each digit a class pair; this note gives the *segment* its class from its internal
digits, and the two agree because both are the same residue arithmetic: $30=\mathrm{lcm}(6,10)$. So the
"subset sequence" reading is not a separate rule to memorise — it is the class rule applied to the
gaps the segment actually contains, and the check on 218,241 segments is that it never once disagrees
with reading the class off the endpoints.
