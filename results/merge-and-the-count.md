# The merged segment: why the count per segment is not 1, and what rate it runs at

You are right that this count is not fixed, and the amount by which it fails to be fixed is now
measured over five decades. The short version:

$$\text{pairs per segment}=1.14\ \text{at }10^4,\quad1.07\ \text{at }10^9,\quad
\text{and the merge rate itself is }\frac{2C_2}{\log p}\ \text{— no free parameter.}$$

## 1. What the count actually is

Using the definitions already in [`merged-keys.md`](merged-keys.md): a handoff is **merged** when no
lone prime sits between the departing pair's partner and the arriving pair — i.e. the arriving pair
begins at the very next prime. A *segment* in your sense is a maximal run of pairs joined by merged
handoffs: single twin (1), double twin merged (2), triple (3), and so on.

Census of all twin pairs below $10^9$ (3,424,506 pairs, 3,424,505 handoffs), recomputed for this note:

| objects with | 1 pair | 2 pairs | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| count | 2,971,978 | 203,254 | 13,982 | 955 | 47 | 2 | 1 |

* merged handoffs: **234,287** (6.84%) — the record's number, reproduced exactly;
* distinct segments: 3,190,219, so **1.0734 pairs per segment**;
* pairs living inside a merged segment: 452,528, i.e. **13.2%**;
* adjacent-merge occurrences: **16,046** — also the record's number, and it is a count of *adjacent
  pairs of merges*, which is why it exceeds the 13,982 three-pair segments (a run of $k$ merges
  contributes $k-1$);
* the widest segment below $10^9$ has **7 pairs**, at $p=678{,}771{,}479$: airs
  $10,58,4,58,28,10$, and its span is $168+2\cdot7=182$, exactly as the identity below says.

So the count per segment takes the values $1,2,\dots,7$: **not fixed, mean 1.073**. That part of your
statement is confirmed by counting.

## 2. Why it changes, and at what rate

A merge happens when the air — the distance from the departing pair's partner to the next twin
start — is **exactly one prime gap**, because only then does no lone prime intervene. That is a
condition on the *next prime after a fixed point*, which has a rate with no free parameter:

$$\Pr(\text{next prime } q \text{ starts a twin})=\frac{\text{twin density}}{\text{prime density}}
=\frac{2C_2/\log^2q}{1/\log q}=\frac{2C_2}{\log q}=0.7574\ldots\times\frac{2}{\log q}.$$

Measured, decade by decade (merged handoffs / all handoffs):

| decade | $\langle t\rangle$ | merged share | $\times\langle t\rangle$ |
|---|---|---|---|
| $10^4$–$10^5$ | 10.71 | 0.1217 | 1.303 |
| $10^5$–$10^6$ | 13.01 | 0.1009 | 1.313 |
| $10^6$–$10^7$ | 15.32 | 0.0868 | 1.330 |
| $10^7$–$10^8$ | 17.64 | 0.0763 | 1.346 |
| $10^8$–$10^9$ | 19.94 | 0.0670 | 1.336 |
| $10^9$–$10^{10}$ | 22.25 | 0.0598 | 1.331 |

$$p_{\rm merge}\cdot\langle t\rangle=1.327\pm0.016,\qquad 2C_2=1.32032\ \ (\text{predicted, no parameter}).$$

$+0.5\%\pm1.2\%$ over five decades. **The merge rate is not a constant — it falls as $1/\log p$ — and
the constant behind it is $2C_2$, the same number that runs the pair count and the air law.** So the
"double" and "triple" are not a separate phenomenon with their own statistics: they are the next prime
after a pair happening to be a twin, at the rate the twin density says it should be.

Hence the count per segment drifts as the sequence grows:

$$\text{pairs per segment}=\frac{1}{1-p_{\rm merge}}: \quad 1.139\ (10^4)\ \to\ 1.064\ (10^{10}).$$

Seven per cent across five decades. If a law is stated per segment, that is the drift it inherits.

## 3. What this decides: which count is the unit

This is where your observation earns its keep. Write the air law with the two normalisations:

| unit | coefficient at $10^4$ | at $10^9$ | drift | value at $10^9$ |
|---|---|---|---|---|
| per **handoff** | 0.7574 | 0.7574 | 0.05% | $1/(2C_2)=0.75739$ |
| per **segment** | 0.8624 | 0.8055 | 7% | 0.813 |

The per-handoff normalisation is flat and lands on $1/(2C_2)$; the per-segment normalisation drifts 7%
and lands on $0.813$, which is not a number anything predicts. So the **unit of the law is the
handoff** — the pair-to-pair transition — and the merged segment is a *description* of how the pairs
cluster, not a unit. Your count is the right thing to ask about; the answer is that the pairs, not the
segments, are what the arithmetic counts.

## 4. Where the hierarchy stops, and why — not by rarity, by residue

The deepening is killed by small primes, exactly:

* **zero air** ($p,p+2,p+4$ all prime): one of any three consecutive odd numbers is divisible by 3, so
  the divisible one must *be* 3 — hence $p=3$, and $(3,5),(5,7)$ is the only zero-air join in the
  sequence. A run of *four* of step 2 is impossible outright: $p=3$ would force $p+6=9$. Lean:
  `triple_only_three`, `no_quadruple`.
* **the minimal merge** ($\text{air}=4$) is the quadruplet $p,p+2,p+6,p+8$, whose offsets
  $\{0,2,6,8\}$ occupy only four of the five classes mod 5 — so nothing forbids it, and it is common
  (28,388 below $10^9$). Lean: `air_four_is_quadruplet`, `quadruplet_residues`.
* **the next level** $\{0,2,6,8,12,14\}$ occupies **all five** classes mod 5, so one member is
  divisible by 5 and must be 5: $p=5$, the sextuplet $5,7,11,13,17,19$, occurring **once**. That is why
  the class-14 triple has floor 44 and not 14 (`merged-keys.md`). Lean: `sextuplet_only_five`.

So the merge hierarchy thins by a factor $2C_2/\log p$ per level *and* loses entire patterns to 3 and
to 5. It stops for arithmetic reasons, not for statistical ones.

## 5. The exact bookkeeping

A merged object of $k$ pairs is its pairs plus its airs: its span is $2k+\sum\text{air}$
(Lean: `object_total`). In the record's totals this is the triple identity
$T=T_1+T_2-2$ (Lean: `merged_total`), and the class of any merge is the sum of the parts' classes
minus 2 (`merged_class`) — so a merge shifts the class by $+28\equiv-2\pmod{30}$ and the value ladder
by $-2$. That is the "−2 per merge" you can see in the 14-triple's floor: $44=8+8-2+30$.

## 6. On the element side there is no merge — but the parity is not fixed either

In the fission table $Z$ is a proton count, and it is *exactly* additive: $Z_1+Z_2=Z$, with no
correction, because two nuclei do not merge and share a proton. So the merge structure has no
element-side analogue, and the pin I measured ($\langle Z\rangle_H=53.96\pm0.09$) is a mean, not a
fixed value: individual fragments spread with s.d. **2.3** around it.

What *is* not fixed on the element side is the parity, and it is measurable in the same data:

| parent | odd-$Z$ share (light) | even/odd $Z$ yield | even/odd $N$ yield |
|---|---|---|---|
| $^{235}$U | 0.380 | **1.64** | 1.15 |
| $^{239}$Pu | 0.429 | 1.32 | 1.10 |
| $^{244}$Cm (SF) | 0.413 | 1.43 | 1.10 |
| $^{245}$Cm | 0.465 | 1.16 | 0.99 |
| $^{252}$Cf | 0.489 | **1.10** | 1.01 |

So "one unit per fragment" is not fixed either: even-$Z$ fragments carry 1.64× the odd-$Z$ weight in
U-235 and only 1.10× in Cf-252. The pairing preference — the element-side version of your point — has a
size, and it decays as $Z$ rises.

## 7. One paragraph

The count per segment is not 1 and not fixed: it is 1.073 at $10^9$, ranged 1 to 7, drifting as
$1/(1-2C_2/\log p)$. The rate law is measured to 0.5% over five decades and predicted with no
parameter, and it uses the same $2C_2$ as the pair count and the air law. Because that rate drifts, a
law normalised per segment drifts with it — which is how your objection decides something: the air law
is per handoff, and only in that normalisation does it sit still at $1/(2C_2)$. The hierarchy above the
triple exists where residues allow and is annihilated where they do not, by 3 at the zero-air join and
by 5 at the sextuplet.

*(The arithmetic in §5 is proved in [`merge-theorems.lean`](merge-theorems.lean) — `merged_total`,
`object_total`, `triple_only_three`, `no_quadruple`, `sextuplet_only_five`, and, for the `T` column's
excess, `totals_excess` / `totals_span`.)*
