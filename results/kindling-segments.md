# Kindling and firewood against the segments: many gaps or few

The record's ratio is $S/V=4/\text{air}$ — the pair is surface (4 units), the air is volume. Every
handoff has one air, but handoffs are of **two kinds**, and only one of them is a normal gap:

* an **external** air ends a segment. It is any gap between twin starts, so it follows the measured law:
  mean $t^2/(2C_2)-2\approx309.7$ at $10^{9}$.
* an **internal** air joins two pairs into one segment. By definition of a merge there is no prime
  between the partner and the next start, so an internal air **is a single prime gap** — mean $22.45$,
  median $16$, max $196$, and all 234,287 of them satisfy air $\equiv4\pmod6$.

So the ratio is $0.013$ outside a segment and $0.178$ inside one: **a segment is kindling inside and
firewood outside**, and the factor is $13.8$ — the same factor by which the internal air is smaller than
the external one. `scripts/kindling_segments.py`, [`tableV3_kindling.csv`](tableV3_kindling.csv).

## 1. The per-size table

| segments of $k$ pairs | count | mean internal air | $S/V$ inside | mean external air | $S/V$ outside | **$S/V$ of the segment** |
|---|---|---|---|---|---|---|
| 1 (lone pair) | 2,971,978 | — | — | 309.4 | 0.013 | **0.013** |
| 2 | 203,254 | 22.45 | 0.178 | 313.2 | 0.013 | **0.356** |
| 3 | 13,982 | 22.49 | 0.178 | 316.4 | 0.013 | **0.267** |
| 4 | 955 | 22.52 | 0.178 | 325.6 | 0.012 | **0.237** |
| 5 | 47 | 22.19 | 0.180 | 298.6 | 0.013 | **0.225** |
| 6 | 2 | 28.00 | 0.143 | 412.0 | 0.010 | **0.171** |
| 7 | 1 | 28.00 | 0.143 | 454.0 | 0.009 | **0.167** |

Two things are worth reading off it.

**The internal gap does not depend on the size of the segment.** 22.45, 22.49, 22.52, 22.19 — flat. A
merge costs one prime gap each time; the cost does not grow with the length of the segment. The
mechanism is the one in [`merge-and-the-count.md`](merge-and-the-count.md): the next prime after a pair's
partner happens to be a twin start, at rate $2C_2/\log p$, and the gap it leaves is whatever that prime
gap is.

**The segment's own ratio falls as the segment grows.** Surface $4$ per pair, volume one prime gap
($\approx22.5$) per *extra* pair, so

$$\frac{S}{V}(k)=\frac{4k}{22.45\,(k-1)}:\qquad 0.356\ (k=2),\ 0.267\ (3),\ 0.237\ (4),\ 0.225\ (5),\
0.167\ (7).$$

So among segments: **the two-pair merge is the most kindling-like thing in the sequence**, and each
further pair makes it a little more firewood-like, because the 4 units of material at the end are
amortised over one more gap of air. The lone pair, measured against its external air, is firewood by a
further factor of $27$: $0.013$.

## 2. What that means in your two words

| reading | which gaps | $S/V$ | what it corresponds to |
|---|---|---|---|
| kindling | the **internal** gaps — one prime gap each, and only where a merge happened | $0.14$–$0.36$ | 203k–14k objects, 13.2% of pairs |
| firewood | the **external** gaps — the full $t^2/(2C_2)$ law | $0.013$ | 2.97M lone pairs |
| the intermediate | a long segment (5–7 pairs) — many internal gaps, but each one costs 4 units of surface | $0.17$ | 50 objects |

So "segments with many gaps" and "segments with limited gaps" are not the same kindling: a *few* gaps
maximise the ratio (k = 2), *many* gaps dilute it (k → 7), and *no* gaps at all — the lone pair — is the
firewood extreme. The five-value quantisation of [`kindling-firewood.md`](kindling-firewood.md) is the
*class* statement (air mod 30 → five values); the actual airs take 4 to 196, and the interval that
matters here is not the class but which side of the merge the air sits on.

## 3. The one arithmetic consequence

Since an internal air is a prime gap, the internal airs are a **subsample of the prime gaps**, not of the
air law — and the sample is biased upward: mean $22.45$ against the mean prime gap $19.67$ at the same
height. The bias is a residue effect, not a surprise: an internal air goes from a partner
($\equiv1\bmod6$) to an arriving start ($\equiv5\bmod6$), so it is always a **1→5 gap**, and those are
the larger of the three gap classes. Kindling is made of the 1→5 gaps; that is the whole of why its air
is $22$ and firewood's is $310$.
