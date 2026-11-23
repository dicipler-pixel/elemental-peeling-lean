# Kindling and firewood: the ratio does show, and it is quantised

## 1. What I claimed, and what I did not

I said two things that are not about this ratio: that the *last digit of Z* carries no element property
beyond parity ($\text{Spearman}=+0.059$, $p=0.61$), and that no single coordinate reproduces all four
property surfaces at once. Neither is a claim that a ratio fails to show. The surface-to-volume ratio does
show, and it is computable exactly.

## 2. Surface is the pair, volume is the air

A twin segment is $2+\text{air}+2$: the two pairs are the **surface** (4 units of "material" at the ends)
and the air is the **volume** (the space between). Then

$$\frac{S}{V}=\frac{4}{\text{air}},$$

and because air is confined to five classes, the ratio takes **exactly five values, one per class**:

| class (air mod 30) | 4 | 10 | 16 | 22 | 28 |
|---|---|---|---|---|---|
| $S/V=4/\text{air}$ | **1.000** | **0.400** | **0.250** | **0.182** | **0.143** |
| share of segments | 11.9% | 23.6% | 22.1% | 11.1% | 31.2% |

So the ratio is not free: it is quantised, and the quantisation is the same five classes that carry the
end digits. In a 3-D piece of length $d$, $S/V\propto1/d$ is continuous; here it is a five-rung ladder.

## 3. The 1 : 3 line is exactly excluded

Kindling $:$ firewood $=1:3$ means the small stuff is a quarter of the mix, i.e. $S/V=\tfrac13$, i.e.

$$\frac{4}{\text{air}}=\frac13\ \Longrightarrow\ \text{air}=12 .$$

But air $\equiv4\pmod6$, and $12\equiv0$: **air = 12 cannot occur**, so the exact 1:3 point is not on the
ladder. The admissible ratios bracket it — class 10 gives $0.400$ and class 16 gives $0.250$, with
$0.333$ strictly between them. The ratio exists; the *exact* value is forbidden by the same residue that
makes five classes instead of thirty.

The same computation kills the other reading: $\text{air}/T=\tfrac34$ needs the same air $=12$, so **3/4 is
not a mixture fraction of a segment.** What is $3/4$ is the *slope* $c$ in $\langle\text{air}\rangle=ct^2$
— a coefficient, not a proportion.

## 4. And the count-versus-volume split is the whole effect

| band | segments | share of count | air carried | share of volume |
|---|---|---|---|---|
| small ($\text{air}\le10$) | 103,865 | **3.0%** | 868,328 | **0.1%** |
| medium (16–34) | 229,765 | 6.7% | 5,743,942 | 0.6% |
| large (40–199) | 1,339,282 | 39.1% | 148,970,128 | 15.0% |
| logs ($\ge200$) | 1,751,591 | **51.1%** | 837,567,776 | **84.3%** |

The small pieces are thirty times more common than they are heavy; the logs are 1.6 times less common
than they are heavy. Mean $S/V$ by count is 0.052, by volume 0.0138 — a factor of 3.8.

The 1:3 line, read two ways, puts the cut a **factor of three** apart in size:

| reading | cut | $S/V$ at the cut | share of count | share of volume |
|---|---|---|---|---|
| 25% of segments | air $\le88$ | 0.045 | 25% | 3.4% |
| 25% of the air | air $\le268$ | 0.015 | 61% | 25% |

So *the ratio that defines kindling is itself the factor between the two cuts* — 268/88 = 3.05. That is
the surface-to-volume effect stated exactly: a ratio of 3 in size corresponds to a ratio of 3 in the two
ways of counting, and to a factor of 30 in how the smallest pieces count against how much they weigh.

## 5. The one-line answer

Surface to volume is $4/\text{air}$, it takes five values (1, 0.4, 0.25, 0.18, 0.14), and the 1:3 point
falls between the second and third because air $=12$ is forbidden by air $\equiv4\pmod6$. The ratio shows;
the *exact* 1:3 does not, and the reason is arithmetic, not measurement.
