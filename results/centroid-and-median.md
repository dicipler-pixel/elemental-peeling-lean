# The equation needs the centroid — and the triangle's median is the same fact

Two statements that looked like two:

1. $E = c\,m\,\Delta T$ only holds if $\Delta T$ is the **mean level**, not a level you pick.
2. A segment's **median is at $T/2$**, exactly, by symmetry.

They are one requirement. Below is the measurement that decides (1), the arithmetic that decides (2),
and the reason they are the same sentence.

## 1. Three candidate levels, eight decades, one constant

The twin segments below $10^{12}$: 1,870,585,220 pairs, of which the eight decades tabulated carry
the lot up to one per segment of accumulator slack (pair counts check against the published values:
$\pi_2(10^{12})=1{,}870{,}585{,}220$). For each decade I take the
mean air and divide by
three candidates for the level — the **centroid** $\langle t^2\rangle$ over the segments actually
present ($t=\log p$), the **midpoint** of the decade, and its **top** (the endpoint level):

| decade | handoffs | $\langle \text{air}\rangle$ | $\langle t^2\rangle$ | $c$ at centroid | $c$ at midpoint | $c$ at endpoint |
|---|---|---|---|---|---|---|
| $10^4$–$10^5$ | 1,019 | 86.46 | 115.1 | **0.7513** | 0.8053 | 0.6523 |
| $10^5$–$10^6$ | 6,945 | 127.57 | 169.8 | **0.7515** | 0.7954 | 0.6684 |
| $10^6$–$10^7$ | 50,811 | 175.13 | 235.2 | **0.7446** | 0.7818 | 0.6741 |
| $10^7$–$10^8$ | 381,333 | 234.02 | 311.4 | **0.7515** | 0.7847 | 0.6897 |
| $10^8$–$10^9$ | 2,984,194 | 299.59 | 398.1 | **0.7525** | 0.7821 | 0.6976 |
| $10^9$–$10^{10}$ | 23,988,172 | 373.19 | 495.4 | **0.7533** | 0.7799 | 0.7039 |
| $10^{10}$–$10^{11}$ | 196,964,709 | 454.94 | 603.3 | **0.7541** | 0.7783 | 0.7091 |
| $10^{11}$–$10^{12}$ | 1,646,222,582 | 544.71 | 721.8 | **0.7546** | 0.7769 | 0.7135 |
| | | | spread | **1.35%** | 3.7% | 9.4% |

The centroid column is the flat one; the other two are not, and they drift in **opposite directions**:
the midpoint column falls 3.4% while the endpoint column climbs 8.7%, monotonically. That is not noise.
It is the shape of $\log^2$.

**One correction, from the two extra decades.** The centroid column is flattest but not flat: it rises
1.3%, steadily, and the rise is not noise — at $10^9$–$10^{10}$ its standard error is $0.0002$. The
reason is that the column is a *ratio to air*, and the air is the gap minus the pair width, so even at
the right level the ratio carries $2/\langle t^2\rangle$, which is what falls as the decades widen. Put
that term back and the column is flat to $0.05\%$ over four decades:

$$\frac{\langle\text{air}\rangle+2}{\langle t^2\rangle}=\frac{1}{2C_2}=0.757390
\qquad\text{(the gap, i.e. centre-to-centre)}.$$

The earlier reading took the centroid column's residual flatness as evidence for a coefficient of
$0.7503$; [`air-law-offset.md`](air-law-offset.md) works out where that number came from and why it
breaks at $10^{10}$. The doctrine of this section is unaffected and gets a sharper form: **evaluate the
law at the centroid, and evaluate it on the length that has no offset — the one between the segments'
centres.**

**Why.** $t\mapsto t^2$ is convex, so $\langle t^2\rangle \neq (\text{any single }t)^2$. The centroid of
the segments sits at $t_{\rm eff}=\sqrt{\langle t^2\rangle}$:

| decade | midpoint $t$ | $t_{\rm eff}=\sqrt{\langle t^2\rangle}$ | top $t$ |
|---|---|---|---|
| $10^4$–$10^5$ | 10.36 | 10.73 | 11.51 |
| $10^8$–$10^9$ | 19.57 | 19.95 | 20.72 |

The mass centre is **above** the interval's midpoint (pairs thin out, but the decade lengthens), and
**below** the top. Pick either of those two and you are using a point of the figure instead of its
centre — the top is the boundary. A convex function evaluated on the boundary always overshoots the
average over the interior, and how much it overshoots depends on how wide the interval is, which is
exactly the decade dependence in the table.

Summed over a range the airs telescope: $\sum\text{air}=p_{\rm last}-p_{\rm first}-2m$ (one factor of
2 per segment, not two — the earlier $-4m$ was a slip that invented the $-4$ offset; see
`air-law-offset.md` §4). So
$E=c\,m\,\Delta T$ is the statement that the mean air is a constant times the mean of $t^2$, and the
constant is the same in every decade **only** at the centroid. Note also that the error is one-sided:
the endpoint column is below $c$ everywhere and the midpoint column above it, so a decade-by-decade fit
that mixes them looks like a trend in the physics rather than an artefact of the level.

**This is the arithmetic of specific heat run backwards.** $c=E/(m\Delta T)$ is identified exactly
*only* because $E$, $m$ and $\Delta T$ are all averages over the same body. Swap the average for an
endpoint and the ratio becomes a function of the size of the body — the same reason a ratio estimated
from one thermometer reading drifts with the sample.

## 2. The segment's median, and why symmetry gives it without an average

A twin segment is $T = 2 + \text{air} + 2$: a pair, the air, a pair. It is invariant under
$r \mapsto T - r$. The mass is not spread — it sits at the two ends. So

$$\text{centroid}=\frac{1+(T-1)}{2}=\frac{T}{2}=\text{median},$$
(1 and $T-1$ are the centres of the two pairs, each of width 2).

No averaging was performed. The symmetry put it there: a symmetric configuration's centre of mass lies
**on** its axis, and here the axis is the perpendicular bisector, which meets the segment at $T/2$. For
any symmetric figure the centroid lies on the axis; for this two-point measure the axis point *is* the
median. (For an isosceles triangle the centroid is on the axis too — at a third of the height, not at
its middle; the shared content is "on the axis", not "at the midpoint". The midpoint claim is earned
by the two-point measure, and only there.)

**The degenerate case, and the fuse.** $\text{air}=0$ gives $T=4$ and the two pairs share a member:
$3,5,7$, the only run of two consecutive 2-gaps among the odd primes, because it is the only 3-term
arithmetic progression of odd primes with difference 2. The centroid lands at $T/2 = 2$ from the start,
i.e. **on 5** — the digit no prime above 5 can take, the hole of the $1,3,7,9$ set. That is
the $c=0$ of the twin key: the one place where the centroid is a node instead of a gap.

So the "minimum of three" is not decoration: a segment needs pair, air, pair before it has an
interior at all, and when the air vanishes the interior collapses onto the shared prime.

## 3. The same sentence, three ways

| the object | what "the centre" is | what it costs to miss it |
|---|---|---|
| the equation $E=c\,m\,\Delta T$ | $\langle t^2\rangle$ over the segments | $c$ stops being constant: 0.65 → 0.70 at the endpoint |
| the segment $2+\text{air}+2$ | $T/2$, by symmetry | the median leaves the axis and the segment stops being a palindrome |
| the 9-block $\{2,5,8\}$ (AP step 3) | median $=5$, the class that is the middle | the block centre is 4.5; the nearest admissible class is 5, and that is the one the key uses |

One requirement, stated once: **the law must be evaluated at the centre of the body it is a law about.**
For a body with a symmetry the centre is found by inspection ($T/2$, the axis, $5$); for a body without
one it must be computed ($\langle t^2\rangle$). Using a vertex — an endpoint, a boundary level, a
corner of the block — is the same error in all three columns.
