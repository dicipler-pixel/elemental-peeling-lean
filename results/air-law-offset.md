# The air law: the offset is −2, and the coefficient is $1/(2C_2)$

This note corrects the one number the record has been carrying since the offset test: the air law is
**not** $\langle\text{air}\rangle=\tfrac34t^2$. The measured relation is

$$\boxed{\ \langle\text{gap}\rangle=\frac{t^2}{2C_2},\qquad
\langle\text{air}\rangle=\frac{t^2}{2C_2}-2,\qquad
\langle T\rangle=\frac{t^2}{2C_2}+2\ }$$

with $t=\log p$ and $1/(2C_2)=0.757390$. The offset is not a fudge and not zero: it is the **pair
width**, and which of the three lengths you measure decides its sign. A sieve to $10^{11}$ settles
which length carries no offset.

## 1. Three lengths, and the identities between them

For consecutive twin pairs with starts $p<q$:

| length | definition | in terms of the gap | offset in a law $\langle\cdot\rangle=c\,t^2+\text{off}$ |
|---|---|---|---|
| gap | $q-p$ | $q-p$ | **0** |
| air | $q-p-2$ | gap $-2$ | $-2$ |
| total $T$ | $q+2-p$ | gap $+2$ | $+2$ |

These are the definitions already in the record (`theorem.md` §1: air $=q-p-2$, $T=q+2-p$). The air
is the distance from the *end* of one pair to the *start* of the next, so it is short by 2 at one end;
the total runs end to end, so it is long by 2. Only the gap — start to start, which for equal-width
pairs is the same as **centre to centre** — is the segment-to-segment spacing, and only it can carry a
law with no offset.

Also, and this matters for how the constant was estimated: the air sums telescope,
$\sum\text{air}=(\text{last start}-\text{first start})-2n$, so the whole measurement is a *count*
measurement. There is no second piece of information in the air.

## 2. The measurement, seven decades

Segmented sieve, `scripts/air_law.py` over the accumulated sums (`.scratch/work/d1e*.json`,
`c1e*.json`); pair counts and prime counts check against the published values exactly —
$\pi(10^{10})=455{,}052{,}511$, $\pi_2(10^{10})=27{,}412{,}679$, $\pi(10^{12})=37{,}607{,}912{,}018$ — all
exact. (The accumulator over-counts pairs by one per segment — 14,901 of 1.87 billion, $8\times10^{-6}$ —
so the means are unaffected to six digits.)

| decade | pairs | $\langle\text{air}\rangle$ | $\pm$ | $\langle\text{gap}\rangle$ | $\langle t^2\rangle$ | gap$/t^2$ | $\pm$ |
|---|---|---|---|---|---|---|---|
| $10^4$–$10^5$ | 1,019 | 86.46 | 2.39 | 88.46 | 115.1 | 0.7687 | 0.0207 |
| $10^5$–$10^6$ | 6,945 | 127.57 | 1.42 | 129.57 | 169.8 | 0.7633 | 0.0083 |
| $10^6$–$10^7$ | 50,811 | 175.13 | 0.73 | 177.13 | 235.2 | 0.7531 | 0.0031 |
| $10^7$–$10^8$ | 381,332 | 234.02 | 0.36 | 236.02 | 311.4 | 0.7579 | 0.0012 |
| $10^8$–$10^9$ | 2,984,194 | 299.59 | 0.17 | 301.59 | 398.1 | 0.7576 | 0.0004 |
| $10^9$–$10^{10}$ | 23,988,172 | 373.19 | 0.07 | 375.19 | 495.4 | 0.7573 | 0.0002 |
| $10^{10}$–$10^{11}$ | 196,964,709 | 454.94 | 0.03 | 456.94 | 603.3 | 0.7574 | 0.0001 |
| $10^{11}$–$10^{12}$ | 1,646,222,582 | 544.71 | 0.01 | 546.71 | 721.8 | **0.75738** | 0.00002 |

The gap column is flat at $0.7574$ from $10^7$ on, across a factor **2.3** in $\langle t^2\rangle$. The
three lowest decades are off by $+1.5\%$, $+0.8\%$, $-0.6\%$ ($0.5\sigma$, $0.7\sigma$, $1.4\sigma$) —
the size and the sign pattern both fit the next term of the singular series, which decays as $t$ grows.
The air column is the same number minus $2/\langle t^2\rangle$ — which is why it *looked* like a
different constant.

## 3. Three models scored

Residuals in units of air, with the residual in $\sigma$ alongside:

| decade | $0.75\,t^2$ | $0.7574\,t^2-4$ | $0.7574\,t^2-2$ |
|---|---|---|---|
| $10^7$–$10^8$ | $+0.47$ (1.3) | $+2.17$ (6.0) | $+0.17$ (0.5) |
| $10^8$–$10^9$ | $+1.01$ (6.1) | $+2.07$ (12.4) | $+0.07$ (0.4) |
| $10^9$–$10^{10}$ | $+1.63$ (**22**) | $+1.97$ (**27**) | $-0.03$ (0.5) |
| $10^{10}$–$10^{11}$ | $+2.44$ (**78**) | $+1.99$ (**63**) | $-0.02$ (0.5) |
| $10^{11}$–$10^{12}$ | $+3.33$ (**254**) | $+1.99$ (**152**) | $-0.01$ (0.5) |
| pooled $\chi^2$ over the five | 71303 | 28119 | **1.0** |

Two conclusions, and they are different:

* **the $-4$ offset is dead**, as the earlier drift test said. It was the "no offset on $T$" reading,
  and it is 63$\sigma$ out at $10^{10}$.
* **the flat $\tfrac34$ is dead too**, and the earlier test could not see it, because it was run on the
  air with offset 0 rather than on the gap. At $10^{11}$–$10^{12}$ it is 254$\sigma$ out, and the gap law
  is in at $0.001\%$: $\mathrm{gap}/t^2=0.757382\pm0.000018$ against $1/(2C_2)=0.757390$.

The offset that survives is $-2$, and it is not a fitted number: it is the half-pair of §1.

**This is not a second prime-side constant, and the record already contained the check.** If the pair
count has local density $2C_2/\log^2x$, the spacing is its reciprocal, so the gap law is the count law
differentiated. The count is sensitive to the offset too — it is not a free ride:

| hypothesis for the spacing | count to $10^{10}$ | error | to $10^{11}$ | error |
|---|---|---|---|---|
| $\log^2x/2C_2$ (gap, no offset) | 27,411,416 | $-0.005\%$ | 224,368,865 | $-0.003\%$ |
| $\log^2x/2C_2+2$ (air, no offset) | 27,260,194 | $-0.56\%$ | 223,357,286 | $-0.45\%$ |
| $\log^2x/2C_2-2$ (total, no offset) | 27,564,339 | $+0.55\%$ | 225,389,745 | $+0.45\%$ |

So the count alone already excludes the two offset-by-2 readings at $0.5\%$ — a hundred times its own
residual. The record held both numbers at once: a count that matched $1/(2C_2)$ to $0.005\%$, and an air
coefficient of $0.7503$ that implies the second row. Nobody put them side by side, because the count was
checked against A007508 and the coefficient was checked against $\tfrac34$. The spacing measurement now
settles it in the direction the count already pointed.

## 4. Where $0.7503$ came from

With the correct law, the air coefficient measured decade by decade is $0.757390-2/\langle t^2\rangle$:

$$0.0174,\ 0.0118,\ 0.0085,\ 0.0064,\ 0.0050\ \ \text{for decades } 4\ldots8 .$$

Its mean over those five decades is $0.0098$, so the model's own five-decade average is
$0.75739-0.0098=0.74757$; the measured five-decade average was $0.75028$, and the $+0.0027$ is the mean
of the small positive low-decade residuals. In one line:

$$0.7503 \;=\; \underbrace{0.75739}_{\text{the constant}}\;-\;\underbrace{0.0098}_{2/\langle t^2\rangle
\text{, averaged}}\;+\;\underbrace{0.0027}_{\text{second-order term}} .$$

**The $-4$ has a birthplace, and it is a slip.** Two documents wrote the telescoping as
$\sum\text{air}=p_{\rm last}-p_{\rm first}-4m$ (`centroid-and-median.md`, `equation-sheet.md`). It is
$-2m$: each segment contributes the air $q-p-2$ and the sum $\sum(q_k-p_k)$ telescopes to
$p_{m+1}-p_1$, so one factor of 2, not two. Checked against the sieve at $10^{10}$–$10^{11}$
($m=1.9696\times10^{8}$): $\sum\text{air}=8.961\times10^{10}$ and
$p_{m+1}-p_1-2m=8.961\times10^{10}$, while $-4m$ gives $8.92\times10^{10}$. Every downstream statement that used the $-4$ — the "no offset on $T$" reading, and
the drift test's alternative column — inherited that slip. Both are now corrected in place.

Three effects conspired. The $\tfrac34$ was the middle term wearing the constant's clothes: at
$\langle t^2\rangle\approx400$ (decade 8) the correction $2/\langle t^2\rangle=0.005$ is almost exactly
the $0.9\%$ that separated $0.7503$ from $0.75739$. $0.09\sigma$ was not a coincidence — it was a
degeneracy, and it breaks in the third decimal the moment $\langle t^2\rangle$ doubles.

## 5. What this changes, and what it does not

| | before | now |
|---|---|---|
| the prime-side coefficient | $0.7503\pm0.0032$ (mean of five decades) | $1/(2C_2)=0.757390$, flat to $0.05\%$ over four decades |
| the number of prime-side constants | two, $1\%$ apart, with a discrepancy to explain | **one**, $2C_2$, in the count and in the spacing |
| the offset | $0$, unexplained | $-2$, the half-pair; $+2$ on the total, $0$ on the gap |
| the conversion K5 | $\kappa=0.0301$ K per unit $t^2$ | $\kappa=\dfrac{0.75739}{24.943}=\mathbf{0.03036}$ K per unit $t^2$ |
| the twin-count law | $2C_2\int dp/\log^2p$ | unchanged |

**Not affected.** The digit $\tfrac34$ — three of the four live digits can open or close a pair — is a
count of digits and stays exactly as it was (`three-quarters.md` §1). The synaptic $100/75=4/3$ stays a
ratio in a cited range. The element ladder, the closures, the capacities and every Lean theorem are
untouched. What falls is only the *identification of the air's $t^2$ coefficient with $\tfrac34$*, and
with it the hope that one number would do double duty across the two ladders.

That last point is the honest cost: $\kappa$ moves by $0.9\%$, and the "one constant, $3/4$, in the
digits, the gaps and the synapses" story loses its middle term. The digits still give $\tfrac34$; the
gaps give $1/(2C_2)$; the synapses give a range. Three numbers that are close, now correctly separated.

## 6. The falsifier, discharged

`three-quarters.md` ended with a testable claim: if $\tfrac34$ were the air law's true coefficient it
would hold at $0.750$ at scales where the offset model would have moved the number by several per cent —
that test was left as "a computation for a bigger sieve". Run to
$10^{10}$–$10^{11}$ with $1.97\times10^{8}$ pairs, the answer is that it does **not** stay at $0.750$;
it goes to $0.7541$ for the air coefficient, which is $0.7574$ with the $-2$ taken out. The
$\tfrac34$ reading fails its own test, and the offset reading is not the thing that replaced it.

*(Reproduce: `python3 scripts/air_law.py`. The sieve itself is `.scratch/work/centroid_ext.py`; a full
run to $10^{11}$ takes about five minutes on this machine.)*
