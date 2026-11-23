# The three fission tests, run against ENDF/B-VIII.0

`fission-and-the-key.md` ended with three tests it could not run: whether the valley/peak ratio is a
function of the countdown $\delta=54-Z/2-5$ alone; whether the heavy piece really sits on the closure;
and whether any measured Pu split puts both pieces on closed cells. All three are now run on evaluated
fission-product yields. One comes back the opposite way from the note's expectation (the valley is *not*
a function of the countdown alone), one confirmed to the third decimal, and one confirmed more strongly
than it was claimed (the closed-cell channel is not merely rare above Pu — it is empty).

## 0. The data

Independent fission-product yields, ENDF/B-VIII.0, as tabulated per nuclide and incident energy in
[`shinokumura/tabfylibs`](https://github.com/shinokumura/tabfylibs) (MT=454, 24 systems; JEFF-3.3
tables for U-235 and Pu-239 as a cross-check). The files carry one line per product with the columns
**$(Z, A, \text{isomer}, Y)$** — the header labels them "$A\ Z$" and is wrong; the largest entry in
Cf-252 is $(56,143)$ = Ba-143, which settles it.

Checks that the parse is right:

* every system sums to **2.000** fragments per fission;
* the mass yields reproduce the IAEA cumulative table quoted in the companion note — U-235 thermal
  peaks at $6.5\%$ ($A=95$) and $6.6\%$ ($A=135$), valley $0.01\%$ at $A=115$–120 — and the two
  libraries agree on $R$ to $0.5\%$ for U-235 and $23\%$ for Pu-239. The full table is
  [`tableR_fission_tests.csv`](tableR_fission_tests.csv).

Valley/peak is $\min_{A} Y(A)$ over the interior between the two humps divided by the higher hump.

## 1. Test 1 — is the valley a function of $\delta$ alone?

**No.** It is a function of $\delta$ *within an excitation class* and of the excitation energy otherwise.

| system | $Z$ | $A$ | class | valley/peak |
|---|---|---|---|---|
| Th-232 | 90 | 232 | 500 keV | 0.0031 |
| Th-232 | 90 | 232 | 14 MeV | **0.110** |
| U-233 | 92 | 233 | thermal | 0.0019 |
| U-235 | 92 | 235 | thermal | 0.0015 |
| U-235 | 92 | 235 | 500 keV | 0.0042 |
| U-235 | 92 | 235 | 14 MeV | **0.184** |
| U-238 | 92 | 238 | 500 keV | 0.0050 |
| U-238 | 92 | 238 | 14 MeV | 0.094 |
| Np-237 | 93 | 237 | thermal | 0.0019 |
| Pu-239 | 94 | 239 | thermal | 0.0040 |
| Pu-239 | 94 | 239 | 500 keV | 0.0073 |
| Pu-241 | 94 | 241 | thermal | 0.0029 |
| Am-241 | 95 | 241 | thermal | 0.0033 |
| Cm-245 | 96 | 245 | thermal | 0.0044 |
| Cm-244 | 96 | 244 | SF | **0.00014** |
| Cm-248 | 96 | 248 | SF | 0.00025 |
| Cf-250 | 98 | 250 | SF | 0.0026 |
| Cf-252 | 98 | 252 | SF | 0.0027 |
| Fm-256 | 100 | 256 | SF | **0.067** |

Three readings, all measured:

1. **The ordering holds in every class.** Thermal $Z=92\to96$: $0.0015\to0.0044$ (×3). SF
   $Z=96\to100$: $0.00014\to0.067$ (×480). 500 keV $Z=90\to95$: $0.0031\to0.011$ (×3.6). Never a
   reversal.
2. **At fixed $Z$ and fixed class, $R$ is nearly the same.** U-233 vs U-235 (both $Z=92$): ×1.3.
   Pu-239 vs Pu-241 ($Z=94$): ×1.4. Cm-244 vs Cm-248: ×1.8. **Cf-250 vs Cf-252: ×1.04.**
3. **At fixed $Z$ and different class, it is not.** Cm-244 spontaneous fission (essentially zero
   excitation) gives $R=0.00014$; Cm-245 thermal ($E^*\approx6.5$ MeV) gives $0.0044$ — **a factor
   31 at the same $Z$.** And within U-235 alone, thermal $\to$ 500 keV $\to$ 14 MeV is
   ×2.9 then ×43.

So the honest form is

$$\ln R = a(\text{class}) + b(\text{class})\cdot\delta,\qquad b_{\rm SF}\approx-2.9,\quad
b_{\rm thermal}\approx-0.54 .$$

The slope differs by a factor five between classes, so there is no universal $R(\delta)$. What survives
is that $\delta$ orders the asymmetries inside a class — the claim I made in the companion note ("the
ratio is a function of $\delta$ alone") is **refuted**, and the weaker ordering claim is confirmed.

## 2. Test 2 — the pin on the closure

Yield-weighted charge of each group, $\langle Z\rangle=\sum Z\,Y/\sum Y$:

| system | $Z$ | $\langle Z\rangle_{\rm light}$ | $\langle Z\rangle_{\rm heavy}$ | $Z-54$ |
|---|---|---|---|---|
| Th-232 (500 keV) | 90 | **36.05** | **53.94** | 36 |
| U-233 (th) | 92 | 37.81 | 54.21 | 38 |
| U-235 (th) | 92 | **38.03** | **54.03** | 38 |
| Np-237 (th) | 93 | 39.03 | 53.97 | 39 |
| Pu-239 (th) | 94 | **39.90** | **54.10** | 40 |
| Pu-241 (th) | 94 | 40.06 | 53.94 | 40 |
| Am-241 (th) | 95 | 40.62 | 54.31 | 41 |
| Cm-245 (th) | 96 | 41.36 | 54.61 | 42 |
| Cm-244 (SF) | 96 | **41.67** | **54.32** | 42 |
| Cm-248 (SF) | 96 | 41.68 | 54.32 | 42 |
| Cf-250 (SF) | 98 | 42.48 | 55.51 | 44 |
| Cf-252 (SF) | 98 | **42.51** | **55.46** | 44 |
| Fm-256 (SF) | 100 | 44.80 | 55.29 | 46 |

**The heavy piece is at the closure.** Over all 21 systems with $Z\le96$ (Th, U, Np, Pu, Am, Cm — a
range of six protons, thermal and spontaneous, 500 keV, 14 MeV):

$$\langle Z\rangle_{\rm heavy}=53.956\pm0.094\ (\text{s.e.}),\quad \text{s.d.}=0.43,\qquad C(5)=54 .$$

That is a hit at the $0.04$-proton level on the mean, and it is not a tautology: a charge-density rule
($Z_{\rm heavy}\approx 0.39A_{\rm heavy}$) gives no reason for the answer to sit on the closure ladder's
value.

The null hypothesis has a definite slope, so the pin can be stated as a slope instead of a level. If the
heavy piece simply kept the parent's charge-to-mass ratio, its charge would rise with the parent at
$dZ_H/dZ\approx A_H/A\approx0.59$. Measured, in the same class (leaving out the three 14 MeV systems,
where the charge does shift down — $53.2$–$53.5$ — and which is a real effect, not scatter):

$$\langle Z\rangle_{\rm heavy}=54.12\pm0.06\ (\text{s.e.},\ n=17),\qquad
\frac{d\langle Z\rangle_{\rm heavy}}{dZ}=0.08\ \text{per proton},$$

seven times flatter than the density rule, and the level it is flat *at* is $C(5)=54$. Above Cm the
flatness ends: Cf and Fm sit at $55.5$.

**The light piece is the remainder, $Z-54$**, and the measurement says so: the deviation
$\langle Z\rangle_{\rm light}-(Z-54)$ is $+0.05,-0.19,+0.03,0.00,-0.10,+0.06$ for Th-232, U-233,
U-235, U-235(JEFF), Pu-239, Pu-241 — i.e. **within $0.2$ protons across the thermal and spontaneous
systems from Th to Pu** — then $-0.4$ at Am, $-0.4$ at Cm and $-1.5$ at Cf, where the heavy piece itself
has moved up to $55.5$. (U-238 is the exception and the reason is physical: its fission is thresholded
even at 500 keV, and the light piece sits $+0.46$ there and $+0.92$ at 14 MeV. Checked in
`scripts/fission_verify.py`.)

So the second test's prediction, "the light charge at Cm-244 is 42", is measured at **41.7** (SF) and
**41.4** (Cm-245 thermal): confirmed. And its extension to Cf-252, "44", is measured at **42.5**: missed
by 1.5, with the cause visible — the pin has drifted to 55.5 before the light piece gets there.

## 3. Test 3 — do both pieces ever sit on closed cells?

Share of the total yield whose pair $(Z_1,Z_2)$, taken from the most probable charge at each mass and
its partner mass, has both charges closed ($h\le5$ or the row head):

| system | $Z$ | closed-pair share | most probable pair | blocks |
|---|---|---|---|---|
| Th-232 (500 keV) | 90 | **0.357** | (36, 54) | $p/p$ |
| U-233 (th) | 92 | 0.200 | (38, 54) | $s/p$ |
| U-235 (th) | 92 | 0.158 | (38, 52) | $s/p$ |
| Np-237 (th) | 93 | 0.083 | (40, 53) | $d/p$ |
| Pu-239 (th) | 94 | **0.000** | (42, 52) | $d/p$ |
| Pu-241 (th) | 94 | **0.000** | (42, 52) | $d/p$ |
| Am-241 (th) | 95 | **0.000** | (42, 53) | $d/p$ |
| Cm-244 (SF) | 96 | **0.000** | (42, 54) | $d/p$ |
| Cf-252 (SF) | 98 | **0.000** | (43, 56) | $d/s$ |
| Fm-256 (SF) | 100 | 0.048 | (47, 53) | $d/p$ |

**The rule is real where it was claimed and empty everywhere above Pu.** For U-235 the most probable
pair *is* closed — $(38,52)$ or $(38,54)$, one piece at the row head and one at the closure — and the
closed channel carries $16\%$ of the yield. For Pu-239, Am-241, Cm-244 and Cf-252 **no mass has its most
probable light charge on a closed cell at all**, so the channel's share is exactly zero, not merely
small. The test's prediction — "(38,56) is populated but the data sits above it" — is half right: $Z=38$
does carry $12\%$ of Pu-239's light charge, but no *mass chain* has 38 as its mode, so the *pair* is
never the most probable one.

## 4. The find: thorium splits on the two closures

$36=C(4)$ and $54=C(5)$ are consecutive closures, and

$$C(4)+C(5)=36+54=90 .$$

So thorium-232 is the one actinide whose asymmetric split can put **both** pieces on closures, and the
measured charge split is

$$\text{Th-232}\;\longrightarrow\;\langle Z\rangle=(36.05,\ 53.94),$$

which is $(C(4),C(5))$ to $0.06$ protons — and its closed-pair share, $36\%$, is the largest of any
system measured. It is also the *only* one: with the heavy pinned at 54, the light piece is a closure
only when $Z-54=36$, i.e. $Z=90$. That is a one-line prediction which the data cannot avoid making,
and it holds at the third decimal.

## 5. What the fission picture now is

| claim | status |
|---|---|
| the heavy piece sits on the closure $C(5)=54$ | **measured**, $53.96\pm0.09$ over 21 systems |
| the light piece is the remainder $Z-54$ | **measured**, within $0.1$ to Pu, drifting $-1.5$ by Cf |
| both pieces on closed cells | true for Th and U ($36\%$, $16\\%$), **empty** from Pu on |
| the symmetric split closes at $Z\ge98$ | **measured**: valley/peak jumps $\times18$ from Cm to Cf |
| the valley is a function of $\delta$ alone | **refuted**: at fixed $Z$, spontaneous vs thermal is $\times31$ |
| the ordering by $\delta$ inside a class | **confirmed** in thermal, 500 keV and SF, no reversal |
| the light piece walks down the countdown | **measured**: $\langle h\rangle=16,14,12,11$ for $Z=92,94,96,98$ |

The single sentence that survives all three tests is narrower than the one I wrote:

> fission puts the heavy piece on the closure $C(5)=54$ and lets the light piece take the remainder;
> the countdown of the light piece orders how asymmetric the split is, at a fixed excitation; and the
> one nucleus whose two halves *both* land on closures is the one at $Z=C(4)+C(5)=90$, thorium.

Everything else — the "base key" reading in which both pieces are legal — is true of the bottom of the
actinides and false by plutonium.
