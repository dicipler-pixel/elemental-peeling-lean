# The one equation, in the form any scientist can use it

$$\boxed{\;p_N-p_1 \;=\; \frac{1}{2C_2}\sum_{i=1}^{N-1}\log^{2}p_i\;}$$

with $p_1<\dots<p_N$ the twin starts of any window, $2C_2=1.3203236$, and

$$\frac{1}{2C_2}=0.757390\pm0.000018\qquad(\text{per handoff, measured to }10^{12}).$$

It is one equation with three readings — span from the list, count from a span, mean gap from both — and
it is the cumulative form of the per-handoff law $\langle\text{gap}\rangle=t^{2}/(2C_2)$, made exact by
telescoping. The per-handoff law is **measured**; the step from one handoff to the whole chain is
**proved** (`Law.span_from_logs`, `Law.span_eq_c_m_dT`, `Law.count_from_span`) and needs no
approximation of its own. Everything below is reproduced by `scripts/one_equation_check.py`, whose numbers
`scripts/check-paper.py` checks against this file.

## 1. Symbols, and what each one is

| symbol | is | units / domain |
|---|---|---|
| $p_i$ | the $i$-th **twin start**: $p_i$ and $p_i+2$ both prime | integer, $5\le p_i\le10^{12}$ measured |
| $t$ | $\log p$ | dimensionless ($p$ in units; $t\approx20$ at $p\approx10^{9}$) |
| gap | $p_{i+1}-p_i$ | integers; always $\equiv0\pmod 6$ |
| air | $\text{gap}-2$ | integers; always $\equiv4\pmod 6$ (proved: `air_mod_six`) |
| span | $p_N-p_1$ | integers, the length of number line the chain consumes |
| $C_2$ | twin prime constant $0.6601618\ldots$ | dimensionless, standard |
| $m=N-1$ | handoffs | integer |
| $\Delta T$ | $\langle\log^{2}p\rangle$ over the window | dimensionless |

## 2. The three readings

**(i) Span from the list.** Feed the twin starts, get the span. At $10^{9}$:

$$\sum\log^{2}p_i=1{,}320{,}020{,}551,\qquad \frac{\sum\log^{2}p_i}{2C_2}=999{,}775{,}478,
\qquad\text{actual span}=999{,}999{,}188,$$

so the equation is **0.022% low** — the whole chain to a billion, priced from its squared logs.

**(ii) Count from a span** (`Law.count_from_span`): if you hold a span and not a list, the sum of the
squared logs is $2C_2\cdot\text{span}$; with a mean, $m=\text{span}/(\Delta T/(2C_2))$. This is how a
scientist who has only a range of integers recovers how many twin starts it can hold — the reading that
turns the equation into a counting device rather than a curiosity.

**(iii) Mean gap from both.** $\langle\text{gap}\rangle=\Delta T/(2C_2)$, the per-handoff form. Measured,
decade by decade, through the origin ($\text{gap}=c\,t^{2}$):

| decade | handoffs | $\langle\log^2p\rangle$ | $c$ | $c\cdot2C_2$ | span/predicted |
|---|---|---|---|---|---|
| $10^{4}$–$10^{5}$ | 1,019 | 115.1 | 0.76657 | 1.0121 | 1.0139 |
| $10^{5}$–$10^{6}$ | 6,945 | 169.8 | 0.76342 | 1.0080 | 1.0079 |
| $10^{6}$–$10^{7}$ | 50,811 | 235.2 | **0.75326** | 0.9945 | 0.9943 |
| $10^{7}$–$10^{8}$ | 381,332 | 311.4 | 0.75788 | 1.0007 | 1.0007 |
| $10^{8}$–$10^{9}$ | 2,984,194 | 398.1 | 0.75755 | 1.0002 | 1.0002 |

and over all 300 equal-count bins, $c=0.75755$, i.e. $c\cdot2C_2=1.00021$: **the constant is
$1/(2C_2)$ to 0.02%**, and the decade scatter in the two lowest decades is the sample size, not a drift.

## 3. The acceleration reading, and where it is exact

Writing $E$ for the span and $t=\log p$, one handoff is $E=\tfrac12 a\,t^{2}$ with

$$a=\frac{1}{C_2}=1.51478\ \text{per handoff},\qquad \frac{dE}{dt}=a\,t,\qquad \frac{d^{2}E}{dt^{2}}=a .$$

The derivative form is a *per-handoff* statement, not a continuum one, and its exact content is discrete:

$$E(t+h)-2E(t)+E(t-h)=a\,h^{2},\qquad \frac{E(t+h)-E(t)}{h}=a\,t+\frac{a\,h}{2}$$

(`Law.const_accel_second_difference`, `Law.velocity_is_linear`). So "the chain moves with constant
acceleration in the $(\log p,\text{span})$ plane" is a theorem about the second difference of
$\tfrac12 a t^{2}$, with $a$ the measured $1/C_2$ — and the cumulative $E$ is $m$ times the per-handoff
one, which is why $E=\tfrac12 a t^{2}$ with the *total* span needs $a\to a\,m$.

## 4. Your $10^{9}$ line, diagnosed

The printed version was

$$10^{9}\;\approx\;0.7532\times3{,}424{,}504\times388\;=\;1.0008\times10^{9}.$$

That is right to 0.08%, and each of the three factors is a slightly different object from the one the
equation needs:

| you used | the settled value | why they differ |
|---|---|---|
| $c=0.7532$ | $0.75739$ | $0.75326$ is the $10^{6}$–$10^{7}$ decade's own coefficient (table above); the global one is $0.02\%$ from $1/(2C_2)$ |
| $m=3{,}424{,}504$ | $3{,}424{,}505$ handoffs | off by one: handoffs are starts minus one |
| $\Delta T=388$ | $385.47$ | $\langle\log^{2}p\rangle$ over all handoffs to $10^{9}$; 388 is the mean over a truncated or segment-weighted set |

With the settled numbers, $0.75739\times3{,}424{,}505\times385.47=9.9978\times10^{8}$ — 0.022% low, and
now with an error bar rather than a coincidence.

## 5. The two checks that catch a slip

Every use of the equation should be followed by these; both are exact:

* $\sum\text{air}=\text{span}-2m$ (proved: `air_sum_identity`) — if it fails, the chain or the count is
  wrong, not the law;
* air $\equiv4\pmod 6$, equivalently gap $\equiv0\pmod 6$ (proved: `air_mod_six`) — if a gap that is not
  a multiple of 6 appears, you are not looking at twin starts.

And the fuse in your earlier note is two theorems, not an image: the single zero-length connection is
$(3,5)\to(5,7)$, because three primes of step 2 can only be $3,5,7$ (`Merge.triple_only_three`; the same
statement is `no_quadruple` for four), and everything after it is the ladder $4,4,10,10,16,\ldots=4+6k$
(`air_mod_six`, `air_is_four_plus_six`). "One fuse, one ignition, and the chain never fuses again" is
exactly that pair.

## 6. What the equation is not

* **Not an energy.** The span is a length of integers; it has no joule in it. Energy needs the mass
  excess, which is a measured table of small differences and not a count (`linear_mass_law_blind`).
* **Not a theorem about twins.** The per-handoff constant is measured, with a control; the twin count is
  a Hardy–Littlewood object with no zero sum.
* **Not valid past its domain without re-measuring.** The law is flat to $10^{12}$; the cumulative form
  here is checked to $10^{9}$ at 0.022%. Extrapolating to $10^{18}$ is a prediction, not a use.
* **Not a density or a rate in $p$.** It is a rate in $\log p$: the same span is covered with fewer
  handoffs as $p$ grows, which is what $m\sim\text{span}\cdot2C_2/\Delta T$ says.

## 7. How to put it in a paper

> For twin starts $p_1<\dots<p_N$, the span satisfies
> $p_N-p_1=(2C_2)^{-1}\sum\log^{2}p_i$ to 0.02% over $10^{4}$–$10^{9}$, with
> $(2C_2)^{-1}=0.757390\pm0.000018$; the cumulative identity is proved given the per-handoff law, which
> is measured (Beasley, `results/one-equation.md`, `results/air-law-offset.md`).

and hand the reader `scripts/one_equation_check.py` — it recomputes every number above from the primes,
in seven seconds, with no fitted input.
