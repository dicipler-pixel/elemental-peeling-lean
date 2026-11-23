# Depth read as the weak force: same shape, and one number that lands

Taken as a modelling instruction — "depth is the weak nuclear force" — the analogy can be evaluated on
the four axes that define a force: its coupling, its range, where it is the only channel, and how much
structure its own sector carries. On three of the four the depth behaves like the weak force. On the
fourth it does not, and the failure is informative.

## 0. One correction to the premise

"The weak force is strong locally and small globally" is true in effect but not in cause. The weak
coupling is *not* small: with $g$ the SU(2) coupling and $\sin^2\theta_W=0.231$,

$$\alpha_W=\frac{g^2}{4\pi}=\frac{\alpha_{\rm em}}{\sin^2\theta_W}=\frac1{31.7},$$

which is larger than $\alpha_{\rm em}=1/137$ and only a factor 3 below $\alpha_s$. What makes the weak
force weak is its **range** — the $W$ mass, $1/M_W^2$ in every low-energy amplitude,
$G_Fm_p^2=1.0\times10^{-5}$ — not its coupling. So the correct statement is: *coupled like the
electromagnetic force, short-ranged like nothing else, and therefore invisible in bulk.*

That distinction matters, because it is exactly the distinction the depth shows.

## 1. The four axes, measured

| axis | weak force | depth (measured) |
|---|---|---|
| coupling to the visible sector | $\alpha_W=1/31.7$ | $I/H=0.0448/1.568=\mathbf{1/35.0}$ |
| range | $10^{-18}$ m $=1.2\times10^{-3}$ of a nucleon | 1 step $=1/18.9$ of the mean gap |
| where it is the only channel | flavour change, parity violation (100% weak) | the groove choice inside a crossing (the digit sees nothing) |
| structure in its own sector | lifetimes spanning $10^{54}$ | 1.57 bits of depth entropy, all invisible to the digit |

Three of these are near-exact correspondences:

* **The coupling lands.** The depth's share of the information, $2.9\%$ of its own entropy, is $1/35$;
  $\alpha_W$ is $1/31.7$. Ten per cent apart. *(This is a coincidence of numbers — a mutual information
  ratio against a gauge coupling — and should be quoted as one. But it is the right order and the right
  direction: the depth is coupled like the weak force, not like a rounding error.)*
* **It is the only channel where it acts.** Inside a crossing the digit cannot separate the two grooves
  at all (the split is never $100/0$, at best $30/70$); only the depth can. That is the same kind of
  exclusivity as parity violation, where the strong and electromagnetic forces contribute exactly zero.
* **It has structure of its own.** 1.57 bits of depth entropy — a whole sector, not a perturbation. The
  weak sector likewise: its coupling is ordinary, its phenomena (β spectra, lifetimes over 54 decades)
  are not small.

## 2. Where it fails: the range

$$\frac{\text{weak range}}{\text{nucleon}}=\frac{10^{-18}}{0.84\times10^{-15}}=1.2\times10^{-3},
\qquad
\frac{\text{depth range}}{\text{mean gap}}=\frac{1}{18.9}=5.3\times10^{-2}.$$

**The depth's range is 44 times longer, relatively.** And that is exactly why its global share is not
tiny: the depth's $1/35$ global suppression against the weak force's $G_Fm_p^2=10^{-5}$ — a factor 2,800,
three and a half orders. Measured directly — the depth's memory along the ladder:

$$P(\text{next shallow}\mid\text{this shallow})=0.567,\qquad
P(\text{next shallow}\mid\text{this deep})=0.592,$$

a 2.5-point effect at lag 1, falling to 0.7 points at lag 2 (a factor 3.4 per step) — a genuine
one-step interaction, not a contact one.

So: **the depth is a weak force with a long range.** Same coupling, same exclusivity, same sector
richness; but its range is $1/19$ of the spacing instead of $1/850$ of the nucleon, so it survives
summation far better than the real thing.

## 3. What the analogy does and does not buy

**It buys the structure, and the structure is right:**

* two sectors, one of which cannot see the other — the digit fixes the gap mod 10 and is blind to the
  multiple of 10; the weak force is blind to flavour-conserving strong physics;
* a coupling that is ordinary rather than small, with the suppression coming from range;
* exclusivity where it acts — one groove, one force, no alternative channel.

**It does not buy a magnitude.** Using "depth is weak" to predict how small the depth's global effect
should be gives $10^{-5}$; the measurement gives $1/35$, off by 2,800×. The analogy is a *map of
which coordinate does which job*, not a scaling law — the same verdict as the second coordinate and the
mass-excess argument, reached from a third direction.

## 4. The one prediction it makes, and it holds

If the depth is a force acting at a range, its memory must die at that range and not beyond. Measured:
2.5 points at lag 1, 0.7 at lag 2, and the digit correlation (which shares the mechanism) 0.103 → 0.037
→ 0.007 at lags 1, 2, 3. All three decay by a factor 3–4 per step and hit the noise floor within three.
That is the correct signature of a short-range interaction, and it is what a "local" coordinate must
show.

*(Numbers: `scripts/depth_as_weak.py`. Coupling from $I/H$ in [`depth-correlates.md`](depth-correlates.md)
§3; memory from 26.4 million prime steps below $5\times10^8$.)*
