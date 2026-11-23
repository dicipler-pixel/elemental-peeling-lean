# Does the peel ladder flow? A 20-minute check on the archive

Question asked: is the "peel-rate test" ($\omega/2$ versus $\omega$ at $\Gamma=0$) the thing to run first,
or is the formalization note first?

To answer it I checked whether the ladder is an instance of the flow at all. Data:
`data/H_to_At_thresholds.csv`, the same table `LoopWall/Archive.lean` certifies. Every run$-$1 consecutive
ratio $z_k = \mathrm{IE}_{k+1}/\mathrm{IE}_k$ below is taken from the CSV's own `z` column; 84 elements,
3,570 steps.

## What the framework needs

`LoopWall` defines $z$ as the ratio of successive records, and $\Gamma = (z-1)/(z+1) = \tanh(\tfrac12\log z)$,
then gives the clock $\Gamma = \tanh(\omega\tau/2)$, i.e. $\Gamma' = (\omega/2)(1-\Gamma^2)$.
One removal is one record step, so the only chart the definitions supply is $\tau = k$.
In that chart the framework's statement is that $\log z_k$ is **affine in $k$** — the peel ratios of a
ladder form a geometric progression, one $\omega$ and one offset per element.

## It is not

Per element, $n \ge 6$ steps (79 ladders), $R^2$ of each candidate law against $\Gamma_k$:

| law | median $R^2$ | what it says |
| :-- | :-: | :-- |
| $\Gamma_k = \tanh((p+qk)/2)$ | **0.035** | the framework's clock, $\tau = k$ |
| $\log z_k = p + qk$ (geometric ladder) | **0.025** | the same thing written in $z$ |
| $\Gamma_k = A/k$ | 0.074 | the hyperbolic branch $\Gamma' = -\mu\Gamma^2$ |

All three are poor, and the ranking is against the framework. The ladders are not a smooth flow in $k$
under any of them; the within-element variance is dominated by discrete shell closures, not by a trend.

## The one regular pattern

Pooled median of $k\,\Gamma_k$ over all 84 elements:

| $k$ | 1 | 2 | 3 | 5 | 8 | 12 | 20 | 30 | 40 | 55 | 70 |
| :-- | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: |
| $k\Gamma_k$ | 0.34 | 0.52 | 0.60 | 0.63 | 0.62 | 0.66 | 0.69 | 0.71 | 0.70 | 0.74 | 0.75 |

So asymptotically $\Gamma_k \approx 0.7/k$, equivalently $z_k = 1 + c/k$ with $c = 1.44$
(pooled median of $(z_k-1)k$ over $k\ge2$: **1.44**, interquartile range 1.24–1.86;
per-element medians 80 ladders: 1.44, 10–90% range 1.26–1.47). Equivalently
$\mathrm{IE}_K \propto K^{1.44}$ along a ladder, since $\log z_k \approx c/k$ sums to $c\log K$.

That is the $\Gamma' = -\mu\Gamma^2$ Riccati, not $\Gamma' = (\omega/2)(1-\Gamma^2)$. They disagree
everywhere except at small $\Gamma$, where both are $\Gamma' \approx$ const and $\Gamma' \approx -\mu\Gamma^2$
respectively — they do not agree at $\Gamma = 0$, which is exactly where the declared discriminating
measurement sits.

## Where the wall bites

$z > 3+2\sqrt2 = 5.8284$ at exactly **8** of the 3,570 steps, and all 8 are core-opening steps at $k \le 4$:

| element | $k$ | $z$ |
| :-- | :-: | :-: |
| Li | 1 | 14.03 |
| Be | 2 | 8.45 |
| B | 3 | 6.84 |
| C | 4 | 6.08 |
| Na | 1 | 9.20 |
| K | 1 | 7.29 |
| Rb | 1 | 6.53 |
| Cs | 1 | 5.95 |

This matches `LoopWall/Archive.lean`'s "8 outside" and it is the strongest empirical statement in the repo:
the wall isolates precisely the first removal after a closed shell. It is an *ordering* statement on 8 of
3,570 steps, and by the repo's own cutoff-window theorem it cannot fix the wall's value.

## What follows for the two candidate next steps

1. **The peel-rate test cannot be run as posed.** It needs a chart, and the only chart the definitions
   give ($\tau = k$) is refuted at $R^2 = 0.035$. Choosing another chart makes the clock vacuous: any
   strictly monotone $\Gamma$ is $\tanh$ of *some* $\tau$. Until $\tau$ is tied to an observable, there is
   no experiment, and the $\omega/2$ versus $\omega$ contrast has nothing to discriminate.
2. **The note has something to say, and it is not what I sketched.** Its empirical section is the above:
   a correct, standard smooth-flow algebra; a ladder that is not a smooth flow; one asymptotic slope
   ($\Gamma \approx 0.7/k$); and 8 steps that the wall isolates exactly.

Reproduce: the analysis is plain CSV arithmetic; `python3` on `data/H_to_At_thresholds.csv`, columns
`k`, `z`, `kind == "IE"`, grouped by `symbol`.
