# The merge hierarchy: 2 to 7 pairs, and a correction

Data: primes below $10^{10}$ for the run-length census (27,412,676 handoffs), below $10^{11}$ for the
cumulative totals (224,376,047 handoffs = A007508(11) $-1$).

## Correction first

Last time I reported "merges cluster, +13.5%". **That was a definition slip on my part** and I am
retracting it. I quoted $R_2/R_1$ — the ratio of runs of length 2 to runs of length 1 — as the
continuation probability. It is not. The continuation probability is
$$\frac{\sum_r (r-1)R_r}{\sum_r r\,R_r},$$
because a run of length $r$ contributes $r$ merged handoffs and $r-1$ consecutive pairs. Done
properly:

| $x$ | merged handoffs | consecutive pairs | $P(\text{merge})$ | $P(\text{continue}\mid\text{merged})$ | relative |
|---|---|---|---|---|---|
| $10^9$ | 234,287 | 16,046 | 0.06841 | 0.06849 | +0.1% |
| $10^{10}$ | 1,669,476 | 101,015 | 0.06090 | 0.06051 | −0.6% |
| $10^{11}$ | 12,317,562 | 665,188 | 0.05490 | 0.05400 | −1.6% |

So merges do **not** cluster: the continuation probability matches the baseline to within 2%, with a
hint of a slight *deficit* growing with $x$. My original $10^9$ statement was right; the $10^{10}$
"+13.5%" was wrong. This also means the merge hierarchy is close to independent draws with
$p=P(\text{merge})\approx0.055$ at $10^{11}$.

## The hierarchy itself

| pairs in one segment | count $<10^{10}$ | step ratio |
|---|---|---|
| 2 | 1,473,152 | — |
| 3 | 89,876 | 0.0610 |
| 4 | 5,171 | 0.0575 |
| 5 | 252 | 0.0487 |
| 6 | 9 | 0.0357 |
| 7 | 1 | (0.111) |

Six levels deep. The step ratios *decline* (0.061 → 0.036) even though the average continuation
matches the baseline — the deeper levels need longer spans, so they are individually harder. The last
ratio is one sample and should be ignored.

## Floors by depth — a carry pattern

Minimum total $T$ per class at each depth (classes $8,14,20,26,32$):

| depth | class 8 | class 14 | class 20 | class 26 | class 32 |
|---|---|---|---|---|---|
| 2 pairs | 8 | 14 | 20 | 26 | 32 |
| 3 pairs | 38 | 44 (14 at $p{=}5$) | 20 | 26 | 32 |
| 4 pairs | 38 | 44 | 50 | 56 | 32 |
| 5 pairs | 98 | 44 | 50 | 56 | 62 |

Each depth pushes some classes up by 30 and leaves others; the mechanism is that the minimal
configuration at that depth becomes inadmissible mod 5 or mod 7, exactly as $\{0,2,6,8,12,14\}$ is
killed at depth 3. The deep floors are not simply the shallow floors plus $30k$ — they carry
unevenly, class by class.

A second consequence: at depth $\ge3$ the floor stops being the most probable total. For 4 pairs,
label 7:1 has $44{:}177$ and $74{:}266$ — the *second* rung is commoner than the first. For 1:9 the
mode is at 98 ($98{:}122$ against $38{:}94$). The distribution at depth becomes humped, so a "ladder"
reading is only valid at depth 2.

## Key table: 4 PAIRS (r = 3 merged handoffs), $10^{10}$, 5,171 segments

| label | class | $T$ (count) | min $T$ |
|---|---|---|---|
| 7:3 | 26 | 56:357 · 86:290 · 116:142 · 146:27 · 176:13 · 206:4 · 236:1 | 56 |
| 7:1 | 14 | 44:177 · 74:266 · 104:164 · 134:62 · 164:9 · 194:6 · 224:4 · 284:1 | 44 |
| 9:3 | 14 | 44:198 · 74:271 · 104:147 · 134:53 · 164:12 · 194:4 · 224:1 · 254:1 | 44 |
| 9:1 | 32 | 32:45 · 62:241 · 92:168 · 122:39 · 152:23 · 182:3 · 212:2 · 242:2 | 32 |
| 1:3 | 32 | 32:68 · 62:216 · 92:167 · 122:54 · 152:25 · 182:8 · 212:4 | 32 |
| 7:9 | 32 | 32:73 · 62:201 · 92:128 · 122:67 · 152:26 · 182:7 · 212:3 | 32 |
| 9:9 | 20 | 50:163 · 80:176 · 110:75 · 140:44 · 170:15 · 200:3 · 230:2 | 50 |
| 1:1 | 20 | 50:190 · 80:152 · 110:71 · 140:42 · 170:14 · 200:3 · 230:1 | 50 |
| 1:9 | 8 | 38:94 · 68:90 · 98:122 · 128:85 · 158:35 · 188:9 · 218:4 | 38 |

Same nine labels, same five classes, same value ladder. 5 pairs: 252 segments, floors 98/44/50/56/62;
6 pairs: 9; 7 pairs: 1.

## The spectra at $10^{11}$: positions sharpen, artefacts do not

Peak positions against the independently computed $L$-zeros, primes below $10^{11}$:

| spectrum | predicted | measured | mean error |
|---|---|---|---|
| $\zeta$ | 14.1347, 21.0220, 25.0109, 30.4249, 32.9351 | 14.141, 21.020, 24.999, 30.416, 32.933 | 0.007 |
| $\chi_{-3}$ | 8.0397, 11.2492, 15.7046, 18.2620, 20.4558 | 8.029, 11.241, 15.699, 18.264, 20.445 | 0.006 |
| $\chi_5$ | 6.6485, 9.8314, 11.9589, 16.0338, 17.5670 | 6.639, 9.827, 11.960, 16.035, 17.569 | 0.005 |
| $\chi_{-15}$ | 3.0570, 5.3432, 7.2676, 10.1338, 12.1597 | 3.068, 5.345, 7.262, 10.139, 12.152 | 0.009 |
| quartic | 6.1836, 8.4572, 12.6750, 14.8250, 17.3378 | 6.184, 8.461, 12.679, 14.836, 17.329 | 0.006 |
| $\psi\chi_{-3}$ | 2.7346, 5.2430, 8.4147, 10.1876, 11.9074 | 2.732, 5.225, 8.413, 10.187, 11.912 | 0.006 |

Mean position error **0.006**, against a nominal resolution $2\pi/\log x = 0.248$ — the peaks are
sharp enough that their centroids beat the resolution by 40×.

But **the low-$\gamma$ artefacts did not improve**. The spurious peak at 2.68 in the principal
spectrum went from 14× background at $10^{10}$ to 24× at $10^{11}$. That is the signature of the jump
noise: $\psi$ is a step function, so it carries a $1/\gamma$ tail whose Fourier amplitude grows like
$\sqrt{\log x}$ while the zero-driven signal stays $O(1)$. A longer range therefore *worsens* the
artefact-to-signal ratio at low $\gamma$, even as it sharpens every real peak. Removing it needs a
different analysis (subtract the smooth part per class, or integrate against a test function), not
more primes.

Also confirmed negative: subtracting the trivial-zero term $\frac12\log(1-x^{-2})$ or
$-\operatorname{artanh}(1/x)$ changes the spectra by nothing measurable, so my earlier guess that the
artefact was the parity term was wrong.
