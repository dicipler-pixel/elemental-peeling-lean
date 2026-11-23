# Small jumps that buy a big jump — and what they let you infer

## 1. The neuron's two scales, with measured numbers

| quantity | value | where it comes from |
|---|---|---|
| quantal current (single vesicle) | ~12 pA | Franks & Isaacson, piriform cortex |
| unitary EPSP, mossy fibre → CA3 | $9.6\pm2.4$ mV, decay $\tau=134$ ms | Vyleta & Jonas, eLife 2016 |
| one stimulus fires the cell | $p=0.12$ | same |
| three stimuli at 50 Hz fire it | $p=0.82$ | same |
| threshold above rest | ~30 mV | J. Neurosci 2009, piriform |
| synapses needed to reach it | 75–100 (small cells), 300–400 (large) | same |

So the big jump is ~30 mV of depolarisation, the small jump is 0.5–10 mV, and the ratio — the
**capacity in quanta** — is 3 for the mossy-fibre synapse and 75–400 for a cortical one. The single most
informative number in that table is that one mossy-fibre EPSP fires the cell **12% of the time** and
three fire it **82%**: the big jump is not a bigger version of the small one, it is a *threshold crossing*
that the small ones reach only in number.

## 2. Why the small ones are necessary, not merely sufficient

Because the spike is all-or-none, its size carries nothing. The amplitude is fixed by the cell, so the
only free variables at the output are **whether** and **when**. All the information therefore has to be
carried by *counts* of small jumps — which is why the system is built of them. Three consequences, all
arithmetic:

* **the threshold is a capacity**: 30 mV / 9.6 mV = 3.1 quanta for the mossy fibre, 30/0.3 = 100 for a
  small cortical EPSP. The number of small jumps per big jump is the cell's *resolution*;
* **the leak sets the window**: $\tau=134$ ms means the sum is over the last ~0.1 s. Summation ratios
  measured for that synapse: EPSP2/EPSP1 = 1.86, EPSP3/EPSP1 = 2.60 from summation alone; facilitation
  takes EPSC3/EPSC1 to 3.12. So the third event is worth ~2.6–3.1 of the first, which is what tips 0.12
  into 0.82;
* **the noise scales as $1/\sqrt{n}$**: $n$ quanta that add independently give a mean $nq$ with a spread
  $\sqrt{n}\,q$, so the coefficient of variation is $1/\sqrt{n}$ — 0.58 at 3 quanta, 0.18 at 30, 0.058 at
  300. Reliability is bought in $\sqrt{n}$, not in $n$.

## 3. How that infers — two directions

**(a) What the cell infers.** The spike reports the *integral* of its drive over $\tau$, not the
individual events. The small jumps are only ever seen through their sum, so the sufficient statistic is
the sum: the cell can tell you the drive, and cannot tell you which synapse delivered it. This is exactly
the requirement found on the prime side — a law indexed on a *level* must use the level averaged over
the body, the centroid, never one event (`centroid-and-median.md`). One quantum is an endpoint; the
membrane potential is the centroid.

**(b) What we infer from the small jumps.** This is where the second moment does the work. For $n$
release sites with probability $p$ and quantum $q$,

$$\langle V\rangle = npq,\qquad \operatorname{Var}(V) = np(1-p)q^2
\qquad\Longrightarrow\qquad q = \frac{\operatorname{Var}}{\langle V\rangle}\cdot\frac{1}{1-p}
\;\xrightarrow[p\ \text{small}]{}\; \frac{\operatorname{Var}}{\langle V\rangle}.$$

The **mean** gives the drive and the **variance** gives the quantum: quantal analysis (del Castillo–Katz)
is exactly the statement that the small jumps measure themselves. Without small jumps there would be
nothing to take a variance of — the big jump has no variance to speak of.

## 4. The same two moments in the segment

A twin segment is $2+\text{air}+2$. The interior primes are the small jumps and the air is the big one,
and the correspondence is not a metaphor — it is the same two statistics:

| | neuron | segment |
|---|---|---|
| the sum | $\sum$ quanta $=npq$ | $\sum$ interior gaps $=$ air (exact, no exceptions) |
| the count | $n$ release sites | $m$ inner primes, 13.8 per segment |
| the spread | $\sigma/\mu = 1/\sqrt{n}$ | $\sigma_E/E = 1/\sqrt{m}$ (0.293/0.089/0.027/0.008 vs 0.316/0.100/0.032/0.010) |
| what is inferable | the drive (the integral) | the air (the sum) |
| what is not | which synapse fired | the class or type of the segment beyond its sum (0.005–0.02 bits) |

So both systems build a big jump out of small ones, both make the big jump a *threshold event* (all-or-
none spike; a class in $\{4,10,16,22,28\}$), and both make the small jumps carry their information in the
**first two moments** — mean for the size, variance for the resolution — while the *identity* of the
contributors stays hidden.

## 5. What the analogy predicts, and what would break it

* **predicts** that the trial-to-trial spread of the time-to-threshold falls as $1/\sqrt{n}$, and that
  the quantal count $n$ is recoverable from the variance/mean ratio. Both are standard and both hold.
* **predicts** that the spike *rate*, not the spike shape, carries the signal — which is why the shape is
  stereotyped.
* **would break it** if the big jump carried graded information (it does not: the spike is all-or-none),
  or if the interior of a segment predicted its class (it does not: 0.005–0.02 bits). The two failures
  are the same failure — a threshold collapses the detail into one bit plus a time.

The one line: **small jumps are how a system with a fixed capacity gets its resolution, and the variance
of the small jumps is how you (and it) read the capacity back out.**
