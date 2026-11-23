# The per-system test, run: the digit ratio is a level, not a mechanism

The test I proposed, and its answer: **the level agreement survives and gets sharper; the per-system
tracking fails, and fails for a structural reason.** `scripts/per_system_digit_ratio.py`,
[`tableV9_per_system.csv`](tableV9_per_system.csv).

## 1. Does $R_{\text{digits}}$ move at all?

$R_{\text{digits}}=\sum(\text{closing digits})/\sum(\text{opening digits})$ on any window of handoffs:

| window | handoffs | $R_{\text{digits}}$ |
|---|---|---|
| decade $10^{4}$–$10^{5}$ | 1,019 | 0.7647 |
| decade $10^{6}$–$10^{7}$ | 50,811 | 0.7648 |
| decade $10^{8}$–$10^{9}$ | 2,984,193 | 0.764785 |
| first half of the chain | 1,712,251 | 0.764784 |
| second half | 1,712,251 | 0.765005 |
| all | 3,424,504 | **0.764895** |

The value is a constant of the digit alphabet — closers $\{3,9,1\}$ sum to 13, openers $\{1,7,9\}$ sum to
17 — so restricting the window cannot change it except by noise. Noise is measurable: over 400 random
windows of 2,000 handoffs, s.d. $=0.0143$, so **a move smaller than 0.043 is noise at this window size**,
and a window of $2\times10^{5}$ handoffs reduces that to $\pm0.004$.

## 2. The positional analogue of each parent

The table places a parent at $Z/118$ of its ladder, so its prime-side analogue is the handoff at the same
fraction of the chain ($\log p/\log 10^{9}=Z/118$). $R_{\text{digits}}$ in a $2\times10^{5}$-handoff
window there, against the measured fission ratio:

| $Z$ | $Z/118$ | $R_{\text{digits}}$ there | measured $Z_L/Z_H$ |
|---|---|---|---|
| 90 | 0.7627 | 0.766146 | 0.6854 |
| 92 | 0.7797 | 0.766036 | 0.7113 |
| 93 | 0.7881 | 0.765397 | 0.7232 |
| 94 | 0.7966 | 0.764595 | 0.7414 |
| 95 | 0.8051 | 0.764312 | 0.7458 |
| 96 | 0.8136 | 0.765716 | 0.7639 |
| 98 | 0.8305 | 0.765129 | 0.7659 |
| 100 | 0.8475 | 0.765663 | 0.8103 |

* spread of $R_{\text{digits}}$ across the parents: **s.d. $6.2\times10^{-4}$**, range $0.0018$;
* spread of the fission ratio across the same parents: **range $0.125$ — 68× wider**;
* correlation $r=-0.265$, shuffle null giving $p=0.53$.

So the answer to the proposed test: **they do not track.** A quantity whose entire range is 0.0018 cannot
follow a quantity whose range is 0.125.

## 3. Why, and what would have to be true for tracking

The digit ratio is invariant because the digit alphabet is: each of the three openers and each of the three
closers carries one third of the handoffs at every height (measured shares equal to 0.05%). The only
height-dependent quantities in the twin table are far too small:

| quantity | decade $10^{4}$ | $10^{6}$ | $10^{8}$–$10^{9}$ | total variation |
|---|---|---|---|---|
| counterflow, one way / the other | 1.0453 | 1.0068 | 1.0073 | 4% |
| self-share (diagonal) | 0.3350 | 0.3359 | 0.3326 | 1% |
| $R_{\text{digits}}$ | 0.7647 | 0.7648 | 0.7648 | 0.02% |

The fission ratio varies **21%** across the actinide set, driven by the parent's charge. Nothing in the
digit table varies by 21% at any height, so no window restriction can make it track.

## 4. What does survive — and it is the sharper half

The equation $R_{\text{digits}}=(Z-54)/54$ predicts the crossing at

$$Z^\star=54\Bigl(1+\tfrac{13}{17}\Bigr)=95.29 .$$

Interpolating the measured ratios, the crossing where $Z_L/Z_H=13/17$ happens at

$$Z_{\text{cross}}=96.79\qquad(\text{between }Z=96:0.7639\text{ and }Z=98:0.7659),$$

a difference of $1.50$ in $Z$, i.e. **$2.8\%$ in the ratio — about one standard deviation** of the
system-to-system scatter ($2.7\%$). So the level statement is consistent with the data at $1\sigma$; it is
not a sharp determination, and it cannot be sharpened by more prime data, because the prime side of it is a
constant.

## 5. The honest verdict

| claim | verdict |
|---|---|
| the digit ratio $13/17$ falls inside the fission band | **yes** (0.7647 in 0.668–0.810) |
| its implied charge $Z^\star=95.29$ lands among the measured systems | **yes** — between Am-241 (95) and Cm (96) |
| the measured crossing matches it | **to $1\sigma$** ($96.8$ against $95.3$) |
| the digit ratio *tracks* the fission ratio system by system | **no** — range 0.0018 against 0.125, $p=0.53$ |
| therefore it is a mechanism | **no** — it is a coincidence of *levels*, and a forced one |

The claim is accurate about fission **as a level**: the number the digit alphabet generates is a number the
actinide ratios pass through, at a charge that is one of the ones measured. It is not accurate as a
mechanism, and the test that would have shown a mechanism — per-system tracking — comes out flat by 68×.

What would change that verdict: a prime-side quantity that (i) varies by ~20% across the chain and (ii) is
indexed by a charge-like coordinate. Nothing in the record has both; the closest is the mean gap, which
varies by a factor 7 but is indexed by height, and mapping height to $Z$ by position gives a spurious
positive correlation (both sides monotone in the proxy) — which is why the shuffle control in §2 is the one
that decides.
