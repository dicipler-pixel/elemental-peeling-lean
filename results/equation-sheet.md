# The equation sheet: both tables, every number, and what carries between them

Everything below is either derived here or measured on data already in this repository. Each equation
carries a tag: **[forced]** (a theorem, no fitting), **[measured]** (a number from the data),
**[fitted]** (a number chosen to match), **[convention]** (a choice, no energy behind it).

---

## 0. Two tables, one form

| | primes | elements |
|---|---|---|
| generator | the wheel $30=2\cdot3\cdot5$ — **fixed** | the shell $2n^2$ — **growing** |
| width of a row | 8 slots | $2(2l+1)$ per block |
| capacity of a row | 7 | $2n^2$, exactly |
| recipe | $p \bmod 30 \in \{1,7,11,13,17,19,23,29\}$ | $n+l$ increasing, ties by $n$ |
| balance | at most 7 primes per 30-block | $\sum_l 2(2l+1)=2n^2$ |
| free scale | the magnitude $\log p$ | the shell index $n$ |

The shared form is **capacity + recipe + balance + one free scale**. The shared content is that a
*fixed* capacity can be addressed by a residue (a key), while a *growing* one cannot — §3 measures that.

---

## 1. The primes

### 1.1 The wheel **[forced]**
$$30 = 2\cdot3\cdot5,\qquad \varphi(30)=8,\qquad R=\{1,7,11,13,17,19,23,29\}.$$
Every prime $>5$ is in one class of $R$ mod 30, and the eight classes have equal share of the primes to
0.02% (§3). $8=\varphi(30)$ is also $2+6$, the widths of the $s$ and $p$ blocks — a coincidence of
widths that carries no information (measured: $-0.142$ bits about the block). **[convention]**

### 1.2 The base key: 16 cells **[forced]**
With $b$ the last digit of the lower prime and $e$ the last digit of the upper,
$$\text{gap}\equiv e-b \pmod{10},\qquad 16 = 4\cdot5-4 .$$
The 4 subtracted are the four pairs that land on 5 ($1\to+4$, $3\to+2$, $7\to+8$, $9\to+6$); zero
exceptions in 50.8M gaps. Floors $4,10,16,22,28$ by digit step, five per digit.

### 1.3 The twin key: 9 cells **[forced]**
Twin starts are $p\equiv 11,17,29 \pmod{30}$, so pair types are $13=(1,3)$, $79=(7,9)$, $91=(9,1)$:
$$9 = 3\cdot5-3-3,\qquad \text{floors } 8,14,20,26,32 .$$
The label is the $3\times3$ matrix of pair-type transitions; $T=2+\text{air}+2$ is palindromic, so the
median sits at $T/2$ by symmetry (see `centroid-and-median.md`).

### 1.4 Air **[measured + forced]**
$$\text{air}\equiv\text{class}\pmod{30},\qquad \text{air}\equiv 4 \pmod 6,$$
zero exceptions over 224M handoffs (the mod-6 part is forced: every twin class is $\equiv 2 \pmod 6$ and
$T=\text{air}+4$). The magnitude law is
$$\langle\text{air}\rangle = c\,t^2-2,\qquad t=\log p,\qquad c=\frac{1}{2C_2}=0.75739,$$
flat to 0.05% across four decades when $t^2$ is averaged over the segments (`centroid-and-median.md`).
The offset $-2$ is the half-pair: the offsetless form is the **gap**, $\langle\text{gap}\rangle=c\,t^2$,
start to start. The older number $0.7503\pm0.0032$ was this constant with the offset set to 0, averaged
over five decades; it fails at $10^{10}$ (`air-law-offset.md`).

### 1.5 The energy equation
$$E = c\,m\,\Delta T,\qquad \Delta T=\langle t^2\rangle,\qquad \sum\text{air}=p_{\text{last}}-p_{\text{first}}-2m .$$
$E$ is the summed air, $m$ the number of segments, $\Delta T$ the **centroid** of $t^2$ over them; with
a single level in place of the centroid the constant drifts 0.65 → 0.70 across decades. Equivalently
$\tfrac12 a t^2$ with $a=2c=1.5006$ — a constant "acceleration" in $\log p$.

### 1.6 A row of the prime table **[forced + measured]**
Row index = subset number $s=\lfloor p/30\rfloor+1$. Each column is Bernoulli with occupancy $q$, so
$$\langle\text{subset gap}\rangle = \frac1q = \frac{8}{30}\cdot\frac{x}{\pi(x)},\qquad
P(\text{gap}=1) = 0.1797\ \ (\text{vs } 1/5.244 = 0.1907).$$
Measured over $10^9$: mean 5.2440–5.2452, columns 6,354,987–6,356,475 (0.02% apart). The 6% deficit of
gap-1 pairs against geometric is real and **unexplained**.

### 1.7 Two theorems in the table
$$\text{capacity}=7:\quad 30k+r \bmod 7 = 2k+\mathbb{Z}/7,\ \text{so one of the eight is } \equiv 0 \pmod 7;$$
$$\text{longest run of 1s}=5:\quad \text{seven consecutive terms harbour a multiple of } 7,\ \text{and } 7,\dots,187\notin\mathbb{P}\ (\cdot\,187=11\cdot17).$$

### 1.8 The carry at 2-gaps **[forced]**
$$g\equiv 2 \pmod 6 \ \Longrightarrow\ g_{\text{next}}\neq 2,\ \text{so } g_{\text{next}}\ge 4,$$
because $p\equiv2 \pmod 3 \Rightarrow p+4\equiv 0 \pmod 3$. Zero exceptions in 14,107,248. Unique to the
prime 3: no such exclusion exists mod 5, 7 or 11.

### 1.9 Five scales **[measured]**
Period $=1/\text{density}$ of the thing counted: segment 1, twin digit 3 (classes equal to 0.085%),
prime digit 4 (0.009%), gap digit 5 (shares 17.4–23.0%, **not** equal), mod-30 class 8 (0.023%).

### 1.10 The spectrum
The object is mod 30, so the right spectrum is the five L-functions of conductors $1,3,5,15$, not $\zeta$:
rungs match L-zeros at 12–80× background, $\zeta$-zeros at $p=0.19$ (not significant).

---

## 2. The elements

### 2.1 Width, capacity, depth **[forced]**
$$w_l = 2(2l+1) \to 2,6,10,14,\qquad \sum_{l<n} 2(2l+1)=2n^2 \to 2,8,18,32,$$
$$\mathrm{depth}_l=\#\{n: l+1\le n\le 8-l\} \to 8,6,4,2\quad(s\text{ cut to }7:\ 8s\notin \mathbb{N}_{118}),$$
$$\sum_l w_l\,\mathrm{depth}_l = 2\cdot7+6\cdot6+10\cdot4+14\cdot2 = 14+36+40+28 = 118 = 120-2 .$$
The arithmetic allows 120; the measured sequence stops at 118, two cells ($8s^2$) short.

### 2.2 The index and the register
$$(n+l,\ n)\ \text{increasing},\ 2\ \text{per orbital} \ \Longrightarrow\ 99\ \text{of}\ 118\ \text{exact},\ 19\ \text{exceptions}.$$
The 19 split **ten and nine** by the index gap they cross (§2.3, §2.5).

### 2.3 The step cost **[forced]**
With $k$ electrons in a subshell of capacity $C=2(2l+1)$ and $u=\min(k,C-k)$ unpaired spins,
$$\Phi(k)=\binom{u}{2},\qquad G(k)=\Phi(k+1)-\Phi(k)=
\begin{cases} k, & k\le \tfrac{C-2}{2}\\[2pt] k-(C-1), & k>\tfrac{C-2}{2}\end{cases}$$
$$G_d = 0,1,2,3,4,-4,-3,-2,-1,0,\qquad G_f = 0,1,2,3,4,5,6,-6,-5,-4,-3,-2,-1,0 .$$
A step costs anything from $-4$ to $+4$ (d) or $-6$ to $+6$ (f) exchange quanta; the index charges 1.

### 2.4 The amended rule — family A, ten elements **[fitted, exact]**
Promote $ns\to(n-1)d$ iff $G(k)K > \Delta(k)$ with a linear rung $\Delta(k)=A-Bk$:

| series | $A$ | $B$ | crossing $k^\*=A/B$ | flips predicted = measured |
|---|---|---|---|---|
| 3d | 6.74 | 0.88 | 7.7 | Cr, Cu |
| 4d | 7.51 | 1.88 | 4.0 | Nb Mo Ru Rh Pd Ag |
| 5d | 11.52 | 1.77 | 6.5 | Pt, Au |

Six numbers reproduce all thirty d-block decisions. $B$ is the screening rate: the rung falls by
1–2 exchange quanta per electron, crosses zero inside the series, and after the crossing every element
promotes. That is why the exceptions are a block, not scattered.

### 2.5 The ties — family B, nine elements **[measured]**
$4f$ and $5d$ both have $n+l=7$; $5f$ and $6d$ both have 8. The index orders nothing there and the
tie-break $n$ is a **[convention]**. Measured: the $d$ level wins at $k_f=0,1,7$ in $4f$ (La, Ce, Gd) and
at $k_f=0,1,2,3,4,7$ in $5f$ (Ac, Th, Pa, U, Np, Cm). No linear rung fits — the constraints force the
rung to rise above $+6$ at $f^6$ and fall below $-6$ at $f^8$, so the $f/d$ gap changes sign twice per
series. The half-shell $f^7$ is worth $+6$ quanta and is the largest single step in the table.

---

## 3. What correlates, and how strongly

| structure | primes | elements | status |
|---|---|---|---|
| capacity fixed vs growing | 7 per row, forever | $2n^2$, grows | **the** difference; it decides whether a residue key works |
| width $=2\times$ odd | 8 columns | $2(2l+1)$ | coincidence of widths, $-0.142$ bits measured |
| balance | $\le 7$ of 8 (one hole forced by 7) | $\sum=2n^2$ exact (no hole) | width $-$ capacity $=1$ vs $0$ |
| recipe | residue class | $(n+l,n)$ | both are ranks; only one has a physical meaning |
| the ladder | floors $4,10,\dots$ (step 6) | $2(2l+1)$ (step 4) | both arithmetic; neither predicts the other |
| the register | blocks where two of eight vanish | 19 named elements | both are "law plus named exceptions" |
| the scale | $\log p$ | $n$ | one free scale each |

Measured information, for the record: $I(Z\bmod10;\text{block}) = -0.142$ bits (worse than chance),
$I(Z\bmod10;\text{group}) = +0.108$ bits (mostly parity, since mod 2 alone gives $+0.608$ of 3.795), and
the prime columns are equal to 0.02% while the element blocks are not equal at all.

---

## 4. More terms

**Primes — the next term in the air law is bounded, not found.** Fitting
$\langle\text{air}\rangle = c t^2 + d\,t$ over the five decades gives
$$c = 0.7570\pm0.0081,\qquad d = -0.105\pm0.138,$$
so $d$ is $0.8\sigma$ from zero: at 1% precision below $10^9$ the law is purely quadratic — there is no
measurable linear term. **Note what $c$ came out as: $0.7570\pm0.0081$.** That is $1/(2C_2)=0.75739$ to
$0.05\sigma$ and $\tfrac34$ to $0.9\sigma$ — the two-term fit was already pointing at the
Hardy–Littlewood constant, and the record chose the other reading on the strength of a five-decade mean.
The correct form, settled at $10^{11}$, is
$\langle\text{air}\rangle=\tfrac{1}{2C_2}t^2-2$ (offset $-2$, the half-pair; the offsetless form is the
gap, start to start) — `air-law-offset.md`.

**Elements — the second term is the pairing energy.** The $-4$ step at the half-fill in $G_d$ is where
pairing enters (an electron must double up before it can pair down). Writing the step cost as
$G(k)K + P\cdot[\text{pair formed}]$ reproduces the flat top of $G$ at $k=5$ and adds one parameter per
series; the data do not yet distinguish it from the bare linear rung, so I report the rung alone.

**The next rows of the table** (arithmetic only, no elements yet):

| $n$ | widths | $2n^2$ | filled by $Z\le118$ |
|---|---|---|---|
| 8 | $2,\dots,30$ | 128 | $0$ ($8s$ at $Z=119,120$) |
| 9 | $2,\dots,34$ | 162 | 0 |
| 10 | $2,\dots,38$ | 200 | 0 |

$5g$ ($l=4$, 18 wide) opens at $Z=121$. Note that $5g$ and $8s$ differ by one rung ($n+l=9$ vs 8), so
the same competition that produced family A is available at the head of the g series.

---

## 5. Predictions and their tests

| # | prediction | how it was tested | result |
|---|---|---|---|
| **P1** | twin-pair counts: $N(x)=\frac{1}{c}\int_2^x \frac{dp}{\log^2 p}$ with $c=\tfrac{1}{2C_2}=0.757390$ | compared with A007508 at $10^8,10^9,10^{10},10^{11}$ (sieve counts exact: 440,312 / 3,424,506 / 27,412,679 / 224,376,048) | $+0.013\%,\ +0.023\%,\ -0.005\%,\ -0.003\%$ — no free parameter |
| **P2** | mean air in a decade $=c\langle t^2\rangle-2$ with $c=\tfrac{1}{2C_2}$ | seven decades, centroid form | flat to 0.05% from $10^7$ on; $3/4$ falsified at $78\sigma$ |
| **P3** | capacity 7; longest run of 1s $=5$ | proof + $10^9$ | exact, attained |
| **P4** | the d-block decisions from six numbers | all 30 d elements | 30/30; the ten flips are the ten measured |
| **P5** | the five scales' equalities: 0.009%, 0.023%, 0.085% | measured | as predicted; the 5-class scale fails (17.4–23.0%) |
| **P6** | the 19 exchange promotions split 10 (one rung) + 9 (tie) | classification | exact; no exception crosses two rungs |

Two of these are honest failures of description and should be carried as such:

* $P(\text{gap}=1)=0.1797$ against the geometric $0.1907$: a 6% deficit I have not explained;
* the $f/d$ ordering is not a rung at all — it oscillates by more than 12 quanta inside a series, so no
  linear model covers family B.

## 6. Limits

The element rule is fitted on the d block and *therefore* cannot be claimed as an out-of-sample success
there; its content is that six numbers replace ten names, and that the crossing — not the half-fill —
is what organises the set. The prime side's predictions are out of sample and parameter-free (P1) or
proved (P3). Nothing here predicts a prime from the elements or an element from the primes: the two
tables share a form, and the form is a capacity plus a recipe plus a balance plus one free scale.
