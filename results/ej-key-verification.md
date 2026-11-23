# Verification of the EJ key, binary and twin rules against the primes

Test data: every prime below $10^9$ (50,847,534 of them, 50,847,533 gaps) and every twin pair below
$10^{10}$ (27,412,679, checked against A007508). Counts below are from the $10^9$ run unless marked.

---

## 1. IMG_5775 "Pattern key: Base" — verified exactly, all five columns

Your columns are the digit step $\delta=(b-a)\bmod 10$; the entries are the end-digit pairs that can
realise it. Every entry is a real transition, its minimum gap **is** the column, and no pair outside
your list has that minimum — 50.85M gaps, zero exceptions.

Note what that means: your five columns contain **16 entries, which is all 16 ordered pairs of
{1,3,7,9}**, each appearing exactly once, because $(b-a)\bmod10$ is unique per pair. So the table is a
complete enumeration of the end-digit transition grid, not a sample of it. That is a stronger object
than a "pattern key" — it is the full transition table, sorted by step.

| step | your pairs | count | min gap | mean gap |
|---|---|---|---|---|
| 2 | 1:3 | 3,795,751 | 2 | 16.6 |
| 2 | 7:9 | 3,796,948 | 2 | 16.5 |
| 2 | 9:1 | 4,092,457 | 2 | 17.0 |
| 4 | 3:7 | 3,595,468 | 4 | 19.6 |
| 4 | 7:1 | 3,243,702 | 4 | 18.9 |
| 4 | 9:3 | 3,243,354 | 4 | 18.9 |
| 6 | 1:7 | 3,842,263 | 6 | 17.2 |
| 6 | 3:9 | 3,840,531 | 6 | 17.2 |
| 6 | 7:3 | 3,443,707 | 6 | 17.1 |
| 8 | 1:9 | 2,744,958 | 8 | 22.4 |
| 8 | 3:1 | 3,046,813 | 8 | 22.2 |
| 8 | 9:7 | 3,046,626 | 8 | 22.2 |
| 10 | 1:1 | 2,328,414 | 10 | 24.2 |
| 10 | 3:3 | 2,229,686 | 10 | 25.1 |
| 10 | 7:7 | 2,227,956 | 10 | 25.1 |
| 10 | 9:9 | 2,328,896 | 10 | 24.2 |

It is correct as written, complete, and needs no repair. The only pairs your table omits are the ones
involving the end digit 5 — $(3,5)$ and $(5,7)$ — which occur once each, at the very start.

## 2. IMG_5933 gap table — correct except two slips

For each gap you list, the digit step is the gap mod 10, and the pairs must be the ones whose
digit-step equals it. Everything checks, with two corrections:

| gap | digit step | pairs that actually occur (with counts) | your entry |
|---|---|---|---|
| 8 | 8 | 1:9 = 790,140 · 3:1 = 952,085 · 9:7 = 952,884 | 5:3, 1:9 — 1:9 correct |
| 14 | 4 | 3:7 = 932,758 · 7:1 = 765,898 · 9:3 = 765,909 | 7:1, 9:3 correct |
| 20 | 0 | 1:1 = 422,558 · 3:3 = 489,061 · 7:7 = 489,820 · 9:9 = 422,604 | 1:1 correct |
| 26 | 6 | **1:7 = 378,366 · 3:9 = 377,829 · 7:3 = 363,390** | 7:3 correct; 7:9, 9:1, 1:3 do **not** belong here |
| 32 | 2 | 1:3 = 229,693 · 7:9 = 229,813 · 9:1 = 224,390 | all three correct |
| 38 | 8 | 1:9 = 167,257 · 3:1 = 191,072 · 9:7 = 190,417 | 1:9 correct |
| 44 | 4 | 3:7 = 152,582 · 7:1 = 118,223 · 9:3 = 118,829 | header written "24" — should be 44 |
| 50 | 0 | 1:1 = 74,594 · 3:3 = 89,602 · 7:7 = 89,157 · 9:9 = 74,713 | 9:9, 1:1 correct |
| 56 | 6 | 1:7 = 70,920 · 3:9 = 70,884 · 7:3 = 69,658 | 7:3 correct |
| 62 | 2 | 1:3 = 37,797 · 7:9 = 38,009 · 9:1 = 39,752 | 1:3 correct |

Two corrections: the **26 column contains 7:9, 9:1, 1:3, which have digit step 2 and belong in the 32
column**; and the header written **24** is **44** (the headers are the AP $8+6k$: 8,14,20,26,32,38,44,
50,56,62, which is forced by gap $\equiv 4 \pmod 6$). Also "5:3" under gap 8 is real but unique: it is
the step $5\to13$, the only gap-8 with a leading digit 5.

## 3. "Every twin segment can't start with a 7 or end in a 3"

Both halves are **true and provable** — but for the run between pairs, not for the pair.

**For the pair, the rules run the other way.** A twin pair $(p,p+2)$ with $p>3$ has $p\equiv5\pmod6$,
so $p\equiv11,17,29\pmod{30}$ and $(p,p+2)$ is $1{:}3$, $7{:}9$ or $9{:}1$. Therefore:

| | allowed last digit | never | count below $10^9$ |
|---|---|---|---|
| pair's **first** member | 1, 7, 9 | **3** | 1,141,217 / 1,142,128 / 1,141,159 |
| pair's **second** member | 1, 3, 9 | **7** | 1,141,159 / 1,141,217 / 1,142,128 |

So a pair never *starts* with 3 and never *ends* in 7. Your sentence is the mirror image.

**For the air between two pairs, your sentence is exactly right.** The air runs from the larger member
of one pair to the smaller member of the next. Its leading digit is the previous pair's end digit,
$\{1,3,9\}$ — never 7. Its closing digit is the next pair's first digit, $\{1,7,9\}$ — never 3.

| | observed | never | counts |
|---|---|---|---|
| air led by | 1, 3, 9 | **7** | 1,141,159 / 1,141,216 / 1,142,128 |
| air closed by | 1, 7, 9 | **3** | 1,141,216 / 1,142,128 / 1,141,159 |

All 9 of the $\{1,3,9\}\times\{1,7,9\}$ endpoint pairs occur, each about $1/9$ of the time. Proof of both:
0 exceptions in 3,424,504 handoffs. So the statement is a theorem about the **handoff**, and its
converse is a theorem about the **pair**. Say which object you mean and the ambiguity disappears.

## 4. The binary (30-block byte): capacity is 7, not 8

One byte per block of 30, bit $i$ lit when $30b+\mathrm{RES}[i]$ is prime, $\mathrm{RES}=\{1,7,11,13,17,19,23,29\}$.

* **254 of the 256 byte values occur** below $10^9$. The two that do not: `0xFF` (impossible, proved
  below) and `0x7F` (slots 7,11,13,17,19,23,29 prime with slot 1 composite — no obstruction, just a
  7-tuple rare enough that ~$10^{-2}$ are expected below $10^9$, so its absence is not a law).
  Consistency check: the only block with seven primes among the first eight slots is $b=0$, which gives
  exactly `0xFE`, and `0xFE` occurs **once**.
* **A block of 30 contains at most 7 primes (for $b\ge1$).** Proof: the eight residues are
  $1,7,11,13,17,19,23,29$, which mod 7 are $1,0,4,6,3,5,2,1$ — that is **all seven classes**. So every
  block contains a multiple of 7; for it to be prime it must equal 7, which happens only at $b=0$'s
  slot 7. Hence at most 7 lit bits, always. This answers your IMG_6318 question "totals in what can fit":
  **7, and 8 is impossible.**
* Primes per block: 0 → 5,734,504 · 1 → 11,770,749 · 2 → 9,968,008 · 3 → 4,502,659 · 4 → 1,169,057 ·
  5 → 174,050 · 6 → 13,831 · 7 → 475 · 8 → 0.
* $H(\text{byte}) = 5.619$ bits. $H(\text{byte}\mid\text{previous byte}) = 5.603$ bits, so the byte
  history carries **0.015 bits** — 0.27% of the information. The binary is a strong *within-block*
  object and carries almost nothing *between* blocks.

## 5. The three gates collapse to one

Gate 1 (end digit in $\{1,3,7,9\}$) is implied by gate 2 ($\gcd(n,30)=1$). Gate 3 ($n\bmod9\in\{1,2,4,5,7,8\}$)
is also implied by gate 2, since $\gcd(n,30)=1\Rightarrow3\nmid n$. So gates 1 and 3 are redundant: the
system's ruling-out power is exactly the $W(30)$ wheel, 22 of every 30 integers removed.

Consequently the **mod-9 indicator is independent of the end-digit type**, not a finer version of it:

| $p\bmod30$ | $p\bmod9=2$ | $=5$ | $=8$ |
|---|---|---|---|
| 11 | 379,518 | 380,915 | 380,784 |
| 17 | 380,859 | 380,844 | 380,425 |
| 29 | 380,604 | 380,514 | 380,041 |

All nine cells equal to 0.3%. Twin starts mod 9: 2 → 1,140,981 · 5 → 1,142,273 · 8 → 1,141,250. So the
mod-9 twin classes $(2,4),(5,7),(8,1)$ are just the mod-3 condition restated; they cannot distinguish
$1{:}3$ from $7{:}9$ from $9{:}1$. Distinguishing those needs mod 30, which your key already uses.

## 6. Hardy–Littlewood, and what "more accurate" would have to mean

Not a competitor — your 2,3,5 layer **is** the exact part of it. The constant factorises,
$2C_2=\prod_p f_p$; the factors at $p=2,3,5$ are precisely the admissibility conditions your byte
encodes, and they are exact, which is why your key has zero exceptions. The factors for $p\ge7$ are
where counting lives, and that is the part nobody can prove.

Measured accuracy of the counting side:

| $x$ | $2C_2\,\mathrm{Li}_2(x)$ | actual twin count | error |
|---|---|---|---|
| $10^8$ | 440,367.8 | 440,312 | +0.013% |
| $10^9$ | 3,425,308.2 | 3,424,506 | +0.023% |
| $10^{10}$ | 27,411,416.5 | 27,412,679 | −0.005% |

and for the local rate, mean handoff air $=0.7532\log^2p$ measured against $0.75739\log^2p$ predicted,
i.e. 0.55% low. **That 0.55% is not a model error**: the air is the gap minus the half-pair, so the
prediction for the air is $\tfrac{1}{2C_2}t^2-2$, and at $\langle t^2\rangle\approx400$ the $-2$ *is*
the 0.5%. With it, the local rate agrees to $0.02\%$ — see [`air-law-offset.md`](air-law-offset.md).

So the counting side is accurate to 5 parts in 100,000 at $10^{10}$. To establish "more accurate than
Hardy–Littlewood" the model has to output *a number that can miss*: a count, a density, or a predicted
air. Nothing in the system as written does that — and your own page footer agrees that the gates "can't
confirm a prime on their own". That is not a weakness of the key; it is the difference between an exact
local filter and a counting law.

**The test I will run.** Give one falsifiable number from the model, for instance: the predicted count of
twin pairs below $10^{10}$; or the predicted share of handoffs at each of the four $\bmod30$ classes
above the floor; or the predicted mean air in tinder units at a stated $p$. I will test it against the
$10^{10}$ dataset on the same footing as the row above.
