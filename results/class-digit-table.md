# The class **is** the total gap's end digit

## 1. Derivation

A twin segment runs between consecutive pairs $(p,p+2)$ and $(q,q+2)$. Its total is $T=q+2-p$ and its
air is $\text{air}=T-4=q-p-2$.

**Step 1 — the air has one residue mod 6.** Twin starts are $\equiv 11,17,29 \pmod{30}$, and all three are
$\equiv 2 \pmod 3$; both endpoints are odd. Hence $q-p\equiv 0 \pmod 6$ and

$$\text{air}=q-p-2\equiv 4 \pmod 6 .$$

**Step 2 — five classes, not thirty.** $\text{air}\bmod 30\in\{4,10,16,22,28\}$: the multiples of 6
shifted by 4 — exactly the base key's five classes. Zero exceptions in 3,424,503 segments.

**Step 3 — the bijection.** Since the five classes are $4+6k$ with $k=0..4$,

$$\text{digit}(\text{air}) = \text{air}\bmod 10 \in\{4,0,6,2,8\},$$

five classes, five digits, one each. **The class and the total gap's last digit are the same piece of
information**, so any statement about the class can be read off the last digit and vice versa.

**Step 4 — the pair width is the shift.** $T=\text{air}+4$, so

$$T \bmod 30 = (\text{class}+4)\bmod 30 \in\{8,14,20,26,32\},\qquad
\text{digit}(T)=\big(\text{digit}(\text{air})+4\big)\bmod 10 \in\{8,4,0,6,2\}.$$

The twin key's classes are the base key's plus 4, and the digits likewise — the 4 is the pair, nothing
else.

**Step 5 — the class also fixes the type step.** With $b_g=S\bmod 10$ and $e_p=(Q+2)\bmod 10$,
$\text{class}=(e_p-b_g+2)\bmod 30$, and the nine $(b_g,e_p)$ cells fall into the five classes by their
difference:

| class | cells | type step | kind |
|---|---|---|---|
| 4 | $(1,9)$ | $\tfrac13$ | forward |
| 10 | $(7,1),(9,3)$ | two of the three | forward |
| 16 | $(1,1),(9,9)$ | two | back |
| 22 | $(7,3)$ | one | back |
| 28 | $(1,3),(7,9),(9,1)$ | all three | **self** |

## 2. The table

| class $\equiv$ air | **total end digit** | $T$ class | $T$ end digit | cells | kind | share | $c$ | mean $T$ |
|---|---|---|---|---|---|---|---|---|
| **4** | **4** | 8 | 8 | $(1,9)$ | forward | 11.90% | 0.7363 | 283.6 |
| **10** | **0** | 14 | 4 | $(7,1),(9,3)$ | forward | 23.64% | 0.7204 | 277.5 |
| **16** | **6** | 20 | 0 | $(1,1),(9,9)$ | back | 22.14% | 0.7751 | 298.8 |
| **22** | **2** | 26 | 6 | $(7,3)$ | back | 11.14% | 0.7535 | 290.5 |
| **28** | **8** | $32\equiv2$ | 2 | $(1,3),(7,9),(9,1)$ | **self** | 31.18% | 0.7994 | 308.4 |

Data: [`tableL_class_digit.csv`](tableL_class_digit.csv). The column that matters is the second one: end
digit 8 is 31% of segments and the hottest (0.799); end digit 0 is 24% and the coldest (0.720). Reading
the last digit of the total gap tells you which step happened, how often it happens, and what it costs.

## 3. The same five digits in the Chain Table

The block widths are $2(2l+1)=4l+2$, so

$$w_l \bmod 10 = (4l+2)\bmod 10 \;=\; 2,\,6,\,0,\,4,\,8 \quad (l=0,1,2,3,4),$$

**one block type per even digit, no repeats**, and the cycle restarts at $l=5$ with period 5. So in both
tables the five classes are indexed by the five even digits:

| end digit | 0 | 2 | 4 | 6 | 8 |
|---|---|---|---|---|---|
| **primes** — class | 10 | 22 | 4 | 16 | 28 |
| **elements** — block | $d$ | $s$ | $f$ | $p$ | $g$ |

Both are bijections onto $\{0,2,4,6,8\}$; both use each even digit exactly once. What the two tables share
is the *digit set*, not a pairing — there is no residue argument that would put $s$ with class 22 rather
than class 4, and I am not going to manufacture one. What they do share is stronger than a pairing: in
each table, **the digit is the class**, so a single even number carries the whole classification.
