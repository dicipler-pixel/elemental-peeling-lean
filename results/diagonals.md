# The diagonal: three definitions, one with content, and what the ends are

"Top left to bottom right" is three different objects depending on which table you draw it on. Each is
computed here; only the first is structure.

## 1. The closure staircase — the diagonal that *is* the table

One cell per shell, the last one that closes it:

$$2,\ 10,\ 18,\ 36,\ 54,\ 86,\ 118 \qquad \text{steps } 2,8,8,18,18,32,32 = 2n^2 .$$

Top-left (He, the first closure) to bottom-right (Og). It ends on the last cell of the **p** block, not
of the f block, because $7p$ is where the measured sequence stops. Residues mod 30:
$2,10,18,6,24,26,28$ — every one of them even, none in the wheel's eight classes beyond 2.

This is the only diagonal with content, and the content is the equation: no shell can close anywhere
else, and the increments are the shell capacities.

## 2. The group $=$ period diagonal — what the layout draws

The literal top-left-to-bottom-right cells of the standard grid (group $=$ period):

$$1,\ 4,\ 22,\ 41,\ 74,\ 107 \qquad (\mathrm{H,Be,Ti,Nb,W,Bh}),\qquad \text{steps } 3,18,19,33,33 .$$

Each step is the number of elements between the two cells — the periods spanned plus the groups
advanced (Be$\to$Ti $=8+8+2$, Ti$\to$Nb $=18+1$, Nb$\to$W $=32+1$) — so the diagonal is the period
lengths relabelled ($18\to19$, $32\to33$). No information beyond that. It hits exactly one exception (Nb) out of
six cells, against a base rate of $19/118 = 16\%$ — nothing.

## 3. The prime strip's own diagonal — and the two ends of the element table

Row $s$, column $s \bmod 8$:

$$1,\ 37,\ 71,\ 103,\ 137,\ 169,\ 203,\ 239,\ 241,\ 277,\ 311,\ 343,\dots$$

Prime share on the diagonal 59.0%, off it 61.6%: no structure (the first four are prime, then 169 and
203 are not). But the two *ends* are the interesting part:

* **the diagonal opens on the hole.** $1$ sits in an admissible class (1 mod 30) and is still not
  prime — the only cell in the strip that is admissible and empty;
* **the element table ends on the top rung of the gap ladder.** $118 \equiv 28 \pmod{30}$, and 28 is the
  largest of the base key's five gap classes $4,10,16,22,28$ — the *total* alphabet, not the prime-column
  alphabet. Coprimality with 30 is the admissibility test for a **prime residue**; a total is not a
  residue of a prime and is not asked to pass it. And $118 \equiv 4 \pmod 6$, so the total sits in the
  base-key family (single steps) and *not* in the twin family ($8,14,20,26,32$, all $\equiv 2 \pmod 6$) —
  which is what a table built one electron at a time should do.

So the two tables meet at 1 and at 28: the element table begins in a cell the primes cannot fill (1 is
admissible and not prime) and ends on the largest gap class (28, a total, not a column). Everything they
share in between is the wheel's eight classes.

**How much weight that carries.** Closures mod 30 are $2,10,18,6,24,26,28$ — four of the seven fall in a
key class (base or twin), against $2.33$ expected by chance: $P(X\ge4)=0.17$. The shell increments
$2n^2$ mod 30 are $2,8,18,2,20,12,8$ — five of seven, $P(X\ge5)=0.045$, but that is one of several
statistics examined here and should not be read as a result on its own. And $\pi(118)=30$ exactly is the
prime density ($\mathrm{li}(118)=29.9$), not a signature of the table.

## 4. Your sheets: the equilibrium is a theorem

The column pair "difference between beginning primes" and "difference between end primes" is one
number written twice:

$$(q+2)-(p+2) = q-p \quad\text{always},$$

checked on 58,977 twin transitions below $10^7$: identical in every row. The shared value is
$T-2 = \text{air}+2$, and since $T\equiv 2 \pmod 6$ it is always $\equiv 0 \pmod 6$ — the values taken
are $6, 12, 18, 24, 30, 36, \dots$, never anything else.

So "equilibrium 12:12 / 30:30" is the *rule*, not a case: the ledger's top-left-to-bottom-right
diagonal is the line $\Delta_{\text{begin}} = \Delta_{\text{end}}$, and every pair lies on it. An entry
like 12:6 or 6:120 is either a different quantity or a column slip — the two numbers cannot differ.

What does vary is the shared value's *class*, and that is the twin key: floors $8,14,20,26,32$ for
$T$, i.e. $6,12,18,24,30$ for the difference written in those columns.

## 5. The one-sentence version

The element table's diagonal is $2n^2$ (forced); the layout's diagonal is the period lengths relabelled
(forced, empty); the prime strip's diagonal is noise but it starts on the single hole in the wheel; and
in your own two-column ledger the diagonal is the identity $\Delta_{\text{begin}}=\Delta_{\text{end}}$,
which is why every row reads as a ratio of 1.
