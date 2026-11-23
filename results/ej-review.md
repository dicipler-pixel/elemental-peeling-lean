# Reading E. Johnson, *EJ's Alternate Base Prime Number Pattern and the Twin Prime Counterflow Model*

Zenodo 23484151, DOI 10.5281/zenodo.23484151, 18 pp., CC-BY-4.0, dataset-type record, 117 downloads.

**Short verdict.** Two theorems, both true and both elementary; one conjecture **false** as stated
(counterexample below); one conjecture a **tautology** under the paper's own definition; and no explicit
formula for the twin count in the technical sense — the paper's own §1 says as much. I machine-checked the
mod-9 theorem into the record and verified the other at scale. Nothing here is a criticism of the notation
or of the tables; it is about what the words "theorem" and "explicit formula" are doing.

## 1. What it proves — verified

**Theorem 3.1.** If $p,q>5$ are consecutive primes with terminal digits $d_1,d_2$, then
$g=q-p\equiv d_2-d_1\pmod{10}$.

True, and the paper says why: it "holds for any pair of integers ending in the indicated digits". Zero
violations in 78,494 consecutive pairs below $10^6$ — as it must be, since $q-p\equiv q-p$ is a
congruence identity. So this is a **tautology**, useful as the definition of the gap-group label
($0,2,4,6,8$) and not a fact about primes. The record's base key does the same thing more strongly: it
enumerates the 16 ordered digit pairs and measures which ones occur.

**Theorem 10.2.** Every twin pair $p,p+2>5$ has residues $(2,4)$, $(5,7)$ or $(8,1)$ modulo 9.

True. Measured below $10^6$: 8,167 twins, all in the three classes, split 32.5% / 33.4% / 34.1%. It is
now in the machine-checked record as `twin_mod9` and `twin_transitions_mod9`
([master-theorem.lean](master-theorem.lean), part (N)).

**And it is the record's own mod-3 fact in disguise.** Primes above 3 avoid $0,3,6$ mod 9, so the six
admissible residues pair up under $+2$ as $2\to4$, $5\to7$, $8\to1$; the condition
$p\bmod 9\in\{2,5,8\}$ **is** $p\equiv2\pmod3$, which is the record's `prime_mod3` and the reason the twin
symbol carries only three classes. Both statements are true; neither adds to the other
(`mod9_is_mod3`).

## 2. What fails

**Conjecture 4.3 is false.** It claims the normalized subscript sequence uniquely determines the gap
signature. Counterexample, both genuine segments in the paper's own sense (they end on a $2\sim$):

| segment | subscripts | normalized | gaps |
|---|---|---|---|
| 127, 131, 137, 139 *(the paper's own row)* | 12, 13, 13, 13 | $(0,1,1,1)$ | 4, 6, 2 |
| **211, 223, 227, 229** | 21, 22, 22, 22 | $(0,1,1,1)$ | **12, 4, 2** |

The reason is one line: with $p=10n+d$,

$$g_i=10\,(n_{i+1}-n_i)+(d_{i+1}-d_i),$$

so the subscript differences fix the gap only *modulo 10*; the digits' differences supply the rest, and
the digits are not determined by the subscripts. The conjecture holds **inside one decade** (where all
$\Delta n=0$ and the digits are forced to be a subset of $\{1,3,7,9\}$) and fails as soon as a segment
crosses a decade boundary. That is why the paper's table, which is mostly single-decade, looks convincing.

**Conjecture 6.4 is bookkeeping, and what it really says is "equal total gaps".** Definition 6.1 makes
$\mathrm{bg}_{i+1}=\mathrm{ep}_i$ and $\mathrm{ep}_{i-1}=\mathrm{bg}_i$. Substitute:

$$\underbrace{\mathrm{bg}_{i+1}-\mathrm{bg}_i}_{=\;\mathrm{ep}_i-\mathrm{bg}_i\;=\;T_i}
=\underbrace{\mathrm{ep}_i-\mathrm{ep}_{i-1}}_{=\;\mathrm{ep}_i-\mathrm{bg}_i\;=\;T_i},$$

so the stated identity holds **by definition**, whatever the primes do. And the version the table actually
checks is the *aligned* one, $\mathrm{bg}_i-\mathrm{bg}_{i-1}=\mathrm{ep}_i-\mathrm{ep}_{i-1}$, which
substitutes to

$$T_{i-1}=T_i\qquad\text{— equal total gaps of consecutive segments,}$$

which is exactly why the table's twin-pair rows pass (all $T=2$) and the mixed rows fail (S5 has $T=8$,
S6 has $T=2$). One more thing to note: the table's segments are not consecutive in the prime list at all
(Between 73 and 101 sit 79, 83, 89, 97), so neither form of the identity applies to those rows without
redefining the segmentation.

The remaining material — the Prime Scale, the Lagrange analogy, the discrete-wave and trigonometric
readings — is explicitly interpretive ("correlated but independent perspectives") and makes no claims to
test. The one testable numerical statement in it, that the three mod-9 types have equal density, is
conjectured (10.3) and consistent with what I measured.

## 3. Is there an explicit formula for the twin count? No — and here is what the phrase means

A **classical explicit formula** (Riemann–von Mangoldt, Weil) is an *identity*:

$$\text{counting function}(x)=(\text{smooth main term})+\sum_{\rho}\frac{x^\rho}{\rho}+\text{(small error)},$$

with the sum over zeros of a Dirichlet series that has already been shown to continue meromorphically. It
is what let the previous note pull twelve Riemann zeros out of $\psi(x)$: the formula is exact, so the
zeros are literally in the data.

For twin primes there is no such object, and the reason is structural: twins are not selected by a
Dirichlet character. The natural generating object is a *tuple correlation*, whose main term is the
Hardy–Littlewood singular series $2C_2\prod_{p>2}(1-(p-2)^{-2})$; turning that into an explicit formula
needs a two-variable (circle-method) analysis of $\sum\Lambda(n)\Lambda(n+2)$, not a single $L$-function.
The proposed framework supplies a notation and local filters; it does not supply that object, and its own
§1 states: *"All density and sequence claims beyond the two modular theorems remain conjectural."*

This is exactly what the record measured: the twin-count residual sits **at** the zero bound
(0.0014–0.023% against $0.003$–$0.135\%$) and does not resolve one, while the zeros *were* found in
$\psi$, which has an explicit formula ([`zeros-in-the-primes.md`](zeros-in-the-primes.md)).

**What would change that:** an $L$-function (or a family) whose logarithmic derivative weights pairs
$p,p+2$, with continuation and a functional equation. If the counterflow or the mod-9 cycle is meant to
suggest one, that is the object to write down — and the mod-9 structure alone cannot be it, since mod 9 is
the $3$-adic shadow of the condition $p\equiv2\pmod3$ that the wheel already carries.

## 4. What I could not read

There is a co-paper in the GitHub account, but this connector reaches only the one connected repository
(`dicipler-pixel/elemental-peeling-lean`), so I have not seen it. Give me the URL and I will assess it the
same way — the checks above are cheap and reusable (`scripts/ej_checks.py`), and any theorem in it can go
into the Lean record the way `twin_mod9` just did.
