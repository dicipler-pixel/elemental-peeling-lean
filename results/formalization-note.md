# A machine-checked account of the peel-ratio algebra, with twelve corrections

*Draft, working title. Jeromie Beasley and Elizabeth Johnson.*

## Abstract

We report a Lean 4 formalization of the algebra that underlies the "elemental peel" and "loop
wall" programme: a positive ratio $z$ mapped to the reflection $\Gamma(z) = (z-1)/(z+1) =
\tanh(\tfrac12\log z)$, the level set $\Gamma^2 = 1/2$ (equivalently $z = 3 \pm 2\sqrt2$), the
Riccati flow that $\Gamma$ obeys under a uniform log-ratio phase, its tanh solution and crossing
time, and the functional-equation argument that forces a determinant-additive readout to be a
multiple of $\log$. Every one of those identities is standard — the reflection coefficient of a
mismatched two-port, the logarithmic Cauchy equation, Jacobi's four-square count — and we say so
with citations in §2. What is not standard is the bookkeeping, and that is what this note is for:
a checked artifact in which twelve statements transcribed from prose turned out to be false and
are kept as refutation theorems beside their corrected forms, nine control files state plausible
falsehoods that the checker rejects, and two theorems delimit what the framework's own premises
can and cannot select. We also report what the accompanying ionization-energy archive can and
cannot settle: for this finite archive, and for rational cutoffs, it cannot identify
$3+2\sqrt2$, and we prove that.

## 1. What this is, and what it is not

The programme proposes that a "peel" — a specified removal from a record — has a canonical
reflection, that the level $\Gamma^2 = 1/2$ marks a wall, and that a ledger readout is the
logarithm of the retained volume. Written as mathematics, the claims are elementary; written as
physics, they are not claims at all yet, because nothing in the corpus derives a Hamiltonian, a
spectrum or an observable from the framework.

This note therefore does three things and refuses a fourth.

1. It states the algebra exactly and formalizes it (§3).
2. It lists, with proofs, the places where the prose and the mathematics disagree (§5).
3. It reports the one empirical question the corpus can actually pose — whether the archive
   distinguishes the wall value — and answers it in the negative, with a theorem (§6).

It does not claim that the framework describes nature, and §8 says what would be needed for that.

## 2. The identities are standard, and here is where they live

A referee will find all of the following in a morning, so we put them first.

**The reflection is the Cayley transform in logarithmic coordinates.** For $z>0$,
$\Gamma(z) = (z-1)/(z+1) = \tanh(\tfrac12\log z)$ is the substitution $e^{2u} = z$. In
transmission-line terms it is the load reflection coefficient of a terminated line,
$\Gamma = (Z_L-Z_0)/(Z_L+Z_0)$ with $z = Z_L/Z_0$ positive real — Ellingson, *Electromagnetics I*,
§3.12; Pozar, *Microwave Engineering*. At normal incidence the Fresnel coefficient of a dielectric
interface has the same form, with refractive indices in place of impedances. In
hyperbolic-geometry terms it is the rapidity, $\beta = \tanh\mu$ with $z = e^{2\mu}$. DLMF 4.37.24
gives
$\operatorname{artanh}x = \tfrac12\log\frac{1+x}{1-x}$.

**The flow is a Riccati equation with a 1946 pedigree.** Under a uniform log-ratio phase
$z' = \omega z$, the chain rule along the Cayley transform gives
$\Gamma' = \tfrac{\omega}{2}(1-\Gamma^2)$, whose solution is the tanh kink. The prior art is Walker and Wax,
*J. Appl. Phys.* **17** (1946) 1043–1045, DOI 10.1063/1.1707673, whose abstract reads: "A
first-order differential equation for the voltage reflection coefficient of a non-uniform line is
obtained and it is shown how this equation may be used to calculate the resonant wave-lengths of
tapered lines." That equation is the Riccati form above — it is the projective coordinate of a
$2\times2$ system — though the paper states the equation without using the name. DLMF 4.34.3
supplies $\tanh' = \operatorname{sech}^2$.

**The wall is a quadratic formula.** $\Gamma^2 = 1/2 \iff z^2 - 6z + 1 = 0 \iff z = 3 \pm
2\sqrt2 = (1\pm\sqrt2)^2$, and $\operatorname{artanh}(1/\sqrt2) = \log(1+\sqrt2)$. Nothing here
is a new constant; the wall is the impedance ratio at which reflected power is one half.

**The readout is the logarithmic Cauchy equation.** A differentiable $A$ with
$A(xy) = A(x) + A(y)$ on $(0,1]$ is $c\log x$: substitute $x = e^u$ and apply Cauchy's equation
with regularity — Kuczma, *An Introduction to the Theory of Functional Equations and
Inequalities*, 2nd ed., Ch. 13; Aczél–Dhombres for the multivariate theory.

**The counts are Jacobi's.** The number of norm-one integer quaternions is $r_4(1) = 8$ and of
norm-five is $r_4(5) = 8(1+5) = 48$, instances of $r_4(n) = 8\sum_{d\mid n,\,4\nmid d} d$
(Grosswald, *Representations of Integers as Sums of Squares*).

**The finite linear algebra is standard too.** The compression variance identity is the
orthogonal-projection decomposition of a second moment in operator form; the observer criterion
`observer_iff` is the general quotient and kernel-invariance statement, with the finite-dimensional
stabilisation of the cumulative readout kernels carried separately by Cayley–Hamilton; the quantum
geometric tensor is Provost–Vallée,
*Comm. Math. Phys.* **76** (1980) 289–301, DOI 10.1007/BF02193559.

We take no credit for any of these. The contribution of the artifact is elsewhere.

## 3. The artifact

The library is Lean 4, one module per subject, each importing `Mathlib` and at most the earlier
modules of the same library; nothing outside Lean and Mathlib. No `sorry`, no project axioms, no
`native_decide`. It contains **1,209 theorem declarations plus 23 declarations spelled `lemma`**
in one module. The audit as checked in discovers `theorem` only and so reported 1,209; the repair
that matches both spellings reports 1,232, and this note counts 1,232 and says where the
difference comes from. Every declaration's axiom set is printed by the
kernel and checked to lie inside `{propext, Classical.choice, Quot.sound}`.

Three properties are worth more than the theorem count:

**The verifier can say no.** Nine files under `FalseControls/` state *plausible falsehoods* — that
nitrogen's core opening is outside the wall, that carbon's is inside, that $\Gamma^2$ survives
reversal with its sign, that the archive has a different number of outside steps, that a Hall
incremental form is nonnegative at a stated parameter pair. Each must fail to compile, and should fail
for a mathematical reason rather than a typo; the verifier screens for that by matching the
diagnostic against a mathematical-failure pattern and rejecting anything that looks like a
missing name or a parse error. That is a smoke test, not a proof that no typo caused a
rejection, and we do not claim more. A pipeline that accepted everything would pass every other
check.

**Two of the three generators are byte-reproducible.** `LoopWall/Archive.lean`, the kernel's
recomputation of the whole ionization-energy archive (3,570 ordinary steps, 67 anion rungs),
regenerates from `data/H_to_At_thresholds.csv` to the same bytes; `LoopWall/OpeningMap.lean`,
117 theorems over 3,816 ratios, regenerates from `data/element_thresholds_20261011.json.gz` to
the same bytes (`971be82e…`). The third, `verification/`, is derived and not checked in. For 115
of `OpeningMap`'s 117 theorems the path is data to theorem; the two exceptions — the francium
straddle, an interval statement, and the frozen Rb/Sr prediction, written before the ratios it
names were opened — are historical inputs, emitted verbatim and labelled as such.

**The claims file is written to be falsifiable against the artifact.** `COVERAGE.md` maps each
prose claim to the theorem that carries it and `LIMITATIONS.md` says what is not proved. Where
the two had drifted we corrected the file that was wrong; §5 records the corrections, and the
history shows them being made.

## 4. What is assumed rather than derived

The formal statements are conditional, and it matters which hypothesis is doing the work. In the
current artifact:

- **The phase law is assumed.** `UniformLogRatio` begins from a differentiable phase with
  constant derivative; the closed form $\Gamma = \tanh(\omega\tau/2 + t_0/2)$ is then a
  substitution, and existence theory for the second-order equations is not formalized.
- **The rate law is assumed.** `ReadoutUniqueness` classifies readouts *given* a proportional
  rate law; it does not select the law.
- **The composition law is assumed, and its necessity is proved.** `CompositionBridge` selects
  the logarithm among readings of the normalised determinant that are additive over channel
  blocks and regular — and separately proves that dropping the determinant premise destroys the
  conclusion, since evenness, vanishing at zero balance and append-additivity of a channel sum
  leave both the ledger and $\Gamma^2$ admissible.
- **The wall reading is assumed.** The constant $c = -1$ in $c\log$ is fixed by taking the wall
  value to be $\log 2$; that is a normalisation, not a derivation.
- **There is no first-variation theorem.** The module proves an Euler–Lagrange *residual*
  identity; the passage from stationarity of an action to that residual is the classical
  argument and is not formalized. (The docstring said otherwise until it was corrected.)

## 5. Twelve corrections, and two limits on what the premises select

While formalizing, twelve statements transcribed from the papers' prose turned out to be false.
They are kept in the code as refutation theorems, next to their corrected forms, and listed in
`LIMITATIONS.md`:

raw kernel filtration; the direction of $\omega$ against $\eta$; a two-block sign convention; a
squared scale bound; skew weights taken to imply a potential; the sign of the second probe
($-\sin\Phi$, not $+\sin\Phi$); norm-one quaternions in $\mathbb{Z}^4$ numbering 24 rather than
8; "PSD plus $0<a$ implies positive definite", whose correct criterion is
$0 < a \wedge \omega^2 < 4(ac-b^2)$; proportionality of two log laws without nondegeneracy;
$v \ne c$ offered as a non-null condition; the real part of $Q$ without the complementary block;
and the peel-rate bound without $g \ge 0$. Three further statements in the formalization brief
itself were wrong and are kept the same way: the Euler–Lagrange sign ($T - U$ with
$U = +(\omega^2/8)e^{-2S}$), the wall clock ($2\log(1+\sqrt2)/\omega$, not $\log(1+\sqrt2)/\omega$),
and the readout coefficient sign.

Two of these are structural rather than clerical, and they bound what the framework can claim:

**A 2-jet at zero cannot select the bridge.** $\phi_1 = \Gamma^2/2$ and
$\phi_2 = -\tfrac12\log(1-\Gamma^2)$ agree in value, first and second derivative at $\Gamma = 0$
and disagree in derivative at the wall, so no function of the triple $(\phi, \phi', \phi'')$ at
zero returns every potential's wall force. This is the familiar fact that a finite jet does not
determine a function, instantiated twice.

**Composition alone does not select the ledger.** On the weakest composition law, the ledger and
$\Gamma^2$ are both admissible; determinant dependence and regularity are essential. Selection
is a theorem about *that* premise, not about composition in general.

## 6. What the archive can and cannot settle

`LoopWall/Archive.lean` recomputes the entire table in exact rational arithmetic from the stored
twelve-decimal ratios: 3,570 ordinary steps with 8 outside the wall, 67 anion rungs with 55
outside. The eight ordinary outsiders are exactly the core openings — Li, Be, B, C at $k \le 4$,
Na, K, Rb, Cs at $k = 1$ — which is a real and satisfying agreement.

It is not evidence for the wall's *value*, and the artifact proves this rather than asserting it:
`ordinary_cutoff_window` and `anion_cutoff_window` show that every rational cutoff in
$[5.639665400281, 5.947100834227)$ and in $[5.80790205984, 5.866538776091)$ selects the *same
list* of steps, not merely the same number. Under the supplied uncertainty boxes the
indistinguishable set is $[5.808010272529, 5.866514230542)$, and $3+2\sqrt2 \approx 5.828427$ sits
inside it. The data are compatible with the wall; they cannot locate it. The scope of that statement is
what the theorem gives: this finite list of 3,637 ratios, and rational cutoffs. It is not a claim
about ionization data in general.

Two corollaries worth stating. First, the table certifies the stored decimals, not the raw
energy quotients; an exact recomputation from the quotients changes no classification and the
largest rounding discrepancy is $4.9983\times10^{-13}$ (the Tc $k = 28$ quotient), so the
distinction is immaterial here but should not be blurred. Second, the claim that every central ratio lies in its own interval is
asserted by the generator, which refuses to write the file unless all 3,614 rows pass, and it is
*not* a theorem in the module — the module stores endpoints only. We say so in `LIMITATIONS.md` because it used to say otherwise.

## 7. The ladder is not the flow

The framework's peel ratio is defined on a ladder of successive removals, so the only chart the
definitions supply is the removal index: one removal, one step, $\tau = k$. That is a modelling
choice rather than a consequence of the definitions, and the papers do not supply it either: in
*What the Peel Keeps* the symbol $\tau$ is a time, entering with $\dot\tau > 0$ in the operator
equation for the readout, not a rank in a ladder. The library makes the identification implicitly
when it applies $\Gamma$ to ionization energies, and that is the identification tested here. In that chart the clock
$\Gamma = \tanh(\omega\tau/2)$ predicts that the peel ratios of an element form a geometric
progression, $\log z_k$ affine in $k$. Neither that law nor its nearest rival describes them,
and the two have to be scored on the same response before they can be compared at all:

The clock with a linear phase is *the same model* as a geometric ladder, because
$\operatorname{artanh}\Gamma = \tfrac12\log z$: fitting one fits the other. Scored on the same
response, $\Gamma_k$, over 79 ladders with at least six steps:

| model for $\Gamma_k$ | median $R^2$ |
| :-- | :-: |
| $\tanh((p+qk)/2)$ — the framework's clock, equivalently geometric ladders | 0.035 |
| $A/k$ — the hyperbolic branch $\Gamma' = -\mu\Gamma^2$ | 0.074 |

The sample rule does not matter: with a two-step minimum (83 ladders) the medians are 0.035 and
0.073 as well, and both come from `scripts/ladder_fit.py` — though the six-step filter does drop the Li, Be, B and C ladders, which is where four of
the eight outside steps live. Measuring the geometric fit on $\log z$ instead gives 0.025, a number on a different scale
that we do not compare with these.

Neither law describes a ladder, and the misfit is not a short list of anomalies: the twenty
worst steps of 3,486 carry 16% of the squared residual from $\Gamma_k = A/k$, so the failure is
spread across the ladder rather than concentrated at a few closures. The largest single residuals
do sit at the inner-shell closures, where $z$ jumps by a factor of four — Kr's $k = 34$ step has
$z = 4.21$ against a smooth value near $1.03$.

What survives is asymptotic and weaker than a power law. The product $k\Gamma_k$
settles near $0.7$ for $k \ge 5$, i.e. $z_k = 1 + c/k$ with $c = 1.44$ (pooled median over 84
elements, $k \ge 2$; per-element 10–90% range 1.26–1.47). That is the tail of a solution of
$\Gamma' = -\mu\Gamma^2$, not of $\Gamma' = \tfrac{\omega}{2}(1-\Gamma^2)$ — and the two disagree
exactly at $\Gamma = 0$, which is where the framework's declared discriminating measurement sits.
It is *not* a power law of the ladder: a direct fit of $\log\mathrm{IE}_K$ against $\log K$ gives a
median exponent of 2.00, not 1.44, so the ratio law and the ladder exponent are different
summaries and only the first is supported here.
The pooled slope identifies a constant, not a mechanism: other one-parameter laws fit the tail
about as well, and we do not claim that this Riccati equation is the only one consistent with it.

For completeness, the one-parameter regularisation does have predictive content, and it is worth
being explicit about how much. Predicting $z_k$ from the rank alone by $z_k = 1 + 1.44/k$ gives a
median relative error of 16% in $z_k - 1$ (median absolute error $0.011$ in $z_k$); 68% of the
3,486 steps with $k \ge 2$ fall within 25% and 81% within 50%, and the failures are the
shell-closure steps, where the ratio is off by a factor of up to 170. That is a real regularity,
and it is the framework's rival, not its consequence.

We state this as a constraint on the programme, not a refutation of it: if the peel coordinate is
not the removal index, the framework must say what it is, because any strictly monotone $\Gamma$
is $\tanh$ of *some* coordinate, and a coordinate that is defined by the fit makes the clock
unfalsifiable.

## 8. What would make this physics

One number, written down before it is computed, with the observable named, the protocol for
measuring it fixed, and an uncertainty budget attached — a number a table or a sieve can
contradict. The candidate already in the corpus is the peel rate at zero reflection —
$\omega/2$ for the log-ratio phase against $\omega$ for the angle phase. It is not yet a
prediction, because no measured quantity has been identified with $\omega$; §7 suggests that the
identification must come before the test, not after it.

Until then the honest description is what §1 gave: a checked account of an elementary algebra,
with a precise record of where the prose and the mathematics disagreed, and a proof of what the
existing data cannot decide.

## 9. Reproduction

```bash
lake exe cache get && lake build
python3 scripts/verify.py          # 1232 declarations, three axioms, nine controls rejected
python3 scripts/gen_archive_lean.py     # byte-identical Archive.lean; asserts central containment
python3 scripts/gen_opening_map_lean.py # byte-identical LoopWall/OpeningMap.lean
python3 scripts/ladder_fit.py          # the ladder fits of §7
LEAN_PATH=.:$LEAN_PATH lean -DwarningAsError=true LoopWall/Wall.lean   # per module, warning-clean
```

## Appendix: where each claim lives

| claim | module |
| :-- | :-- |
| $\Gamma = \tanh(\tfrac12\log z)$, telescoping, scale invariance | `LoopWall/Ledger.lean` |
| $\Gamma^2 = 1/2 \iff z = 3\pm2\sqrt2$ | `LoopWall/Wall.lean` |
| $\Gamma' = \tfrac{\omega}{2}(1-\Gamma^2)$, unique wall crossing, rate $\omega/4$ | `LoopWall/WallClock.lean` |
| log-ratio phase, first integral, Euler–Lagrange residual | `LoopWall/UniformLogRatio.lean` |
| angular phase $S'' = \omega^2e^{2S}$, $U$ unbounded below | `LoopWall/UniformAngularBridge.lean` |
| determinant-additive readout is $c\log$; $c = -1$ from the wall | `LoopWall/CompositionBridge.lean` |
| 2-jet at zero cannot select the bridge | `LoopWall/BridgeUnderdetermination.lean` |
| archive recomputation, both cutoff windows | `LoopWall/Archive.lean` |
| opening map, core by core | `LoopWall/OpeningMap.lean` |
