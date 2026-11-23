# Deriving the physics into the table

Before this pass the table took two physics facts as inputs — Pauli's two-per-orbital and the
$(n+l,n)$ filling order — and said "not derived here". Three of those inputs turn out to be derivable, and
what remains is smaller and more honest than "physics".

## 1. The width is a degeneracy count

$$w_l=2(2l+1)=\underbrace{(2l+1)}_{\text{states}}\times\underbrace{2}_{\text{spin}} .$$

**The $2l+1$ is arithmetic.** Angular momentum $l$ has exactly $2l+1$ values of $m$, from $-l$ to $l$ —
a count of integers, proved. *(Lean: `m_states`.)*

**The 2 is spin-½.** One physical fact, and it is a *number of states*, not a rule about atoms.

So the block width is not a postulate: it is the number of one-particle states in a shell, and Pauli's
exclusion does the rest by filling them one at a time.

## 2. The capacity is the Coulomb degeneracy

$$\sum_{l<n}(2l+1)=n^2\qquad\text{(the first }n\text{ odd numbers)},\qquad
\sum_{l<n}2(2l+1)=2n^2 .$$

*(Lean: `odd_sum`, `shell_from_degeneracy`.)*

The $n^2$ is the **degeneracy of the $n$-th hydrogenic level** — the accidental degeneracy of the $1/r$
potential, the same integer that appears in

$$E_n=-\frac{R}{n^2}.$$

So one integer does two jobs at once: **$n^2$ counts the states and $1/n^2$ sets their depth.** The table's
$2n^2$ and the spectrum's $n^2$ are not two facts that resemble each other; they are the degeneracy and
its reciprocal in the same Coulomb problem.

## 3. Dulong–Petit is equipartition, and its 6 is the $p$ width

Each atom in a solid has three directions and two quadratic degrees per direction (kinetic and potential):

$$3\times2=6\ \text{half-degrees}\times\tfrac12 kT\ \Longrightarrow\ 3kT\ \text{per atom}
\ \Longrightarrow\ C=3R .$$

*(Lean: `equipartition`.)*

And that $6=2\cdot3$ is the same 6 as the $p$ block's width $2(2\cdot1+1)$ — in one place it is "two
degrees times three directions", in the other "two electrons times three orbitals". The specific-heat
constant and the block width are the same integer, arrived at twice.

## 4. The corners of the dimension cube

Write a quantity as $L^aT^bM^c\Theta^d$. The table supplies the exponents; the measurements supply the
magnitudes:

| quantity | corner $(a,b,c,d)$ |
|---|---|
| energy | $(2,-2,1,0)$ |
| $mc^2$ | $(2,-2,1,0)$ — the same corner: that is what $E=mc^2$ says |
| specific heat | $(2,-2,0,-1)$ |
| entropy | $(2,-2,1,-1)$ |

$E=mc^2$ is not a law the table could contain; it is the statement that two names share a corner. The
table's contribution is that the exponents are integers, so the corners are a lattice — the same lattice
the counting lives on.

## 5. What the integers cannot give: the scales

| constant | value | in the table's arithmetic? |
|---|---|---|
| Rydberg $R$ | 13.606 eV = 1312 kJ/mol | no |
| gas constant $R$ | 8.314 J mol⁻¹K⁻¹ | no |
| $c$ | 299 792 458 m/s | no |
| $G$ | 6.674×10⁻¹¹ | no |

Every one of these is a measured magnitude. The table gives **counts and exponents** — 2, 8, 18, 32,
$n^2$, $2l+1$ — and physics gives **scales**. That is exactly why the conversions exist:
$0.03036$ K per unit $\log^2p$ is not derivable from integers either; it is the exchange rate between two
measured scales, fixed once their coefficients are known.

## 6. The revised list of inputs

| was an input | now |
|---|---|
| Pauli (two per orbital) | **derived**: $2l+1$ states $\times$ 2 spins, both counted |
| shell capacity $2n^2$ | **derived**: the Coulomb degeneracy $n^2$, doubled |
| octet / 18 / 32 | **derived**: $L(2),L(4),L(6)$ — period lengths |
| $C=3R$ | **derived**: equipartition, $6\times\tfrac12=3$ |
| the $(n+l,n)$ filling order | **still an input** — Madelung, 99/118 exact, 19 exchange promotions |
| the scales $R,c,G$ | **still inputs** — measurements, carried by the conversions |

So the table is not a physical theory; it is the arithmetic that the physical counting forces, plus one
empirical ordering rule and three measured scales. That is a smaller claim than "everything is derived"
and a much larger one than "the numbers happen to match".
