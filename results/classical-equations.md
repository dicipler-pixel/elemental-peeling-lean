# The classical equations: atom → bond → molecule → solid

Everything below is either derived (and flagged), or a measured input carried in from the table. The chain
is: capacities fix the atom, the countdown fixes the bond, the bonds fix the formula, the formula fixes
the mass and the heat capacity.

## The set

| # | equation | from |
|---|---|---|
| **E1** | $w_l=2(2l+1)$, $\sum_{l<m}w_l=2m^2$, $L(m)=2\lceil(m+1)/2\rceil^2$, $W(q)=2\lceil q/2\rceil^2$ | capacities — *proved* |
| **E2** | $v_{\rm core}+h=L(m)$ (definition, 118/118); $v+h=C_{\rm block}$ with $C_s=L(m)$, $C_p=8$, $C_d=18$, $C_f=32$ | **117/118, He a convention** — see `e2-adjustment.md` |
| **E3** | $V=\min(v,\;C-v)$ — the valence | **the bond** |
| **E4** | $a\,V(A)=b\,V(B)$ — the formula | the cross rule, from E3 |
| **E5** | $M=\sum_i a_iM_i$ — the mass | additivity (masses are measured inputs) |
| **E6** | $C_{\rm solid}=3R\,N$ — the molar heat, $N$ atoms per formula | Dulong–Petit / Kopp, the high-$T$ limit |
| **E7** | $c=C/M=3RN\big/\sum_i a_iM_i$ — the specific heat | E5, E6 |
| **E8** | $\langle\text{air}\rangle=c't^2-2$, $c'=1/(2C_2)=0.75739$ | the prime companion (`air-law-offset.md`) |

## 1. The atom

$V$ is not a chemical convention here — it is $\min(v,C-v)$: **an atom takes whichever is smaller, the
electrons it has or the vacancies it lacks.** For the main group $v+h=8$, so $V=\min(v,8-v)\le4$ and

$$V=4 \text{ at group 14},\quad 3 \text{ at 13 and 15},\quad 2 \text{ at 2 and 16},\quad 1 \text{ at 1 and 17},\quad 0 \text{ at 18}.$$

**Scope, exactly:** E3 is exact for period 2 (C, N, O, F, B all match), and a **floor** from period 3,
where hypervalency exceeds it (PCl₅, SF₆). The octet bounds the count; it does not forbid extra bonds once
$d$ orbitals are available.

For the $d$ block the same idea gives the ligand count $h/2$ (Fe(CO)₅, Ni(CO)₄, Cr(CO)₆, and
half-integers exactly where the complex is a radical).

## 2. The molecule

**Formula (E4).** $a\,V(A)=b\,V(B)$, i.e. $a=q/\gcd(p,q)$, $b=p/\gcd(p,q)$:

| pair | $V$ | formula | check |
|---|---|---|---|
| Al, O | 3, 2 | **Al₂O₃** | $2\cdot3=6=3\cdot2$ |
| Ca, Cl | 2, 1 | **CaCl₂** | $1\cdot2=2=2\cdot1$ |
| C, H | 4, 1 | **CH₄** | $1\cdot4=4=4\cdot1$ |
| Na, O | 1, 2 | **Na₂O** | $2\cdot1=2=1\cdot2$ |
| Mg, N | 2, 3 | **Mg₃N₂** | $3\cdot2=6=2\cdot3$ |
| Si, O | 4, 2 | **SiO₂** | $1\cdot4=4=2\cdot2$ |

**Mass (E5)** is additive and needs no structure — it is the one quantity that bonds do not change, which
is why mass stays monotone in $Z$ while every other property is periodic.

**Heat (E6, E7).** The solid's molar heat is $3R$ per mole of *atoms*, so

$$C=3RN,\qquad c=\frac{3RN}{M}.$$

| formula | $N$ | $M$ (u) | $C_{\rm pred}=3RN$ | $c_{\rm pred}$ (J g⁻¹K⁻¹) |
|---|---|---|---|---|
| NaCl | 2 | 58.44 | 49.9 | 0.854 |
| MgO | 2 | 40.30 | 49.9 | 1.238 |
| H₂O | 3 | 18.02 | 74.8 | 4.15 |
| SiO₂ | 3 | 60.08 | 74.8 | 1.245 |
| Al₂O₃ | 5 | 101.96 | 124.7 | 1.223 |
| Fe₂O₃ | 5 | 159.69 | 124.7 | 0.781 |

**E6 is an upper bound, not an equality.** It is Dulong–Petit in molecular form, and it is approached at
high temperature. The deficit is the same one measured on the elements: $C/3R=0.30$ for diamond, 0.40 for
boron, 0.70 for beryllium — light, stiff lattices sit far below the classical limit at 300 K. So E7
predicts the *high-temperature* specific heat, and for a stiff compound the measured value is lower by a
factor set by the Debye temperature.

## 3. What the equations cannot do

| claim | why it fails |
|---|---|
| E3 for hypervalent compounds | PCl₅, SF₆ exceed $\min(v,8-v)$ — the octet is a $p$-block rule |
| E6 for gases | a gas has only its active modes; CO₂ has $C_p=37$ against $9R=75$ |
| E6 for quantum solids | diamond is $0.30$ of $3R$ at 300 K |
| E2 universally | 36 exceptions, all the $s$ block of long periods and He |
| E1 → the element list | the *inventory* (which 118) is Madelung, 99/118 exact |

## 4. The prime companion

The same form one rung down — energy = constant × count × level:

$$E=c'\,m\,t^2-2m,\qquad c'=\frac{1}{2C_2}=0.75739,\ t=\log p,$$

(the $-2m$ is the half-pair per segment: the law is exact on the centre-to-centre gap, and the air is
the gap minus the pair width — `air-law-offset.md`).

with the count $m$ the twin segments and the level $t^2$ the log-squared magnitude. The element side's
version is $Q=3R\,N\,\Delta T$: constant $3R$, count the atoms, level the temperature. **In both, one
constant per unit and everything else multiplicative** — which is the only reason a table of 118 and a
table of primes can be written with the same grammar.
