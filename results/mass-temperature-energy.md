# Mass, temperature, and the one thing counts cannot carry

Yes — the relation exists, and the record already has one version of it. What it does not have is the
quantity that makes the nuclear version work, and that quantity is not a count. So the answer is
"yes, with one missing number", and the missing number can be named exactly.

## 1. The same shape on both sides

| | solid | nucleus |
|---|---|---|
| energy vs temperature | $E=C\,\Delta T$ | $E^*=a\,T^2$ |
| constant | $C=3R=24.94$ J mol⁻¹K⁻¹ | $a=A/K$, $K\approx8$–11 MeV |
| how mass enters | as $1/M$ per gram, $c=3R/M$ | as $A$, the multiplier |
| status in the record | **measured**, $r=0.9955$ over 78 elements | an input, not measured here |

Both are "energy per unit temperature per unit mass". The difference is that one is linear in $T$ and the
other quadratic, and that mass sits in the denominator on one side and the numerator on the other. So the
record's $c=3R/M$ is not wrong about fission — it is the *wrong power law* for it.

## 2. Why the solid version is exact and the nuclear one is not

The mass defect. In a chemical change the energy released is a few eV against a rest mass of
$10^{5}$ MeV per atom — a part in $10^{9}$, far below the precision of any mass table, so $E=3R\Delta T$
can be exact without anyone ever computing a defect. In fission the defect is 200 MeV against 219 GeV:
**one part in a thousand, and that part is the entire energy.**

So on the nuclear side the mass that matters is not the mass, it is the difference between the mass and
$A$ times the nucleon mass — the *mass excess*. The counts give $A$ and $Z$; the excess is a measured
table of small differences of large numbers ($\Delta$ in MeV per nuclide). It is not a count, and no
amount of counting produces it.

## 3. The failure, exactly

The record's mass law is linear in $Z$:

$$M(Z)=2.619\,Z-9.36\ \text{u}.$$

For a split, $Z=Z_1+Z_2$, so the linear terms cancel and the predicted defect is the intercept, whatever
the split point (Lean: `linear_mass_law_blind`):

$$M(Z)-M(Z_1)-M(Z_2)=9.36\ \text{u}=8.72\ \text{GeV}\qquad\text{for every split of every parent,}$$

against the measured 200 MeV — **44× too large and independent of where the split is**. The arithmetic is
in the file: the same 9.360 u comes out for $(36,56)$, $(38,54)$, $(40,52)$ and $(46,46)$.

Two things are wrong at once, and they are worth separating: the *scale* (44×) is the intercept absorbing
the neutron excess, and the *flatness* is the linearity. A linear mass law can price nothing, because a
split's energy is a *difference* of a nonlinear function.

## 4. What the counts do give

**The mass-number balance, exactly and already used:** $A_1+A_2+\nu=A$, which is how the neutron
multiplicity was measured from the yields alone — $\nu=2.40$ (U-235 thermal) to $4.09$ (Fm-256 SF).

**Two temperature proxies, both ordinal.** The first is the charge dispersion at fixed mass — a thermal
fluctuation, so $\sigma_Z^2\propto T$:

| parent | $\sigma_Z$ at low excitation | at 14 MeV | ratio | implied $T$ ratio |
|---|---|---|---|---|
| U-235 | 0.612 (500 keV) | 0.703 | 1.15 | 1.32 |
| U-238 | 0.623 (500 keV) | 0.679 | 1.09 | 1.19 |
| Th-232 | 0.612 (500 keV) | 0.686 | 1.12 | 1.26 |
| Pu-239 | 0.636 (500 keV) | 0.717 | 1.13 | 1.28 |

The second is the multiplicity itself, at fixed $Z$: U-235 gives 2.40 (thermal) → 2.88 (500 keV) → 3.71
(14 MeV). Both proxies are monotone, neither is calibrated, and both saturate — the same verdict as the
four readings in [`four-readings.md`](four-readings.md).

## 5. The answer, in one paragraph

Mass and temperature do relate to energy, and the record's $3R/M$ is a real instance of that relation —
but only because chemistry can afford to ignore the mass defect. Nuclear energy *is* the mass defect, and
the defect is a nonlinear function of both counts, so a single linear mass law prices every split at the
same 8.72 GeV. To get 200 MeV out you must add the mass excess. That is the same conclusion the second
coordinate produced, arrived at from the opposite end: what the table lacks is not the *position* of the
cells but the *depth* of the well between them — and depth is not a count.
