# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The modules are finite scalar and matrix algebra over declared records. They do not derive a
  material Hamiltonian, an optical force, a geometric-phase interpretation, or any empirical
  input of the paper.
* `PauliMemory` uses real and imaginary parts of two orbital samples and an explicit affine
  memory law; the synthetic four-bin observer's coefficients are not CIE calibrations.
* The paper's material tests, numerical experiments, and the periodic-table analyses of the
  VOTKP editions are outside these proofs.
* The hypersurface layer proves finite block identities and a declared constitutive model. It
  does not derive a material Hall coefficient, the existence of waveguide roots, Berry integrals,
  or any gravity identification; the second-order source `N` is an input, not derived.

## The loop-wall layer

`LoopWall/` proves the exact mathematics of *Periodic Table of Elemental Peels* and
*What the Peel Keeps*, and nothing about the world. In particular:

* **The archive certificate is arithmetic, not measurement.** `LoopWall/Archive.lean` reads the
  exact decimal of every ratio in `data/H_to_At_thresholds.csv` as a rational, recomputes its side
  of the wall with the loop-wall predicate, and lets the kernel check the counts (3,570 ordinary
  steps with 8 outside; 67 anion rungs with 55 outside) and the two cutoff windows. It does not
  certify that an entry is the true ionization energy, that its grade in the CSV is the right one,
  or that a ratio is a "core opening" in any physical sense. The CSV's own wall column is not used.
* **A wall side is not a prediction.** `LoopWall.Archive.ordinary_cutoff_window` and
  `anion_cutoff_window` show that every rational cutoff in `[5.639665400281, 5.947100834227)` and
  `[5.80790205984, 5.866538776091)` sorts the archive identically. The value `3 + 2√2` comes from
  the equal-face construction, not from this table, and the table cannot distinguish it from any
  other cutoff in those intervals.
* **Two-face agreement is a one-parameter statement.** `LoopWall.BoundaryAgreement` proves that
  the product and sum forms of the closing test agree at every interior pair exactly at the
  diagonal threshold `t = 1/2`, and gives a strict counterexample at every other `t` in `(0,1)`.
* **The error rectangles are checked at the endpoints the CSV supplies.** `LoopWall/Archive.lean`
  proves that for each of the 3,614 comparisons that carry two widths, the wall quadratic has one
  sign on the whole interval `[z_lower, z_upper]`, so no rectangle crosses the wall, and that
  every central ratio lies in its own interval. The two propagated endpoints themselves are read
  from the CSV; the module does not rebuild them from the two raw widths and their uncertainties,
  and it does not model correlation between the two inputs.
* **Nothing about nuclei, optics in a material, or Russell's octaves is proved.** The optical
  module proves the sign of the normal-incidence reflectance against `1/2` for a homogeneous
  nonmagnetic half-space with a declared complex index; it does not model a surface, a
  polarization average, or a measured spectrum. The octave assignment is a historical reading, not
  a theorem.
* **The observer, compression and junction modules are finite linear algebra.** They prove the
  identities the paper states for a declared `L`, `R`, `J`, `A`, `D`; they do not derive those
  operators from a material, a state space, or a boundary-value problem.

## Corrections found while formalizing

Statements that were false as I first transcribed them; the library records the refutation next to
the corrected statement:

* `LoopWall/Observer.lean`: `ker (R ∘ L^n)` is not a decreasing filtration, so
  `⋂_n ker (R L^n) = ker (R L^(d−1))` fails. The cumulative family
  `obsKer n = ⋂_{k≤n} ker (R L^k)` is the object that stabilizes, at `finrank − 1`, by
  Cayley–Hamilton; `iInf_rawKer_eq` transfers that back to the paper's `N_∞`.
* `LoopWall/Rung.lean`: with `η = (I−E)/2` and `χ = (I+E)/2`, `ω > η` holds exactly when
  `Γ₀² < 1/2`, not `>`. The module proves both the refutation and the correct direction.
* `LoopWall/Junction.lean`: a two-block matrix with lower-left block `Aᴴ` is Hermitian, so its
  residual vanishes and the factor-eight identity is false there. The identity holds for the
  paper's anti-Hermitian convention, lower-left block `−Aᴴ`.
* `LoopWall/Optical.lean`: `T/L ≤ ε_s` with `T/L > 3 + 2√2` gives only `3 + 2√2 < ε_s`, not
  `17 + 12√2 < ε_s`; the squared conclusion needs `(T/L)² ≤ ε_s`.
* `LoopWall/LedgerDescent.lean`: skew weights `w i j + w j i = 0` do **not** make a walk sum a
  potential difference. `chiralWeight` on three vertices has a triangle sum of 3 and no potential;
  the correct hypothesis is the cocycle identity (or loop vanishing).
* `LoopWall/TwoProbes.lean`: the second probe's expectation is `−sin Φ` for the operator
  `B = i(|01⟩⟨10| − |10⟩⟨01|)`, not `+sin Φ`; a probe with `+sin Φ` is exhibited separately.
* `LoopWall/Quaternions.lean`: the norm-one quaternions in `ℤ⁴` number **8** (the Hamilton units),
  not 24. The 24 is the unit group of the Hurwitz order, with half-integer coordinates, which is
  not formalized here.

Formalization is evidence for the mathematics, not for the physical interpretation.
