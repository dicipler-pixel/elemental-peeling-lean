# Ramanujan's gamma fractions as peel steps

*Ramanujan's Gamma Fractions Read as Stacks of Faces* (session record, 13–15 November 2026) reads
each term of a continued fraction as one reflecting face in the same variables as the loop wall.
That reading is exact, and it lands on the same `3 + 2√2`:

| the record says | here |
| :--- | :--- |
| each term is a face with `Γ_n = x/√(x² + (2n−1)²)` | `unified/Bridge/Faces.lean`, `faceRatio_eq_gam` |
| the wall is `2n − 1 = x` | `faceGamma_sq_eq_half_iff`, `faceGamma_sq_eq_half_iff_odd` |
| Brouncker (`x = 1`) has its first face exactly on the wall, `z = 3 + 2√2` | `brouncker_first_face` |
| the error falls like `N^{−x}` | measured — `scripts/ramanujan_faces.py` |
| `error × N^x → 0.40528` at `x = 1`, `0.2500` at `x = 3` | measured: `4/π²` and `1/4` to six digits |

## The exact part

The gamma quotient is

$$4\,\frac{\Gamma\!\left(\frac{x+3}{4}\right)^2}{\Gamma\!\left(\frac{x+1}{4}\right)^2}
= x + \frac{1^2}{2x + \dfrac{3^2}{2x + \dfrac{5^2}{2x + \cdots}}}$$

with step matrices `M_n = [[0, (2n−1)²], [1, 2x]]`. The characteristic roots are `x ± s_n`,
`s_n = √(x² + (2n−1)²)`, so the face's step ratio is `z_n = (s_n + x)/(s_n − x)` and its
reflection is `Γ_n = (z_n − 1)/(z_n + 1) = x/s_n`.

Three consequences, all proved in `unified/Bridge/Faces.lean`:

* **the wall** — `Γ_n² = ½` exactly when `(2n−1)² = x²`, which for positive `x` and `n ≥ 1` is
  `2n − 1 = x`.  So **every odd `x` has a face exactly on the wall** and no even `x` does.  The
  record mentions only Brouncker; the same happens at `x = 3` (face 2), `x = 5` (face 3), and so
  on.  At `x = 10` there is no wall face and the first face is already inside.
* **Brouncker** — at `x = 1` the first face is at the wall with `z₁ = 3 + 2√2`, the same constant
  as every other leg of this body.
* **inside the disk** — every face has `|Γ_n| < 1`, so no face is ever past perfect reflection.

## The measured part

`python3 scripts/ramanujan_faces.py` checks the fraction against its closed form, the face formula,
the wall, the two constants, and the power law.  All pass.

The record's own checker, `checker/chk1.py` in the session package, reproduces the whole angle
table when re-run here (it then crashes in a later `polyroots` step on this VM, after the table
has been printed; the table itself is what is claimed): `x = ½` 19.0467° → 18.52 at N = 3200; `x = 1` 15.2824° → 15.2667;
`x = 3` 8.0591° → 8.0501; `x = 10` 2.8028° → 2.7939; two-parameter `x = 3, n = ½` 6.0848° →
6.0759; `√(πe/2)` 33.2520° → 32.9994 at N = 51200; Rogers–Ramanujan 0.0534°; `ζ(3)` 11.4232° →
11.3516.  The measured error exponents are 0.49, 1.00, 3.00 and 9.9995, and the rank-one residual
exponent is one higher in each case — exactly as the record states.

So the numerical section is reproducible from its own scripts.  What is *not* derived is the
constant: the record notes that `error × N^x` tends to `4/π²` at `x = 1` and to `1/4` at `x = 3`
and that nobody has derived either.  Re-running confirms both to six digits; neither is proved
here, and neither is claimed as a theorem.

## What this leg adds to the body

The fraction is a **stack of the same faces** as the peel: same `z`, same `Γ`, same wall, same
`⊕` composition.  The difference is what plays the role of the charge — the fraction's parameter
`x` instead of an element's ionisation index — and that the stack is infinite, so its ledger
`Σ 2 artanh Γ_n` diverges like `x log N` and the truncation error obeys a power law whose exponent
*is* `x`.  The record's rule "error × product of the z's stays fixed" is then the statement that
the stack's attenuation is the product of the faces' ratios, which is the same composition law as
`unified/Bridge/Composition.lean`, tested here on a family that converges by four different laws.

Not checked here: the ζ(3) one-term-versus-pair reading, the `x = 0` tied case, the claim that the
rule "holds to within a constant" for the factorial and stretched-exponential fractions, and the
`N^{−x}` behaviour below `x = ½`.  Those are the record's own measurements; the shipped checker
covers the angles and the exponents, not the rule's bookkeeping.

## Provenance

The session record and its scripts are `attachments/we-have-dirac-time-wy47/ramanujan_faces_session_2026-11-15 (2).zip`
(19 files, `checker/chk1.py` the independent eye).  Nothing in the package was edited.  The paper
itself is HTML/Markdown in the same zip; its Lean library is `ramanujan-challenge-lean`, which this
repository does not contain.
