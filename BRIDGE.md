# The bridge from phase motion to the potential

The open step in the framework is stated as: *an equation showing how the null or phase motion
determines `V_k`, and why its readout must be the ledger.* This file records what is now proved
about that step, what is a choice, and what would count as deriving it.

The equation of motion for `Γ` now exists: `LoopWall/PhaseBridge.lean` (62 theorems, fifth round).

## What a bridge equation has to contain

A bridge is two things, not one:

1. **A rule for the phase coordinate.** How a configuration `X` produces a peel coordinate
   `Γ(X)`, i.e. which two readings are compared and in what order. In the library this is
   `Γ = G X = (X - 1)/(X + 1)` with `G` differentiable off `X = -1`
   (`LoopWall/PeelPotential.lean`, `hasDerivAt_G`, `deriv_G`).
2. **A potential on that coordinate.** A function `φ` with `V = φ ∘ Γ`
   (`LoopWall/PeelPotential.lean`, the definition `V`).

Everything else follows by the chain rule, and that part is not a choice:

```
force = -φ'(Γ) · 2/(1+X)^2 · X'        (potentialForce_eq)
```

with the ledger potential `φled Γ = -(1/2) log (1 - Γ^2)` giving `φled' Γ = Γ/(1-Γ^2)`
(`deriv_φled`).

## The equation of motion for `Γ` (new)

Two phase motions are already theorems about the same object: the log-ratio spacing
`t = log (I/J)` with `Γ = tanh (t/2) = G (exp t)` (`LoopWall/Ledger.lean`), and the chromatic
angle with `Γ = -cos φ` (`LoopWall/ChromaticAngle.lean`, `peel_eq_neg_cos`). Each one, made
uniform, is an equation of motion for `Γ` — and the first is *equivalent* to one:

| Phase motion | `Γ` obeys | Theorem |
| :--- | :--- | :--- |
| `z' = ω z` (uniform log-ratio, `z = exp t`) | `Γ' = (ω/2)(1 - Γ²)` | `peel_ode_of_phase_ode` |
| `Γ' = (ω/2)(1 - Γ²)`, conversely | `((1+Γ)/(1-Γ))' = ω · (1+Γ)/(1-Γ)` | `phase_ode_of_peel_ode` |
| `φ' = ω` (uniform angle) | `Γ' = ω sin φ`, `Γ'' = -ω² Γ`, `(Γ')² = ω²(1-Γ²)` | `angle_peel_ode`, `angle_peel_harmonic`, `angle_speed_sq` |

The first two rows are the important structural fact: the peel equation of motion is **not a new
postulate**. It is the uniform-log-ratio phase statement written in the peel variable, and each
direction reconstructs the other. The angle motion is a different motion of the same coordinate:
the peel becomes a harmonic oscillator of frequency `ω`.

## What the equation of motion forces

Along the peel equation of motion the ledger has rate `S' = (ω/2) Γ` (`ledger_rate`): it is the
readout whose rate of change is *proportional to the peel itself*, not to a function of it. That
is the precise sense in which the readout "must be the ledger", and it already fixes the potential
up to an affine map, since `φ'(Γ)(1-Γ²) = Γ` has only that one solution family.

The potential then obeys a closed second-order equation in the ledger variable — this is the
bridge equation for `V_k`:

```
S'' = (ω²/4) exp (-2 S)          (ledger_second_order)
(S')² = (ω²/4) (1 - exp (-2 S))  (ledger_speed_sq)
½ (S')² + (ω²/8) exp (-2 S) = ω²/8   (ledger_energy_eq)
```

and `ledger_is_euler_lagrange` identifies it as the Euler–Lagrange equation of
`½ S'² - (ω²/8) exp (-2 S)`. The angle phase gives the other one,
`S'' = ω² exp (2 S)` (`angle_ledger_second_order`), with rate `S' = -ω cot φ`
(`angle_ledger_rate`).

## What the equation of motion does not force

The phase motion determines *a* potential on `Γ`, and it is not the ledger. If the oscillator's
coordinate is read through the peel, `X = (1+Γ)/(1-Γ)`, its potential is

```
harmPotInPeel m ω Γ = (m ω²/2) ((1+Γ)/(1-Γ))²      (harmPotInPeel_G: it is ½mω²z² at Γ = G z)
```

which is `m ω²/2` at `Γ = 0` and `(m ω²/2)(17 + 12√2)` at the wall (`harmPotInPeel_zero`,
`harmPotInPeel_wall`). The ledger is `0` and `½ log 2` there (`φled_zero`, `φled_wall`). For
`m = ω = 1` that is `16.9853…` against `0.34657…` — a factor of `49.0`, at the wall. Their forces at
zero reflection are `2 m ω²` and `0` (`deriv_harmPotInPeel_zero`, `deriv_φled_zero`), so the two
are separated by a first-derivative measurement and not only by a global one.

That is compatible with, and sharper than, the previous round's theorem that no function of the
2-jet at `Γ = 0` computes the wall force
(`LoopWall/BridgeUnderdetermination.lean`, `no_function_of_two_jet_computes_wall_force`): locality
of order two cannot select the bridge, and neither phase motion is preferred by the peel calculus
alone.

## What does select the ledger

The composition principle, as before, and now exactly. For a two-channel colour with shares
`p₀ + p₁ = 1` and `Γ = p₀ - p₁`,

```
φled Γ = -(1/2) log (p₀ p₁) - log 2          (φled_eq_log_det_shares)
2 φled Γ = -log (1 - Γ²)                     (two_φled_eq_neg_log_volume)
```

so the ledger **is** the log-determinant reading of the shares. `LoopWall/MatrixLedger.lean` shows
that the log-determinant ledger is additive over channels (`Sm_append`, `channel_additive_ledger`)
while the scalar spacing form is not (`scalarLedger_not_additive`), and
`LoopWall/FisherMatrix.lean` identifies the two-channel matrix ledger with `2 φled`
(`matrixLedger_eq_two_scalarLedgerPotential`).

`LoopWall/CompositionBridge.lean` turns that into a classification, and states its own scope. For a
readout `A` of the **normalised determinant** — the volume `4 det p = 1 - Γ²` — additivity over
independently appended channel blocks forces `A (x y) = A x + A y` on `(0,1]`
(`determinantReadout_append`, `mul_add_of_append_additive`); interior differentiability with a left
derivative at `1` then forces `A = c · log` (`eq_const_mul_log_of_append_additive`); and the wall
reading `log 2` forces `c = -1` (`coefficient_eq_neg_one_of_wall_normalization`,
`determinantReadout_eq_matrixLedger_of_wall_normalization`). So a determinant readout required to
compose across independent channels **is** the ledger, with no free constant left.

The scope matters and the module proves the boundary: evenness, vanishing at zero balance and
append-additivity of a *channel sum* do not select the ledger — `append_additivity_alone_does_not_select_ledger`
exhibits the ledger and `Γ²` as two even, zero-normalised, append-additive channel sums that differ
at the wall. Determinant dependence (or an equivalent premise) and regularity are the essential
hypotheses. A readout required to compose is the ledger; a readout required only to be an additive
sum of channel functions need not be.

## The wall has a clock (a discriminating prediction)

Both phase motions date the wall exactly, and they disagree:

| | log-ratio phase | angle phase |
| :--- | :--- | :--- |
| time to the wall from `Γ = 0` | `2 log (1+√2)/ω ≈ 1.7627/ω` (`wall_clock`, `log_wall_ratio`) | `φ = π/4`, i.e. `π/(4ω) ≈ 0.7854/ω` (`angle_wall_clock`) |
| phase ratio at the wall | `z = 3 + 2√2` (`G_at_wall_ratio`, `wall_ratio_sq`) | — |
| peel rate at `Γ = 0` | `ω/2` (`peel_rate_at_zero_log_ratio`) | `ω` (`peel_speed_sq_at_zero_angle`) |
| peel rate at the wall `Γ² = 1/2` | `ω/4` (`peel_rate_at_wall_log_ratio`) | `ω/√2`, i.e. `2√2` times that (`angle_speed_sq`) |

The two bridges differ in the *first* derivative of the motion at `Γ = 0`, so a measurement of the
peel rate at zero reflection, divided by the frequency, decides between them: `1/2` or `1`. That is
the cheapest experiment the framework has.

## Status of the alternatives

| Candidate | What it fixes | Where it stands |
| :--- | :--- | :--- |
| The quadratic `(1/2)Γ^2` | nothing beyond the 2-jet | provable, gives force `Γ` (`deriv_phi1_wall`) |
| The ledger `-(1/2)log(1-Γ^2)` | the `√S` metric (Sra 2016) and the log-det composition | provable, force `Γ/(1-Γ^2)`, selected by composition |
| A ruler member `sqrt(log cosh(aΓ/2))/a` | the local slope only | provable, finite readings differ by `a` |
| The oscillator's own potential in `Γ` | the phase motion, if the oscillator is the source | provable (`harmPotInPeel_G`), and it is not the ledger |
| An equation for `Γ` from the dynamics | everything, given the phase motion | **now formalized**: the two motions above, with the two bridge equations |

The honest summary: the *consequences* of a bridge are theorems, the *equation of motion* for the
phase coordinate is now a theorem, and the *selection* of the bridge is not a consequence of the
peel calculus — it is decided by whether the composition principle or the oscillator is taken as
primary. The two choices are now separated by exact numbers: `2 m ω²` against `0` in the force at
`Γ = 0`, `(m ω²/2)(17+12√2)` against `½ log 2` at the wall, `1.7627/ω` against `0.7854/ω` in the
time to the wall, and `ω/2` against `ω` in the peel rate at zero reflection.
