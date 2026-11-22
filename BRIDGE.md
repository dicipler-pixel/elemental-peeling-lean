# The bridge from phase motion to the potential

The open step in the framework is stated as: *an equation showing how the null or phase motion
determines `V_k`, and why its readout must be the ledger.* This file records what is now proved
about that step, what is a choice, and what would count as deriving it.

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

## What is forced

**The wall values.** `φled (1/√2) = (1/2) log 2` and `φled' (1/√2) = √2`
(`φled_wall`, `deriv_φled_wall`). The wall is not a singular point of the ledger potential: it is
differentiable and continuous there (`abs_wall_lt_one`, `wall_log_argument_pos`,
`differentiableAt_φled_wall`, `continuousAt_φled_wall`). The only singularity is at `|Γ| → 1`.

**The local constant.** The ledger's square root has slope `1/(2√2)` at `t = 0`, and every member of
the ruler family `sqrt (log (cosh (a t / 2)))/a` has the same slope while its finite readings differ
(`LoopWall/LocalRuler.lean`, `ruler_right_slope`, `ruler_one_strictAntiOn`).

**Additivity, when it holds.** The scalar ledger is *not* additive in the spacing — `t₁ = t₂ = 2` is
a witness (`LoopWall/MatrixLedger.lean`, `scalarLedger_not_additive`) — while the log-determinant
ledger is additive over channels and over direct sums
(`Sm_eq_sum_scalar`, `Sm_append`, `channel_additive_ledger`). So if a bridge is required to compose
across independent channels, the object it produces is the matrix ledger, and the scalar ledger is
its one-channel summand. For a single two-channel colour the two are not merely related but equal up
to a factor: `matrixLedger = 2 * scalarLedgerPotential` (`LoopWall/FisherMatrix.lean`), with
`det = (1 - Γ²)/4` and the wall at `det = 1/8`. That is why the same local constant appears in the
scalar and the determinant readings.

## What is not forced

**The choice of `φ` from local data.** Two potentials with the same value, first and second
derivative at `Γ = 0` — `(1/2)Γ^2` and the ledger — have different forces at the wall
(`LoopWall/BridgeUnderdetermination.lean`, `equal_two_jets_but_different_wall_forces`). The universal
form is proved: no function of the 2-jet at `0` computes the wall force
(`no_function_of_two_jet_computes_wall_force`). Locality of order two therefore cannot select the
bridge, and neither can the local ruler, for the same reason.

## What would count as deriving the bridge

One of the following, and nothing weaker:

* **A composition principle.** A requirement that the potential compose across independent
  channels, or across a subdivision of one channel, together with the normalisation at `Γ = 0`.
  `LoopWall/MatrixLedger.lean` shows the composition principle selects the log-determinant form; the
  scalar form is then the summand.
* **A dynamical postulate with a witness.** A stated equation of motion for `Γ` (not for `X`
  alone), from which `φ` is recovered as a first integral or as a Lyapunov function. The library has
  the pieces — `LoopWall/Hamiltonian.lean` for the conservative and damped cases,
  `LoopWall/PeelPotential.lean` for the frozen and phase-dependent oscillator — but the equation for
  `Γ` itself is not in it, because it has not been specified.
* **A measurement model** that fixes which two readings are compared and how they are combined. This
  is where the colour side bears: for two channels the peel *is* minus the cosine of the chromatic
  angle (`LoopWall/ChromaticAngle.lean`, `peel_eq_neg_cos`), so a bridge that reads the colour angle
  has its `Γ` fixed by the angle, and only `φ` remains to be chosen.

## Status of the alternatives

| Candidate | What it fixes | Where it stands |
| :--- | :--- | :--- |
| The quadratic `(1/2)Γ^2` | nothing beyond the 2-jet | provable, gives force `Γ` (`deriv_phi1_wall`) |
| The ledger `-(1/2)log(1-Γ^2)` | the `√S` metric (Sra 2016) and the log-det composition | provable, force `Γ/(1-Γ^2)` |
| A ruler member `sqrt(log cosh(aΓ/2))/a` | the local slope only | provable, finite readings differ by `a` |
| An equation for `Γ` from the dynamics | everything, if supplied | not formalized: no such equation has been stated |

The honest summary: the *consequences* of a bridge are now theorems, and the *selection* of a bridge
is not, and provably cannot be from local data. What the mathematics asks for is a composition
principle or an equation for the phase coordinate; either would settle it.
