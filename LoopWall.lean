/-
# The loop wall: peel steps, reflections, and what the archive keeps

The second layer of the library.  `ElementalPeeling` (the root modules) proves the finite algebra
of *Elemental Peeling and What the Boundary Retains*; this layer proves the exact mathematics of
the loop-wall papers, in which a removal ladder is read through the reflection
`Γ(z) = (z - 1)/(z + 1)` of its successive energy ratios `z = IE(k+1)/IE(k)`.

Rule and wall: `Elements` (the reflection, both branches of the wall, the element certificates),
`Wall` (the wall as an equality, `z = 3 ± 2√2`, reciprocal), `Clock` (face apex, double angle, the
two-boost condition, the envelope), `CutoffWindow` (the finite max/min lemma and the data window).

The ledger: `Ledger` (`Γ = tanh(½ log z)`, telescoping, scale invariance, reconstruction, the
ν-chain), `LedgerDescent` (loop-vanishing ledgers are endpoint potentials), `SumRule` and `Jensen`
(`T > L` and the `S/(1+S)` bound), `AngularRate` (the angular derivative and its zero).

Two faces and the rung: `TwoFace`, `BoundaryAgreement`, `Rung` (product versus sum form, the
uniqueness of `t = 1/2`, `Γ₀ = η/χ`, the direction of `ω` against `η`).

The archive: `Archive` (kernel recount of all 3,570 steps and 67 rungs, both cutoff windows, the
error rectangles, the C/N margin), `OpeningMap` (the noble-core opening map).

Linear algebra and optics: `Observer`, `CompressionVariance`, `Junction`, `TwoLevel`, `Positivity`,
`A2`, `Quaternions`, `TwoProbes`, `Optical`.

`README.md` gives the counts, `COVERAGE.md` maps each paper claim to its theorem, and
`LIMITATIONS.md` says what none of this establishes.
-/
import LoopWall.Elements
import LoopWall.Wall
import LoopWall.Clock
import LoopWall.TwoFace
import LoopWall.BoundaryAgreement
import LoopWall.Archive
import LoopWall.OpeningMap
import LoopWall.Observer
import LoopWall.TwoLevel
import LoopWall.CutoffWindow
import LoopWall.CompressionVariance
import LoopWall.Ledger
import LoopWall.Optical
import LoopWall.Rung
import LoopWall.Junction
import LoopWall.SumRule
import LoopWall.LedgerDescent
import LoopWall.Jensen
import LoopWall.AngularRate
import LoopWall.A2
import LoopWall.TwoProbes
import LoopWall.Quaternions
import LoopWall.Positivity
import LoopWall.ScalarLedger
import LoopWall.Oscillator
import LoopWall.RestFrame
import LoopWall.Hamiltonian
import LoopWall.SpacingLaw
import LoopWall.LocalRuler
import LoopWall.QuantumGeometricTensor
import LoopWall.TwoFieldAction
import LoopWall.PolarizerPorts
import LoopWall.Schrodinger
import LoopWall.ChromaticAngle
import LoopWall.BridgeUnderdetermination
import LoopWall.MatrixLedger
import LoopWall.PeelPotential
import LoopWall.ColourWheel
import LoopWall.FisherMatrix
