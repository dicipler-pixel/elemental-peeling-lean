import DiracTime.PathLedger
import LoopWall.Ledger
import LoopWall.LedgerDescent
import LoopWall.CompositionBridge

/-!
# The signed peel ledger and path-ledger descent

This file separates the signed ratio ledger from the even scalar/determinant
composition readouts.  All external theorems used here are the actual declarations
in repositories A and B; source locations are recorded at their use sites.
-/

namespace LedgerInterface

open ElementalPeeling.LoopWall

/-! ## `tanh` does not change the descent criterion -/

section TanhDescent

variable {X : Type*} {Q : X → X → Type*}

/-- If a ledger is additive and reversal-odd on a connected path system, then
`tanh (ℓ/2)` is a function of the ordered endpoints exactly when every loop is
silent.  This is the literal `DiracTime.PathLedger.descent_iff` from
`DiracTime/PathLedger.lean:21-41`, transported through injectivity of `tanh`. -/
theorem tanh_descent_iff
    (comp : ∀ {x y z : X}, Q x y → Q y z → Q x z)
    (rev : ∀ {x y : X}, Q x y → Q y x)
    (ℓ : ∀ {x y : X}, Q x y → ℝ)
    (hcomp : ∀ {x y z : X} (p : Q x y) (q : Q y z),
      ℓ (comp p q) = ℓ p + ℓ q)
    (hrev : ∀ {x y : X} (p : Q x y), ℓ (rev p) = -ℓ p)
    (hconn : ∀ x y : X, Nonempty (Q x y)) :
    (∃ n : X → ℝ, ∀ {x y : X} (γ : Q x y),
      Real.tanh (ℓ γ / 2) = Real.tanh ((n y - n x) / 2)) ↔
      ∀ {x : X} (c : Q x x), Real.tanh (ℓ c / 2) = 0 := by
  constructor
  · rintro ⟨n, hn⟩ x c
    rw [hn c]
    simp
  · intro hsilent
    have hzero : ∀ {x : X} (c : Q x x), ℓ c = 0 := by
      intro x c
      have ht : ℓ c / 2 = 0 := by
        apply Real.tanh_injective
        simpa using hsilent c
      linarith
    obtain ⟨n, hn⟩ :=
      (DiracTime.PathLedger.descent_iff (X := X) (P := Q)
        comp rev ℓ hcomp hrev hconn).2 hzero
    exact ⟨n, fun γ => by rw [hn γ]⟩

end TanhDescent

/-! ## The positive peel-ratio ledger is a genuine instance -/

/-- Positive threshold readings, the vertices of the peel configuration graph. -/
abbrev PosReading := {x : ℝ // 0 < x}

/-- The signed ratio assigned to an edge `x → y` is `y/x`. -/
noncomputable def peelWeight (x y : PosReading) : ℝ := Real.log (y.1 / x.1)

/-- Arbitrary chained paths, not just paths along a fixed `ℕ`-indexed ladder.
This is `LedgerDescent.Path` from `LoopWall/LedgerDescent.lean:68-91`. -/
abbrev PeelPath (x y : PosReading) :=
  LedgerDescent.SymRel.Path (LedgerDescent.complete PosReading) x y

/-- Path concatenation (`LoopWall/LedgerDescent.lean:78-81`). -/
def peelComp {x y z : PosReading} (p : PeelPath x y) (q : PeelPath y z) :
    PeelPath x z :=
  LedgerDescent.SymRel.Path.append (LedgerDescent.complete PosReading) p q

/-- Path reversal (`LoopWall/LedgerDescent.lean:83-86`). -/
def peelRev {x y : PosReading} (p : PeelPath x y) : PeelPath y x :=
  LedgerDescent.SymRel.Path.reverse (LedgerDescent.complete PosReading) p

/-- Sum of signed logarithmic ratios along a path. -/
noncomputable def peelLedger {x y : PosReading} (p : PeelPath x y) : ℝ :=
  LedgerDescent.walkSum peelWeight p.steps

/-- The reflection readout of a whole path. -/
noncomputable def peelReflection {x y : PosReading} (p : PeelPath x y) : ℝ :=
  Real.tanh (peelLedger p / 2)

lemma peelWeight_skew (x y : PosReading) :
    peelWeight x y + peelWeight y x = 0 := by
  unfold peelWeight
  rw [Real.log_div (ne_of_gt y.2) (ne_of_gt x.2),
    Real.log_div (ne_of_gt x.2) (ne_of_gt y.2)]
  ring

lemma peelWeight_cocycle : LedgerDescent.WeightCocycle peelWeight := by
  intro x y z
  unfold peelWeight
  rw [Real.log_div (ne_of_gt y.2) (ne_of_gt x.2),
    Real.log_div (ne_of_gt z.2) (ne_of_gt y.2),
    Real.log_div (ne_of_gt z.2) (ne_of_gt x.2)]
  ring

/-- Concatenation additivity uses `walkSum_append` at
`LoopWall/LedgerDescent.lean:176-180`. -/
lemma peelLedger_comp {x y z : PosReading}
    (p : PeelPath x y) (q : PeelPath y z) :
    peelLedger (peelComp p q) = peelLedger p + peelLedger q := by
  change LedgerDescent.walkSum peelWeight (p.steps ++ q.steps) = _
  exact LedgerDescent.walkSum_append peelWeight p.steps q.steps

/-- Reversal oddness uses `walkSum_reverseSteps` at
`LoopWall/LedgerDescent.lean:183-196`. -/
lemma peelLedger_rev {x y : PosReading} (p : PeelPath x y) :
    peelLedger (peelRev p) = -peelLedger p := by
  change LedgerDescent.walkSum peelWeight (LedgerDescent.reverseSteps p.steps) = _
  exact LedgerDescent.walkSum_reverseSteps peelWeight peelWeight_skew p.steps

/-- The complete positive-reading graph is connected by one-step paths. -/
lemma peelPath_connected (x y : PosReading) : Nonempty (PeelPath x y) :=
  ⟨LedgerDescent.SymRel.Path.single (LedgerDescent.complete PosReading)
    (LedgerDescent.completeStep x y)⟩

/-- **Literal instance of repo B's theorem.**  The ratio ledger satisfies every
hypothesis of `DiracTime.PathLedger.descent_iff`; no additional loop hypothesis
is hidden in this equivalence. -/
theorem peel_descent_iff :
    (∃ n : PosReading → ℝ, ∀ {x y : PosReading} (p : PeelPath x y),
      peelLedger p = n y - n x) ↔
      ∀ {x : PosReading} (c : PeelPath x x), peelLedger c = 0 :=
  DiracTime.PathLedger.descent_iff (X := PosReading) (P := PeelPath)
    peelComp peelRev (@peelLedger) peelLedger_comp peelLedger_rev peelPath_connected

/-- The elemental ledger telescopes on every path, with explicit potential `log`.
The proof uses the actual cocycle telescoping theorem at
`LoopWall/LedgerDescent.lean:272-275`. -/
theorem peelLedger_eq_log_sub {x y : PosReading} (p : PeelPath x y) :
    peelLedger p = Real.log y.1 - Real.log x.1 := by
  change LedgerDescent.walkSum peelWeight p.steps = _
  rw [LedgerDescent.walkSum_eq_weight_of_cocycle peelWeight peelWeight_cocycle p]
  exact Real.log_div (ne_of_gt y.2) (ne_of_gt x.2)

/-- In particular, the loop-silence side of `peel_descent_iff` is automatic for
ratios of endpoint readings. -/
theorem peel_loop_silent {x : PosReading} (c : PeelPath x x) : peelLedger c = 0 := by
  rw [peelLedger_eq_log_sub]
  ring

/-- The forward side is inhabited by the elemental potential itself. -/
theorem peel_log_potential :
    ∃ n : PosReading → ℝ, ∀ {x y : PosReading} (p : PeelPath x y),
      peelLedger p = n y - n x :=
  ⟨fun x => Real.log x.1, fun p => peelLedger_eq_log_sub p⟩

/-- The reflection form of descent, specialized to the peel paths. -/
theorem peelReflection_descent_iff :
    (∃ n : PosReading → ℝ, ∀ {x y : PosReading} (p : PeelPath x y),
      peelReflection p = Real.tanh ((n y - n x) / 2)) ↔
      ∀ {x : PosReading} (c : PeelPath x x), peelReflection c = 0 := by
  simpa only [peelReflection] using
    (tanh_descent_iff (X := PosReading) (Q := PeelPath)
      peelComp peelRev (@peelLedger) peelLedger_comp peelLedger_rev peelPath_connected)

/-- In the peel instance the reflection potential criterion is inhabited
unconditionally, by the same potential `log`. -/
theorem peelReflection_log_potential :
    ∃ n : PosReading → ℝ, ∀ {x y : PosReading} (p : PeelPath x y),
      peelReflection p = Real.tanh ((n y - n x) / 2) := by
  refine ⟨fun x => Real.log x.1, fun p => ?_⟩
  unfold peelReflection
  rw [peelLedger_eq_log_sub]

/-- The reflection loop-silence side is likewise automatic in this instance. -/
theorem peelReflection_loop_silent {x : PosReading} (c : PeelPath x x) :
    peelReflection c = 0 := by
  unfold peelReflection
  rw [peel_loop_silent]
  norm_num

/-- Along a path, `tanh(ℓ/2)` is exactly repo A's reflection of the endpoint
ratio.  The final identity is `gam_eq_tanh_half_log` at
`LoopWall/Ledger.lean:34-42`. -/
theorem peelReflection_eq_endpoint_gam {x y : PosReading} (p : PeelPath x y) :
    peelReflection p = Ledger.gam (y.1 / x.1) := by
  unfold peelReflection
  rw [peelLedger_eq_log_sub]
  calc
    Real.tanh ((Real.log y.1 - Real.log x.1) / 2) =
        Real.tanh (Real.log (y.1 / x.1) / 2) := by
      rw [Real.log_div (ne_of_gt y.2) (ne_of_gt x.2)]
    _ = Ledger.gam (y.1 / x.1) :=
      (Ledger.gam_eq_tanh_half_log _ (div_pos y.2 x.2)).symm

/-- The corresponding reflection is reversal-odd. -/
theorem peelReflection_rev {x y : PosReading} (p : PeelPath x y) :
    peelReflection (peelRev p) = -peelReflection p := by
  unfold peelReflection
  rw [peelLedger_rev]
  have h : -peelLedger p / 2 = -(peelLedger p / 2) := by ring
  rw [h, Real.tanh_neg]

/-! ## Additivity and skewness alone do not imply silence -/

/-- Repo A's explicit cyclic three-graph has an unsilent loop.  Its walk sums are
additive by `walkSum_append` (`LoopWall/LedgerDescent.lean:176-180`) and
reversal-odd by `walkSum_reverseSteps` plus `chiralWeight_skew`
(`LoopWall/LedgerDescent.lean:183-196,283-285`).  Thus these two hypotheses alone
cannot prove loop silence.  The nonzero value is the proved triangle sum at
`LoopWall/LedgerDescent.lean:287-290`. -/
theorem chiral_ledger_has_unsilent_loop :
    ¬ LedgerDescent.VanishesOnLoops
      (LedgerDescent.walkSum LedgerDescent.chiralWeight) := by
  intro h
  have ht := h (LedgerDescent.trianglePath (0 : Fin 3) 1 2)
  rw [LedgerDescent.chiralWeight_triangle_sum] at ht
  norm_num at ht

/-- The same cycle with real coefficients, for the `tanh` formulation. -/
noncomputable def realChiralWeight (i j : Fin 3) : ℝ :=
  (LedgerDescent.chiralWeight i j : ℝ)

lemma realChiralWeight_skew (i j : Fin 3) :
    realChiralWeight i j + realChiralWeight j i = 0 := by
  unfold realChiralWeight
  exact_mod_cast LedgerDescent.chiralWeight_skew i j

lemma realChiralWeight_triangle_sum :
    LedgerDescent.walkSum realChiralWeight
      (LedgerDescent.trianglePath (0 : Fin 3) 1 2).steps = 3 := by
  norm_num [realChiralWeight, LedgerDescent.chiralWeight,
    LedgerDescent.trianglePath, LedgerDescent.walkSum]

/-- Thus additivity and reversal-oddness do not make a real reflection ledger
silent on loops.  Additivity is again `walkSum_append`; reversal-oddness follows
from `walkSum_reverseSteps realChiralWeight realChiralWeight_skew`. -/
theorem real_chiral_reflection_loop_not_silent :
    Real.tanh (LedgerDescent.walkSum realChiralWeight
      (LedgerDescent.trianglePath (0 : Fin 3) 1 2).steps / 2) ≠ 0 := by
  rw [realChiralWeight_triangle_sum]
  intro h
  have hz : (3 : ℝ) / 2 = 0 := by
    apply Real.tanh_injective
    simpa using h
  norm_num at hz

/-! ## The even composition readouts are not the signed path ledger -/

open CompositionBridge FisherMatrix PeelPotential ScalarLedger

/-- Reversing a positive peel step swaps its readings, but the scalar ledger is
unchanged (`S_swap`, `LoopWall/ScalarLedger.lean:131-134`).  At `(I,J)=(2,1)` it
is nonzero by `S_eq_zero_iff` (`LoopWall/ScalarLedger.lean:103-123`), so it cannot
be reversal-odd. -/
theorem scalar_composition_ledger_not_reversal_odd :
    ∃ I J : ℝ, 0 < I ∧ 0 < J ∧ S J I ≠ -S I J := by
  refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
  rw [S_swap]
  intro h
  have hz : S 2 1 = 0 := by linarith
  have heq := (S_eq_zero_iff (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1)).1 hz
  norm_num at heq

/-- Channel swap is exactly reversal of the two readings in the coordinates of
`CompositionBridge` (`LoopWall/CompositionBridge.lean:120-129,397-401`). -/
theorem swapShares_readingShares (I J : ℝ) :
    swapShares (readingShares I J) = readingShares J I := by
  funext i
  fin_cases i <;> simp [swapShares, readingShares, add_comm]

/-- A physical wall colour refutes reversal-oddness of the actual normalized-
determinant readout.  Swap invariance is `normalizedDet_swap` at
`LoopWall/CompositionBridge.lean:151-154`; the nonvanishing wall value is supplied
by `wall_colour_witness` at `LoopWall/CompositionBridge.lean:336-350`. -/
theorem determinant_composition_readout_not_reversal_odd :
    ∃ q : Fin 2 → ℝ, (∀ i, 0 < q i) ∧ q 0 + q 1 = 1 ∧
      (balance q) ^ 2 = 1 / 2 ∧
      -Real.log (normalizedDet (swapShares q)) ≠
        -(-Real.log (normalizedDet q)) := by
  obtain ⟨q, hq, hnorm, hwall, hvalue⟩ := wall_colour_witness
  refine ⟨q, hq, hnorm, hwall, ?_⟩
  rw [normalizedDet_swap]
  intro hodd
  have hne : (-Real.log (normalizedDet q)) ≠ 0 := by
    rw [hvalue]
    exact ne_of_gt (Real.log_pos (by norm_num))
  apply hne
  linarith

end LedgerInterface
