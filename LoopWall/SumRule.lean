import Mathlib

/-!
# The sum rule T > L for f x = x/(1+x)

Direction D4.  `f_lt_self` and the finite strict inequality `sum_f_lt_sum`; the ENNReal lift
`fENN` with `fENN_lt_self` (including `r = ∞`); `lintegral_fENN_lt` with the finiteness
hypothesis `∫⁻ a ≠ ∞`, which `counting_measure_counterexample` shows is necessary.

Written in the second parallel formalization round (swarm `smws2pzvk`, direction m3),
then recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem` so the
repository audit sees it, trailing `#print axioms` lines removed because `scripts/verify.py` audits
every named theorem.  See PROVENANCE.md.
-/

open scoped BigOperators ENNReal

namespace ElementalPeeling.LoopWall.SumRule

/-- The scalar shrinking map in the sum rule. -/
noncomputable def f (x : ℝ) : ℝ := x / (1 + x)

theorem f_pos {x : ℝ} (hx : 0 < x) : 0 < f x := by
  exact div_pos hx (by linarith)

theorem f_lt_self {x : ℝ} (hx : 0 < x) : f x < x := by
  rw [f, div_lt_iff₀ (by linarith : (0 : ℝ) < 1 + x)]
  nlinarith [mul_pos hx hx]

theorem f_le_self {x : ℝ} (hx : 0 ≤ x) : f x ≤ x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [f]
  · exact (f_lt_self hx).le

/-- Termwise comparison is strict on any finite nonempty family. -/
theorem sum_f_lt_sum {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) : ∑ i, f (x i) < ∑ i, x i := by
  let i₀ : ι := Classical.choice inferInstance
  exact Finset.sum_lt_sum
    (fun i _ => (f_lt_self (hx i)).le)
    ⟨i₀, Finset.mem_univ i₀, f_lt_self (hx i₀)⟩

/-- The ENNReal-valued integrand obtained by applying `f` to the real part. -/
noncomputable def fENN (r : ℝ≥0∞) : ℝ≥0∞ := ENNReal.ofReal (f r.toReal)

/-- The pointwise comparison also holds at `r = ∞`, where `r.toReal = 0`. -/
theorem fENN_lt_self {r : ℝ≥0∞} (hr : 0 < r) : fENN r < r := by
  by_cases htop : r = ∞
  · subst r
    simp [fENN, f]
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hreal : 0 < r.toReal := ENNReal.toReal_pos hr0 htop
    have hlt := f_lt_self hreal
    rw [fENN]
    calc
      ENNReal.ofReal (f r.toReal) < ENNReal.ofReal r.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff hreal).2 hlt
      _ = r := ENNReal.ofReal_toReal htop

theorem fENN_le_self (r : ℝ≥0∞) : fENN r ≤ r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [fENN, f]
  · exact (fENN_lt_self (pos_iff_ne_zero.2 hr)).le

/-- Corrected integral form: finiteness of the dominating integral is essential. -/
theorem lintegral_fENN_lt {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (a : α → ℝ≥0∞) (ha : Measurable a) (hapos : ∀ᵐ t ∂μ, 0 < a t)
    (hane : ∫⁻ t, a t ∂μ ≠ 0) (hafin : ∫⁻ t, a t ∂μ ≠ ∞) :
    ∫⁻ t, fENN (a t) ∂μ < ∫⁻ t, a t ∂μ := by
  have hle : (fun t => fENN (a t)) ≤ᵐ[μ] a :=
    Filter.Eventually.of_forall (fun t => fENN_le_self (a t))
  have hfin : ∫⁻ t, fENN (a t) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hafin (MeasureTheory.lintegral_mono_ae hle)
  have hμ : μ ≠ 0 := by
    intro hμ
    apply hane
    simp [hμ]
  exact MeasureTheory.lintegral_strict_mono hμ ha.aemeasurable hfin
    (hapos.mono (fun t ht => fENN_lt_self ht))

/-- In the counterexample both integrals diverge, so infinity cannot be strictly below itself. -/
theorem counting_measure_integrals_eq_top :
    (∫⁻ _t : ℕ, fENN (1 : ℝ≥0∞) ∂MeasureTheory.Measure.count) = ∞ ∧
      (∫⁻ _t : ℕ, (1 : ℝ≥0∞) ∂MeasureTheory.Measure.count) = ∞ := by
  simp [fENN, f]

/-- The stated integral claim without a finiteness hypothesis is false. -/
theorem counting_measure_counterexample :
    let μ : MeasureTheory.Measure ℕ := MeasureTheory.Measure.count
    let a : ℕ → ℝ≥0∞ := fun _ => 1
    Measurable a ∧ (∀ᵐ t ∂μ, 0 < a t) ∧ (∫⁻ t, a t ∂μ) ≠ 0 ∧
      ¬(∫⁻ t, fENN (a t) ∂μ) < (∫⁻ t, a t ∂μ) := by
  simp [fENN, f]


end ElementalPeeling.LoopWall.SumRule
