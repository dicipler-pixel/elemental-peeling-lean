import Mathlib

/-!
# The spacing law is forced, and where regularity enters

Direction D1 of the third round.  If the spacing of two positive readings depends only on their
ratio and is additive over composition, then `continuous_additive_eq_mul` plus the log/exp transfer
(`continuousOn_multiplicative_eq_log`) makes it a constant times `log`: `log` is the only
continuous (or monotone: `monotone_additive_eq_mul`) law with `s (x * y) = s x + s y`.

Two repairs to my transcription are recorded.  Proportionality of two such laws needs
nondegeneracy of the second (`multiplicative_laws_proportional_of_nondegenerate`), since the zero
law satisfies every other hypothesis (`proportionality_fails_without_nondegeneracy`).  And
additivity alone is not enough: `additivity_alone_does_not_suffice` constructs an additive map
from a Hamel-style argument (independent `{1}`, `√2` outside its rational span) that is not
`x ↦ c x`.

Written in the third parallel formalization round (swarm `smws58h9u`, direction m8), recompiled and
reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.SpacingLaw

open Set Module

/-- Cauchy's additive functional equation, with continuity. -/
theorem continuous_additive_eq_mul (f : ℝ → ℝ) (hf : Continuous f)
    (hadd : ∀ x y, f (x + y) = f x + f y) : ∃ c, ∀ x, f x = c * x := by
  let F : ℝ →+ ℝ :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        simp only [add_zero] at h
        linarith
      map_add' := hadd }
  have hF : Continuous F := hf
  refine ⟨f 1, fun x => ?_⟩
  have h := map_real_smul F hF x 1
  simpa [F, smul_eq_mul, mul_comm] using h

/-- A multiplicative law on positive reals becomes additive after `exp`. -/
theorem continuousOn_multiplicative_eq_log (s : ℝ → ℝ)
    (hs : ContinuousOn s (Ioi 0))
    (hmul : ∀ x y, 0 < x → 0 < y → s (x * y) = s x + s y) :
    ∃ c, ∀ x, 0 < x → s x = c * Real.log x := by
  let f : ℝ → ℝ := fun t => s (Real.exp t)
  have hf_on : ContinuousOn f Set.univ := by
    apply hs.comp Real.continuous_exp.continuousOn
    intro x _
    exact Real.exp_pos x
  have hf : Continuous f := continuousOn_univ.mp hf_on
  have hadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    dsimp [f]
    rw [Real.exp_add, hmul _ _ (Real.exp_pos x) (Real.exp_pos y)]
  obtain ⟨c, hc⟩ := continuous_additive_eq_mul f hf hadd
  refine ⟨c, fun x hx => ?_⟩
  have h := hc (Real.log x)
  dsimp [f] at h
  simpa [Real.exp_log hx] using h

/-- The literal globally-continuous version is a corollary.  The positive-domain
version above is the useful formulation: a nonzero logarithm has no continuous
extension to `0`. -/
theorem continuous_multiplicative_eq_log (s : ℝ → ℝ) (hs : Continuous s)
    (hmul : ∀ x y, 0 < x → 0 < y → s (x * y) = s x + s y) :
    ∃ c, ∀ x, 0 < x → s x = c * Real.log x :=
  continuousOn_multiplicative_eq_log s hs.continuousOn hmul

/-- Two logarithmic laws are proportional when the second is nondegenerate. -/
theorem multiplicative_laws_proportional_of_nondegenerate
    (s₁ s₂ : ℝ → ℝ)
    (hs₁ : ContinuousOn s₁ (Ioi 0)) (hs₂ : ContinuousOn s₂ (Ioi 0))
    (hmul₁ : ∀ x y, 0 < x → 0 < y → s₁ (x * y) = s₁ x + s₁ y)
    (hmul₂ : ∀ x y, 0 < x → 0 < y → s₂ (x * y) = s₂ x + s₂ y)
    (hne : ∃ x, 0 < x ∧ s₂ x ≠ 0) :
    ∃ k, ∀ x, 0 < x → s₁ x = k * s₂ x := by
  obtain ⟨c₁, hc₁⟩ := continuousOn_multiplicative_eq_log s₁ hs₁ hmul₁
  obtain ⟨c₂, hc₂⟩ := continuousOn_multiplicative_eq_log s₂ hs₂ hmul₂
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hne
  have hc₂ne : c₂ ≠ 0 := by
    intro hc
    apply hx₀ne
    rw [hc₂ x₀ hx₀, hc, zero_mul]
  refine ⟨c₁ / c₂, fun x hx => ?_⟩
  rw [hc₁ x hx, hc₂ x hx]
  field_simp

/-- The unrestricted proportionality assertion is false: the zero law is a
second, degenerate solution. -/
theorem proportionality_fails_without_nondegeneracy :
    ¬ (∀ s₁ s₂ : ℝ → ℝ,
      ContinuousOn s₁ (Ioi 0) → ContinuousOn s₂ (Ioi 0) →
      (∀ x y, 0 < x → 0 < y → s₁ (x * y) = s₁ x + s₁ y) →
      (∀ x y, 0 < x → 0 < y → s₂ (x * y) = s₂ x + s₂ y) →
      ∃ k, ∀ x, 0 < x → s₁ x = k * s₂ x) := by
  intro h
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
  have hzero : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioi 0) := continuousOn_const
  obtain ⟨k, hk⟩ := h Real.log (fun _ => 0) hlog hzero
    (fun x y hx hy => Real.log_mul (ne_of_gt hx) (ne_of_gt hy))
    (fun _ _ _ _ => by simp)
  have h := hk (Real.exp 1) (Real.exp_pos 1)
  simpa using h

/-- Cauchy's additive functional equation, with monotonicity instead of
continuity. -/
theorem monotone_additive_eq_mul (f : ℝ → ℝ) (hf : Monotone f)
    (hadd : ∀ x y, f (x + y) = f x + f y) : ∃ c, ∀ x, f x = c * x := by
  let F : ℝ →+ ℝ :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        simp only [add_zero] at h
        linarith
      map_add' := hadd }
  have hzero : f 0 = 0 := F.map_zero
  have hrat : ∀ q : ℚ, f (q : ℝ) = (q : ℝ) * f 1 := by
    intro q
    have h := map_ratCast_smul F ℝ ℝ q 1
    simpa [F, smul_eq_mul] using h
  have hc : 0 ≤ f 1 := by
    have h := hf (show (0 : ℝ) ≤ 1 by norm_num)
    rwa [hzero] at h
  refine ⟨f 1, fun x => ?_⟩
  by_cases hc0 : f 1 = 0
  · have hz : ∀ z : ℝ, 0 ≤ z → f z = 0 := by
      intro z hz
      obtain ⟨q, hq⟩ := exists_rat_gt z
      have h₁ := hf hz
      have h₂ := hf hq.le
      rw [hzero] at h₁
      rw [hrat q, hc0, mul_zero] at h₂
      exact le_antisymm h₂ h₁
    by_cases hx : 0 ≤ x
    · rw [hz x hx, hc0, zero_mul]
    · have hxneg : x < 0 := lt_of_not_ge hx
      have hx' : 0 ≤ -x := neg_nonneg.mpr hxneg.le
      have h := F.map_neg x
      change f (-x) = -f x at h
      rw [hz (-x) hx'] at h
      rw [hc0, zero_mul]
      linarith
  · have hcpos : 0 < f 1 := lt_of_le_of_ne hc (Ne.symm hc0)
    rcases lt_trichotomy (f x) (f 1 * x) with h | h | h
    · have hdiv : f x / f 1 < x := by
        apply (div_lt_iff₀ hcpos).2
        simpa [mul_comm] using h
      obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hdiv
      have hm := hf hq₂.le
      rw [hrat q] at hm
      have hq := (div_lt_iff₀ hcpos).1 hq₁
      exfalso
      exact (not_le_of_gt hq) hm
    · exact h
    · have hdiv : x < f x / f 1 := by
        apply (lt_div_iff₀ hcpos).2
        simpa [mul_comm] using h
      obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hdiv
      have hm := hf hq₁.le
      rw [hrat q] at hm
      have hq := (lt_div_iff₀ hcpos).1 hq₂
      exfalso
      exact (not_le_of_gt hq) hm

/-- The monotone form of the positive-ratio logarithm theorem. -/
theorem monotoneOn_multiplicative_eq_log (s : ℝ → ℝ)
    (hs : MonotoneOn s (Ioi 0))
    (hmul : ∀ x y, 0 < x → 0 < y → s (x * y) = s x + s y) :
    ∃ c, ∀ x, 0 < x → s x = c * Real.log x := by
  let f : ℝ → ℝ := fun t => s (Real.exp t)
  have hf : Monotone f := by
    intro x y hxy
    exact hs (Real.exp_pos x) (Real.exp_pos y) (Real.exp_le_exp.mpr hxy)
  have hadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    dsimp [f]
    rw [Real.exp_add, hmul _ _ (Real.exp_pos x) (Real.exp_pos y)]
  obtain ⟨c, hc⟩ := monotone_additive_eq_mul f hf hadd
  refine ⟨c, fun x hx => ?_⟩
  have h := hc (Real.log x)
  dsimp [f] at h
  simpa [Real.exp_log hx] using h


/-- Additivity by itself does not force real homogeneity.  A Hamel basis of
`ℝ` over `ℚ`, containing `1` and `√2`, gives an explicit additive function
sending `1` to `0` and `√2` to `1`.  No function `x ↦ c*x` has these values. -/
theorem additivity_alone_does_not_suffice :
    ∃ f : ℝ → ℝ, (∀ x y, f (x + y) = f x + f y) ∧
      ¬ ∃ c, ∀ x, f x = c * x := by
  have hone : LinearIndepOn ℚ id ({1} : Set ℝ) :=
    LinearIndepOn.singleton one_ne_zero
  have hsqrt_not_span : Real.sqrt 2 ∉ Submodule.span ℚ ({1} : Set ℝ) := by
    rw [show Submodule.span ℚ ({1} : Set ℝ) = ℚ ∙ (1 : ℝ) by rfl]
    rw [Submodule.mem_span_singleton]
    rintro ⟨q, hq⟩
    apply irrational_sqrt_two.ne_rat q
    simpa [smul_eq_mul] using hq.symm
  have hli : LinearIndepOn ℚ id (insert (Real.sqrt 2) ({1} : Set ℝ)) :=
    hone.id_insert hsqrt_not_span
  let b := Module.Basis.extend hli
  let i_one : hli.extend (Set.subset_univ _) :=
    ⟨1, Module.Basis.subset_extend hli (by simp)⟩
  let i_sqrt : hli.extend (Set.subset_univ _) :=
    ⟨Real.sqrt 2, Module.Basis.subset_extend hli (by simp)⟩
  have hb_one : b i_one = 1 := Module.Basis.extend_apply_self hli i_one
  have hb_sqrt : b i_sqrt = Real.sqrt 2 := Module.Basis.extend_apply_self hli i_sqrt
  let g : hli.extend (Set.subset_univ _) → ℝ :=
    fun i => if (i : ℝ) = Real.sqrt 2 then 1 else 0
  let L : ℝ →ₗ[ℚ] ℝ := b.constr ℚ g
  have hL_one : L 1 = 0 := by
    rw [← hb_one]
    change (b.constr ℚ g) (b i_one) = 0
    rw [b.constr_basis]
    dsimp [g, i_one]
    rw [if_neg]
    exact fun h => irrational_sqrt_two.ne_rat 1 (by simpa using h.symm)
  have hL_sqrt : L (Real.sqrt 2) = 1 := by
    rw [← hb_sqrt]
    change (b.constr ℚ g) (b i_sqrt) = 1
    rw [b.constr_basis]
    simp [g, i_sqrt]
  refine ⟨fun x => L x, fun x y => L.map_add x y, ?_⟩
  rintro ⟨c, hc⟩
  have h₁ := hc 1
  have h₂ := hc (Real.sqrt 2)
  dsimp at h₁ h₂
  rw [hL_one] at h₁
  rw [hL_sqrt] at h₂
  have hc0 : c = 0 := by simpa using h₁.symm
  rw [hc0, zero_mul] at h₂
  exact one_ne_zero h₂


end ElementalPeeling.LoopWall.SpacingLaw
