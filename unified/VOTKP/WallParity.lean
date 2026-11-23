/-
VOTKP §11.5, Proposition 11.1: parity at a wall (Jeromie Beasley).

For a Seifert matrix `V` (size `2g`) and `ω` on the unit circle, the Hermitian form
`H(ω) = (1 − ω)V + (1 − ω̄)Vᵀ` has signature `σ_ω`. Two facts carry the proposition.

* `det_factor`: `det H(ω) = (1 − ω̄)^{2g} det(V − ωVᵀ)`, so along `ω = e^{iπt}` the real function
  `det H` is the Alexander polynomial times a factor that does not vanish for `ω ≠ 1`.
* `parity_at_wall`: if along a Hermitian path `det H(t) = (t − t₀)^m g(t)` with `g` of one sign
  on both sides, then half the change of the signature across `t₀` is congruent to `m` mod 2.
  In particular, at a simple root (`m = 1`) the signature jumps by an odd multiple of 2, so it
  does jump. The sign of a nonsingular Hermitian determinant is `(−1)^{#negative eigenvalues}`
  (`sign_prod`), which is the whole mechanism.

The order of the zero of `det H` at a root of multiplicity `m` is the hypothesis `hdet`; that
the jump at a simple root is exactly `±2` (not `±6`, …) uses analytic eigenvalue branches
(Rellich; Kato, Ch. II) and is not formalized here.
Developed with AI assistance.
-/
import Mathlib

namespace VOTKP.WallParity

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Proposition 11.1, the factorization.** On the unit circle,
`det((1 − ω)V + (1 − ω̄)Vᵀ) = (1 − ω̄)^{size} det(V − ωVᵀ)`. -/
theorem det_factor (V : Matrix n n ℂ) (ω : ℂ) (hω : Complex.normSq ω = 1) :
    ((1 - ω) • V + (1 - starRingEnd ℂ ω) • Vᵀ).det
      = (1 - starRingEnd ℂ ω) ^ Fintype.card n * (V - ω • Vᵀ).det := by
  have hc : ω * starRingEnd ℂ ω = 1 := by
    rw [Complex.mul_conj, hω, Complex.ofReal_one]
  have h1 : (1 - ω) = (1 - starRingEnd ℂ ω) * (-ω) := by
    linear_combination (-1 : ℂ) * hc
  have h2 : (1 - ω) • V + (1 - starRingEnd ℂ ω) • Vᵀ
      = (1 - starRingEnd ℂ ω) • (V - ω • Vᵀ)ᵀ := by
    rw [h1]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.sub_apply,
      smul_eq_mul]
    ring
  rw [h2, Matrix.det_smul, Matrix.det_transpose]

/-- The number of negative eigenvalues of a Hermitian matrix. -/
noncomputable def negCount (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => hA.eigenvalues i < 0).card

/-- The number of positive eigenvalues of a Hermitian matrix. -/
noncomputable def posCount (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- The signature `σ = #positive − #negative`. -/
noncomputable def signature (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℤ :=
  (posCount A hA : ℤ) - negCount A hA

lemma signature_nonsingular (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hnz : ∀ i, hA.eigenvalues i ≠ 0) :
    signature A hA = (Fintype.card n : ℤ) - 2 * negCount A hA := by
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset n))
    (fun i => hA.eigenvalues i < 0)
  have hf : (Finset.univ.filter fun i => 0 < hA.eigenvalues i)
      = Finset.univ.filter fun i => ¬ hA.eigenvalues i < 0 :=
    Finset.filter_congr fun i _ =>
      ⟨fun h => not_lt.mpr h.le, fun h => lt_of_le_of_ne (not_lt.mp h) (hnz i).symm⟩
  rw [Finset.card_univ] at hc
  unfold signature posCount negCount
  rw [hf]
  omega

/-- The sign of a product of nonzero reals is `(−1)^{#negative factors}`. -/
theorem sign_prod (f : n → ℝ) (hf : ∀ i, f i ≠ 0) :
    0 < (-1 : ℝ) ^ (Finset.univ.filter fun i => f i < 0).card * ∏ i, f i := by
  have h : ∏ i, f i = (∏ i, if f i < 0 then (-1 : ℝ) else 1) * ∏ i, |f i| := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [abs_of_neg hi]
      ring
    · rw [abs_of_nonneg (not_lt.mp hi)]
      ring
  have hs : ∏ i, (if f i < 0 then (-1 : ℝ) else 1)
      = (-1) ^ (Finset.univ.filter fun i => f i < 0).card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hsq : ((-1 : ℝ) ^ (Finset.univ.filter fun i => f i < 0).card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hp : 0 < ∏ i, |f i| := Finset.prod_pos fun i _ => abs_pos.mpr (hf i)
  rw [h, hs]
  have e : (-1 : ℝ) ^ (Finset.univ.filter fun i => f i < 0).card
      * ((-1) ^ (Finset.univ.filter fun i => f i < 0).card * ∏ i, |f i|)
      = ((-1 : ℝ) ^ (Finset.univ.filter fun i => f i < 0).card) ^ 2 * ∏ i, |f i| := by ring
  rw [e, hsq, one_mul]
  exact hp

/-- The product of the eigenvalues of a Hermitian matrix is the (real) determinant. -/
lemma prod_eigenvalues_eq (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : ℝ)
    (hdet : A.det = (x : ℂ)) : ∏ i, hA.eigenvalues i = x := by
  have h := hA.det_eq_prod_eigenvalues
  rw [hdet, ← RCLike.ofReal_prod] at h
  exact ((RCLike.ofReal_inj (K := ℂ)).mp h).symm

/-- **Proposition 11.1, parity at a wall.** Along a Hermitian path with
`det H(t) = (t − t₀)^m g(t)` and `g` of one sign at `t₁ < t₀ < t₂`, the signature changes by
`2j` with `j ≡ m (mod 2)`. -/
theorem parity_at_wall (H : ℝ → Matrix n n ℂ) (hH : ∀ t, (H t).IsHermitian) (t0 : ℝ) (m : ℕ)
    (g : ℝ → ℝ) (hdet : ∀ t, (H t).det = (((t - t0) ^ m * g t : ℝ) : ℂ))
    (t1 t2 : ℝ) (h1 : t1 < t0) (h2 : t0 < t2) (hg : 0 < g t1 * g t2) :
    ∃ j : ℤ, signature (H t2) (hH t2) - signature (H t1) (hH t1) = 2 * j ∧ j ≡ m [ZMOD 2] := by
  have hprod : ∀ t, ∏ i, (hH t).eigenvalues i = (t - t0) ^ m * g t := fun t =>
    prod_eigenvalues_eq (H t) (hH t) _ (hdet t)
  have hg1 : g t1 ≠ 0 := left_ne_zero_of_mul hg.ne'
  have hg2 : g t2 ≠ 0 := right_ne_zero_of_mul hg.ne'
  have hne : ∀ t, t ≠ t0 → g t ≠ 0 → ∀ i, (hH t).eigenvalues i ≠ 0 := by
    intro t ht hgt i hi
    have h0 : ∏ j, (hH t).eigenvalues j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hprod t] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact pow_ne_zero m (sub_ne_zero.mpr ht) h
    · exact hgt h
  have hnz1 := hne t1 h1.ne hg1
  have hnz2 := hne t2 h2.ne' hg2
  have hA := sign_prod _ hnz1
  have hB := sign_prod _ hnz2
  rw [hprod t1] at hA
  rw [hprod t2] at hB
  set N1 := negCount (H t1) (hH t1) with hN1
  set N2 := negCount (H t2) (hH t2) with hN2
  have hA' : 0 < (-1 : ℝ) ^ N1 * ((t1 - t0) ^ m * g t1) := hA
  have hB' : 0 < (-1 : ℝ) ^ N2 * ((t2 - t0) ^ m * g t2) := hB
  have e1 : (t1 - t0) ^ m = (-1) ^ m * (t0 - t1) ^ m := by
    rw [← mul_pow, neg_one_mul, neg_sub]
  have hp1 : 0 < (t0 - t1) ^ m := pow_pos (by linarith) m
  have hp2 : 0 < (t2 - t0) ^ m := pow_pos (by linarith) m
  have hbr : 0 < (t0 - t1) ^ m * (t2 - t0) ^ m * (g t1 * g t2) := mul_pos (mul_pos hp1 hp2) hg
  have key : 0 < (-1 : ℝ) ^ (N1 + N2 + m) * ((t0 - t1) ^ m * (t2 - t0) ^ m * (g t1 * g t2)) := by
    have hm := mul_pos hA' hB'
    rw [e1] at hm
    have e2 : (-1 : ℝ) ^ (N1 + N2 + m) * ((t0 - t1) ^ m * (t2 - t0) ^ m * (g t1 * g t2))
        = (-1) ^ N1 * ((-1) ^ m * (t0 - t1) ^ m * g t1) * ((-1) ^ N2 * ((t2 - t0) ^ m * g t2)) := by
      ring
    rw [e2]
    exact hm
  have hsign : 0 < (-1 : ℝ) ^ (N1 + N2 + m) := by nlinarith
  have heven : Even (N1 + N2 + m) := by
    rcases Nat.even_or_odd (N1 + N2 + m) with h | h
    · exact h
    · rw [h.neg_one_pow] at hsign
      norm_num at hsign
  obtain ⟨r, hr⟩ := heven
  refine ⟨(N1 : ℤ) - N2, ?_, ?_⟩
  · rw [signature_nonsingular _ _ hnz1, signature_nonsingular _ _ hnz2, ← hN1, ← hN2]
    ring
  · rw [Int.modEq_iff_dvd]
    exact ⟨(r : ℤ) - N1, by omega⟩

end VOTKP.WallParity
