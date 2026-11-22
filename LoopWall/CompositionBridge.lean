import Mathlib
import LoopWall.PeelPotential
import LoopWall.FisherMatrix
import LoopWall.MatrixLedger
import LoopWall.ScalarLedger

/-!
Direction B5 of the fifth round (swarm `smws70oju`, member m4). This is the selection theorem the
bridge needed: a normalised readout of a two-channel colour that is additive under appending
channels satisfies `A (x y) = A x + A y` on `(0,1]`, hence — with interior differentiability and a
left derivative at `1` — `A = c · log`. Matching the wall reading `log 2` then forces `c = -1`, so the
log-determinant ledger is the *only* additive readout of that normalisation. Composition selects the
ledger; the equation of motion does not.

Written in the fifth parallel formalization round and recompiled here before acceptance;
imports hoisted, namespace prefixed to `ElementalPeeling.LoopWall`, nothing else changed.
-/

/-!
# Composition determines the logarithmic determinant readout

The composition law used here is multiplication of the normalised determinant
`d p = 4 * det (shareMatrix p)` when independent two-channel blocks are appended.
A regular readout of `d` which turns this multiplication into addition is a
multiple of `log d`.  We then use the library's determinant/balance identities
to identify that readout with the matrix ledger and the scalar ledger potential.
-/

namespace ElementalPeeling.LoopWall.CompositionBridge

open Set
open scoped BigOperators
open ElementalPeeling.LoopWall.PeelPotential
open ElementalPeeling.LoopWall.FisherMatrix

noncomputable section
set_option maxHeartbeats 1000000

/-- A multiplicative readout on the physical determinant interval is logarithmic.
Only interior differentiability and a one-sided derivative at the normalised
point `1` are needed; no global regularity away from `(0,1]` is assumed. -/
theorem eq_const_mul_log_of_mul_add_on_Ioc
    {A : ℝ → ℝ} {c : ℝ}
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      A (x * y) = A x + A y)
    (hA : DifferentiableOn ℝ A (Ioo (0 : ℝ) 1))
    (hA1 : HasDerivWithinAt A c (Ioc (0 : ℝ) 1) 1) :
    ∀ x ∈ Ioc (0 : ℝ) 1, A x = c * Real.log x := by
  have hA_one : A 1 = 0 := by
    have h := hmul 1 (by norm_num) 1 (by norm_num)
    norm_num at h ⊢
    linarith
  have hderiv (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
      y * deriv A y = c := by
    have hyA : HasDerivAt A (deriv A y) y :=
      ((hA y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
    have hlin : HasDerivWithinAt (fun x : ℝ => x * y) y (Ioc (0 : ℝ) 1) 1 := by
      convert (hasDerivAt_id (1 : ℝ)).mul_const y |>.hasDerivWithinAt using 1 <;> simp
    have hyA' : HasDerivAt A (deriv A y) (1 * y) := by simpa using hyA
    have hcomp : HasDerivWithinAt (fun x : ℝ => A (x * y)) (deriv A y * y)
        (Ioc (0 : ℝ) 1) 1 := hyA'.comp_hasDerivWithinAt 1 hlin
    have hcomp' : HasDerivWithinAt (fun x : ℝ => A x + A y) (deriv A y * y)
        (Ioc (0 : ℝ) 1) 1 := by
      apply hcomp.congr
      · intro x hx
        symm
        exact hmul x hx y ⟨hy.1, hy.2.le⟩
      · symm
        exact hmul 1 (by norm_num) y ⟨hy.1, hy.2.le⟩
    have hright : HasDerivWithinAt (fun x : ℝ => A x + A y) c
        (Ioc (0 : ℝ) 1) 1 := hA1.add_const (A y)
    have heq := (uniqueDiffOn_Ioc (0 : ℝ) 1 1 (by norm_num)).eq_deriv
      (Ioc (0 : ℝ) 1) hcomp' hright
    nlinarith
  let D : ℝ → ℝ := fun x => A x - c * Real.log x
  have hD : ∀ x ∈ Ioc (0 : ℝ) 1, HasDerivWithinAt D 0 (Ioc (0 : ℝ) 1) x := by
    intro x hx
    by_cases hx1 : x = 1
    · subst x
      have hlog : HasDerivWithinAt Real.log (1 : ℝ)⁻¹ (Ioc (0 : ℝ) 1) 1 :=
        (Real.hasDerivAt_log one_ne_zero).hasDerivWithinAt
      convert hA1.sub (hlog.const_mul c) using 1
      norm_num [D]
    · have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
      have hxA : HasDerivAt A (deriv A x) x :=
        ((hA x hxIoo).differentiableAt (isOpen_Ioo.mem_nhds hxIoo)).hasDerivAt
      have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx.1)
      have h : HasDerivWithinAt D (deriv A x - c * x⁻¹) (Ioc (0 : ℝ) 1) x := by
        exact (hxA.sub (hlog.const_mul c)).hasDerivWithinAt
      convert h using 1
      have hc := hderiv x hxIoo
      field_simp [ne_of_gt hx.1]
      nlinarith
  have hDconst (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) : D x = D 1 := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun _ : ℝ => (0 : ℝ)) (C := 0)
      (fun y hy => hD y hy) (fun _ _ => by norm_num) (convex_Ioc (0 : ℝ) 1)
      (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 by norm_num) hx
    have hz : D x - D 1 = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa using h) (norm_nonneg _)
    exact sub_eq_zero.mp hz
  intro x hx
  have h := hDconst x hx
  simp [D, hA_one] at h
  linarith

/-- The normalised determinant of a two-channel colour.  Appending independent
blocks multiplies these numbers. -/
def normalizedDet (p : Fin 2 → ℝ) : ℝ := 4 * (shareMatrix p).det

/-- The colour obtained by exchanging its two channels. -/
def swapShares (p : Fin 2 → ℝ) : Fin 2 → ℝ := ![p 1, p 0]

/-- Shares realising a prescribed signed balance. -/
def sharesOfBalance (Γ : ℝ) : Fin 2 → ℝ := ![(1 + Γ) / 2, (1 - Γ) / 2]

@[simp] theorem swapShares_zero (p : Fin 2 → ℝ) : swapShares p 0 = p 1 := rfl
@[simp] theorem swapShares_one (p : Fin 2 → ℝ) : swapShares p 1 = p 0 := rfl
@[simp] theorem sharesOfBalance_zero (Γ : ℝ) : sharesOfBalance Γ 0 = (1 + Γ) / 2 := rfl
@[simp] theorem sharesOfBalance_one (Γ : ℝ) : sharesOfBalance Γ 1 = (1 - Γ) / 2 := rfl

/-- Normalisation expresses the determinant as the complement of squared balance. -/
theorem normalizedDet_eq_one_sub_balance_sq (p : Fin 2 → ℝ)
    (hnorm : p 0 + p 1 = 1) :
    normalizedDet p = 1 - (balance p) ^ 2 := by
  rw [normalizedDet, shareMatrix_det_balance p hnorm]
  ring

/-- Positive normalised colours have determinant exactly in the physical interval. -/
theorem normalizedDet_mem_Ioc (p : Fin 2 → ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : p 0 + p 1 = 1) :
    normalizedDet p ∈ Ioc (0 : ℝ) 1 := by
  constructor
  · rw [normalizedDet, shareMatrix_det_two]
    have h0 := hp 0
    have h1 := hp 1
    positivity
  · rw [normalizedDet_eq_one_sub_balance_sq p hnorm]
    have h := sq_nonneg (balance p)
    linarith

/-- The determinant is invariant under exchanging the channels. -/
theorem normalizedDet_swap (p : Fin 2 → ℝ) :
    normalizedDet (swapShares p) = normalizedDet p := by
  simp [normalizedDet, shareMatrix_det_two, mul_comm]

/-- The prescribed-balance shares really have that balance. -/
@[simp] theorem balance_sharesOfBalance (Γ : ℝ) :
    balance (sharesOfBalance Γ) = Γ := by
  simp [balance]
  ring

/-- The prescribed-balance shares are normalised. -/
@[simp] theorem sharesOfBalance_sum (Γ : ℝ) :
    sharesOfBalance Γ 0 + sharesOfBalance Γ 1 = 1 := by
  simp
  ring

/-- Any reflection strictly inside `(-1,1)` gives positive normalised shares. -/
theorem sharesOfBalance_pos {Γ : ℝ} (hΓ : |Γ| < 1) :
    ∀ i, 0 < sharesOfBalance Γ i := by
  have hlo : -1 < Γ := (neg_lt_of_abs_lt hΓ)
  have hhi : Γ < 1 := lt_of_abs_lt hΓ
  intro i
  fin_cases i <;> simp <;> linarith

/-- Consequently every positive determinant at most one is realised by a colour. -/
theorem exists_colour_with_normalizedDet (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) 1) :
    ∃ p : Fin 2 → ℝ, (∀ i, 0 < p i) ∧ p 0 + p 1 = 1 ∧ normalizedDet p = d := by
  let Γ := Real.sqrt (1 - d)
  have hnonneg : 0 ≤ 1 - d := sub_nonneg.mpr hd.2
  have hΓnonneg : 0 ≤ Γ := Real.sqrt_nonneg _
  have hΓsq : Γ ^ 2 = 1 - d := Real.sq_sqrt hnonneg
  have hsmall : 1 - d < 1 := by linarith [hd.1]
  have hΓlt : Γ < 1 := by
    have h := Real.sqrt_lt_sqrt hnonneg hsmall
    simpa [Γ] using h
  have habs : |Γ| < 1 := by simpa [abs_of_nonneg hΓnonneg] using hΓlt
  refine ⟨sharesOfBalance Γ, sharesOfBalance_pos habs, sharesOfBalance_sum Γ, ?_⟩
  rw [normalizedDet_eq_one_sub_balance_sq _ (sharesOfBalance_sum Γ),
    balance_sharesOfBalance, hΓsq]
  ring

/-- Up to the universal coefficient `c`, a composition-additive determinant
readout is the negative matrix ledger. -/
theorem determinantReadout_eq_neg_matrixLedger
    {A : ℝ → ℝ} {c : ℝ}
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      A (x * y) = A x + A y)
    (hA : DifferentiableOn ℝ A (Ioo (0 : ℝ) 1))
    (hA1 : HasDerivWithinAt A c (Ioc (0 : ℝ) 1) 1)
    (p : Fin 2 → ℝ) (hp : ∀ i, 0 < p i) (hnorm : p 0 + p 1 = 1) :
    A (normalizedDet p) = -c * matrixLedger p := by
  rw [eq_const_mul_log_of_mul_add_on_Ioc hmul hA hA1 _
    (normalizedDet_mem_Ioc p hp hnorm)]
  unfold matrixLedger normalizedDet
  ring

/-- The same readout is a fixed multiple of the scalar ledger potential;
this is the library factor `matrixLedger = 2 * scalarLedgerPotential`. -/
theorem determinantReadout_eq_scalarLedgerPotential
    {A : ℝ → ℝ} {c : ℝ}
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      A (x * y) = A x + A y)
    (hA : DifferentiableOn ℝ A (Ioo (0 : ℝ) 1))
    (hA1 : HasDerivWithinAt A c (Ioc (0 : ℝ) 1) 1)
    (p : Fin 2 → ℝ) (hp : ∀ i, 0 < p i) (hnorm : p 0 + p 1 = 1) :
    A (normalizedDet p) = (-2 * c) * φled (balance p) := by
  rw [determinantReadout_eq_neg_matrixLedger hmul hA hA1 p hp hnorm,
    matrixLedger_eq_two_scalarLedgerPotential p hnorm]
  unfold scalarLedgerPotential φled
  ring

/-- In unnormalised logarithm coordinates the result contains the exact affine
constant `log 4`; it is derived from `p₀p₁ = (1-Γ²)/4`. -/
theorem log_shareProduct_eq_affine_ledger
    (p : Fin 2 → ℝ) (hp : ∀ i, 0 < p i) (hnorm : p 0 + p 1 = 1) :
    Real.log (p 0 * p 1) = -2 * φled (balance p) - Real.log 4 := by
  have hdet : p 0 * p 1 = (1 - (balance p) ^ 2) / 4 := by
    rw [← shareMatrix_det_two, shareMatrix_det_balance p hnorm]
  have hcomp : 0 < 1 - (balance p) ^ 2 := by
    have h := (normalizedDet_mem_Ioc p hp hnorm).1
    rwa [normalizedDet_eq_one_sub_balance_sq p hnorm] at h
  rw [hdet, Real.log_div (ne_of_gt hcomp) (by norm_num : (4 : ℝ) ≠ 0)]
  unfold φled
  ring

/-- Determinant readouts are even under channel exchange, as required for a
colour readout. -/
theorem determinantReadout_even (A : ℝ → ℝ) (p : Fin 2 → ℝ) :
    A (normalizedDet (swapShares p)) = A (normalizedDet p) := by
  rw [normalizedDet_swap]

/-- The determinant coordinate for a family of independent two-channel blocks. -/
def blockDet {n : ℕ} (p : Fin n → Fin 2 → ℝ) : ℝ :=
  ∏ i, normalizedDet (p i)

/-- Independent block composition multiplies normalised determinants. -/
theorem blockDet_append {m n : ℕ} (p : Fin m → Fin 2 → ℝ)
    (q : Fin n → Fin 2 → ℝ) :
    blockDet (Fin.append p q) = blockDet p * blockDet q := by
  unfold blockDet
  rw [Fin.prod_univ_add]
  simp_rw [Fin.append_left, Fin.append_right]

/-- Products of physical determinants remain in the physical interval. -/
theorem blockDet_mem_Ioc {n : ℕ} (p : Fin n → Fin 2 → ℝ)
    (hp : ∀ i j, 0 < p i j) (hnorm : ∀ i, p i 0 + p i 1 = 1) :
    blockDet p ∈ Ioc (0 : ℝ) 1 := by
  constructor
  · apply Finset.prod_pos
    intro i _
    exact (normalizedDet_mem_Ioc (p i) (hp i) (hnorm i)).1
  · apply Finset.prod_le_one₀
    · intro i _
      exact (normalizedDet_mem_Ioc (p i) (hp i) (hnorm i)).1.le
    · intro i _
      exact (normalizedDet_mem_Ioc (p i) (hp i) (hnorm i)).2

/-- Thus `hmul` is precisely additivity of a determinant readout over
independently appended blocks. -/
theorem determinantReadout_append
    {A : ℝ → ℝ}
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      A (x * y) = A x + A y)
    {m n : ℕ} (p : Fin m → Fin 2 → ℝ) (q : Fin n → Fin 2 → ℝ)
    (hp : ∀ i j, 0 < p i j) (hnormp : ∀ i, p i 0 + p i 1 = 1)
    (hq : ∀ i j, 0 < q i j) (hnormq : ∀ i, q i 0 + q i 1 = 1) :
    A (blockDet (Fin.append p q)) = A (blockDet p) + A (blockDet q) := by
  rw [blockDet_append]
  exact hmul _ (blockDet_mem_Ioc p hp hnormp) _ (blockDet_mem_Ioc q hq hnormq)

/-- A wall observation with exactly the matrix-ledger value `log 2` fixes
the coefficient left free by the composition law. -/
theorem coefficient_eq_neg_one_of_wall_normalization
    {A : ℝ → ℝ} {c : ℝ}
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      A (x * y) = A x + A y)
    (hA : DifferentiableOn ℝ A (Ioo (0 : ℝ) 1))
    (hA1 : HasDerivWithinAt A c (Ioc (0 : ℝ) 1) 1)
    (q : Fin 2 → ℝ) (hq : ∀ i, 0 < q i) (hnorm : q 0 + q 1 = 1)
    (hwall : (balance q) ^ 2 = 1 / 2)
    (hvalue : A (normalizedDet q) = Real.log 2) : c = -1 := by
  have h := determinantReadout_eq_neg_matrixLedger hmul hA hA1 q hq hnorm
  rw [matrixLedger_at_wall q hnorm hwall, hvalue] at h
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hz : (1 + c) * Real.log 2 = 0 := by nlinarith
  have hc : 1 + c = 0 := (mul_eq_zero.mp hz).resolve_right hlog
  linarith

/-- With the wall normalisation, composition selects the matrix ledger itself,
not merely an arbitrary logarithmic scale. -/
theorem determinantReadout_eq_matrixLedger_of_wall_normalization
    {A : ℝ → ℝ} {c : ℝ}
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      A (x * y) = A x + A y)
    (hA : DifferentiableOn ℝ A (Ioo (0 : ℝ) 1))
    (hA1 : HasDerivWithinAt A c (Ioc (0 : ℝ) 1) 1)
    (q : Fin 2 → ℝ) (hq : ∀ i, 0 < q i) (hnormq : q 0 + q 1 = 1)
    (hwall : (balance q) ^ 2 = 1 / 2)
    (hvalue : A (normalizedDet q) = Real.log 2)
    (p : Fin 2 → ℝ) (hp : ∀ i, 0 < p i) (hnormp : p 0 + p 1 = 1) :
    A (normalizedDet p) = matrixLedger p := by
  have hc := coefficient_eq_neg_one_of_wall_normalization hmul hA hA1
    q hq hnormq hwall hvalue
  rw [determinantReadout_eq_neg_matrixLedger hmul hA hA1 p hp hnormp, hc]
  ring

/-- The canonical candidate satisfies every regularity and composition hypothesis;
in particular, the uniqueness theorem is non-vacuous. -/
theorem logarithmic_readout_witness :
    ∃ (A : ℝ → ℝ) (c : ℝ),
      (∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
        A (x * y) = A x + A y) ∧
      DifferentiableOn ℝ A (Ioo (0 : ℝ) 1) ∧
      HasDerivWithinAt A c (Ioc (0 : ℝ) 1) 1 := by
  refine ⟨fun x => -Real.log x, -1, ?_, ?_, ?_⟩
  · intro x hx y hy
    change -Real.log (x * y) = -Real.log x + -Real.log y
    rw [Real.log_mul (ne_of_gt hx.1) (ne_of_gt hy.1)]
    ring
  · intro x hx
    exact (Real.differentiableAt_log (ne_of_gt hx.1)).neg.differentiableWithinAt
  · convert (Real.hasDerivAt_log one_ne_zero).neg.hasDerivWithinAt using 1
    norm_num

/-- There is a positive colour at the wall, so the wall-normalisation hypothesis
is also realised inside the framework. -/
theorem wall_colour_witness :
    ∃ q : Fin 2 → ℝ, (∀ i, 0 < q i) ∧ q 0 + q 1 = 1 ∧
      (balance q) ^ 2 = 1 / 2 ∧
      (-Real.log (normalizedDet q)) = Real.log 2 := by
  refine ⟨sharesOfBalance wall, sharesOfBalance_pos abs_wall_lt_one,
    sharesOfBalance_sum wall, ?_, ?_⟩
  · rw [balance_sharesOfBalance]
    exact wall_sq
  · change matrixLedger (sharesOfBalance wall) = Real.log 2
    apply matrixLedger_at_wall
    · exact sharesOfBalance_sum wall
    · rw [balance_sharesOfBalance]
      exact wall_sq

/-- An arbitrary channel-separable readout of signed channel balances. -/
def channelSum {n : ℕ} (f : ℝ → ℝ) (Γ : Fin n → ℝ) : ℝ := ∑ i, f (Γ i)

/-- Every channel sum is append-additive, independently of its one-channel law. -/
theorem channelSum_append {m n : ℕ} (f : ℝ → ℝ)
    (Γ : Fin m → ℝ) (Δ : Fin n → ℝ) :
    channelSum f (Fin.append Γ Δ) = channelSum f Γ + channelSum f Δ := by
  unfold channelSum
  rw [Fin.sum_univ_add]
  simp_rw [Fin.append_left, Fin.append_right]

/-- Symmetry, vanishing at zero balance, and append-additivity do not by
themselves choose the logarithmic summand: the quadratic summand is a different
counterexample.  The exhibited point is the physical wall, not an endpoint. -/
theorem append_additivity_alone_does_not_select_ledger :
    ∃ f g : ℝ → ℝ,
      f 0 = 0 ∧ g 0 = 0 ∧ Function.Even f ∧ Function.Even g ∧
      (∀ {m n : ℕ} (Γ : Fin m → ℝ) (Δ : Fin n → ℝ),
        channelSum f (Fin.append Γ Δ) = channelSum f Γ + channelSum f Δ) ∧
      (∀ {m n : ℕ} (Γ : Fin m → ℝ) (Δ : Fin n → ℝ),
        channelSum g (Fin.append Γ Δ) = channelSum g Γ + channelSum g Δ) ∧
      ∃ Γ : Fin 1 → ℝ, (∀ i, |Γ i| < 1) ∧
        channelSum f Γ ≠ channelSum g Γ := by
  refine ⟨scalarLedgerPotential, fun Γ => Γ ^ 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [scalarLedgerPotential]
  · norm_num
  · intro Γ
    simp [scalarLedgerPotential]
  · intro Γ
    simp
  · intro m n Γ Δ
    exact channelSum_append _ _ _
  · intro m n Γ Δ
    exact channelSum_append _ _ _
  · refine ⟨fun _ => wall, fun _ => abs_wall_lt_one, ?_⟩
    simp only [channelSum, Fin.sum_univ_one]
    have hled : scalarLedgerPotential wall = (1 / 2 : ℝ) * Real.log 2 := by
      exact φled_wall
    rw [hled, wall_sq]
    have hlt := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at hlt
    intro h
    nlinarith

/-- The two shares associated with positive readings `I,J`. -/
def readingShares (I J : ℝ) : Fin 2 → ℝ := ![I / (I + J), J / (I + J)]

@[simp] theorem readingShares_zero (I J : ℝ) : readingShares I J 0 = I / (I + J) := rfl
@[simp] theorem readingShares_one (I J : ℝ) : readingShares I J 1 = J / (I + J) := rfl

/-- Their balance is the library scalar-ledger reflection. -/
theorem balance_readingShares (I J : ℝ) :
    balance (readingShares I J) = ElementalPeeling.LoopWall.ScalarLedger.G I J := by
  change I / (I + J) - J / (I + J) = (I - J) / (I + J)
  rw [← sub_div]

/-- Positive readings give positive shares. -/
theorem readingShares_pos {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    ∀ i, 0 < readingShares I J i := by
  intro i
  fin_cases i <;> simp <;> positivity

/-- Positive readings give normalised shares. -/
theorem readingShares_sum {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    readingShares I J 0 + readingShares I J 1 = 1 := by
  have hden : I + J ≠ 0 := ne_of_gt (add_pos hI hJ)
  change I / (I + J) + J / (I + J) = 1
  rw [← add_div, div_self hden]

/-- The normalised determinant ledger of the two readings is twice their
scalar ledger, with no extra unproved affine constant. -/
theorem matrixLedger_readingShares (I J : ℝ) (hI : 0 < I) (hJ : 0 < J) :
    matrixLedger (readingShares I J) =
      2 * ElementalPeeling.LoopWall.ScalarLedger.S I J := by
  rw [matrixLedger_eq_two_scalarLedgerPotential _ (readingShares_sum hI hJ),
    balance_readingShares,
    ElementalPeeling.LoopWall.ScalarLedger.S_eq_neg_half_log_one_sub_G_sq hI hJ]
  rfl

/-- Consequently the library `Sm = Σ S` and `matrixLedger = 2 φled` are the
same channel decomposition, with a factor two rather than competing ledgers. -/
theorem Sm_eq_half_sum_matrixLedger {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ElementalPeeling.LoopWall.MatrixLedger.Sm a b =
      (1 / 2 : ℝ) * ∑ i, matrixLedger (readingShares (a i) (b i)) := by
  rw [ElementalPeeling.LoopWall.MatrixLedger.Sm_eq_sum_scalar a b ha hb,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    ElementalPeeling.LoopWall.MatrixLedger.S (a i) (b i) =
        ElementalPeeling.LoopWall.ScalarLedger.S (a i) (b i) := rfl
    _ = (1 / 2 : ℝ) * matrixLedger (readingShares (a i) (b i)) := by
      rw [matrixLedger_readingShares _ _ (ha i) (hb i)]
      ring

/-- Block append and scalar-spacing additivity are different statements: the
former is the library theorem below; the latter is false by the library's
explicit `t₁ = t₂ = 2` counterexample. -/
theorem Sm_append_reconciled {m n : ℕ} (a₁ b₁ : Fin m → ℝ) (a₂ b₂ : Fin n → ℝ)
    (ha₁ : ∀ i, 0 < a₁ i) (hb₁ : ∀ i, 0 < b₁ i)
    (ha₂ : ∀ i, 0 < a₂ i) (hb₂ : ∀ i, 0 < b₂ i) :
    ElementalPeeling.LoopWall.MatrixLedger.Sm
        (Fin.append a₁ a₂) (Fin.append b₁ b₂) =
      ElementalPeeling.LoopWall.MatrixLedger.Sm a₁ b₁ +
        ElementalPeeling.LoopWall.MatrixLedger.Sm a₂ b₂ :=
  ElementalPeeling.LoopWall.MatrixLedger.Sm_append a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂

/-- The scalar non-additivity witness remains valid and concerns adding two
spacings in one channel, not composing independent channels. -/
theorem scalar_spacing_nonadditivity_reconciled :
    ∃ t₁ t₂ : ℝ,
      Real.log (Real.cosh ((t₁ + t₂) / 2)) ≠
        Real.log (Real.cosh (t₁ / 2)) + Real.log (Real.cosh (t₂ / 2)) :=
  ElementalPeeling.LoopWall.MatrixLedger.scalarLedger_not_additive

/-- In terms of the unnormalised product of shares, composition determines a
multiple of its logarithm plus the proved normalisation constant `c * log 4`. -/
theorem determinantReadout_eq_affine_log_shareProduct
    {A : ℝ → ℝ} {c : ℝ}
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      A (x * y) = A x + A y)
    (hA : DifferentiableOn ℝ A (Ioo (0 : ℝ) 1))
    (hA1 : HasDerivWithinAt A c (Ioc (0 : ℝ) 1) 1)
    (p : Fin 2 → ℝ) (hp : ∀ i, 0 < p i) (hnorm : p 0 + p 1 = 1) :
    A (normalizedDet p) = c * Real.log (p 0 * p 1) + c * Real.log 4 := by
  rw [eq_const_mul_log_of_mul_add_on_Ioc hmul hA hA1 _
    (normalizedDet_mem_Ioc p hp hnorm)]
  unfold normalizedDet
  rw [shareMatrix_det_two, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
    (mul_ne_zero (ne_of_gt (hp 0)) (ne_of_gt (hp 1)))]
  ring

/-- A balanced colour has zero readout, so the normalisation at `Γ = 0` is a
consequence of composition, not an extra additive constant. -/
theorem determinantReadout_zero_of_balance_zero
    {A : ℝ → ℝ} {c : ℝ}
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      A (x * y) = A x + A y)
    (hA : DifferentiableOn ℝ A (Ioo (0 : ℝ) 1))
    (hA1 : HasDerivWithinAt A c (Ioc (0 : ℝ) 1) 1)
    (p : Fin 2 → ℝ) (hp : ∀ i, 0 < p i) (hnorm : p 0 + p 1 = 1)
    (hbalance : balance p = 0) : A (normalizedDet p) = 0 := by
  rw [determinantReadout_eq_scalarLedgerPotential hmul hA hA1 p hp hnorm,
    hbalance]
  norm_num [φled]

/-- Additivity over literally appended physical colour blocks implies the
multiplicative functional equation on every pair of determinant values. -/
theorem mul_add_of_append_additive
    {A : ℝ → ℝ}
    (happend : ∀ {m n : ℕ} (p : Fin m → Fin 2 → ℝ) (q : Fin n → Fin 2 → ℝ),
      (∀ i j, 0 < p i j) → (∀ i, p i 0 + p i 1 = 1) →
      (∀ i j, 0 < q i j) → (∀ i, q i 0 + q i 1 = 1) →
      A (blockDet (Fin.append p q)) = A (blockDet p) + A (blockDet q)) :
    ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      A (x * y) = A x + A y := by
  intro x hx y hy
  obtain ⟨p, hp, hnormp, hpx⟩ := exists_colour_with_normalizedDet x hx
  obtain ⟨q, hq, hnormq, hqy⟩ := exists_colour_with_normalizedDet y hy
  let P : Fin 1 → Fin 2 → ℝ := fun _ => p
  let Q : Fin 1 → Fin 2 → ℝ := fun _ => q
  have hPpos : ∀ i j, 0 < P i j := by intro i; exact hp
  have hQpos : ∀ i j, 0 < Q i j := by intro i; exact hq
  have hPnorm : ∀ i, P i 0 + P i 1 = 1 := by intro i; exact hnormp
  have hQnorm : ∀ i, Q i 0 + Q i 1 = 1 := by intro i; exact hnormq
  have h := happend P Q hPpos hPnorm hQpos hQnorm
  rw [blockDet_append] at h
  simp only [blockDet, Fin.prod_univ_one, P, Q] at h
  simpa only [hpx, hqy] using h

/-- Classification stated directly from the independent-channel composition
principle rather than from an abstract Cauchy equation. -/
theorem eq_const_mul_log_of_append_additive
    {A : ℝ → ℝ} {c : ℝ}
    (happend : ∀ {m n : ℕ} (p : Fin m → Fin 2 → ℝ) (q : Fin n → Fin 2 → ℝ),
      (∀ i j, 0 < p i j) → (∀ i, p i 0 + p i 1 = 1) →
      (∀ i j, 0 < q i j) → (∀ i, q i 0 + q i 1 = 1) →
      A (blockDet (Fin.append p q)) = A (blockDet p) + A (blockDet q))
    (hA : DifferentiableOn ℝ A (Ioo (0 : ℝ) 1))
    (hA1 : HasDerivWithinAt A c (Ioc (0 : ℝ) 1) 1) :
    ∀ x ∈ Ioc (0 : ℝ) 1, A x = c * Real.log x :=
  eq_const_mul_log_of_mul_add_on_Ioc (mul_add_of_append_additive happend) hA hA1

end
end ElementalPeeling.LoopWall.CompositionBridge
