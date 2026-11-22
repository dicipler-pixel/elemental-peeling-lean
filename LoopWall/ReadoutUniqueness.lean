import Mathlib
import LoopWall.PeelPotential

/-!
Direction B4 of the fifth round (swarm `smws70oju`, member m5). The uniqueness of the readout: on
the whole interval `(-1,1)`, a differentiable `R` whose rate along the uniform log-ratio flow is
proportional to the peel differs from `φled` by a constant, with the exact factor `2λ/ω` (note the
sign: it is plus, not the minus I wrote in the task); the normalised case selects `φled` itself. The
constant-rate readout is `artanh`, i.e. the log-ratio, and is provably not affine in `φled`.

Written in the fifth parallel formalization round and recompiled here before acceptance;
imports hoisted, namespace prefixed to `ElementalPeeling.LoopWall`, nothing else changed.
-/

/-!
# Readouts distinguished by uniform log-ratio phase motion

For the B2 peel velocity `(ω / 2) * (1 - Γ²)`, a readout whose time
rate is proportional to `Γ` is forced to be an affine function of the
ledger.  A readout with constant time rate is instead an affine function
of `artanh Γ`.  All constancy arguments take place on the whole interval
`(-1, 1)`, and the nonzero-frequency hypothesis is explicit.
-/

namespace ElementalPeeling.LoopWall.ReadoutUniqueness

open Set
open ElementalPeeling.LoopWall.PeelPotential

noncomputable section

/-- The velocity of the peel under uniform motion of the log-ratio phase. -/
def uniformPeelVelocity (ω Γ : ℝ) : ℝ := (ω / 2) * (1 - Γ ^ 2)

/-- The two inverse-hyperbolic readout primitives have value zero at the origin. -/
@[simp] theorem φled_zero : φled 0 = 0 := by simp [φled]

/-- Membership in the open peel interval is the hypothesis used by `deriv_φled`. -/
theorem abs_lt_one_of_mem_peelInterval {Γ : ℝ} (hΓ : Γ ∈ Ioo (-1) 1) : |Γ| < 1 :=
  abs_lt.mpr hΓ

/-- The B2 velocity denominator is nonzero throughout the open peel interval. -/
theorem one_sub_sq_pos_of_mem_peelInterval {Γ : ℝ} (hΓ : Γ ∈ Ioo (-1) 1) :
    0 < 1 - Γ ^ 2 :=
  sub_pos.mpr (sq_lt_one_of_abs_lt_one (abs_lt_one_of_mem_peelInterval hΓ))

/-- The scalar ledger has exactly the rate proportional to the peel. -/
theorem ledger_uniform_rate {ω : ℝ} {Γ : ℝ} (hΓ : Γ ∈ Ioo (-1) 1) :
    deriv φled Γ * uniformPeelVelocity ω Γ = (ω / 2) * Γ := by
  rw [deriv_φled (abs_lt_one_of_mem_peelInterval hΓ), uniformPeelVelocity]
  field_simp [ne_of_gt (one_sub_sq_pos_of_mem_peelInterval hΓ)]

/-- On `(-1,1)`, `artanh` has the derivative expected of the log-ratio clock. -/
theorem hasDerivAt_artanh_on_peelInterval {Γ : ℝ} (hΓ : Γ ∈ Ioo (-1) 1) :
    HasDerivAt Real.artanh (1 / (1 - Γ ^ 2)) Γ := by
  have hnumpos : 0 < 1 + Γ := by linarith [hΓ.1]
  have hdenpos : 0 < 1 - Γ := by linarith [hΓ.2]
  have hsq : 1 - Γ ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos_of_mem_peelInterval hΓ)
  have hnum : HasDerivAt (fun x : ℝ => 1 + x) 1 Γ := by
    simpa [add_comm] using (hasDerivAt_id Γ).const_add (1 : ℝ)
  have hden : HasDerivAt (fun x : ℝ => 1 - x) (-1) Γ := by
    convert (hasDerivAt_const Γ (1 : ℝ)).sub (hasDerivAt_id Γ) using 1
    · ext x
      rfl
    · ring
  have hquot : HasDerivAt (fun x : ℝ => (1 + x) / (1 - x))
      (2 / (1 - Γ) ^ 2) Γ := by
    convert hnum.div hden (ne_of_gt hdenpos) using 1
    ring
  have hlog := hquot.log (ne_of_gt (div_pos hnumpos hdenpos))
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hhalf' : HasDerivAt
      (fun x : ℝ => (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)))
      (1 / (1 - Γ ^ 2)) Γ := by
    convert hhalf using 1
    field_simp [ne_of_gt hnumpos, ne_of_gt hdenpos, hsq]
    ring
  apply hhalf'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hΓ] with x hx
  exact Real.artanh_eq_half_log (Ioo_subset_Icc_self hx)

/-- **Ledger uniqueness.**  If a readout has rate `lam Γ` under the B2 flow,
then it is an affine function of `φled`, on the whole open peel interval.

The sign is positive: this follows directly from `deriv_φled`. -/
theorem readout_eq_affine_ledger_of_rate
    {R : ℝ → ℝ} {ω lam Γ : ℝ}
    (hR : DifferentiableOn ℝ R (Ioo (-1) 1)) (hω : ω ≠ 0)
    (hrate : ∀ x ∈ Ioo (-1) 1,
      deriv R x * uniformPeelVelocity ω x = lam * x)
    (hΓ : Γ ∈ Ioo (-1) 1) :
    R Γ = (2 * lam / ω) * φled Γ + R 0 := by
  let k : ℝ := 2 * lam / ω
  let F : ℝ → ℝ := fun x => k * φled x + R 0
  have hF : ∀ x ∈ Ioo (-1) 1,
      HasDerivAt F (k * (x / (1 - x ^ 2))) x := by
    intro x hx
    exact ((hasDerivAt_φled (abs_lt_one_of_mem_peelInterval hx)).const_mul k).add_const (R 0)
  have hderiv : Set.EqOn (deriv R) (deriv F) (Ioo (-1) 1) := by
    intro x hx
    rw [(hF x hx).deriv]
    have hb := hrate x hx
    have hden := ne_of_gt (one_sub_sq_pos_of_mem_peelInterval hx)
    dsimp [k, uniformPeelVelocity] at hb ⊢
    field_simp [hω, hden] at hb ⊢
    nlinarith
  have hzero : (0 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have hFdiff : DifferentiableOn ℝ F (Ioo (-1) 1) := by
    intro x hx
    exact (hF x hx).differentiableAt.differentiableWithinAt
  have heq := isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo hR hFdiff hderiv hzero
    (by simp [F]) hΓ
  exact heq

/-- **Clock uniqueness.**  If a readout has constant rate `c` under the B2
flow, then it is an affine function of `artanh Γ`, not of the ledger. -/
theorem readout_eq_affine_artanh_of_constant_rate
    {R : ℝ → ℝ} {ω c Γ : ℝ}
    (hR : DifferentiableOn ℝ R (Ioo (-1) 1)) (hω : ω ≠ 0)
    (hrate : ∀ x ∈ Ioo (-1) 1,
      deriv R x * uniformPeelVelocity ω x = c)
    (hΓ : Γ ∈ Ioo (-1) 1) :
    R Γ = (2 * c / ω) * Real.artanh Γ + R 0 := by
  let k : ℝ := 2 * c / ω
  let F : ℝ → ℝ := fun x => k * Real.artanh x + R 0
  have hF : ∀ x ∈ Ioo (-1) 1,
      HasDerivAt F (k * (1 / (1 - x ^ 2))) x := by
    intro x hx
    exact ((hasDerivAt_artanh_on_peelInterval hx).const_mul k).add_const (R 0)
  have hderiv : Set.EqOn (deriv R) (deriv F) (Ioo (-1) 1) := by
    intro x hx
    rw [(hF x hx).deriv]
    have hb := hrate x hx
    have hden := ne_of_gt (one_sub_sq_pos_of_mem_peelInterval hx)
    dsimp [k, uniformPeelVelocity] at hb ⊢
    field_simp [hω, hden] at hb ⊢
    nlinarith
  have hzero : (0 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have hFdiff : DifferentiableOn ℝ F (Ioo (-1) 1) := by
    intro x hx
    exact (hF x hx).differentiableAt.differentiableWithinAt
  have heq := isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo hR hFdiff hderiv hzero
    (by simp [F]) hΓ
  exact heq

/-- Positive ratios lie in the domain on which `G` is the peel reflection. -/
theorem G_mem_peelInterval {z : ℝ} (hz : 0 < z) : G z ∈ Ioo (-1) 1 := by
  have hzp : 0 < z + 1 := by linarith
  constructor
  · rw [G, lt_div_iff₀ hzp]
    linarith
  · rw [G, div_lt_one hzp]
    linarith

/-- Twice `artanh` of the peel is exactly the log-ratio coordinate. -/
theorem two_mul_artanh_G {z : ℝ} (hz : 0 < z) :
    2 * Real.artanh (G z) = Real.log z := by
  have hz1 : z + 1 ≠ 0 := by positivity
  have hratio : (1 + G z) / (1 - G z) = z := by
    rw [G]
    field_simp [hz1]
    ring
  rw [Real.artanh_eq_half_log (Ioo_subset_Icc_self (G_mem_peelInterval hz)), hratio]
  ring

/-- In the original positive-ratio coordinate, a constant-rate readout is an
affine function of `t = log z`, with coefficient `c / ω`. -/
theorem readout_eq_affine_log_ratio_of_constant_rate
    {R : ℝ → ℝ} {ω c z : ℝ}
    (hR : DifferentiableOn ℝ R (Ioo (-1) 1)) (hω : ω ≠ 0)
    (hrate : ∀ x ∈ Ioo (-1) 1,
      deriv R x * uniformPeelVelocity ω x = c)
    (hz : 0 < z) :
    R (G z) = (c / ω) * Real.log z + R 0 := by
  rw [readout_eq_affine_artanh_of_constant_rate hR hω hrate (G_mem_peelInterval hz)]
  have ht := two_mul_artanh_G hz
  have hart : Real.artanh (G z) = Real.log z / 2 := by linarith
  rw [hart]
  ring

/-- With the ledger's own normalization `(ω/2) Γ` and zero value at the
origin, the unique readout is exactly `φled`. -/
theorem readout_eq_ledger_of_normalized_rate
    {R : ℝ → ℝ} {ω Γ : ℝ}
    (hR : DifferentiableOn ℝ R (Ioo (-1) 1)) (hω : ω ≠ 0)
    (hrate : ∀ x ∈ Ioo (-1) 1,
      deriv R x * uniformPeelVelocity ω x = (ω / 2) * x)
    (hzero : R 0 = 0) (hΓ : Γ ∈ Ioo (-1) 1) :
    R Γ = φled Γ := by
  have h := readout_eq_affine_ledger_of_rate hR hω hrate hΓ
  rw [hzero, add_zero] at h
  have hcoeff : 2 * (ω / 2) / ω = 1 := by field_simp [hω]
  rw [hcoeff, one_mul] at h
  exact h

/-- At zero frequency, the proportional-rate hypothesis only says `lam = 0`. -/
theorem proportional_rate_forces_zero_coefficient_at_zero_frequency
    {R : ℝ → ℝ} {lam : ℝ}
    (hrate : ∀ x ∈ Ioo (-1) 1,
      deriv R x * uniformPeelVelocity 0 x = lam * x) :
    lam = 0 := by
  have h := hrate (1 / 2 : ℝ) (by norm_num)
  simp [uniformPeelVelocity] at h
  linarith

/-- Zero-frequency nonuniqueness, explicitly: the identity readout satisifies
`lam = 0`, but is not equal to its value at the origin throughout the interval. -/
theorem zero_frequency_identity_counterexample :
    ∃ R : ℝ → ℝ, DifferentiableOn ℝ R (Ioo (-1) 1) ∧
      (∀ x ∈ Ioo (-1) 1,
        deriv R x * uniformPeelVelocity 0 x = (0 : ℝ) * x) ∧
      R (1 / 2 : ℝ) ≠ (2 * (0 : ℝ) / 0) * φled (1 / 2 : ℝ) + R 0 := by
  refine ⟨id, differentiable_id.differentiableOn, ?_, ?_⟩
  · intro x hx
    simp [uniformPeelVelocity]
  · norm_num

/-- `artanh` is odd on the open peel interval. -/
theorem artanh_neg_on_peelInterval {Γ : ℝ} (hΓ : Γ ∈ Ioo (-1) 1) :
    Real.artanh (-Γ) = -Real.artanh Γ := by
  have hnumpos : 0 < 1 + Γ := by linarith [hΓ.1]
  have hdenpos : 0 < 1 - Γ := by linarith [hΓ.2]
  have hneg : -Γ ∈ Ioo (-1 : ℝ) 1 := by constructor <;> linarith [hΓ.1, hΓ.2]
  rw [Real.artanh_eq_half_log (Ioo_subset_Icc_self hneg),
    Real.artanh_eq_half_log (Ioo_subset_Icc_self hΓ)]
  have hratio : (1 + -Γ) / (1 - -Γ) = ((1 + Γ) / (1 - Γ))⁻¹ := by
    field_simp [ne_of_gt hnumpos, ne_of_gt hdenpos]
    ring
  rw [hratio, Real.log_inv]
  ring

/-- The ledger is even, whereas the log-ratio clock is odd. -/
@[simp] theorem φled_neg (Γ : ℝ) : φled (-Γ) = φled Γ := by
  simp [φled]

/-- The clock is not an affine rescaling of the ledger on `(-1,1)`.
The proof uses exact symmetry about zero and strict positivity at the wall. -/
theorem artanh_not_affine_ledger :
    ¬ ∃ a b : ℝ, ∀ Γ ∈ Ioo (-1) 1, Real.artanh Γ = a * φled Γ + b := by
  rintro ⟨a, b, h⟩
  have hzero : (0 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have h0 := h 0 hzero
  simp only [Real.artanh_zero, φled_zero, mul_zero, zero_add] at h0
  have hb : b = 0 := by linarith
  have hw : wall ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp abs_wall_lt_one
  have hnw : -wall ∈ Ioo (-1 : ℝ) 1 :=
    abs_lt.mp (by simpa using abs_wall_lt_one)
  have hwpos : 0 < wall := by
    rw [wall]
    positivity
  have hawpos : 0 < Real.artanh wall := Real.artanh_pos ⟨hwpos, hw.2⟩
  have hp := h wall hw
  have hn := h (-wall) hnw
  rw [artanh_neg_on_peelInterval hw, φled_neg, hb, add_zero] at hn
  rw [hb, add_zero] at hp
  linarith

/-- The stated rate law is concretely satisfiable by the ledger itself at
`ω = 2`, `lam = 1`. -/
theorem ledger_unit_rate_witness {Γ : ℝ} (hΓ : Γ ∈ Ioo (-1) 1) :
    deriv φled Γ * uniformPeelVelocity 2 Γ = (1 : ℝ) * Γ := by
  simpa using (ledger_uniform_rate (ω := (2 : ℝ)) hΓ)

/-- Hence the negative sign in the initially proposed formula is false,
already at the wall: the positive-rate witness `R = φled`, `ω = 2`,
`lam = 1` cannot equal minus itself. -/
theorem negative_ledger_sign_is_false_at_wall :
    φled wall ≠ -(2 * (1 : ℝ) / 2) * φled wall + φled 0 := by
  have hw : φled wall = (1 / 2 : ℝ) * Real.log 2 := φled_wall
  rw [hw, φled_zero]
  norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end

end ElementalPeeling.LoopWall.ReadoutUniqueness
