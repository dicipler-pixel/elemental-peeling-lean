import DiracTime.PredictiveQuotient
import LoopWall.Wall

/-!
# Predictive quotients of explicit peel models

The loop-wall repository defines ratios and ledgers, but no continuation/readout pair.
This file supplies explicit pairs and computes their predictive quotients.  The scalar
multiplicative model is the literal ladder `I_{n+1} = z I_n`, observed by its present
reading.  Later sections distinguish that model from optional alternative readouts.
-/

namespace PeelPredictive

open DiracTime.PredictiveQuotient
open ElementalPeeling.LoopWall.Ledger

universe u v

/-- The quotient by the zero submodule is linearly equivalent to the original space. -/
noncomputable def quotientBotLinearEquiv {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] : (V ⧸ (⊥ : Submodule K V)) ≃ₗ[K] V := by
  simpa using
    ((LinearMap.id : V →ₗ[K] V).quotKerEquivRange.trans
      (LinearEquiv.ofTop _ (by simp)))

/-- A zero unobservable subspace preserves predictor dimension. -/
theorem finrank_quotient_of_unobservable_eq_bot {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (L : V →ₗ[K] V) (R : V →ₗ[K] W)
    (h : unobservable L R = ⊥) :
    Module.finrank K (V ⧸ unobservable L R) = Module.finrank K V := by
  rw [h]
  exact quotientBotLinearEquiv.finrank_eq

/-- If everything is unobservable, the predictor is zero-dimensional. -/
theorem finrank_quotient_of_unobservable_eq_top {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (L : V →ₗ[K] V) (R : V →ₗ[K] W)
    (h : unobservable L R = ⊤) :
    Module.finrank K (V ⧸ unobservable L R) = 0 := by
  rw [h, Module.finrank_zero_iff]
  exact Submodule.Quotient.subsingleton_iff.mpr rfl

/-- A surjective scalar readout whose kernel is already predictively closed has a
one-dimensional predictive quotient. -/
theorem finrank_quotient_of_unobservable_eq_ker {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (L : V →ₗ[K] V) (R : V →ₗ[K] K) (hR : Function.Surjective R)
    (h : unobservable L R = LinearMap.ker R) :
    Module.finrank K (V ⧸ unobservable L R) = 1 := by
  rw [h]
  calc
    Module.finrank K (V ⧸ LinearMap.ker R) = Module.finrank K (LinearMap.range R) :=
      R.quotKerEquivRange.finrank_eq
    _ = Module.finrank K K :=
      (LinearEquiv.ofTop (LinearMap.range R) (LinearMap.range_eq_top.mpr hR)).finrank_eq
    _ = 1 := Module.finrank_self K

/-- Scalar continuation `x ↦ z * x`: one rung of the multiplicative peel ladder. -/
def peelContinuation (z : ℝ) : ℝ →ₗ[ℝ] ℝ := z • LinearMap.id

@[simp] theorem peelContinuation_apply (z x : ℝ) : peelContinuation z x = z * x := rfl

/-- Iterating the scalar continuation gives the literal geometric ladder. -/
@[simp] theorem peelContinuation_pow_apply (z x : ℝ) (n : ℕ) :
    (peelContinuation z ^ n) x = z ^ n * x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, peelContinuation_apply, ih, pow_succ]
      ring

/-- A scalar gate on the present reading.  It is linear in the state; the coefficient
is a model parameter, not a state variable. -/
def gatedReadout (r : ℝ) : ℝ →ₗ[ℝ] ℝ := r • LinearMap.id

@[simp] theorem gatedReadout_apply (r x : ℝ) : gatedReadout r x = r * x := rfl

/-- A nonzero scalar gate is injective, so the time-zero term makes every future
state observable. -/
theorem unobservable_gated_of_ne_zero (L : ℝ →ₗ[ℝ] ℝ) {r : ℝ} (hr : r ≠ 0) :
    unobservable L (gatedReadout r) = ⊥ := by
  ext x
  rw [mem_unobservable]
  constructor
  · intro h
    have h0 := h 0
    simpa [hr] using h0
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    simp

/-- The zero gate makes every state unobservable, independently of continuation. -/
theorem unobservable_gated_zero (L : ℝ →ₗ[ℝ] ℝ) :
    unobservable L (gatedReadout 0) = ⊤ := by
  ext x
  simp [mem_unobservable]

/-- Exact predictive dimension of every scalar gated linear system. -/
theorem finrank_quotient_gated (L : ℝ →ₗ[ℝ] ℝ) (r : ℝ) :
    Module.finrank ℝ (ℝ ⧸ unobservable L (gatedReadout r)) =
      if r = 0 then 0 else 1 := by
  split_ifs with hr
  · subst r
    exact finrank_quotient_of_unobservable_eq_top L _ (unobservable_gated_zero L)
  · rw [unobservable_gated_of_ne_zero L hr]
    exact quotientBotLinearEquiv.finrank_eq.trans (Module.finrank_self ℝ)

/-- The canonical observation of the current ladder entry. -/
def presentReadout : ℝ →ₗ[ℝ] ℝ := gatedReadout 1

@[simp] theorem presentReadout_apply (x : ℝ) : presentReadout x = x := by
  simp [presentReadout]

/-- **Scalar ladder theorem.**  The minimal predictor is one-dimensional for every
ratio `z`, with no nonzeroness hypothesis and no exception at either wall. -/
theorem predictiveDimension_peel (z : ℝ) :
    Module.finrank ℝ (ℝ ⧸ unobservable (peelContinuation z) presentReadout) = 1 := by
  have h : unobservable (peelContinuation z) presentReadout = ⊥ :=
    unobservable_gated_of_ne_zero _ one_ne_zero
  exact (finrank_quotient_of_unobservable_eq_bot _ _ h).trans (Module.finrank_self ℝ)

/-- Consequently ratio-dependent continuation alone cannot produce a wall jump in
this scalar model. -/
theorem predictiveDimension_peel_independent (z w : ℝ) :
    Module.finrank ℝ (ℝ ⧸ unobservable (peelContinuation z) presentReadout) =
      Module.finrank ℝ (ℝ ⧸ unobservable (peelContinuation w) presentReadout) := by
  rw [predictiveDimension_peel, predictiveDimension_peel]

/-- The upper-wall specialization of the dimension-one theorem. -/
theorem predictiveDimension_peel_at_upper_wall :
    Module.finrank ℝ
      (ℝ ⧸ unobservable (peelContinuation (3 + 2 * Real.sqrt 2)) presentReadout) = 1 :=
  predictiveDimension_peel _

end PeelPredictive


namespace PeelPredictive

open DiracTime.PredictiveQuotient
open ElementalPeeling.LoopWall.Ledger

noncomputable section

/-- The signed margin to the squared wall, in the real-ledger coordinate. -/
def wallMargin (z : ℝ) : ℝ := gam z * gam z - 1 / 2

/-- An optional wall-gated observation.  This is a new model choice: it is not the
`presentReadout` of the original ladder, and is included to delimit what the scalar
no-jump theorem does and does not imply. -/
def wallGatedReadout (z : ℝ) : ℝ →ₗ[ℝ] ℝ := gatedReadout (wallMargin z)

/-- The gated system loses its present reading exactly on the squared wall. -/
theorem finrank_quotient_wallGated (z : ℝ) :
    Module.finrank ℝ
      (ℝ ⧸ unobservable (peelContinuation z) (wallGatedReadout z)) =
        if gam z * gam z = 1 / 2 then 0 else 1 := by
  rw [wallGatedReadout, finrank_quotient_gated]
  split_ifs with h1 h2 <;> try rfl
  all_goals
    first
    | (exfalso; exact h1 (sub_eq_zero.mpr (by assumption)))
    | (exfalso; exact h2 (sub_eq_zero.mp h1))

/-- At the transparent ratio the wall gate is nonzero and the quotient has dimension one. -/
theorem predictiveDimension_wallGated_one :
    Module.finrank ℝ
      (ℝ ⧸ unobservable (peelContinuation 1) (wallGatedReadout 1)) = 1 := by
  rw [finrank_quotient_wallGated]
  norm_num [gam]

/-- At the upper wall the same gate is zero and the quotient has dimension zero. -/
theorem predictiveDimension_wallGated_upper_wall :
    Module.finrank ℝ
      (ℝ ⧸ unobservable (peelContinuation (3 + 2 * Real.sqrt 2))
        (wallGatedReadout (3 + 2 * Real.sqrt 2))) = 0 := by
  rw [finrank_quotient_wallGated]
  have hz : 0 < (3 : ℝ) + 2 * Real.sqrt 2 := by positivity
  have hw : gam (3 + 2 * Real.sqrt 2) * gam (3 + 2 * Real.sqrt 2) = 1 / 2 :=
    (ElementalPeeling.LoopWall.Wall.wall_eq_iff _ hz).2 (Or.inl rfl)
  simp [hw]

/-- **Counterexample to an unrestricted no-jump assertion.**  Once a wall-dependent
readout is allowed, the same scalar peel continuation does have a wall rank jump. -/
theorem wallGated_counterexample :
    Module.finrank ℝ
      (ℝ ⧸ unobservable (peelContinuation 1) (wallGatedReadout 1)) = 1 ∧
    Module.finrank ℝ
      (ℝ ⧸ unobservable (peelContinuation (3 + 2 * Real.sqrt 2))
        (wallGatedReadout (3 + 2 * Real.sqrt 2))) = 0 :=
  ⟨predictiveDimension_wallGated_one, predictiveDimension_wallGated_upper_wall⟩

end
end PeelPredictive


namespace PeelPredictive

open DiracTime.PredictiveQuotient

noncomputable section

/-- Homogenization of the affine ledger update `x ↦ x + ℓ`.  The second coordinate
is the bookkeeping coordinate fixed at one on physically embedded initial states. -/
def ledgerContinuation (ell : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (x.1 + ell * x.2, x.2)
  map_add' x y := by
    apply Prod.ext <;> simp; ring
  map_smul' c x := by
    apply Prod.ext <;> simp [mul_add]; ring

/-- Observation of the first, logarithmic-ledger coordinate. -/
def ledgerReadout : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ledgerContinuation_apply (ell : ℝ) (x : ℝ × ℝ) :
    ledgerContinuation ell x = (x.1 + ell * x.2, x.2) := rfl

@[simp] theorem ledgerReadout_apply (x : ℝ × ℝ) : ledgerReadout x = x.1 := rfl

/-- The iterates are the expected affine translations in the first coordinate. -/
@[simp] theorem ledgerContinuation_pow_apply (ell : ℝ) (x : ℝ × ℝ) (n : ℕ) :
    (ledgerContinuation ell ^ n) x = (x.1 + (n : ℝ) * ell * x.2, x.2) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, ledgerContinuation_apply, ih]
      apply Prod.ext
      · simp only [Nat.cast_add, Nat.cast_one]
        ring
      · rfl

/-- With nonzero log-ratio, observations at times zero and one already recover both
homogenized coordinates. -/
theorem unobservable_ledger_of_ne_zero {ell : ℝ} (hell : ell ≠ 0) :
    unobservable (ledgerContinuation ell) ledgerReadout = ⊥ := by
  ext x
  rw [mem_unobservable]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have hx1 : x.1 = 0 := by simpa using h0
    simp only [pow_one, ledgerContinuation_apply, ledgerReadout_apply] at h1
    have hx2 : x.2 = 0 := by
      have he : ell * x.2 = 0 := by rwa [hx1, zero_add] at h1
      exact (mul_eq_zero.mp he).resolve_left hell
    have hx : x = 0 := Prod.ext hx1 hx2
    simpa using hx
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    simp

theorem unobservable_ledger_zero :
    unobservable (ledgerContinuation 0) ledgerReadout = LinearMap.ker ledgerReadout := by
  apply unobservable_eq_ker_of_closes
  intro x hx
  change ledgerReadout (ledgerContinuation 0 x) = 0
  change ledgerReadout x = 0 at hx
  simpa using hx

theorem ledgerReadout_surjective : Function.Surjective ledgerReadout :=
  fun y => ⟨(y, 0), rfl⟩

/-- Exact predictive dimension for the homogenized `ℓ`-ledger. -/
theorem predictiveDimension_ledger (ell : ℝ) :
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (ledgerContinuation ell) ledgerReadout) =
        if ell = 0 then 1 else 2 := by
  split_ifs with h
  · subst ell
    exact finrank_quotient_of_unobservable_eq_ker _ _ ledgerReadout_surjective
      unobservable_ledger_zero
  · have hb := unobservable_ledger_of_ne_zero h
    rw [hb]
    exact quotientBotLinearEquiv.finrank_eq.trans (by norm_num [Module.finrank_prod])

/-- The continuation attached to a ratio by its additive log ledger. -/
def logLedgerContinuation (z : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  ledgerContinuation (Real.log z)

/-- The additive-ledger predictor changes at the transparent ratio, not by a wall
condition: its dimension is one exactly when `log z = 0`, and two otherwise. -/
theorem predictiveDimension_logLedger (z : ℝ) :
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (logLedgerContinuation z) ledgerReadout) =
        if Real.log z = 0 then 1 else 2 :=
  predictiveDimension_ledger _

lemma log_eq_zero_iff_of_positive {z : ℝ} (hz : 0 < z) : Real.log z = 0 ↔ z = 1 := by
  constructor
  · intro h
    rcases Real.log_eq_zero.mp h with h0 | h1 | hneg
    · linarith
    · exact h1
    · linarith
  · rintro rfl
    exact Real.log_one

/-- For positive ratios the only additive-ledger rank jump is at `z = 1`. -/
theorem predictiveDimension_logLedger_of_pos {z : ℝ} (hz : 0 < z) :
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (logLedgerContinuation z) ledgerReadout) =
        if z = 1 then 1 else 2 := by
  rw [predictiveDimension_logLedger]
  by_cases h : z = 1
  · subst z
    simp
  · have hl : Real.log z ≠ 0 := fun hl => h ((log_eq_zero_iff_of_positive hz).mp hl)
    simp [h, hl]

/-- At the upper wall the additive-ledger model is two-dimensional, just as at any
other nontransparent positive ratio. -/
theorem predictiveDimension_logLedger_upper_wall :
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (logLedgerContinuation (3 + 2 * Real.sqrt 2))
        ledgerReadout) = 2 := by
  have hz : 0 < (3 : ℝ) + 2 * Real.sqrt 2 := by positivity
  rw [predictiveDimension_logLedger_of_pos hz]
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hne : (3 : ℝ) + 2 * Real.sqrt 2 ≠ 1 := by linarith
  simp [hne]

/-- At the transparent ratio the same model is one-dimensional. -/
theorem predictiveDimension_logLedger_one :
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (logLedgerContinuation 1) ledgerReadout) = 1 := by
  rw [logLedgerContinuation, Real.log_one]
  exact finrank_quotient_of_unobservable_eq_ker _ _ ledgerReadout_surjective
    unobservable_ledger_zero

end
end PeelPredictive


namespace PeelPredictive

open DiracTime.PredictiveQuotient

/-- "Minimal dimension one" in the precise sense of DiracTime's minimality theorem:
every linear summary sufficient for all future scalar-ladder observations has rank
at least one. -/
theorem one_le_finrank_range_of_sufficient_peel {S : Type*} [AddCommGroup S] [Module ℝ S]
    (z : ℝ) (F : ℝ →ₗ[ℝ] S)
    (hF : ∀ v w, F v = F w → ∀ n : ℕ,
      presentReadout ((peelContinuation z ^ n) v) =
        presentReadout ((peelContinuation z ^ n) w)) :
    1 ≤ Module.finrank ℝ (LinearMap.range F) := by
  have h := finrank_quotient_le_of_sufficient (peelContinuation z) presentReadout F hF
  rw [predictiveDimension_peel] at h
  exact h

end PeelPredictive


namespace PeelPredictive

open DiracTime.PredictiveQuotient

/-- Two scalar continuation channels. -/
def diagonalContinuation (a b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (a * x.1, b * x.2)
  map_add' x y := by
    apply Prod.ext <;> simp [mul_add]
  map_smul' c x := by
    apply Prod.ext <;> simp <;> ring

/-- A fixed, surjective observation of both channels. -/
def sumReadout : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun x := x.1 + x.2
  map_add' _ _ := by simp [add_add_add_comm]
  map_smul' _ _ := by simp [mul_add]

@[simp] theorem diagonalContinuation_apply (a b : ℝ) (x : ℝ × ℝ) :
    diagonalContinuation a b x = (a * x.1, b * x.2) := rfl

@[simp] theorem diagonalContinuation_pow_apply (a b : ℝ) (x : ℝ × ℝ) (n : ℕ) :
    (diagonalContinuation a b ^ n) x = (a ^ n * x.1, b ^ n * x.2) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, diagonalContinuation_apply, ih]
      apply Prod.ext <;> simp [pow_succ] <;> ring

/-- Distinct channel rates are separated by observations at times zero and one. -/
theorem unobservable_diagonal_of_ne {a b : ℝ} (hab : a ≠ b) :
    unobservable (diagonalContinuation a b) sumReadout = ⊥ := by
  ext x
  rw [mem_unobservable]
  constructor
  · intro h
    have h0 : x.1 + x.2 = 0 := by simpa [sumReadout] using h 0
    have h1 : a * x.1 + b * x.2 = 0 := by simpa [sumReadout] using h 1
    have he : (a - b) * x.1 = 0 := by
      calc
        (a - b) * x.1 = (a * x.1 + b * x.2) - b * (x.1 + x.2) := by ring
        _ = 0 := by rw [h0, h1]; ring
    have hx1 : x.1 = 0 := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hab)
    have hx2 : x.2 = 0 := by rw [hx1, zero_add] at h0; exact h0
    have hx : x = 0 := Prod.ext hx1 hx2
    simpa using hx
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    simp [sumReadout]

/-- Equal channel rates make the present sum a complete predictive state. -/
theorem unobservable_diagonal_self (a : ℝ) :
    unobservable (diagonalContinuation a a) sumReadout = LinearMap.ker sumReadout := by
  apply unobservable_eq_ker_of_closes
  intro x hx
  change a * x.1 + a * x.2 = 0
  change x.1 + x.2 = 0 at hx
  rw [← mul_add, hx, mul_zero]

theorem sumReadout_surjective : Function.Surjective sumReadout :=
  fun y => ⟨(y, 0), by simp [sumReadout]⟩

/-- Exact predictive dimension for two diagonal channels with sum readout. -/
theorem predictiveDimension_diagonal (a b : ℝ) :
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (diagonalContinuation a b) sumReadout) =
        if a = b then 1 else 2 := by
  split_ifs with h
  · subst b
    exact finrank_quotient_of_unobservable_eq_ker _ _ sumReadout_surjective
      (unobservable_diagonal_self a)
  · have hb := unobservable_diagonal_of_ne h
    rw [hb]
    exact quotientBotLinearEquiv.finrank_eq.trans (by norm_num [Module.finrank_prod])

/-- An auxiliary rate which collides with `z` exactly on the wall quadratic. -/
def wallCodedRate (z : ℝ) : ℝ := z + (z ^ 2 - 6 * z + 1)

/-- The ladder channel plus the auxiliary wall-coded channel. -/
def wallPairContinuation (z : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  diagonalContinuation z (wallCodedRate z)

/-- Away from the wall quadratic the auxiliary rate differs from the ladder rate. -/
theorem wallCodedRate_ne (z : ℝ) (hz : z ^ 2 - 6 * z + 1 ≠ 0) : wallCodedRate z ≠ z := by
  unfold wallCodedRate
  intro h
  apply hz
  linarith

/-- At `z = 1` this two-channel system has predictive dimension two. -/
theorem predictiveDimension_wallPair_one :
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (wallPairContinuation 1) sumReadout) = 2 := by
  rw [wallPairContinuation, predictiveDimension_diagonal]
  have h : (1 : ℝ) ≠ wallCodedRate 1 := by
    unfold wallCodedRate
    norm_num
  simp [h]

/-- At the upper wall the fixed-readout two-channel system has predictive dimension
one, because the two rates coincide there. -/
theorem predictiveDimension_wallPair_upper_wall :
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (wallPairContinuation (3 + 2 * Real.sqrt 2))
        sumReadout) = 1 := by
  rw [wallPairContinuation, predictiveDimension_diagonal]
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he : wallCodedRate (3 + 2 * Real.sqrt 2) = 3 + 2 * Real.sqrt 2 := by
    unfold wallCodedRate
    nlinarith
  simp [he]

/-- A wall rank jump with a fixed nonzero readout: no zero-readout trick is used. -/
theorem wallPair_counterexample :
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (wallPairContinuation 1) sumReadout) = 2 ∧
    Module.finrank ℝ
      ((ℝ × ℝ) ⧸ unobservable (wallPairContinuation (3 + 2 * Real.sqrt 2))
        sumReadout) = 1 :=
  ⟨predictiveDimension_wallPair_one, predictiveDimension_wallPair_upper_wall⟩

end PeelPredictive
