import Mathlib

/-!
# The linear observer: which readouts close under the dynamics

Direction D1.  `observer_iff`: a compressed linear observer `M` with `M ∘ R = R ∘ L` exists iff
`R` vanishes on `ker R`; the reverse direction constructs `M` through the quotient and
`LinearMap.exists_extend`.  The module also proves that the literal family `ker (R ∘ L^n)` is NOT
a decreasing filtration and that `⋂_n ker (R L^n) = ker (R L^(d−1))` is false (`rawKer_*`), then
proves the correct statements for the cumulative family `obsKer n = ⋂_{k≤n} ker (R L^k)`, including
Cayley–Hamilton stabilisation `iInf_obsKer_eq` at `finrank − 1`.

Written in the parallel formalization round (swarm `smws25izm`, direction m6),
then recompiled and reviewed here; namespace and header added, trailing `#print axioms` lines
removed because `scripts/verify.py` audits every named theorem.  See PROVENANCE.md.
-/

/-!
# Direction D1: the linear-observer criterion

The first theorem is valid without finite-dimensionality. For the filtration in
part (ii), the literal kernels `ker (R ∘ L^n)` do **not** form a decreasing
filtration. Below we first state the literal definition, then provide explicit
counterexamples. The corrected `obsKer` uses all readouts through time `n`.
Its stabilization uses Cayley--Hamilton.
-/

namespace ElementalPeeling.LoopWall.Observer

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}
variable [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- A readout admits a linear compressed observer iff its kernel is invariant
under the dynamics. -/
theorem observer_iff (L : V →ₗ[K] V) (R : V →ₗ[K] W) :
    (∃ M : W →ₗ[K] W, ∀ x, M (R x) = R (L x)) ↔
      (∀ x, R x = 0 → R (L x) = 0) := by
  constructor
  · rintro ⟨M, hM⟩ x hx
    rw [← hM x, hx, map_zero]
  · intro h
    have hker : LinearMap.ker R ≤ LinearMap.ker (R.comp L) := by
      intro x hx
      exact h x hx
    let q : (V ⧸ LinearMap.ker R) →ₗ[K] W :=
      (LinearMap.ker R).liftQ (R.comp L) hker
    let r : LinearMap.range R →ₗ[K] W :=
      q.comp R.quotKerEquivRange.symm.toLinearMap
    obtain ⟨M, hM⟩ := LinearMap.exists_extend r
    refine ⟨M, fun x => ?_⟩
    let y : LinearMap.range R := ⟨R x, ⟨x, rfl⟩⟩
    have hx := LinearMap.congr_fun hM y
    have he : R.quotKerEquivRange.symm y = (LinearMap.ker R).mkQ x := by
      exact R.quotKerEquivRange_symm_apply_image x y.property
    simp only [r, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at hx
    change M (R x) = q (R.quotKerEquivRange.symm y) at hx
    rw [he] at hx
    exact hx

end ElementalPeeling.LoopWall.Observer

namespace ElementalPeeling.LoopWall.Observer

variable {K : Type u} {V : Type v} {W : Type w}
variable [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- The literal, uncorrected family of kernels appearing in D1(ii). -/
def rawKer (L : V →ₗ[K] V) (R : V →ₗ[K] W) (n : ℕ) : Submodule K V :=
  LinearMap.ker (R.comp (L ^ n))

/-- Corrected observable kernels: all readouts at times `0, ..., n` vanish.
This is the standard observability filtration, rather than the literal
single-kernel family `rawKer`. -/
def obsKer (L : V →ₗ[K] V) (R : V →ₗ[K] W) (n : ℕ) : Submodule K V :=
  ⨅ k : Fin (n + 1), rawKer L R k

@[simp] theorem mem_obsKer (L : V →ₗ[K] V) (R : V →ₗ[K] W) (n : ℕ) (x : V) :
    x ∈ obsKer L R n ↔ ∀ k : Fin (n + 1), R ((L ^ (k : ℕ)) x) = 0 := by
  simp [obsKer, rawKer, LinearMap.mem_ker]

/-- With the corrected definition, larger time windows give smaller kernels. -/
theorem obsKer_antitone (L : V →ₗ[K] V) (R : V →ₗ[K] W) :
    Antitone (obsKer L R) := by
  intro m n hmn x hx
  rw [mem_obsKer] at hx ⊢
  intro k
  exact hx ⟨k, by omega⟩

/-- The valid mapping direction for the observability filtration is
`L : N(n+1) → N n`, the reverse of the direction printed in D1(ii). -/
theorem map_mem_obsKer_of_mem_succ (L : V →ₗ[K] V) (R : V →ₗ[K] W)
    (n : ℕ) (x : V) (hx : x ∈ obsKer L R (n + 1)) : L x ∈ obsKer L R n := by
  rw [mem_obsKer] at hx ⊢
  intro k
  have hk := hx ⟨(k : ℕ) + 1, by omega⟩
  simpa [pow_succ, Module.End.mul_apply] using hk

/-- If all readouts through dimension `d-1` vanish, then the readout of
the evaluation of any polynomial of degree below `d` also vanishes. -/
theorem readout_aeval_eq_zero [FiniteDimensional K V]
    (L : V →ₗ[K] V) (R : V →ₗ[K] W)
    {p : Polynomial K} {d : ℕ} (hp : p.natDegree < d) (x : V)
    (hx : ∀ k : Fin d, R ((L ^ (k : ℕ)) x) = 0) :
    R ((Polynomial.aeval L p) x) = 0 := by
  rw [Polynomial.aeval_eq_sum_range' hp]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro k hk
  have hklt : k < d := Finset.mem_range.mp hk
  rw [hx ⟨k, hklt⟩]
  simp

/-- **Cayley--Hamilton stabilization.** For the corrected cumulative
observable kernels, the infinite intersection stabilizes at `d-1` in
finite dimension `d`. -/
theorem iInf_obsKer_eq [FiniteDimensional K V]
    (L : V →ₗ[K] V) (R : V →ₗ[K] W) :
    (⨅ n : ℕ, obsKer L R n) = obsKer L R (Module.finrank K V - 1) := by
  set d := Module.finrank K V with hd
  by_cases hd0 : d = 0
  · have hz : ∀ x : V, x = 0 := finrank_zero_iff_forall_zero.mp (by simpa [d] using hd0)
    have htop (n : ℕ) : obsKer L R n = ⊤ := by
      apply top_unique
      intro x _
      rw [mem_obsKer]
      intro k
      rw [hz x]
      simp
    simp [htop]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hchar : L.charpoly.natDegree = d := by
      simpa [d] using (LinearMap.charpoly_natDegree L)
    have hne : L.charpoly ≠ 1 := by
      intro h
      have hh := congrArg Polynomial.natDegree h
      rw [hchar] at hh
      have : d = 0 := by simpa using hh
      exact hd0 this
    apply le_antisymm
    · exact iInf_le _ _
    · refine le_iInf fun n => ?_
      intro x hx
      rw [mem_obsKer] at hx ⊢
      intro k
      have hx' : ∀ j : Fin d, R ((L ^ (j : ℕ)) x) = 0 := by
        intro j
        exact hx ⟨j, by omega⟩
      have hp : ((Polynomial.X ^ (k : ℕ)) %ₘ L.charpoly).natDegree < d := by
        rw [← hchar]
        exact Polynomial.natDegree_modByMonic_lt _ L.charpoly_monic hne
      rw [L.pow_eq_aeval_mod_charpoly]
      exact readout_aeval_eq_zero L R hp x hx'

/-- First-coordinate readout on the plane. -/
def badR : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The planar map `(x,y) ↦ (y,y)`. It is a counterexample to every
assertion in the literal D1(ii). -/
def badL : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (x.2, x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `rawKer` need not be antitone: here `(1,0)` is in `N 1` but not `N 0`. -/
theorem rawKer_not_antitone : ¬ Antitone (rawKer badL badR) := by
  intro h
  have hx1 : (1, 0) ∈ rawKer badL badR 1 := by
    norm_num [rawKer, badR, badL, LinearMap.mem_ker]
  have hx0 := h (Nat.zero_le 1) hx1
  norm_num [rawKer, badR, badL, LinearMap.mem_ker] at hx0

/-- The stated mapping direction is false: `x ∈ N n` does not imply
`L x ∈ N (n+1)`. -/
theorem rawKer_map_direction_false :
    ¬ (∀ (n : ℕ) (x : ℝ × ℝ), x ∈ rawKer badL badR n →
      badL x ∈ rawKer badL badR (n + 1)) := by
  intro h
  have hx0 : (0, 1) ∈ rawKer badL badR 0 := by
    norm_num [rawKer, badR, badL, LinearMap.mem_ker]
  have hx1 := h 0 (0, 1) hx0
  norm_num [rawKer, badR, badL, LinearMap.mem_ker] at hx1

/-- In dimension two, the whole intersection is not `N (2-1) = N 1`.
Indeed `(1,0)` belongs to the right side but not to `N 0`. -/
theorem rawKer_intersection_false :
    (⨅ n : ℕ, rawKer badL badR n) ≠
      rawKer badL badR (Module.finrank ℝ (ℝ × ℝ) - 1) := by
  have hd : Module.finrank ℝ (ℝ × ℝ) - 1 = 1 := by norm_num
  rw [hd]
  intro heq
  have hx1 : (1, 0) ∈ rawKer badL badR 1 := by
    norm_num [rawKer, badR, badL, LinearMap.mem_ker]
  have hall : (1, 0) ∈ (⨅ n : ℕ, rawKer badL badR n) := by
    rw [heq]
    exact hx1
  have hx0 := (iInf_le (fun n : ℕ => rawKer badL badR n) 0) hall
  norm_num [rawKer, badR, badL, LinearMap.mem_ker] at hx0

/-- The swap dynamics for the two-by-two falsifier. -/
def swapL : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The first-coordinate projection, regarded as a `1 × 2` matrix. -/
def firstRow : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

/-- The compressed first power vanishes: `R L Rᴴ = 0`. -/
theorem compressed_swap_first : firstRow * swapL * firstRow.conjTranspose = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [firstRow, swapL, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]

/-- The compressed second power is the identity: `R L² Rᴴ = 1`. -/
theorem compressed_swap_second : firstRow * (swapL ^ 2) * firstRow.conjTranspose = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [firstRow, swapL, Matrix.mul_apply, Fin.sum_univ_two, pow_two,
    Matrix.conjTranspose_apply]

/-- Consequently, squaring the retained one-step compressed operator cannot
recover the retained readout of the square. -/
theorem compressed_swap_square_disagrees :
    (firstRow * swapL * firstRow.conjTranspose) ^ 2 ≠ firstRow * (swapL ^ 2) * firstRow.conjTranspose := by
  rw [compressed_swap_first, compressed_swap_second]
  norm_num

/-- The intersection of the cumulative family is the intersection of all the single-readout
kernels, so `iInf_obsKer_eq` is a statement about `⋂ n, ker (R ∘ L^n)` — the object the paper
calls `N_∞`. -/
theorem iInf_obsKer_eq_iInf_rawKer {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (L : V →ₗ[K] V) (R : V →ₗ[K] W) :
    (⨅ n : ℕ, obsKer L R n) = (⨅ n : ℕ, rawKer L R n) := by
  refine le_antisymm ?_ ?_
  · apply le_iInf
    intro n
    exact (iInf_le (fun k : ℕ => obsKer L R k) n).trans
      (iInf_le (fun k : Fin (n + 1) => rawKer L R k) ⟨n, Nat.lt_succ_self n⟩)
  · apply le_iInf
    intro n
    rw [obsKer]
    exact le_iInf fun k => iInf_le (fun m : ℕ => rawKer L R m) (k : ℕ)

/-- **The paper's stabilisation, stated for the literal kernels.**  In finite dimension `d`, the
intersection of all the single-readout kernels is the cumulative kernel through `d − 1`. -/
theorem iInf_rawKer_eq [FiniteDimensional K V] (L : V →ₗ[K] V) (R : V →ₗ[K] W) :
    (⨅ n : ℕ, rawKer L R n) = obsKer L R (Module.finrank K V - 1) := by
  rw [← iInf_obsKer_eq_iInf_rawKer L R, iInf_obsKer_eq]

end ElementalPeeling.LoopWall.Observer
